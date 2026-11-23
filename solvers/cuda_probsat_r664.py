"""RTX 3090 Full-Power 328-Block Pure Exponential probSAT + Elite-Cloning Hunter for R(6, 6; 4) >= 661 & >= 685!
Fixes the premature 42k-step restart cutoff of `rtx3090_cuda_r664_hunter.py` (which hit MIN_VIOL = 1 on q=659!)
by running 328 blocks (4/SM across all 82 SMs), 100% exponential probSAT (cb in [3.2..8.5]), 240,000 steps/round, and elite cloning!
"""
import hashlib
import json
import os
import sys
import time
import numpy as np
import cupy as cp
from rtx3090_cuda_r664_hunter import build_clauses_via_rust

CUDA_ELITE_R664 = r'''
extern "C" {

__device__ __forceinline__ unsigned int xorshift32(unsigned int &state) {
    unsigned int x = state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    state = x;
    return x;
}

__global__ void init_elite_walkers(
    const unsigned long long* __restrict__ clause_lo,
    const unsigned long long* __restrict__ clause_mid,
    const unsigned long long* __restrict__ clause_hi,
    const unsigned short* __restrict__ meta,
    const unsigned char* __restrict__ seed_col,
    int seed_mode,
    int n_vars,
    int n_cl,
    unsigned int base_seed,
    unsigned char* __restrict__ g_col,
    unsigned short* __restrict__ g_st,
    int* __restrict__ g_break,
    unsigned int* __restrict__ g_viol,
    int* __restrict__ g_viol_cnt,
    int max_viol
) {
    int bid = blockIdx.x;
    int tid = threadIdx.x;
    __shared__ unsigned long long s_mask[3];
    __shared__ int s_break[256];
    __shared__ int s_vcnt;

    if (tid < 256) s_break[tid] = 0;
    if (tid == 0) {
        s_vcnt = 0;
        unsigned int rng = base_seed ^ ((unsigned int)(bid + 1) * 2654435761U);
        for (int k = 0; k < 8; ++k) xorshift32(rng);
        unsigned long long m0 = 0ULL, m1 = 0ULL, m2 = 0ULL;
        g_col[bid * 256 + 0] = 0;
        bool use_elite = (seed_mode == 1 && bid < 220);
        int flips_to_do = 2 + (bid % 7); // mutate 2..8 variables out of ~138!
        int flipped_mask_idx[8];
        if (use_elite) {
            for (int f = 0; f < flips_to_do; ++f) {
                flipped_mask_idx[f] = 1 + (int)(xorshift32(rng) % (unsigned int)(n_vars - 1));
            }
        }
        for (int v = 1; v < n_vars; ++v) {
            unsigned char bit;
            if (use_elite) {
                bit = seed_col[v];
                for (int f = 0; f < flips_to_do; ++f) {
                    if (flipped_mask_idx[f] == v) bit = 1 - bit;
                }
            } else {
                bit = (unsigned char)(xorshift32(rng) & 1U);
            }
            g_col[bid * 256 + v] = bit;
            if (bit) {
                if (v < 64) m0 |= (1ULL << v);
                else if (v < 128) m1 |= (1ULL << (v - 64));
                else m2 |= (1ULL << (v - 128));
            }
        }
        s_mask[0] = m0; s_mask[1] = m1; s_mask[2] = m2;
    }
    __syncthreads();

    unsigned long long m0 = s_mask[0], m1 = s_mask[1], m2 = s_mask[2];
    unsigned short* my_st = g_st + ((size_t)bid * (size_t)n_cl);
    unsigned int* my_viol = g_viol + ((size_t)bid * (size_t)max_viol);

    for (int cid = tid; cid < n_cl; cid += blockDim.x) {
        unsigned long long s0 = m0 & clause_lo[cid];
        unsigned long long s1 = m1 & clause_mid[cid];
        unsigned long long s2 = m2 & clause_hi[cid];
        int oc = __popcll(s0) + __popcll(s1) + __popcll(s2);
        unsigned short mv = meta[cid];
        int len = mv & 15;
        int xall = mv >> 4;

        int xo = 0;
        unsigned long long rem = s0;
        while (rem) { int b = __ffsll((long long)rem) - 1; xo ^= b; rem &= rem - 1ULL; }
        rem = s1;
        while (rem) { int b = __ffsll((long long)rem) - 1; xo ^= (b + 64); rem &= rem - 1ULL; }
        rem = s2;
        while (rem) { int b = __ffsll((long long)rem) - 1; xo ^= (b + 128); rem &= rem - 1ULL; }

        my_st[cid] = (unsigned short)((xo << 4) | oc);
        if (oc == 0 || oc == len) {
            int pos = atomicAdd(&s_vcnt, 1);
            if (pos < max_viol) my_viol[pos] = (unsigned int)cid;
        } else {
            if (oc == 1) atomicAdd(&s_break[xo], 1);
            if (oc + 1 == len) atomicAdd(&s_break[xall ^ xo], 1);
        }
    }
    __syncthreads();

    if (tid < 256) g_break[bid * 256 + tid] = s_break[tid];
    if (tid == 0) g_viol_cnt[bid] = (s_vcnt < max_viol) ? s_vcnt : max_viol;
}

__global__ void step_elite_walkers(
    const unsigned long long* __restrict__ clause_lo,
    const unsigned long long* __restrict__ clause_mid,
    const unsigned long long* __restrict__ clause_hi,
    const unsigned short* __restrict__ meta,
    const unsigned int* __restrict__ adj_flat,
    const int* __restrict__ adj_off,
    int n_vars,
    int n_cl,
    int n_steps,
    int step_base,
    unsigned int slice_seed,
    unsigned char* __restrict__ g_col,
    unsigned short* __restrict__ g_st,
    int* __restrict__ g_break,
    unsigned int* __restrict__ g_viol,
    int* __restrict__ g_viol_cnt,
    int* __restrict__ g_min_viol,
    unsigned char* __restrict__ g_best_col,
    int* __restrict__ g_solved_bid,
    unsigned char* __restrict__ g_sol_col,
    int max_viol
) {
    int bid = blockIdx.x;
    int tid = threadIdx.x;

    __shared__ unsigned char s_col[256];
    __shared__ int s_break[256];
    __shared__ int s_tabu[256];
    __shared__ int s_vcnt;
    __shared__ int s_pick_v;
    __shared__ unsigned char s_old_c;
    __shared__ bool s_done;
    __shared__ float s_prob[64];
    __shared__ unsigned int s_keep[2048];
    __shared__ int s_new_vcnt;

    // 100% Pure Exponential probSAT across fine-grained cb spectrum [3.10 .. 8.38]!
    float cb = 3.10f + (float)(bid % 33) * 0.16f;

    if (tid < 64) s_prob[tid] = powf(cb, -(float)tid);
    if (tid < 256) {
        s_col[tid] = g_col[bid * 256 + tid];
        s_break[tid] = g_break[bid * 256 + tid];
        s_tabu[tid] = 0;
    }
    if (tid == 0) {
        s_vcnt = g_viol_cnt[bid];
        s_done = (*g_solved_bid >= 0);
    }
    __syncthreads();

    unsigned short* my_st = g_st + ((size_t)bid * (size_t)n_cl);
    unsigned int* my_viol = g_viol + ((size_t)bid * (size_t)max_viol);
    unsigned char* my_best = g_best_col + ((size_t)bid * 256ULL);
    unsigned int rng = slice_seed ^ ((unsigned int)(bid + 1) * 2246822519U);

    for (int stp = 1; stp <= n_steps; ++stp) {
        if (s_done) break;

        if (tid == 0) {
            int cv = s_vcnt;
            if (cv < g_min_viol[bid]) {
                g_min_viol[bid] = cv;
                if (cv <= 3) {
                    for (int v = 0; v < n_vars; ++v) my_best[v] = s_col[v];
                }
            }
            if (cv == 0) {
                int prev = atomicCAS(g_solved_bid, -1, bid);
                if (prev == -1) {
                    for (int v = 0; v < n_vars; ++v) g_sol_col[v] = s_col[v];
                }
                s_done = true;
            } else {
                unsigned int cid = my_viol[xorshift32(rng) % (unsigned int)cv];
                unsigned long long m0 = clause_lo[cid] & ~1ULL;
                unsigned long long m1 = clause_mid[cid];
                unsigned long long m2 = clause_hi[cid];

                int cands[16], bks[16], zeros[16];
                int nc = 0, nz = 0;

                unsigned long long rem = m0;
                while (rem) {
                    int v = __ffsll((long long)rem) - 1; rem &= rem - 1ULL;
                    int bk = s_break[v] > 0 ? s_break[v] : 0;
                    cands[nc] = v; bks[nc] = bk; nc++;
                    if (bk == 0) zeros[nz++] = v;
                }
                rem = m1;
                while (rem) {
                    int v = (__ffsll((long long)rem) - 1) + 64; rem &= rem - 1ULL;
                    int bk = s_break[v] > 0 ? s_break[v] : 0;
                    cands[nc] = v; bks[nc] = bk; nc++;
                    if (bk == 0) zeros[nz++] = v;
                }
                rem = m2;
                while (rem) {
                    int v = (__ffsll((long long)rem) - 1) + 128; rem &= rem - 1ULL;
                    int bk = s_break[v] > 0 ? s_break[v] : 0;
                    cands[nc] = v; bks[nc] = bk; nc++;
                    if (bk == 0) zeros[nz++] = v;
                }

                int chosen = cands[0];
                if (nz > 0) {
                    chosen = zeros[xorshift32(rng) % (unsigned int)nz];
                } else {
                    float ws[16]; float wsum = 0.0f;
                    for (int i = 0; i < nc; ++i) {
                        int bk = bks[i] < 63 ? bks[i] : 63;
                        float w = s_prob[bk];
                        if (s_tabu[cands[i]] > stp && cv <= 6) w *= 0.12f;
                        ws[i] = w; wsum += w;
                    }
                    float r = ((xorshift32(rng) & 0xFFFFFF) * (1.0f / 16777216.0f)) * wsum;
                    float acc = 0.0f;
                    chosen = cands[nc - 1];
                    for (int i = 0; i < nc; ++i) {
                        acc += ws[i];
                        if (r <= acc) { chosen = cands[i]; break; }
                    }
                }
                s_pick_v = chosen;
                s_old_c = s_col[chosen];
                s_col[chosen] = 1 - s_old_c;
                s_tabu[chosen] = stp + 4 + (int)(xorshift32(rng) & 3U);
            }
        }
        __syncthreads();
        if (s_done) break;

        int pv = s_pick_v;
        unsigned char old_c = s_old_c;
        unsigned short pv_shift = (unsigned short)(pv << 4);
        int beg = adj_off[pv];
        int end = adj_off[pv + 1];

        if (old_c == 0) {
            for (int idx = beg + tid; idx < end; idx += blockDim.x) {
                unsigned int ac = adj_flat[idx];
                unsigned short cell = my_st[ac];
                unsigned short mv = meta[ac];
                int prev_oc = cell & 15;
                int len = mv & 15;
                if (prev_oc == 1) atomicAdd(&s_break[cell >> 4], -1);
                if (prev_oc + 1 == len && prev_oc > 0) atomicAdd(&s_break[(mv ^ cell) >> 4], -1);
                unsigned short new_cell = (cell ^ pv_shift) + 1;
                my_st[ac] = new_cell;
                int new_oc = prev_oc + 1;
                if (new_oc == len) {
                    int pos = atomicAdd(&s_vcnt, 1);
                    if (pos < max_viol) my_viol[pos] = ac;
                }
                if (new_oc > 0 && new_oc < len) {
                    if (new_oc == 1) atomicAdd(&s_break[new_cell >> 4], 1);
                    if (new_oc + 1 == len) atomicAdd(&s_break[(mv ^ new_cell) >> 4], 1);
                }
            }
        } else {
            for (int idx = beg + tid; idx < end; idx += blockDim.x) {
                unsigned int ac = adj_flat[idx];
                unsigned short cell = my_st[ac];
                unsigned short mv = meta[ac];
                int prev_oc = cell & 15;
                int len = mv & 15;
                if (prev_oc == 1 && prev_oc < len) atomicAdd(&s_break[cell >> 4], -1);
                if (prev_oc + 1 == len) atomicAdd(&s_break[(mv ^ cell) >> 4], -1);
                unsigned short new_cell = (cell ^ pv_shift) - 1;
                my_st[ac] = new_cell;
                int new_oc = prev_oc - 1;
                if (new_oc == 0) {
                    int pos = atomicAdd(&s_vcnt, 1);
                    if (pos < max_viol) my_viol[pos] = ac;
                }
                if (new_oc > 0 && new_oc < len) {
                    if (new_oc == 1) atomicAdd(&s_break[new_cell >> 4], 1);
                    if (new_oc + 1 == len) atomicAdd(&s_break[(mv ^ new_cell) >> 4], 1);
                }
            }
        }
        __syncthreads();

        if (tid == 0) {
            if (s_vcnt > max_viol) s_vcnt = max_viol;
            s_new_vcnt = 0;
        }
        __syncthreads();

        int cur_len = s_vcnt;
        if (cur_len <= 2048) {
            for (int i = tid; i < cur_len; i += blockDim.x) {
                unsigned int cid = my_viol[i];
                int oc = my_st[cid] & 15;
                int len = meta[cid] & 15;
                if (oc == 0 || oc == len) {
                    int dst = atomicAdd(&s_new_vcnt, 1);
                    s_keep[dst] = cid;
                }
            }
            __syncthreads();
            int kept = s_new_vcnt;
            for (int i = tid; i < kept; i += blockDim.x) my_viol[i] = s_keep[i];
            if (tid == 0) s_vcnt = kept;
        } else if ((stp & 3) == 0) {
            if (tid == 0) {
                int w = 0;
                for (int i = 0; i < cur_len; ++i) {
                    unsigned int cid = my_viol[i];
                    int oc = my_st[cid] & 15;
                    int len = meta[cid] & 15;
                    if (oc == 0 || oc == len) my_viol[w++] = cid;
                }
                s_vcnt = w;
            }
        }
        __syncthreads();
    }

    if (tid < 256) {
        g_col[bid * 256 + tid] = s_col[tid];
        g_break[bid * 256 + tid] = s_break[tid];
    }
    if (tid == 0) g_viol_cnt[bid] = s_vcnt;
}

} // extern "C"
'''


def hunt_elite_r664(q: int, seconds: float, cache_dir: str, out_dir: str, n_blocks: int = 328):
    t_b = time.time()
    q, nv, n_cl, cls_of, lo, mid, hi, meta, adj_flat, adj_off = build_clauses_via_rust(q, cache_dir)
    build_s = time.time() - t_b

    mod = cp.RawModule(code=CUDA_ELITE_R664)
    k_init = mod.get_function("init_elite_walkers")
    k_step = mod.get_function("step_elite_walkers")

    d_lo = cp.asarray(lo)
    d_mid = cp.asarray(mid)
    d_hi = cp.asarray(hi)
    d_meta = cp.asarray(meta)
    d_adj_flat = cp.asarray(adj_flat)
    d_adj_off = cp.asarray(adj_off)

    max_viol = 65536
    d_col = cp.zeros((n_blocks, 256), dtype=cp.uint8)
    d_best_col = cp.zeros((n_blocks, 256), dtype=cp.uint8)
    d_seed = cp.zeros(256, dtype=cp.uint8)
    d_st = cp.zeros((n_blocks, n_cl), dtype=cp.uint16)
    d_break = cp.zeros((n_blocks, 256), dtype=cp.int32)
    d_viol = cp.zeros((n_blocks, max_viol), dtype=cp.uint32)
    d_vcnt = cp.zeros(n_blocks, dtype=cp.int32)
    d_min_viol = cp.full(n_blocks, n_cl, dtype=cp.int32)
    d_solved_bid = cp.full(1, -1, dtype=cp.int32)
    d_sol_col = cp.zeros(256, dtype=cp.uint8)

    t0 = time.time()
    deadline = t0 + seconds
    total_flips = 0
    restart_idx = 0
    seed_mode = 0
    global_best = n_cl
    steps_per_slice = 5000
    slices_per_restart = 48  # 240,000 steps per walker (~78.7M flips per round across 328 blocks!)

    while time.time() < deadline:
        restart_idx += 1
        seed_init = np.uint32((int(time.time() * 1000) ^ (restart_idx * 0x9E3779B9)) & 0xFFFFFFFF)
        k_init(
            (n_blocks,),
            (256,),
            (d_lo, d_mid, d_hi, d_meta, d_seed, np.int32(seed_mode), np.int32(nv), np.int32(n_cl), seed_init, d_col, d_st, d_break, d_viol, d_vcnt, np.int32(max_viol)),
        )
        for sl in range(slices_per_restart):
            if time.time() >= deadline:
                break
            sl_seed = np.uint32((int(seed_init) ^ ((sl + 1) * 0x85EBCA6B)) & 0xFFFFFFFF)
            k_step(
                (n_blocks,),
                (256,),
                (
                    d_lo, d_mid, d_hi, d_meta, d_adj_flat, d_adj_off,
                    np.int32(nv), np.int32(n_cl), np.int32(steps_per_slice), np.int32(sl * steps_per_slice),
                    sl_seed, d_col, d_st, d_break, d_viol, d_vcnt, d_min_viol, d_best_col, d_solved_bid, d_sol_col, np.int32(max_viol),
                ),
            )
            cp.cuda.Stream.null.synchronize()
            total_flips += n_blocks * steps_per_slice
            if int(d_solved_bid.get()[0]) >= 0:
                sol = d_sol_col.get()[:nv]
                dt = time.time() - t0
                table = "00" + "".join("1" if sol[cls_of[lam]] == 1 else "0" for lam in range(2, q))
                sha = hashlib.sha256(table.encode("ascii")).hexdigest()
                cert_path = os.path.join(out_dir, f"CONFIRMED_RTX3090_R664_PSL_ge_{q+2}.json")
                json.dump(
                    {
                        "name": f"F{q+1}",
                        "claim": f"R(6,6;4) >= {q + 2}",
                        "q": q,
                        "points": q + 1,
                        "uniformity": 4,
                        "sizes": [6, 6],
                        "group": f"PSL(2,{q})",
                        "num_classes": nv,
                        "table": table,
                        "tau_table": "--" + table[2:],
                        "table_sha256": sha,
                        "solve_seconds": round(dt, 3),
                        "total_flips": total_flips,
                    },
                    open(cert_path, "w", encoding="utf-8"),
                    indent=2,
                )
                print(
                    f"🏆🏆🏆 RTX 3090 ELITE WORLD_RECORD_SAT [PSL q={q} => R(6,6;4) >= {q+2}] | vars={nv} cl={n_cl} solve={dt:.2f}s flips={total_flips:,} ({total_flips/dt:,.0f} flips/s) -> {cert_path}",
                    flush=True,
                )
                return cert_path

        mins = d_min_viol.get()
        best_bid = int(np.argmin(mins))
        bv = int(mins[best_bid])
        if bv <= 3 and bv <= global_best:
            global_best = bv
            d_seed = d_best_col[best_bid].copy()
            seed_mode = 1
            print(f"  [q={q} Round {restart_idx} | {time.time()-t0:.1f}s] flips={total_flips:,} -> Elite MIN_VIOL={bv} cloned!", flush=True)

    dt = time.time() - t0
    best_v = int(d_min_viol.get().min())
    print(
        f"[RTX 3090 ELITE PSL q={q} n={q+1}] vars={nv} cl={n_cl} build={build_s:.1f}s solve={dt:.1f}s -> MIN_VIOL={best_v} flips={total_flips:,} ({total_flips/dt:,.0f} flips/s)",
        flush=True,
    )
    return None


if __name__ == "__main__":
    s_dir = sys.argv[1]
    secs = float(sys.argv[2])
    for pq in [int(x) for x in sys.argv[3:]]:
        hunt_elite_r664(pq, secs, s_dir, s_dir, n_blocks=328)
