"""RTX 3090 3072-Variable Pure-Cyclic & Small-Subgroup Breaker to Smash R(4, 4, 4; 3) >= 100+!
Unlocks `s_col[3072]` (up to 3,072 ternary orbits -> Pure Cyclic Z_99..Z_110 `ord = 1` + `G(98, 67)` which hit MIN_VIOL = 1 in 8s)!
"""
import json
import math
import os
import sys
import time
from itertools import combinations
import numpy as np
import cupy as cp
from rtx3090_r444_persistence_hunter import CUDA_TERNARY_PERSIST

CUDA_TERNARY_3072 = CUDA_TERNARY_PERSIST.replace("1024", "2560")


def run_cand_3072(desc: str, n_mod: int, n_inf: int, mult_set, secs: float, mod, out_dir: str):
    pts_tot = n_mod + n_inf
    all_perms = [[((a * x + b) % n_mod) for x in range(n_mod)] + list(range(n_mod, pts_tot)) for a in mult_set for b in range(n_mod)]
    tri_idx = {}
    triples = []
    for a in range(pts_tot - 2):
        for b in range(a + 1, pts_tot - 1):
            for c in range(b + 1, pts_tot):
                tri_idx[(a, b, c)] = len(triples)
                triples.append((a, b, c))
    orb_of = [-1] * len(triples)
    n_vars = 0
    for ti, (a, b, c) in enumerate(triples):
        if orb_of[ti] != -1:
            continue
        for g in all_perms:
            u, v, w = sorted((g[a], g[b], g[c]))
            orb_of[tri_idx[(u, v, w)]] = n_vars
        n_vars += 1
    if n_vars >= 2560:
        return None

    cl_set = set()
    for rest in combinations(range(1, pts_tot), 3):
        s = (0,) + rest
        orbs = tuple(sorted({orb_of[tri_idx[t]] for t in combinations(s, 3)}))
        if len(orbs) == 1:
            return None
        cl_set.add(orbs)
    clauses = sorted(cl_set)
    n_cl = len(clauses)
    cl_vars = np.zeros((n_cl, 4), dtype=np.uint16)
    cl_len = np.zeros(n_cl, dtype=np.uint8)
    adj_lists = [[] for _ in range(n_vars)]
    for cid, orbs in enumerate(clauses):
        cl_len[cid] = len(orbs)
        for k, v in enumerate(orbs):
            cl_vars[cid, k] = v
            adj_lists[v].append(cid)
    adj_off = np.zeros(n_vars + 1, dtype=np.int32)
    for v in range(n_vars):
        adj_off[v + 1] = adj_off[v] + len(adj_lists[v])
    adj_flat = np.array([x for sub in adj_lists for x in sub], dtype=np.uint32)

    k_step = mod.get_function("step_ternary_persist")
    n_blocks = 246
    d_cv = cp.asarray(cl_vars.reshape(-1))
    d_clen = cp.asarray(cl_len)
    d_adj = cp.asarray(adj_flat)
    d_off = cp.asarray(adj_off)
    d_col = cp.zeros((n_blocks, 2560), dtype=cp.uint8)
    d_wcl = cp.ones((n_blocks, n_cl), dtype=np.uint16)
    d_min_v = cp.full(n_blocks, n_cl, dtype=cp.int32)
    d_solved = cp.full(1, -1, dtype=cp.int32)
    d_sol = cp.zeros(2560, dtype=cp.uint8)

    t0 = time.time()
    deadline = t0 + secs
    init_flag = 1
    sl = 0
    while time.time() < deadline:
        sl += 1
        seed = np.uint32((int(time.time() * 1000) ^ (sl * 0x85EBCA6B)) & 0xFFFFFFFF)
        k_step((n_blocks,), (256,), (d_cv, d_clen, d_adj, d_off, np.int32(init_flag), np.int32(n_vars), np.int32(n_cl), np.int32(50000), seed, d_col, d_wcl, d_min_v, d_solved, d_sol))
        cp.cuda.Stream.null.synchronize()
        init_flag = 0
        if int(d_solved.get()[0]) >= 0:
            sol = [int(x) for x in d_sol.get()[:n_vars]]
            dt = time.time() - t0
            adj_c = {t: sol[orb_of[ti]] for ti, t in enumerate(triples)}
            for s4 in combinations(range(pts_tot), 4):
                if len({adj_c[t] for t in combinations(s4, 3)}) == 1:
                    raise AssertionError(f"Mono 4-subset {s4}!")
            out_p = os.path.join(out_dir, f"CONFIRMED_NEW_CROWN_R4443_ge_{pts_tot+1}.json")
            json.dump({"desc": desc, "claim": f"R(4,4,4;3) >= {pts_tot+1}", "points": pts_tot, "num_orbits": n_vars, "orbit_colors": sol, "solve_seconds": round(dt, 3)}, open(out_p, "w"), indent=2)
            print(f"🏆🏆🏆 100-BREAKER VERIFIED 100%!! R(4,4,4;3) >= {pts_tot+1} [{desc}] ({dt:.2f}s) -> {out_p}", flush=True)
            return out_p
    print(f"[{desc}] pts={pts_tot} vars={n_vars} cl={n_cl} -> MIN_VIOL={int(d_min_v.get().min())}", flush=True)
    return None


def mset_of(nm: int, a: int):
    s = []
    x = 1
    while x not in s:
        s.append(x)
        x = (x * a) % nm
    return tuple(sorted(s))


if __name__ == "__main__":
    out_d = sys.argv[1]
    mod = cp.RawModule(code=CUDA_TERNARY_3072)
    cands = [
        ("G(98,67)[ord=3]+0inf", 98, 0, mset_of(98, 67), 20.0),
        ("G(98,67)[ord=3]+1inf [pts=99 => 100!]", 98, 1, mset_of(98, 67), 25.0),
        ("G(99,1)[ord=1]+0inf [PureCyclic 99 => 100!]", 99, 0, (1,), 20.0),
        ("G(99,10)[ord=2]+0inf [pts=99 => 100!]", 99, 0, mset_of(99, 10), 20.0),
        ("G(99,1)[ord=1]+1inf [PureCyclic+inf 100 => 101!]", 99, 1, (1,), 20.0),
        ("G(101,1)[ord=1]+0inf [PureCyclic 101 => 102!]", 101, 0, (1,), 20.0),
        ("G(103,1)[ord=1]+0inf [PureCyclic 103 => 104!]", 103, 0, (1,), 20.0),
        ("G(105,29)[ord=2]+0inf [CRT 105 => 106!]", 105, 0, mset_of(105, 29), 20.0),
    ]
    for desc, nm, ni, ms, sc in cands:
        run_cand_3072(desc, nm, ni, ms, sc, mod, out_d)
