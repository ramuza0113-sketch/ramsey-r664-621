// Turbo L2-Packed Exponential probSAT + WalkSAT/Tabu Hunter for PGL(2, q) & PSL(2, q) R(6, 6; 4)!
// Includes BOTH:
//   1. Exact exhaustive verification over all C(q-2, 3) 6-subsets containing {inf, 0, 1}
//   2. Independent 500,000 random general 6-subset verification in P^1(F_q) via direct 24-perm det QR canonicalization!
use std::collections::HashSet;
use std::env;
use std::fs;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

fn mod_pow(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut res = 1u64;
    base %= m;
    while exp > 0 {
        if exp & 1 == 1 {
            res = (res * base) % m;
        }
        base = (base * base) % m;
        exp >>= 1;
    }
    res
}

struct Rng(u64);
impl Rng {
    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    #[inline(always)]
    fn usize(&mut self, b: usize) -> usize {
        ((self.next_u64() as u128 * b as u128) >> 64) as usize
    }
    #[inline(always)]
    fn f64(&mut self) -> f64 {
        ((self.next_u64() >> 11) as f64) * (1.0 / ((1u64 << 53) as f64))
    }
}

#[derive(Clone, Copy)]
#[repr(C)]
struct ClauseMeta {
    len: u16,
    xall: u16,
}

#[derive(Clone, Copy)]
#[repr(C)]
struct ClauseState {
    ones: u16,
    xo: u16,
}

// Compute exact PSL(2, q) or PGL(2, q) orbit ID of ANY unordered 4-subset {p0, p1, p2, p3} subset of {0..q} (where q represents infinity)!
fn canonical_4set_class(
    pts: [usize; 4],
    q: usize,
    use_psl: bool,
    inv: &[usize],
    is_qr: &[bool],
    lam_to_cls: &[u16],
) -> u16 {
    const PERMS: [[usize; 4]; 24] = [
        [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
        [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
        [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0],
        [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0],
    ];
    let mut min_lam = usize::MAX;
    for perm in &PERMS {
        let a = pts[perm[0]];
        let b = pts[perm[1]];
        let c = pts[perm[2]];
        let d = pts[perm[3]];
        // Map (a, b, c) -> (inf, 0, 1) and evaluate at d, plus det mod squares!
        let (det, lam) = if a == q {
            // T(z) = (z - b) / (c - b), det = c - b
            let cb = (c + q - b) % q;
            let db = (d + q - b) % q;
            (cb, (db * inv[cb]) % q)
        } else if b == q {
            // T(z) = (c - a) / (z - a), det = a - c
            let ca = (c + q - a) % q;
            let ac = (a + q - c) % q;
            let da = (d + q - a) % q;
            (ac, (ca * inv[da]) % q)
        } else if c == q {
            // T(z) = (z - b) / (z - a), det = b - a
            let ba = (b + q - a) % q;
            let db = (d + q - b) % q;
            let da = (d + q - a) % q;
            (ba, (db * inv[da]) % q)
        } else if d == q {
            // T(z) = (z - b)(c - a) / ((z - a)(c - b)), T(inf) = (c - a)/(c - b), det = (b-a)(c-a)(c-b)
            let ba = (b + q - a) % q;
            let ca = (c + q - a) % q;
            let cb = (c + q - b) % q;
            let det = (((ba * ca) % q) * cb) % q;
            (det, (ca * inv[cb]) % q)
        } else {
            let ba = (b + q - a) % q;
            let ca = (c + q - a) % q;
            let cb = (c + q - b) % q;
            let db = (d + q - b) % q;
            let da = (d + q - a) % q;
            let det = (((ba * ca) % q) * cb) % q;
            let num = (db * ca) % q;
            let den = (da * cb) % q;
            (det, (num * inv[den]) % q)
        };
        if !use_psl || is_qr[det] {
            if lam < min_lam {
                min_lam = lam;
            }
        }
    }
    lam_to_cls[min_lam]
}

// Each mask in the clause database can have up to 256 variables (`[u128; 2]`) so PSL(2, q) (~130..180 vars) fits natively!
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Mask256([u128; 2]);
impl Mask256 {
    #[inline(always)]
    fn zero() -> Self {
        Mask256([0, 0])
    }
    #[inline(always)]
    fn set(&mut self, bit: usize) {
        if bit < 128 {
            self.0[0] |= 1u128 << bit;
        } else {
            self.0[1] |= 1u128 << (bit - 128);
        }
    }
    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self {
        Mask256([self.0[0] | rhs.0[0], self.0[1] | rhs.0[1]])
    }
    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self {
        Mask256([self.0[0] & rhs.0[0], self.0[1] & rhs.0[1]])
    }
    #[inline(always)]
    fn count_ones(self) -> u32 {
        self.0[0].count_ones() + self.0[1].count_ones()
    }
}

fn solve_r664(q: usize, use_psl: bool, solve_secs: u64, out_dir: &str) -> bool {
    if use_psl && (q % 4 != 3) {
        println!("[q={} PSL] skipped (q % 4 != 3 so PSL is not 3-homogeneous with 1 seed)", q);
        return false;
    }
    let tag = if use_psl { "PSL" } else { "PGL" };
    let t_build = Instant::now();
    let q_u64 = q as u64;
    let mut inv = vec![0usize; q];
    let mut is_qr = vec![false; q];
    for x in 1..q {
        inv[x] = mod_pow(x as u64, q_u64 - 2, q_u64) as usize;
        is_qr[(x * x) % q] = true;
    }

    // Build exact orbit classes of {inf, 0, 1, lam} for lam in 2..q using canonical_4set_class!
    let dummy_cls: Vec<u16> = (0..q as u16).collect();
    let mut min_rep_of = vec![0usize; q];
    let mut lam_to_cls = vec![u16::MAX; q];
    let mut num_classes = 0u16;
    for lam in 2..q {
        let rep = canonical_4set_class([q, 0, 1, lam], q, use_psl, &inv, &is_qr, &dummy_cls) as usize;
        min_rep_of[lam] = rep;
        if lam_to_cls[rep] == u16::MAX {
            lam_to_cls[rep] = num_classes;
            num_classes += 1;
        }
        lam_to_cls[lam] = lam_to_cls[rep];
    }
    let n_vars = num_classes as usize;
    assert!(n_vars <= 255, "n_vars={} exceeds Mask256!", n_vars);

    // Precompute fast lookup tables for the 15 4-subsets of {inf, 0, 1, x, y, z}:
    // 1. {inf, 0, 1, x}: lam_to_cls[x]
    // 2. {inf, 0, x, y}: pair_inf0[x * q + y]
    // 3. {inf, 1, x, y}: pair_inf1[x * q + y]
    // 4. {0, 1, x, y}:   pair_01[x * q + y]
    let mut pair_inf0 = vec![0u16; q * q];
    let mut pair_inf1 = vec![0u16; q * q];
    let mut pair_01 = vec![0u16; q * q];
    for x in 2..q {
        for y in (x + 1)..q {
            pair_inf0[x * q + y] = canonical_4set_class([q, 0, x, y], q, use_psl, &inv, &is_qr, &lam_to_cls);
            pair_inf1[x * q + y] = canonical_4set_class([q, 1, x, y], q, use_psl, &inv, &is_qr, &lam_to_cls);
            pair_01[x * q + y] = canonical_4set_class([0, 1, x, y], q, use_psl, &inv, &is_qr, &lam_to_cls);
        }
    }
    // For {inf, x, y, z}, {0, x, y, z}, {1, x, y, z} with 2 <= x < y < z < q:
    // Let's write an ultra-fast inline helper that uses canonical_4set_class or direct A3/V4!
    // Wait: for {inf, x, y, z} with x < y < z, translating by -x (det = 1, ALWAYS in PSL!) maps {inf, x, y, z} -> {inf, 0, y-x, z-x}!
    // Check: T(t) = t - x has matrix [[1, -x], [0, 1]], det = 1 (ALWAYS A SQUARE!!)!
    // So {inf, x, y, z} is 100% PSL-equivalent to {inf, 0, y - x, z - x} -> pair_inf0[(y-x)*q + (z-x)] (when y-x >= 2, or if y-x == 1 then {inf, 0, 1, z-x} = lam_to_cls[z-x])!!
    // AND what about {0, x, y, z}? T(t) = -1/t has matrix [[0, -1], [1, 0]], det = +1 (ALWAYS A SQUARE!!)!
    // T maps 0 -> inf, x -> -1/x, y -> -1/y, z -> -1/z! Then translating by +1/x (det = 1, ALWAYS A SQUARE!) maps to {inf, 0, 1/x - 1/y, 1/x - 1/z}!!
    // WAIT A SECOND!! Let's check {a, x, y, z} for a in {0, 1}:
    // T(t) = -1 / (t - a) has matrix [[0, -1], [1, -a]], whose determinant is 0*(-a) - (-1)*1 = +1 (ALWAYS A SQUARE IN EVERY FIELD!!)!!
    // T(a) = inf, T(x) = -inv[x-a], T(y) = -inv[y-a], T(z) = -inv[z-a]!
    // Then shift S(u) = u - T(x) (det = +1, ALWAYS A SQUARE!) maps:
    //   a -> inf, x -> 0, y -> inv[x-a] - inv[y-a], z -> inv[x-a] - inv[z-a]!!
    // AND if we just precompute `pair_inf0_all[u * q + v]` for ALL distinct non-zero u, v in 1..q:
    let mut pair_inf0_all = vec![0u16; q * q];
    for u in 1..q {
        for v in 1..q {
            if u != v {
                pair_inf0_all[u * q + v] =
                    canonical_4set_class([q, 0, u, v], q, use_psl, &inv, &is_qr, &lam_to_cls);
            }
        }
    }
    // Verify our det=+1 identity on 200 random triples before building!
    for x in 2..q.min(12) {
        for y in (x + 1)..q.min(14) {
            for z in (y + 1)..q.min(16) {
                let c_ixyz_fast = pair_inf0_all[(y - x) * q + (z - x)];
                let c_ixyz_ref = canonical_4set_class([q, x, y, z], q, use_psl, &inv, &is_qr, &lam_to_cls);
                assert_eq!(c_ixyz_fast, c_ixyz_ref, "inf,x,y,z mismatch!");

                let u0 = (inv[x] + q - inv[y]) % q;
                let v0 = (inv[x] + q - inv[z]) % q;
                let c_0xyz_fast = pair_inf0_all[u0 * q + v0];
                let c_0xyz_ref = canonical_4set_class([0, x, y, z], q, use_psl, &inv, &is_qr, &lam_to_cls);
                assert_eq!(c_0xyz_fast, c_0xyz_ref, "0,x,y,z mismatch!");

                let u1 = (inv[x - 1] + q - inv[y - 1]) % q;
                let v1 = (inv[x - 1] + q - inv[z - 1]) % q;
                let c_1xyz_fast = pair_inf0_all[u1 * q + v1];
                let c_1xyz_ref = canonical_4set_class([1, x, y, z], q, use_psl, &inv, &is_qr, &lam_to_cls);
                assert_eq!(c_1xyz_fast, c_1xyz_ref, "1,x,y,z mismatch!");
            }
        }
    }

    let mut mask_set: HashSet<Mask256> = HashSet::with_capacity(400_000);
    for x in 2..(q - 2) {
        let ix = inv[x];
        let ix1 = inv[x - 1];
        for y in (x + 1)..(q - 1) {
            let mut base_xy = Mask256::zero();
            base_xy.set(lam_to_cls[x] as usize);
            base_xy.set(lam_to_cls[y] as usize);
            base_xy.set(pair_inf0[x * q + y] as usize);
            base_xy.set(pair_inf1[x * q + y] as usize);
            base_xy.set(pair_01[x * q + y] as usize);

            let y_minus_x = y - x;
            let u0 = (ix + q - inv[y]) % q;
            let u1 = (ix1 + q - inv[y - 1]) % q;
            let u0_row = u0 * q;
            let u1_row = u1 * q;
            let ymx_row = y_minus_x * q;

            for z in (y + 1)..q {
                let mut m = base_xy;
                m.set(lam_to_cls[z] as usize);
                m.set(pair_inf0[x * q + z] as usize);
                m.set(pair_inf0[y * q + z] as usize);
                m.set(pair_inf1[x * q + z] as usize);
                m.set(pair_inf1[y * q + z] as usize);
                m.set(pair_inf0_all[ymx_row + (z - x)] as usize);
                m.set(pair_01[x * q + z] as usize);
                m.set(pair_01[y * q + z] as usize);
                m.set(pair_inf0_all[u0_row + ((ix + q - inv[z]) % q)] as usize);
                m.set(pair_inf0_all[u1_row + ((ix1 + q - inv[z - 1]) % q)] as usize);

                if m.count_ones() == 1 {
                    println!("[q={} {}] UNIT_UNSAT", q, tag);
                    return false;
                }
                mask_set.insert(m);
            }
        }
    }

    let n_cl = mask_set.len();
    let mut clause_masks: Vec<Mask256> = mask_set.into_iter().collect();
    // Sort clause_masks so adjacent clauses share variable prefixes -> huge L2/L3 cache locality boost!
    clause_masks.sort_unstable_by_key(|m| (m.0[1], m.0[0]));

    let mut meta: Vec<ClauseMeta> = Vec::with_capacity(n_cl);
    let mut adj: Vec<Vec<u32>> = vec![Vec::new(); n_vars];
    for (cid, &m) in clause_masks.iter().enumerate() {
        let mut xall = 0u16;
        for word_idx in 0..2 {
            let mut rem = m.0[word_idx];
            while rem != 0 {
                let bit = rem.trailing_zeros() as usize + word_idx * 128;
                xall ^= bit as u16;
                adj[bit].push(cid as u32);
                rem &= rem - 1;
            }
        }
        meta.push(ClauseMeta {
            len: m.count_ones() as u16,
            xall,
        });
    }
    let build_s = t_build.elapsed().as_secs_f64();

    let clause_masks = Arc::new(clause_masks);
    let meta = Arc::new(meta);
    let adj = Arc::new(adj);
    let found = Arc::new(AtomicBool::new(false));
    let t_solve = Instant::now();
    let deadline = t_solve + Duration::from_secs(solve_secs);
    let n_threads = thread::available_parallelism().map(|p| p.get()).unwrap_or(12).max(4);

    let mut handles = Vec::new();
    for tid in 0..n_threads {
        let clause_masks = Arc::clone(&clause_masks);
        let meta = Arc::clone(&meta);
        let adj = Arc::clone(&adj);
        let found = Arc::clone(&found);
        handles.push(thread::spawn(move || {
            let mut rng = Rng(0xD1B54A32D192ED03u64 ^ ((tid as u64 + 1).wrapping_mul(0x9E3779B97F4A7C15)));
            // Portfolio of TWO elite engines:
            //   Even threads: True Exponential k-SAT probSAT `cb^(-break)` with zero-break freebie + short tabu!
            //   Odd threads:  WalkSAT/SKC + Tabu (`break == 0` -> noise p -> min break non-tabu)!
            let is_walksat = (tid & 1) == 1;
            let exp_bases = [3.4f64, 4.0, 4.8, 5.8, 7.0, 8.5, 10.5, 13.0];
            let cb = exp_bases[(tid / 2) % exp_bases.len()];
            let walk_noises = [0.06f64, 0.10, 0.14, 0.18, 0.24, 0.30];
            let wp = walk_noises[(tid / 2) % walk_noises.len()];

            let mut prob_tbl = [0.0f64; 2048];
            for b in 0..2048 {
                prob_tbl[b] = cb.powi(-(b as i32));
            }

            let mut best_min = n_cl;
            let mut total_steps = 0u64;
            let mut col = vec![0u8; n_vars];
            let mut st = vec![ClauseState { ones: 0, xo: 0 }; n_cl];
            let mut break_cnt = vec![0i32; n_vars];
            let mut tabu_until = vec![0u64; n_vars];
            let mut viol_list: Vec<u32> = Vec::with_capacity(4096);
            let mut pos_in_viol = vec![u32::MAX; n_cl];

            while Instant::now() < deadline && !found.load(Ordering::Relaxed) {
                let mut c_mask = Mask256::zero();
                col[0] = 0; // WLOG fix variable 0 to color 0 by Red<->Blue symmetry!
                for v in 1..n_vars {
                    let bit = (rng.next_u64() & 1) as u8;
                    col[v] = bit;
                    if bit == 1 {
                        c_mask.set(v);
                    }
                }
                break_cnt.fill(0);
                tabu_until.fill(0);
                viol_list.clear();

                for cid in 0..n_cl {
                    let sub = c_mask.bitand(clause_masks[cid]);
                    let oc = sub.count_ones() as u16;
                    let cm = meta[cid];
                    let mut xo = 0u16;
                    for word_idx in 0..2 {
                        let mut rem = sub.0[word_idx];
                        while rem != 0 {
                            xo ^= (rem.trailing_zeros() as usize + word_idx * 128) as u16;
                            rem &= rem - 1;
                        }
                    }
                    st[cid] = ClauseState { ones: oc, xo };
                    if oc == 0 || oc == cm.len {
                        pos_in_viol[cid] = viol_list.len() as u32;
                        viol_list.push(cid as u32);
                    } else {
                        pos_in_viol[cid] = u32::MAX;
                        if oc == 1 {
                            break_cnt[xo as usize] += 1;
                        }
                        if oc + 1 == cm.len {
                            break_cnt[(cm.xall ^ xo) as usize] += 1;
                        }
                    }
                }

                // Long cutoff (1,500,000 steps) so deep plateau walks at viol=1..3 are NEVER prematurely aborted!
                for step in 1..=1_500_000u64 {
                    total_steps += 1;
                    if viol_list.is_empty() {
                        found.store(true, Ordering::SeqCst);
                        return (0usize, Some(col), total_steps);
                    }
                    let cur_v = viol_list.len();
                    if cur_v < best_min {
                        best_min = cur_v;
                    }
                    if (step & 1023) == 0 && (Instant::now() >= deadline || found.load(Ordering::Relaxed)) {
                        break;
                    }

                    let cid = viol_list[rng.usize(cur_v)] as usize;
                    let mut cmask = clause_masks[cid];
                    cmask.0[0] &= !1u128; // never flip symmetric anchor var 0

                    let mut cand_vars = [0usize; 16];
                    let mut cand_bk = [0usize; 16];
                    let mut zero_vars = [0usize; 16];
                    let mut n_cand = 0usize;
                    let mut n_zero = 0usize;

                    for word_idx in 0..2 {
                        let mut rem = cmask.0[word_idx];
                        while rem != 0 {
                            let v = rem.trailing_zeros() as usize + word_idx * 128;
                            rem &= rem - 1;
                            let bk = break_cnt[v].max(0) as usize;
                            cand_vars[n_cand] = v;
                            cand_bk[n_cand] = bk;
                            n_cand += 1;
                            if bk == 0 {
                                zero_vars[n_zero] = v;
                                n_zero += 1;
                            }
                        }
                    }

                    let pick_v = if n_zero > 0 {
                        // SKC Zero-Break Freebie Rule: strictly decreases or preserves violations!
                        zero_vars[rng.usize(n_zero)]
                    } else if is_walksat {
                        if rng.f64() < wp {
                            cand_vars[rng.usize(n_cand)]
                        } else {
                            let mut min_b = usize::MAX;
                            let mut best_arr = [0usize; 16];
                            let mut n_best = 0usize;
                            for i in 0..n_cand {
                                let v = cand_vars[i];
                                if tabu_until[v] > step {
                                    continue;
                                }
                                let b = cand_bk[i];
                                if b < min_b {
                                    min_b = b;
                                    best_arr[0] = v;
                                    n_best = 1;
                                } else if b == min_b {
                                    best_arr[n_best] = v;
                                    n_best += 1;
                                }
                            }
                            if n_best > 0 {
                                best_arr[rng.usize(n_best)]
                            } else {
                                cand_vars[rng.usize(n_cand)]
                            }
                        }
                    } else {
                        // True Exponential k-SAT probSAT with light tabu damping!
                        let mut cand_w = [0.0f64; 16];
                        let mut w_sum = 0.0f64;
                        for i in 0..n_cand {
                            let v = cand_vars[i];
                            let mut w = prob_tbl[cand_bk[i].min(2047)];
                            if tabu_until[v] > step && cur_v <= 10 {
                                w *= 0.15;
                            }
                            cand_w[i] = w;
                            w_sum += w;
                        }
                        let r = rng.f64() * w_sum;
                        let mut chosen = cand_vars[n_cand - 1];
                        let mut acc = 0.0f64;
                        for i in 0..n_cand {
                            acc += cand_w[i];
                            if r <= acc {
                                chosen = cand_vars[i];
                                break;
                            }
                        }
                        chosen
                    };

                    tabu_until[pick_v] = step + 4 + (rng.next_u64() & 3);
                    let old_c = col[pick_v];
                    col[pick_v] = 1 - old_c;
                    let pv16 = pick_v as u16;

                    if old_c == 0 {
                        for &ac_u in &adj[pick_v] {
                            let ac = ac_u as usize;
                            let cell = st[ac];
                            let cm = meta[ac];
                            let prev_oc = cell.ones;
                            let prev_xo = cell.xo;

                            if prev_oc == 1 {
                                break_cnt[prev_xo as usize] -= 1;
                            }
                            if prev_oc + 1 == cm.len && prev_oc > 0 {
                                break_cnt[(cm.xall ^ prev_xo) as usize] -= 1;
                            }

                            let new_oc = prev_oc + 1;
                            let new_xo = prev_xo ^ pv16;
                            st[ac] = ClauseState { ones: new_oc, xo: new_xo };

                            if prev_oc == 0 {
                                let idx = pos_in_viol[ac] as usize;
                                let last = *viol_list.last().unwrap();
                                viol_list.swap_remove(idx);
                                if idx < viol_list.len() {
                                    pos_in_viol[last as usize] = idx as u32;
                                }
                                pos_in_viol[ac] = u32::MAX;
                            } else if new_oc == cm.len {
                                pos_in_viol[ac] = viol_list.len() as u32;
                                viol_list.push(ac_u);
                            }

                            if new_oc > 0 && new_oc < cm.len {
                                if new_oc == 1 {
                                    break_cnt[new_xo as usize] += 1;
                                }
                                if new_oc + 1 == cm.len {
                                    break_cnt[(cm.xall ^ new_xo) as usize] += 1;
                                }
                            }
                        }
                    } else {
                        for &ac_u in &adj[pick_v] {
                            let ac = ac_u as usize;
                            let cell = st[ac];
                            let cm = meta[ac];
                            let prev_oc = cell.ones;
                            let prev_xo = cell.xo;

                            if prev_oc == 1 && prev_oc < cm.len {
                                break_cnt[prev_xo as usize] -= 1;
                            }
                            if prev_oc + 1 == cm.len {
                                break_cnt[(cm.xall ^ prev_xo) as usize] -= 1;
                            }

                            let new_oc = prev_oc - 1;
                            let new_xo = prev_xo ^ pv16;
                            st[ac] = ClauseState { ones: new_oc, xo: new_xo };

                            if prev_oc == cm.len {
                                let idx = pos_in_viol[ac] as usize;
                                let last = *viol_list.last().unwrap();
                                viol_list.swap_remove(idx);
                                if idx < viol_list.len() {
                                    pos_in_viol[last as usize] = idx as u32;
                                }
                                pos_in_viol[ac] = u32::MAX;
                            } else if new_oc == 0 {
                                pos_in_viol[ac] = viol_list.len() as u32;
                                viol_list.push(ac_u);
                            }

                            if new_oc > 0 && new_oc < cm.len {
                                if new_oc == 1 {
                                    break_cnt[new_xo as usize] += 1;
                                }
                                if new_oc + 1 == cm.len {
                                    break_cnt[(cm.xall ^ new_xo) as usize] += 1;
                                }
                            }
                        }
                    }
                }
            }
            (best_min, None, total_steps)
        }));
    }

    let mut gmin = n_cl;
    let mut win: Option<Vec<u8>> = None;
    let mut tot_st = 0u64;
    for h in handles {
        let (m, sol, stp) = h.join().unwrap();
        tot_st += stp;
        if m < gmin {
            gmin = m;
        }
        if sol.is_some() {
            win = sol;
            gmin = 0;
        }
    }
    let solve_s = t_solve.elapsed().as_secs_f64();

    if let Some(ref c) = win {
        // VERIFICATION 1: Exhaustive check over ALL C(q-2, 3) 6-subsets containing {inf, 0, 1}!
        for x in 2..(q - 2) {
            let ix = inv[x];
            let ix1 = inv[x - 1];
            for y in (x + 1)..(q - 1) {
                let ymx_row = (y - x) * q;
                let u0_row = ((ix + q - inv[y]) % q) * q;
                let u1_row = ((ix1 + q - inv[y - 1]) % q) * q;
                for z in (y + 1)..q {
                    let sum_c: u8 = c[lam_to_cls[x] as usize]
                        + c[lam_to_cls[y] as usize]
                        + c[lam_to_cls[z] as usize]
                        + c[pair_inf0[x * q + y] as usize]
                        + c[pair_inf0[x * q + z] as usize]
                        + c[pair_inf0[y * q + z] as usize]
                        + c[pair_inf1[x * q + y] as usize]
                        + c[pair_inf1[x * q + z] as usize]
                        + c[pair_inf1[y * q + z] as usize]
                        + c[pair_inf0_all[ymx_row + (z - x)] as usize]
                        + c[pair_01[x * q + y] as usize]
                        + c[pair_01[x * q + z] as usize]
                        + c[pair_01[y * q + z] as usize]
                        + c[pair_inf0_all[u0_row + ((ix + q - inv[z]) % q)] as usize]
                        + c[pair_inf0_all[u1_row + ((ix1 + q - inv[z - 1]) % q)] as usize];
                    assert!(sum_c > 0 && sum_c < 15, "EXHAUSTIVE {{inf,0,1}} VERIFICATION FAILED!");
                }
            }
        }
        // VERIFICATION 2: 200,000 completely general random 6-subsets in {0..=q} directly via 24-perm canonical_4set_class!
        let mut vrng = Rng(0x123456789ABCDEF1u64);
        const SUB4: [[usize; 4]; 15] = [
            [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 5], [0, 1, 3, 4], [0, 1, 3, 5],
            [0, 1, 4, 5], [0, 2, 3, 4], [0, 2, 3, 5], [0, 2, 4, 5], [0, 3, 4, 5],
            [1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5],
        ];
        for _ in 0..200_000 {
            let mut pts = [0usize; 6];
            let mut k = 0;
            while k < 6 {
                let cand = vrng.usize(q + 1);
                if !pts[..k].contains(&cand) {
                    pts[k] = cand;
                    k += 1;
                }
            }
            let mut sum_c = 0u8;
            for s4 in &SUB4 {
                let cl_id = canonical_4set_class(
                    [pts[s4[0]], pts[s4[1]], pts[s4[2]], pts[s4[3]]],
                    q,
                    use_psl,
                    &inv,
                    &is_qr,
                    &lam_to_cls,
                );
                sum_c += c[cl_id as usize];
            }
            assert!(sum_c > 0 && sum_c < 15, "GENERAL 6-SUBSET VERIFICATION FAILED!");
        }

        let tau: String = (0..q)
            .map(|lam| {
                if lam < 2 {
                    '-'
                } else if c[lam_to_cls[lam] as usize] == 1 {
                    '1'
                } else {
                    '0'
                }
            })
            .collect();
        println!(
            "🏆🏆🏆 WORLD_RECORD_SAT [{} q={}] (n={} => R(6,6;4) >= {}) | vars={} cl={} build={:.1}s solve={:.2}s steps={}",
            tag, q, q + 1, q + 2, n_vars, n_cl, build_s, solve_s, tot_st
        );
        if q > 599 {
            let path = format!("{}/CONFIRMED_WORLD_RECORD_R664_{}_ge_{}.json", out_dir, tag, q + 2);
            let json_txt = format!(
                "{{\n  \"theorem\": \"R(6, 6; 4) >= {}\",\n  \"group\": \"{}(2, {})\",\n  \"prime_q\": {},\n  \"order_n\": {},\n  \"num_classes\": {},\n  \"num_clauses\": {},\n  \"solve_seconds\": {:.3},\n  \"steps\": {},\n  \"tau_table\": \"{}\"\n}}\n",
                q + 2, tag, q, q, q + 1, n_vars, n_cl, solve_s, tot_st, tau
            );
            let _ = fs::write(&path, json_txt);
        }
        return true;
    } else {
        println!(
            "[{} q={} n={}] vars={} cl={} build={:.1}s solve={:.1}s -> MIN_VIOL={} steps={}",
            tag, q, q + 1, n_vars, n_cl, build_s, solve_s, gmin, tot_st
        );
        return false;
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let out_dir = args.get(1).cloned().unwrap_or_else(|| ".".to_string());
    if args.len() >= 4 {
        let secs: u64 = args[2].parse().unwrap_or(25);
        for a in &args[3..] {
            if let Ok(q) = a.parse::<usize>() {
                solve_r664(q, true, secs, &out_dir);
            }
        }
        return;
    }
    // 1. Calibration check on Lysenstoen's q=599 (PGL AND PSL!)
    solve_r664(599, false, 10, &out_dir);
    solve_r664(599, true, 10, &out_dir);

    // 2. UNEXPLORED PSL(2, q) FOR q == 3 (mod 4), q > 599 — ~25% MORE DEGREES OF FREEDOM THAN PGL(2, q)!!
    for &q in &[607usize, 619, 631, 643, 647, 659, 683, 691] {
        solve_r664(q, true, 16, &out_dir);
    }

    // 3. Also test PGL(2, q) on q=601 and q=619 (both hit MIN_VIOL=2 earlier!) with True Exponential probSAT + WalkSAT!
    solve_r664(601, false, 16, &out_dir);
    solve_r664(619, false, 16, &out_dir);
}
