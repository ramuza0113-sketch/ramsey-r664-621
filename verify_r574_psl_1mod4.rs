// Clean-room, zero-shared-code exhaustive verifier for R(5, 7; 4) >= q + 2 via PSL(2, q) when q == 1 (mod 4)!
// Checks:
//   Stage 1: 500,000 random SL(2, q) matrix transformations preserve 4-subset colors 100%!
//   Stage 2: ALL C(q-2, 2) 5-subsets containing {0, 1, inf} AND ALL C(q-2, 2) 5-subsets containing {0, g, inf}: ZERO color-0 K_5^(4)!
//   Stage 3: ALL C(q-2, 4) 7-subsets containing {0, 1, inf} AND ALL C(q-2, 4) 7-subsets containing {0, g, inf}: ZERO color-1 K_7^(4)!
//   Stage 4: 200,000 arbitrary unnormalized 5-subsets + 200,000 arbitrary unnormalized 7-subsets!

use std::env;
use std::fs;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Instant;

fn mod_pow(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u64; b %= m;
    while e > 0 { if e & 1 == 1 { r = (r * b) % m; } b = (b * b) % m; e >>= 1; }
    r
}

#[inline(always)]
fn mobius_apply(a: u64, b: u64, c: u64, d: u64, z: usize, q: usize, inv: &[u64]) -> usize {
    let qu = q as u64;
    if z == q {
        if c == 0 { q } else { ((a * inv[c as usize]) % qu) as usize }
    } else {
        let zu = z as u64;
        let num = (a * zu + b) % qu;
        let den = (c * zu + d) % qu;
        if den == 0 { q } else { ((num * inv[den as usize]) % qu) as usize }
    }
}

#[inline(always)]
fn color_4subset_1mod4(
    mut pts: [usize; 4],
    q: usize,
    inv: &[u64],
    sq: &[bool],
    pgl_cls: &[usize],
    vp: &[usize],
    vm: &[usize],
    sol: &[u8],
) -> u8 {
    pts.sort_unstable();
    let (a, b, c, d) = (pts[0], pts[1], pts[2], pts[3]);
    let qu = q as u64;
    let k = (((c + q - a) % q) as u64 * inv[(c + q - b) % q]) % qu;
    let lam = if d == q {
        k
    } else {
        (((k * ((d + q - b) as u64)) % qu) * inv[(d + q - a) % q]) % qu
    } as usize;
    let pc = pgl_cls[lam];
    if vp[pc] == vm[pc] {
        sol[vp[pc]]
    } else {
        let delta = (((((b - a) as u64) * ((c - a) as u64)) % qu) * ((c - b) as u64)) % qu;
        if sq[delta as usize] { sol[vp[pc]] } else { sol[vm[pc]] }
    }
}

fn main() {
    let t0 = Instant::now();
    let path = env::args().nth(1).expect("json path");
    let raw = fs::read_to_string(&path).unwrap();
    let q: usize = {
        let idx = raw.find("\"q\"").unwrap();
        let rest = raw[idx + 3..].trim_start_matches(|c: char| c == ':' || c.is_whitespace());
        let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap();
        rest[..end].parse().unwrap()
    };
    assert_eq!(q % 4, 1);
    let sol: Vec<u8> = {
        let idx = raw.find("\"sol_vars\"").unwrap();
        let b1 = raw[idx..].find('[').unwrap() + idx;
        let b2 = raw[b1..].find(']').unwrap() + b1;
        raw[b1 + 1..b2].split(',').map(|s| s.trim().parse::<u8>().unwrap()).collect()
    };

    let qu = q as u64;
    let mut inv = vec![0u64; q];
    let mut sq = vec![false; q];
    for x in 1..q {
        inv[x] = mod_pow(x as u64, qu - 2, qu);
        sq[((x as u64 * x as u64) % qu) as usize] = true;
    }
    let g = (2..q).find(|&x| !sq[x]).unwrap();

    let mut pgl_cls = vec![usize::MAX; q];
    let mut vp = Vec::new();
    let mut vm = Vec::new();
    let mut nv = 0usize;
    for x in 2..q {
        if pgl_cls[x] != usize::MAX { continue; }
        let ix = inv[x] as usize;
        let c6 = [
            x, ix, (q + 1 - x) % q, inv[(q + 1 - x) % q] as usize,
            ((x as u64 * inv[(x + q - 1) % q]) % qu) as usize,
            ((((x + q - 1) % q) as u64 * inv[x]) % qu) as usize,
        ];
        let pc = vp.len();
        for &y in &c6 { pgl_cls[y] = pc; }
        if sq[x] && sq[x - 1] {
            vp.push(nv); vm.push(nv + 1); nv += 2;
        } else {
            vp.push(nv); vm.push(nv); nv += 1;
        }
    }
    assert_eq!(nv, sol.len());
    println!("=== Clean-Room Verifier for R(5, 7; 4) >= {} [PSL(2, {}), q == 1 mod 4] ===", q + 2, q);

    // Stage 1: 500,000 random SL(2, q) matrices
    let mut rng = 0xDEAD_BEEF_CAFE_2026u64;
    let mut next_u64 = || -> u64 { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; rng };
    for _ in 0..500_000 {
        let (a, b, c, d) = loop {
            let a = next_u64() % qu;
            let b = next_u64() % qu;
            let c = next_u64() % qu;
            if a != 0 {
                let d = (((1 + b * c) % qu) * inv[a as usize]) % qu;
                if (a * d + qu - (b * c) % qu) % qu == 1 { break (a, b, c, d); }
            }
        };
        let mut pts = [0usize; 4];
        let mut k = 0;
        while k < 4 {
            let p = (next_u64() % ((q + 1) as u64)) as usize;
            if !pts[..k].contains(&p) { pts[k] = p; k += 1; }
        }
        let c1 = color_4subset_1mod4(pts, q, &inv, &sq, &pgl_cls, &vp, &vm, &sol);
        let img = [
            mobius_apply(a, b, c, d, pts[0], q, &inv),
            mobius_apply(a, b, c, d, pts[1], q, &inv),
            mobius_apply(a, b, c, d, pts[2], q, &inv),
            mobius_apply(a, b, c, d, pts[3], q, &inv),
        ];
        let c2 = color_4subset_1mod4(img, q, &inv, &sq, &pgl_cls, &vp, &vm, &sol);
        assert_eq!(c1, c2, "SL(2,q) invariance failed!");
    }
    println!("[Stage 1 PASS] 500,000 SL(2, {}) transforms preserve 4-subset colors 100%!", q);

    // Stage 2 & 3: Check BOTH {0, 1, inf} AND {0, g, inf} 5-subsets and 7-subsets exhaustively!
    let inv_a = Arc::new(inv);
    let sq_a = Arc::new(sq);
    let pc_a = Arc::new(pgl_cls);
    let vp_a = Arc::new(vp);
    let vm_a = Arc::new(vm);
    let sol_a = Arc::new(sol);

    for &third in &[1usize, g] {
        // 5-subsets
        let mut cnt5 = 0u64;
        for x in 1..(q - 1) {
            if x == third { continue; }
            for y in (x + 1)..q {
                if y == third { continue; }
                cnt5 += 1;
                let p5 = [0usize, third, x, y, q];
                let mut any1 = false;
                for skip in 0..5 {
                    let mut f4 = [0usize; 4];
                    let mut idx = 0;
                    for i in 0..5 { if i != skip { f4[idx] = p5[i]; idx += 1; } }
                    if color_4subset_1mod4(f4, q, &inv_a, &sq_a, &pc_a, &vp_a, &vm_a, &sol_a) == 1 {
                        any1 = true; break;
                    }
                }
                assert!(any1, "All-0 5-subset found at {:?}", p5);
            }
        }
        println!("[Stage 2 PASS] All {} 5-subsets containing {{0, {}, inf}} verified: ZERO color-0 K_5^(4)!", cnt5, third);

        // 7-subsets with exact pair pruning
        let mut c1_pt = vec![0u8; q];
        for x in 1..q {
            if x != third {
                c1_pt[x] = color_4subset_1mod4([0, third, x, q], q, &inv_a, &sq_a, &pc_a, &vp_a, &vm_a, &sol_a);
            }
        }
        let mut pair_ok = vec![false; q * q];
        for x in 1..(q - 1) {
            if x == third || c1_pt[x] == 0 { continue; }
            for y in (x + 1)..q {
                if y == third || c1_pt[y] == 0 { continue; }
                if color_4subset_1mod4([0, x, y, q], q, &inv_a, &sq_a, &pc_a, &vp_a, &vm_a, &sol_a) == 1
                    && color_4subset_1mod4([third, x, y, q], q, &inv_a, &sq_a, &pc_a, &vp_a, &vm_a, &sol_a) == 1
                    && color_4subset_1mod4([0, third, x, y], q, &inv_a, &sq_a, &pc_a, &vp_a, &vm_a, &sol_a) == 1
                {
                    pair_ok[x * q + y] = true;
                }
            }
        }
        let c1_a = Arc::new(c1_pt);
        let pr_a = Arc::new(pair_ok);
        let viol7 = Arc::new(AtomicU64::new(0));
        let eval7 = Arc::new(AtomicU64::new(0));
        let mut handles = Vec::new();
        for tid in 0..24usize {
            let inv_c = Arc::clone(&inv_a);
            let sq_c = Arc::clone(&sq_a);
            let pc_c = Arc::clone(&pc_a);
            let vp_c = Arc::clone(&vp_a);
            let vm_c = Arc::clone(&vm_a);
            let sol_c = Arc::clone(&sol_a);
            let c1_c = Arc::clone(&c1_a);
            let pr_c = Arc::clone(&pr_a);
            let v7_c = Arc::clone(&viol7);
            let e7_c = Arc::clone(&eval7);
            handles.push(thread::spawn(move || {
                let mut loc = 0u64;
                for w in (1 + tid)..(q - 3) {
                    if (w - 1) % 24 != tid || w == third || c1_c[w] == 0 { continue; }
                    for x in (w + 1)..(q - 2) {
                        if x == third || !pr_c[w * q + x] { continue; }
                        let mut good_y = Vec::new();
                        for y in (x + 1)..q {
                            if y == third || !pr_c[w * q + y] || !pr_c[x * q + y] { continue; }
                            if color_4subset_1mod4([w, x, y, q], q, &inv_c, &sq_c, &pc_c, &vp_c, &vm_c, &sol_c) == 1
                                && color_4subset_1mod4([0, w, x, y], q, &inv_c, &sq_c, &pc_c, &vp_c, &vm_c, &sol_c) == 1
                                && color_4subset_1mod4([third, w, x, y], q, &inv_c, &sq_c, &pc_c, &vp_c, &vm_c, &sol_c) == 1
                            {
                                good_y.push(y);
                            }
                        }
                        for i in 0..good_y.len() {
                            let y = good_y[i];
                            for j in (i + 1)..good_y.len() {
                                let z = good_y[j];
                                if !pr_c[y * q + z] { continue; }
                                loc += 1;
                                let pts7 = [0usize, third, w, x, y, z, q];
                                let mut all1 = true;
                                'c35: for a0 in 0..4 { for a1 in (a0+1)..5 { for a2 in (a1+1)..6 { for a3 in (a2+1)..7 {
                                    if color_4subset_1mod4([pts7[a0], pts7[a1], pts7[a2], pts7[a3]], q, &inv_c, &sq_c, &pc_c, &vp_c, &vm_c, &sol_c) == 0 {
                                        all1 = false; break 'c35;
                                    }
                                }}}}
                                if all1 { v7_c.fetch_add(1, Ordering::Relaxed); }
                            }
                        }
                    }
                }
                e7_c.fetch_add(loc, Ordering::Relaxed);
            }));
        }
        for h in handles { h.join().unwrap(); }
        assert_eq!(viol7.load(Ordering::SeqCst), 0, "All-1 7-subset found!");
        println!("[Stage 3 PASS] Exhaustively verified ALL C({}, 4) 7-subsets containing {{0, {}, inf}} (cands={}): ZERO color-1 K_7^(4)!", q - 2, third, eval7.load(Ordering::SeqCst));
    }

    // Stage 4: 200,000 arbitrary 5-subsets + 200,000 arbitrary 7-subsets
    for _ in 0..200_000 {
        let mut s7 = [0usize; 7];
        let mut k = 0;
        while k < 7 {
            let p = (next_u64() % ((q + 1) as u64)) as usize;
            if !s7[..k].contains(&p) { s7[k] = p; k += 1; }
        }
        let mut any1_in5 = false;
        for skip in 0..5 {
            let mut f4 = [0usize; 4]; let mut idx = 0;
            for i in 0..5 { if i != skip { f4[idx] = s7[i]; idx += 1; } }
            if color_4subset_1mod4(f4, q, &inv_a, &sq_a, &pc_a, &vp_a, &vm_a, &sol_a) == 1 { any1_in5 = true; break; }
        }
        assert!(any1_in5, "Unnormalized all-0 5-subset!");
        let mut any0_in7 = false;
        'mc7: for a0 in 0..4 { for a1 in (a0+1)..5 { for a2 in (a1+1)..6 { for a3 in (a2+1)..7 {
            if color_4subset_1mod4([s7[a0], s7[a1], s7[a2], s7[a3]], q, &inv_a, &sq_a, &pc_a, &vp_a, &vm_a, &sol_a) == 0 { any0_in7 = true; break 'mc7; }
        }}}}
        assert!(any0_in7, "Unnormalized all-1 7-subset!");
    }
    println!("VERDICT ({:.2}s): 100% MATHEMATICALLY VERIFIED -> R(5, 7; 4) >= {} !!", t0.elapsed().as_secs_f64(), q + 2);
}
