// Standalone Clean-Room First-Principles Verifier for R(6, 6; 4) >= q + 2 via PSL(2, q) (q == 3 mod 4)
// Zero external dependencies; reads ONLY a JSON rule file containing `"prime_q"` (or `"q"`) and `"tau_table"` (or `"table"`).
// Computationally proves from scratch:
//   [1] Primality of q and q == 3 (mod 4).
//   [2] Well-definedness on ALL 12 SL(2, q) (det == 1 mod q) stabilizer/coset images of 4-subsets.
//   [3] Exhaustive 3-homogeneity over ALL C(q+1, 3) unordered 3-subsets {u, v, w} in P^1(F_q) via explicit det=1 matrices.
//   [4] 1,000,000 random (4-subset E, matrix M in SL(2, q)) invariance tests: color(M(E)) == color(E).
//   [5] Exhaustive check of ALL C(q-2, 3) 6-subsets containing {inf, 0, 1} -> 0 monochromatic K_6^(4) in either color!
//   [6] 500,000 arbitrary random 6-subsets in P^1(F_q) evaluated directly without symmetry reduction!
use std::env;
use std::fs;
use std::sync::Arc;
use std::thread;
use std::time::Instant;

#[inline(always)]
fn mod_add(a: u64, b: u64, q: u64) -> u64 {
    (a + b) % q
}
#[inline(always)]
fn mod_sub(a: u64, b: u64, q: u64) -> u64 {
    (a + q - (b % q)) % q
}
#[inline(always)]
fn mod_mul(a: u64, b: u64, q: u64) -> u64 {
    (a * b) % q
}
fn mod_pow(mut base: u64, mut exp: u64, q: u64) -> u64 {
    let mut r = 1u64;
    base %= q;
    while exp > 0 {
        if exp & 1 == 1 {
            r = (r * base) % q;
        }
        base = (base * base) % q;
        exp >>= 1;
    }
    r
}

#[inline(always)]
fn apply_mat(m: [u64; 4], z: u64, q: u64, inv: &[u64]) -> u64 {
    let (a, b, c, d) = (m[0], m[1], m[2], m[3]);
    if z == q {
        if c == 0 {
            q
        } else {
            mod_mul(a, inv[c as usize], q)
        }
    } else {
        let num = mod_add(mod_mul(a, z, q), b, q);
        let den = mod_add(mod_mul(c, z, q), d, q);
        if den == 0 {
            q
        } else {
            mod_mul(num, inv[den as usize], q)
        }
    }
}

#[inline(always)]
fn sl2_map_to_inf01(x0: u64, x1: u64, x2: u64, q: u64, sqrt_qr: &[Option<u64>], inv: &[u64]) -> Option<[u64; 4]> {
    let (a, b, c, d) = if x0 == q {
        (1, mod_sub(0, x1, q), 0, mod_sub(x2, x1, q))
    } else if x1 == q {
        (0, mod_sub(x2, x0, q), 1, mod_sub(0, x0, q))
    } else if x2 == q {
        (1, mod_sub(0, x1, q), 1, mod_sub(0, x0, q))
    } else {
        let k_num = mod_sub(x2, x0, q);
        let k_den = mod_sub(x2, x1, q);
        (
            k_num,
            mod_sub(0, mod_mul(k_num, x1, q), q),
            k_den,
            mod_sub(0, mod_mul(k_den, x0, q), q),
        )
    };
    let det = mod_sub(mod_mul(a, d, q), mod_mul(b, c, q), q);
    let s = sqrt_qr[det as usize]?;
    let inv_s = inv[s as usize];
    let m = [
        mod_mul(a, inv_s, q),
        mod_mul(b, inv_s, q),
        mod_mul(c, inv_s, q),
        mod_mul(d, inv_s, q),
    ];
    debug_assert_eq!(mod_sub(mod_mul(m[0], m[3], q), mod_mul(m[1], m[2], q), q), 1);
    Some(m)
}

#[inline(always)]
fn color_4subset_strict(
    pts: [u64; 4],
    q: u64,
    tau: &[u8],
    sqrt_qr: &[Option<u64>],
    inv: &[u64],
    check_all_12: bool,
) -> u8 {
    const PERMS: [[usize; 4]; 24] = [
        [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1],
        [1, 0, 2, 3], [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
        [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0],
        [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0],
    ];
    let mut valid_cnt = 0usize;
    let mut first_col = 255u8;
    for p in &PERMS {
        if let Some(m) = sl2_map_to_inf01(pts[p[0]], pts[p[1]], pts[p[2]], q, sqrt_qr, inv) {
            let lam = apply_mat(m, pts[p[3]], q, inv);
            assert!(lam >= 2 && lam < q, "Invalid lambda={}", lam);
            let c = tau[lam as usize];
            if !check_all_12 {
                return c;
            }
            if valid_cnt == 0 {
                first_col = c;
            } else {
                assert_eq!(c, first_col, "PSL(2, {}) well-definedness VIOLATED on {:?}", q, pts);
            }
            valid_cnt += 1;
        }
    }
    assert_eq!(valid_cnt, 12, "Expected 12 SL(2,{}) maps, got {}", q, valid_cnt);
    first_col
}

fn extract_str<'a>(raw: &'a str, key: &str) -> Option<&'a str> {
    let pat = format!("\"{}\":", key);
    let idx = raw.find(&pat)? + pat.len();
    let rest = raw[idx..].trim_start();
    if rest.starts_with('"') {
        let s = &rest[1..];
        let end = s.find('"')?;
        Some(&s[..end])
    } else {
        let end = rest.find(|c: char| !c.is_ascii_digit())?;
        Some(&rest[..end])
    }
}

fn main() {
    let t0 = Instant::now();
    let json_path = env::args().nth(1).expect("Usage: verify_r664_psl <rule.json>");
    let raw = fs::read_to_string(&json_path).expect("Failed to read JSON file");
    let q_str = extract_str(&raw, "q")
        .or_else(|| extract_str(&raw, "prime_q"))
        .expect("Missing q / prime_q");
    let q: u64 = q_str.parse().expect("Invalid prime q");
    let qu = q as usize;
    let tau_str = extract_str(&raw, "table")
        .or_else(|| extract_str(&raw, "tau_table"))
        .expect("Missing table / tau_table");

    for d in 2..q {
        assert_ne!(q % d, 0, "{} is not prime!", q);
    }
    assert_eq!(q % 4, 3, "q={} must satisfy q == 3 (mod 4)", q);
    assert_eq!(tau_str.len(), qu, "table len {} != q={}", tau_str.len(), q);

    let mut tau = vec![255u8; qu];
    let mut n0 = 0usize;
    let mut n1 = 0usize;
    for (i, ch) in tau_str.chars().enumerate() {
        if i < 2 {
            assert!(ch == '-' || ch == '0', "Expected '-' or '0' at unused index {}", i);
        } else if ch == '0' {
            tau[i] = 0;
            n0 += 1;
        } else if ch == '1' {
            tau[i] = 1;
            n1 += 1;
        } else {
            panic!("Invalid char {} at index {}", ch, i);
        }
    }
    println!("[Check 1 PASS] q={} is prime (q == 3 mod 4), order n={}, proves R(6, 6; 4) >= {} (zeros={}, ones={}).", q, q + 1, q + 2, n0, n1);

    let mut inv = vec![0u64; qu];
    let mut sqrt_qr: Vec<Option<u64>> = vec![None; qu];
    for x in 1..q {
        inv[x as usize] = mod_pow(x, q - 2, q);
        sqrt_qr[mod_mul(x, x, q) as usize] = Some(x);
    }

    for u in 1..q {
        for v in (u + 1)..q {
            let _ = color_4subset_strict([q, 0, u, v], q, &tau, &sqrt_qr, &inv, true);
            if u >= 2 {
                let _ = color_4subset_strict([0, 1, u, v], q, &tau, &sqrt_qr, &inv, true);
            }
        }
    }
    println!("[Check 2 PASS] All 12 SL(2, {}) Stabilizer/Coset images agree 100% ({:.2}s).", q, t0.elapsed().as_secs_f64());

    let t3 = Instant::now();
    let mut count_3sets = 0u64;
    for u in 0..(q + 1) {
        for v in (u + 1)..(q + 1) {
            for w in (v + 1)..(q + 1) {
                let m = sl2_map_to_inf01(u, v, w, q, &sqrt_qr, &inv)
                    .or_else(|| sl2_map_to_inf01(u, w, v, q, &sqrt_qr, &inv))
                    .expect("3-homogeneity FAILED!");
                assert_eq!(mod_sub(mod_mul(m[0], m[3], q), mod_mul(m[1], m[2], q), q), 1);
                let im0 = apply_mat(m, u, q, &inv);
                let im1 = apply_mat(m, v, q, &inv);
                let im2 = apply_mat(m, w, q, &inv);
                assert_eq!(im0, q);
                assert!((im1 == 0 && im2 == 1) || (im1 == 1 && im2 == 0));
                count_3sets += 1;
            }
        }
    }
    assert_eq!(count_3sets, (q + 1) * q * (q - 1) / 6);
    println!("[Check 3 PASS] Exhaustively verified explicit det=1 SL(2, {}) map -> {{inf,0,1}} for ALL {} 3-subsets ({:.2}s)!", q, count_3sets, t3.elapsed().as_secs_f64());

    let t4 = Instant::now();
    let mut state = 0xCAFEBABE_98765432u64;
    let mut next_u64 = || -> u64 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for idx in 0..1_000_000usize {
        let m = loop {
            let a = next_u64() % q;
            let b = next_u64() % q;
            let c = next_u64() % q;
            let d = next_u64() % q;
            let det = mod_sub(mod_mul(a, d, q), mod_mul(b, c, q), q);
            if det != 0 {
                if let Some(s) = sqrt_qr[det as usize] {
                    let is = inv[s as usize];
                    break [mod_mul(a, is, q), mod_mul(b, is, q), mod_mul(c, is, q), mod_mul(d, is, q)];
                }
            }
        };
        let mut e = [0u64; 4];
        let mut k = 0;
        while k < 4 {
            let p = next_u64() % (q + 1);
            if !e[..k].contains(&p) {
                e[k] = p;
                k += 1;
            }
        }
        let me = [
            apply_mat(m, e[0], q, &inv),
            apply_mat(m, e[1], q, &inv),
            apply_mat(m, e[2], q, &inv),
            apply_mat(m, e[3], q, &inv),
        ];
        let c1 = color_4subset_strict(e, q, &tau, &sqrt_qr, &inv, idx < 2000);
        let c2 = color_4subset_strict(me, q, &tau, &sqrt_qr, &inv, idx < 2000);
        assert_eq!(c1, c2);
    }
    println!("[Check 4 PASS] 1,000,000 / 1,000,000 random SL(2, {}) matrix transformations preserved 4-edge colors ({:.2}s)!", q, t4.elapsed().as_secs_f64());

    let t5 = Instant::now();
    let mut c_inf0 = vec![0u8; qu * qu];
    let mut c_inf1 = vec![0u8; qu * qu];
    let mut c_01 = vec![0u8; qu * qu];
    for x in 2..qu {
        for y in (x + 1)..qu {
            c_inf0[x * qu + y] = color_4subset_strict([q, 0, x as u64, y as u64], q, &tau, &sqrt_qr, &inv, true);
            c_inf1[x * qu + y] = color_4subset_strict([q, 1, x as u64, y as u64], q, &tau, &sqrt_qr, &inv, true);
            c_01[x * qu + y] = color_4subset_strict([0, 1, x as u64, y as u64], q, &tau, &sqrt_qr, &inv, true);
        }
    }

    let tau = Arc::new(tau);
    let inv = Arc::new(inv);
    let sqrt_qr = Arc::new(sqrt_qr);
    let c_inf0 = Arc::new(c_inf0);
    let c_inf1 = Arc::new(c_inf1);
    let c_01 = Arc::new(c_01);
    let n_threads = thread::available_parallelism().map(|p| p.get()).unwrap_or(12).max(4);
    let mut handles = Vec::new();
    for tid in 0..n_threads {
        let tau = Arc::clone(&tau);
        let inv = Arc::clone(&inv);
        let sqrt_qr = Arc::clone(&sqrt_qr);
        let c_inf0 = Arc::clone(&c_inf0);
        let c_inf1 = Arc::clone(&c_inf1);
        let c_01 = Arc::clone(&c_01);
        handles.push(thread::spawn(move || {
            let mut checked = 0u64;
            let mut min_sum = 15u8;
            let mut max_sum = 0u8;
            let mut x = 2 + tid;
            while x < qu - 2 {
                let xu = x as u64;
                for y in (x + 1)..(qu - 1) {
                    let yu = y as u64;
                    let base = tau[x] + tau[y] + c_inf0[x * qu + y] + c_inf1[x * qu + y] + c_01[x * qu + y];
                    let m_ixy = sl2_map_to_inf01(q, xu, yu, q, &sqrt_qr, &inv)
                        .unwrap_or_else(|| sl2_map_to_inf01(q, yu, xu, q, &sqrt_qr, &inv).unwrap());
                    let m_0xy = sl2_map_to_inf01(0, xu, yu, q, &sqrt_qr, &inv)
                        .unwrap_or_else(|| sl2_map_to_inf01(0, yu, xu, q, &sqrt_qr, &inv).unwrap());
                    let m_1xy = sl2_map_to_inf01(1, xu, yu, q, &sqrt_qr, &inv)
                        .unwrap_or_else(|| sl2_map_to_inf01(1, yu, xu, q, &sqrt_qr, &inv).unwrap());

                    for z in (y + 1)..qu {
                        let zu = z as u64;
                        let sum = base
                            + tau[z]
                            + c_inf0[x * qu + z]
                            + c_inf0[y * qu + z]
                            + c_inf1[x * qu + z]
                            + c_inf1[y * qu + z]
                            + c_01[x * qu + z]
                            + c_01[y * qu + z]
                            + tau[apply_mat(m_ixy, zu, q, &inv) as usize]
                            + tau[apply_mat(m_0xy, zu, q, &inv) as usize]
                            + tau[apply_mat(m_1xy, zu, q, &inv) as usize];
                        assert!(sum >= 1 && sum <= 14, "MONOCHROMATIC 6-SET at ({},{},{}) sum={}!", x, y, z, sum);
                        if sum < min_sum {
                            min_sum = sum;
                        }
                        if sum > max_sum {
                            max_sum = sum;
                        }
                        checked += 1;
                    }
                }
                x += n_threads;
            }
            (checked, min_sum, max_sum)
        }));
    }
    let mut tot_6sets = 0u64;
    let mut gmin_s = 15u8;
    let mut gmax_s = 0u8;
    for h in handles {
        let (ch, mn, mx) = h.join().unwrap();
        tot_6sets += ch;
        if mn < gmin_s {
            gmin_s = mn;
        }
        if mx > gmax_s {
            gmax_s = mx;
        }
    }
    assert_eq!(tot_6sets, (q - 2) * (q - 3) * (q - 4) / 6);
    println!(
        "[Check 5 PASS] Exhaustively verified ALL {} 6-subsets containing {{inf,0,1}}: ZERO monochromatic K_6^(4)! (1-edges: {}..={}, {:.2}s)",
        tot_6sets, gmin_s, gmax_s, t5.elapsed().as_secs_f64()
    );

    let t6 = Instant::now();
    const SUB4: [[usize; 4]; 15] = [
        [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 5], [0, 1, 3, 4], [0, 1, 3, 5],
        [0, 1, 4, 5], [0, 2, 3, 4], [0, 2, 3, 5], [0, 2, 4, 5], [0, 3, 4, 5],
        [1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 4, 5], [1, 3, 4, 5], [2, 3, 4, 5],
    ];
    for _ in 0..500_000 {
        let mut s6 = [0u64; 6];
        let mut k = 0;
        while k < 6 {
            let p = next_u64() % (q + 1);
            if !s6[..k].contains(&p) {
                s6[k] = p;
                k += 1;
            }
        }
        let mut sum = 0u8;
        for q4 in &SUB4 {
            sum += color_4subset_strict([s6[q4[0]], s6[q4[1]], s6[q4[2]], s6[q4[3]]], q, &tau, &sqrt_qr, &inv, false);
        }
        assert!(sum >= 1 && sum <= 14);
    }
    println!("[Check 6 PASS] 500,000 / 500,000 arbitrary random 6-subsets in P^1(F_{}) verified directly ({:.2}s)!", q, t6.elapsed().as_secs_f64());
    println!("=============================================================================");
    println!("ALL 6 INDEPENDENT PROOFS PASSED 100%: R(6, 6; 4) >= {} IS VERIFIED!", q + 2);
    println!("=============================================================================");
}
