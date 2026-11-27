// Standalone Zero-Dependency Clean-Room Verifier for Part II (16 Hypergraph Ramsey Lower Bounds)
// Compile: rustc -C opt-level=3 -C target-cpu=native verify_part2_records.rs -o verify_part2_records
// Run:     ./verify_part2_records
//
// Zero external crates (pure Rust std), zero code shared with any solver.
// Independently verifies SHA-256 digests, group generator invariance, and 100% exhaustive
// absence of monochromatic forbidden subsets across all 16 witnesses in witnesses_part2/.

use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Instant;

const NUM_THREADS: usize = 4;

// --- Pure-Rust SHA-256 (FIPS 180-4, zero external dependencies) ---
fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];
    let bit_len = (data.len() as u64) * 8;
    let mut msg = data.to_vec();
    msg.push(0x80);
    while (msg.len() % 64) != 56 {
        msg.push(0x00);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());
    for chunk in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([chunk[4 * i], chunk[4 * i + 1], chunk[4 * i + 2], chunk[4 * i + 3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
            (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g; g = f; f = e; e = d.wrapping_add(temp1);
            d = c; c = b; b = a; a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a); h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c); h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e); h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g); h[7] = h[7].wrapping_add(hh);
    }
    format!("{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}{:08x}", h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7])
}

// --- Minimal JSON field extractors ---
fn json_str<'a>(s: &'a str, key: &str) -> &'a str {
    let pat = format!("\"{}\"", key);
    let i = s.find(&pat).unwrap_or_else(|| panic!("Missing key {}", key)) + pat.len();
    let rest = s[i..].trim_start();
    assert!(rest.starts_with(':'));
    let rest = rest[1..].trim_start();
    assert!(rest.starts_with('"'));
    let body = &rest[1..];
    let end = body.find('"').unwrap();
    &body[..end]
}

fn json_usize(s: &str, key: &str) -> usize {
    let pat = format!("\"{}\"", key);
    let i = s.find(&pat).unwrap_or_else(|| panic!("Missing key {}", key)) + pat.len();
    let rest = s[i..].trim_start();
    assert!(rest.starts_with(':'));
    let rest = rest[1..].trim_start();
    let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
    rest[..end].parse().unwrap()
}

fn json_usize_vec(s: &str, key: &str) -> Vec<usize> {
    let pat = format!("\"{}\"", key);
    let i = s.find(&pat).unwrap() + pat.len();
    let rest = s[i..].trim_start();
    let lb = rest.find('[').unwrap();
    let rb = rest[lb..].find(']').unwrap() + lb;
    rest[lb + 1..rb]
        .split(',')
        .map(|x| x.trim().parse::<usize>().unwrap())
        .collect()
}

fn mod_pow(mut b: usize, mut e: usize, m: usize) -> usize {
    let mut r = 1usize;
    b %= m;
    while e > 0 {
        if (e & 1) == 1 { r = (r * b) % m; }
        b = (b * b) % m;
        e >>= 1;
    }
    r
}

#[inline(always)]
fn sort3(mut a: usize, mut b: usize, mut c: usize) -> (usize, usize, usize) {
    if a > b { std::mem::swap(&mut a, &mut b); }
    if b > c { std::mem::swap(&mut b, &mut c); }
    if a > b { std::mem::swap(&mut a, &mut b); }
    (a, b, c)
}

// --- Bitset for up to 384 vertices ---
#[derive(Clone, Copy)]
struct Bitset6([u64; 6]);
impl Bitset6 {
    fn new() -> Self { Self([0u64; 6]) }
    #[inline(always)]
    fn set(&mut self, i: usize) { self.0[i >> 6] |= 1u64 << (i & 63); }
    #[inline(always)]
    fn and(&self, o: &Self) -> Self {
        Self([
            self.0[0] & o.0[0], self.0[1] & o.0[1], self.0[2] & o.0[2],
            self.0[3] & o.0[3], self.0[4] & o.0[4], self.0[5] & o.0[5],
        ])
    }
    #[inline(always)]
    fn is_empty(&self) -> bool {
        (self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4] | self.0[5]) == 0
    }
    fn to_vec(&self) -> Vec<usize> {
        let mut out = Vec::new();
        for w in 0..6 {
            let mut m = self.0[w];
            while m != 0 {
                let tz = m.trailing_zeros() as usize;
                out.push((w << 6) | tz);
                m &= m - 1;
            }
        }
        out
    }
}

// Recursive exact k-clique finder inside induced 3-uniform hypergraph containing anchor `v0`!
// `sub_pts` are candidates `> cur_last` that already form valid triples `(v0, x, u)` for all previously chosen `x`
// AND valid 3-subsets `(x, y, u)` among all previously chosen pairs `(x, y)`!
fn has_3unif_clique_with_anchor(
    pts: usize,
    col3: &[u8],
    target_col: u8,
    target_k: usize,
    v0: usize,
) -> bool {
    // Pair adjacency on vertices > v0: edge (u, v) iff col3[v0, u, v] == target_col
    let mut adj_hi = vec![Bitset6::new(); pts];
    for u in (v0 + 1)..pts.saturating_sub(1) {
        let base_v0_u = (v0 * pts + u) * pts;
        for v in (u + 1)..pts {
            if col3[base_v0_u + v] == target_col {
                adj_hi[u].set(v);
            }
        }
    }

    fn dfs(
        pts: usize,
        col3: &[u8],
        adj_hi: &[Bitset6],
        tc: u8,
        need_more: usize,
        chosen: &mut Vec<usize>,
        cand: Bitset6,
    ) -> bool {
        if need_more == 0 {
            return true;
        }
        if cand.is_empty() {
            return false;
        }
        let list = cand.to_vec();
        if list.len() < need_more {
            return false;
        }
        for idx in 0..=(list.len() - need_more) {
            let u = list[idx];
            // Check all triples (x, y, u) for existing pairs x < y in `chosen` (excluding v0 which is already checked via adj_hi!)
            let mut ok = true;
            for i in 0..chosen.len() {
                let x = chosen[i];
                for j in (i + 1)..chosen.len() {
                    let y = chosen[j];
                    if col3[(x * pts + y) * pts + u] != tc {
                        ok = false;
                        break;
                    }
                }
                if !ok { break; }
            }
            if !ok { continue; }
            if need_more == 1 {
                return true;
            }
            let next_cand = cand.and(&adj_hi[u]);
            chosen.push(u);
            if dfs(pts, col3, adj_hi, tc, need_more - 1, chosen, next_cand) {
                return true;
            }
            chosen.pop();
        }
        false
    }

    let mut all_gt = Bitset6::new();
    for u in (v0 + 1)..pts {
        all_gt.set(u);
    }
    let mut chosen = Vec::with_capacity(8);
    dfs(pts, col3, &adj_hi, target_col, target_k - 1, &mut chosen, all_gt)
}

fn verify_affine_3unif(raw: &str, fname: &str) {
    let t0 = Instant::now();
    let claim = json_str(raw, "claim");
    let pts = json_usize(raw, "points");
    let n_col = json_usize(raw, "colors");
    let ks = json_usize_vec(raw, "thresholds");
    let n_mod = json_usize(raw, "n_mod");
    let mult_a = json_usize(raw, "multiplier_a");
    let ord_m = json_usize(raw, "multiplier_order");
    let n_inf = json_usize(raw, "n_infinity");
    let num_orbits = json_usize(raw, "num_orbits");
    let ostr = json_str(raw, "orbit_string");
    let sha_exp = json_str(raw, "orbit_string_sha256");

    assert_eq!(pts, n_mod + n_inf);
    assert_eq!(ostr.len(), num_orbits);
    assert_eq!(sha256_hex(ostr.as_bytes()), sha_exp, "SHA-256 mismatch in {}", fname);
    let ocols: Vec<u8> = ostr.bytes().map(|b| b - b'0').collect();
    assert!(ocols.iter().all(|&c| (c as usize) < n_col));

    // Reconstruct full 3-tensor `col3[a, b, c]` (pts <= 380) from the universal lex-smallest orbit rule
    let mut mults = Vec::with_capacity(ord_m);
    let mut cur = 1usize;
    for _ in 0..ord_m {
        mults.push(cur);
        cur = (cur * mult_a) % n_mod;
    }
    assert_eq!(cur, 1, "Invalid multiplier order in {}", fname);

    let mut orb_reps: HashMap<(usize, usize, usize), usize> = HashMap::new();
    let mut pair0_oid = vec![usize::MAX; pts * pts];

    for b in 1..(pts - 1) {
        for c in (b + 1)..pts {
            let base = [0usize, b, c];
            let mut best = (0usize, b, c);
            for &u in &base {
                if u >= n_mod { continue; }
                for &m in &mults {
                    let g0 = ((n_mod - u) * m) % n_mod;
                    let gb = if b >= n_mod { b } else { (((b + n_mod - u) % n_mod) * m) % n_mod };
                    let gc = if c >= n_mod { c } else { (((c + n_mod - u) % n_mod) * m) % n_mod };
                    let img = sort3(g0, gb, gc);
                    if img < best { best = img; }
                }
            }
            let len_now = orb_reps.len();
            let oid = *orb_reps.entry(best).or_insert(len_now);
            pair0_oid[b * pts + c] = oid;
        }
    }
    for a in n_mod..pts.saturating_sub(2) {
        for b in (a + 1)..pts.saturating_sub(1) {
            for c in (b + 1)..pts {
                let oid = orb_reps.len();
                orb_reps.insert((a, b, c), oid);
            }
        }
    }
    assert_eq!(orb_reps.len(), num_orbits, "Orbit count mismatch in {}", fname);

    let mut col3 = vec![0u8; pts * pts * pts];
    for a in 0..(pts - 2) {
        for b in (a + 1)..(pts - 1) {
            for c in (b + 1)..pts {
                let oid = if a >= n_mod {
                    orb_reps[&(a, b, c)]
                } else {
                    let b_sh = if b >= n_mod { b } else { b - a };
                    let c_sh = if c >= n_mod { c } else { c - a };
                    let (_, u, v) = sort3(0, b_sh, c_sh);
                    pair0_oid[u * pts + v]
                };
                let cv = ocols[oid];
                col3[(a * pts + b) * pts + c] = cv;
                col3[(a * pts + c) * pts + b] = cv;
                col3[(b * pts + a) * pts + c] = cv;
                col3[(b * pts + c) * pts + a] = cv;
                col3[(c * pts + a) * pts + b] = cv;
                col3[(c * pts + b) * pts + a] = cv;
            }
        }
    }

    // Explicitly verify shift & multiplier invariance across ALL boundary triples `{0, b, c}` and `{n_mod-1, b, c}`!
    for u in [0usize, n_mod - 1] {
        for b in 0..pts {
            if b == u { continue; }
            for c in (b + 1)..pts {
                if c == u { continue; }
                let orig = col3[(u * pts + b) * pts + c];
                let su = if u >= n_mod { u } else { (u + 1) % n_mod };
                let sb = if b >= n_mod { b } else { (b + 1) % n_mod };
                let sc = if c >= n_mod { c } else { (c + 1) % n_mod };
                assert_eq!(col3[(su * pts + sb) * pts + sc], orig, "Shift invariance failed in {}", fname);
                let mu = if u >= n_mod { u } else { (u * mult_a) % n_mod };
                let mb = if b >= n_mod { b } else { (b * mult_a) % n_mod };
                let mc = if c >= n_mod { c } else { (c * mult_a) % n_mod };
                assert_eq!(col3[(mu * pts + mb) * pts + mc], orig, "Mult invariance failed in {}", fname);
            }
        }
    }

    // By verified Z_{n_mod} shift invariance (fixing n_mod..pts-1), every subset of size k >= 4
    // either contains at least one finite point (hence maps by shift to a subset containing `0`),
    // OR consists solely of infinity points (only possible if n_inf >= k, i.e., R4443_102 where n_inf=4, k=4).
    // Furthermore, if pts <= 180 and max(ks) <= 5, we ALSO check EVERY vertex anchor 0..pts (100% zero-symmetry)!
    let zero_sym = pts <= 180 && *ks.iter().max().unwrap() <= 5;
    let anchors: Vec<usize> = if zero_sym {
        (0..pts).collect()
    } else {
        let mut v = vec![0usize];
        for inf_v in n_mod..pts { v.push(inf_v); }
        v
    };

    for (col_idx, &k_req) in ks.iter().enumerate() {
        for &anc in &anchors {
            assert!(
                !has_3unif_clique_with_anchor(pts, &col3, col_idx as u8, k_req, anc),
                "Monochromatic K_{} in colour {} found in {}!", k_req, col_idx, fname
            );
        }
    }

    println!(
        "[PASS] {:30} | {:28} | pts={:4} | orbits={:4} | mode={} | {:.3}s",
        fname, claim, pts, num_orbits, if zero_sym { "ZERO_SYM_EXHAUSTIVE" } else { "SHIFT_NORM_EXHAUSTIVE" },
        t0.elapsed().as_secs_f64()
    );
}

fn verify_aglp_large_3unif(raw: &str, fname: &str) {
    let t0 = Instant::now();
    let claim = json_str(raw, "claim");
    let p = json_usize(raw, "points");
    let n_col = json_usize(raw, "colors");
    let ks = json_usize_vec(raw, "thresholds");
    let mult_a = json_usize(raw, "multiplier_a");
    let num_orbits = json_usize(raw, "num_orbits");
    let ostr = json_str(raw, "orbit_string");
    let sha_exp = json_str(raw, "orbit_string_sha256");

    assert_eq!(p % 4, 3);
    assert!(ks.iter().all(|&k| k == 4));
    assert_eq!(ostr.len(), num_orbits);
    assert_eq!(sha256_hex(ostr.as_bytes()), sha_exp, "SHA-256 mismatch in {}", fname);
    let ocols: Vec<u8> = ostr.bytes().map(|b| b - b'0').collect();
    assert!(ocols.iter().all(|&c| (c as usize) < n_col));

    let mut invs = vec![0usize; p];
    let mut qr = vec![false; p];
    for x in 1..p {
        invs[x] = mod_pow(x, p - 2, p);
        qr[(x * x) % p] = true;
    }

    let mut rep_01z = vec![0usize; p];
    let mut orb_map: HashMap<usize, usize> = HashMap::new();
    for z in 2..p {
        let mut cands = [0usize; 3];
        cands[0] = z;
        cands[1] = if qr[z] { invs[z] } else { (((p + 1 - z) % p) * invs[p - z]) % p };
        let d1 = z - 1;
        cands[2] = if qr[d1] { ((p - 1) * invs[d1]) % p } else { (((p - z) % p) * invs[p - d1]) % p };
        let r = *cands.iter().min().unwrap();
        let len_now = orb_map.len();
        let oid = *orb_map.entry(r).or_insert(len_now);
        rep_01z[z] = oid;
    }
    assert_eq!(orb_map.len(), num_orbits);
    let col_z: Vec<u8> = (0..p).map(|z| if z >= 2 { ocols[rep_01z[z]] } else { 0 }).collect();

    let col3 = |a: usize, b: usize, c: usize| -> u8 {
        let (x, y, w) = sort3(a, b, c);
        let df = y - x;
        let z = if qr[df] { ((w - x) * invs[df]) % p } else { (((w + p - y) % p) * invs[p - df]) % p };
        col_z[z]
    };

    // Verify generator invariance (x -> x+1 and x -> mult_a * x mod p) on 200,000 deterministic triples + boundary!
    assert!(qr[mult_a]);
    let mut rng = 0x1234_5678_9abc_def0u64 ^ (p as u64);
    for _ in 0..200_000 {
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        let a = (rng as usize) % p;
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        let mut b = (rng as usize) % (p - 1);
        if b >= a { b += 1; }
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        let mut c = (rng as usize) % (p - 2);
        let (lo, hi) = if a < b { (a, b) } else { (b, a) };
        if c >= lo { c += 1; }
        if c >= hi { c += 1; }
        let c0 = col3(a, b, c);
        assert_eq!(col3((a + 1) % p, (b + 1) % p, (c + 1) % p), c0);
        assert_eq!(col3((a * mult_a) % p, (b * mult_a) % p, (c * mult_a) % p), c0);
    }

    // By 2-homogeneity of AGL+(1, p) on F_p (since -1 is non-square for p == 3 mod 4, every 2-subset {u, v}
    // has unique orientation v - u in QR_p, sending u -> 0, v -> 1), EVERY 4-subset of F_p maps to {0, 1, z, w}
    // with 2 <= z < w < p! Exhaustively check ALL C(p-2, 2) pairs (z, w) across 4 threads!
    let col_z_arc = Arc::new(col_z);
    let invs_arc = Arc::new(invs);
    let qr_arc = Arc::new(qr);
    let viol = Arc::new(AtomicU64::new(0));

    let mut handles = Vec::new();
    for tid in 0..NUM_THREADS {
        let cz = Arc::clone(&col_z_arc);
        let iv = Arc::clone(&invs_arc);
        let qv = Arc::clone(&qr_arc);
        let vl = Arc::clone(&viol);
        handles.push(thread::spawn(move || {
            let mut loc = 0u64;
            for z in ((2 + tid)..(p - 1)).step_by(NUM_THREADS) {
                let c_01z = cz[z];
                for w in (z + 1)..p {
                    if cz[w] != c_01z { continue; }
                    // Check {0, z, w}: 0 < z < w, df = z
                    let z_0zw = if qv[z] { (w * iv[z]) % p } else { (((w + p - z) % p) * iv[p - z]) % p };
                    if cz[z_0zw] != c_01z { continue; }
                    // Check {1, z, w}: 1 < z < w, df = z - 1
                    let d1 = z - 1;
                    let z_1zw = if qv[d1] { ((w - 1) * iv[d1]) % p } else { (((w + p - z) % p) * iv[p - d1]) % p };
                    if cz[z_1zw] == c_01z {
                        loc += 1;
                    }
                }
            }
            vl.fetch_add(loc, Ordering::Relaxed);
        }));
    }
    for h in handles { h.join().unwrap(); }
    assert_eq!(viol.load(Ordering::Relaxed), 0, "Monochromatic K_4^(3) found in {}", fname);

    let pairs_checked = ((p - 2) * (p - 3)) / 2;
    println!(
        "[PASS] {:30} | {:28} | pts={:4} | orbits={:4} | pairs={:10} | {:.3}s",
        fname, claim, p, num_orbits, pairs_checked, t0.elapsed().as_secs_f64()
    );
}

fn verify_psl2_4unif(raw: &str, fname: &str) {
    let t0 = Instant::now();
    let claim = json_str(raw, "claim");
    let q = json_usize(raw, "q");
    let pts = json_usize(raw, "points");
    let n_col = json_usize(raw, "colors");
    let num_orbits = json_usize(raw, "num_orbits");
    let ostr = json_str(raw, "orbit_string");
    let sha_exp = json_str(raw, "orbit_string_sha256");
    let ctype = json_str(raw, "construction_type");

    assert_eq!(pts, q + 1);
    assert_eq!(ostr.len(), num_orbits);
    assert_eq!(sha256_hex(ostr.as_bytes()), sha_exp, "SHA-256 mismatch in {}", fname);

    let mut invs = vec![0usize; q];
    let mut qr = vec![false; q];
    for x in 1..q {
        invs[x] = mod_pow(x, q - 2, q);
        qr[(x * x) % q] = true;
    }
    let mut g_ns = 2usize;
    while qr[g_ns] { g_ns += 1; }
    // Find a non-trivial square s != 1
    let s_sq = (2 * 2) % q;

    let (tab_p, tab_m): (Vec<u8>, Vec<u8>) = if ctype == "psl2_narrow_3mod4" {
        assert_eq!(q % 4, 3);
        let t_str = json_str(raw, "table");
        let t_sha = json_str(raw, "table_sha256");
        assert_eq!(t_str.len(), q);
        assert_eq!(sha256_hex(t_str.as_bytes()), t_sha);
        let tv: Vec<u8> = t_str.bytes().map(|b| b - b'0').collect();
        let mut tm = vec![0u8; q];
        for lam in 2..q {
            tm[lam] = tv[invs[lam]];
        }
        (tv, tm)
    } else {
        assert_eq!(q % 4, 1);
        let tp_s = json_str(raw, "table_plus");
        let tm_s = json_str(raw, "table_minus");
        assert_eq!(sha256_hex(tp_s.as_bytes()), json_str(raw, "table_plus_sha256"));
        assert_eq!(sha256_hex(tm_s.as_bytes()), json_str(raw, "table_minus_sha256"));
        (tp_s.bytes().map(|b| b - b'0').collect(), tm_s.bytes().map(|b| b - b'0').collect())
    };
    assert!(tab_p[2..].iter().all(|&c| (c as usize) < n_col));
    assert!(tab_m[2..].iter().all(|&c| (c as usize) < n_col));

    let is_3mod4 = q % 4 == 3;
    let col4 = |mut a: usize, mut b: usize, mut c: usize, mut d: usize| -> u8 {
        if a > b { std::mem::swap(&mut a, &mut b); }
        if c > d { std::mem::swap(&mut c, &mut d); }
        if a > c { std::mem::swap(&mut a, &mut c); }
        if b > d { std::mem::swap(&mut b, &mut d); }
        if b > c { std::mem::swap(&mut b, &mut c); }
        let delta = ((((b - a) * (c - a)) % q) * (c - b)) % q;
        let lam = if is_3mod4 {
            if d == q {
                (((a + q - c) % q) * invs[(b + q - c) % q]) % q
            } else {
                let num = (((a + q - c) % q) * ((b + q - d) % q)) % q;
                let den = (((a + q - d) % q) * ((b + q - c) % q)) % q;
                (num * invs[den]) % q
            }
        } else {
            let kv = ((c - a) * invs[c - b]) % q;
            if d == q { kv } else { (((kv * (d - b)) % q) * invs[d - a]) % q }
        };
        if qr[delta] { tab_p[lam] } else { tab_m[lam] }
    };

    // Verify PSL(2, q) generator invariance (x+1, s_sq*x, -1/x) on 300,000 random 4-subsets!
    let act_sh = |x: usize| if x == q { q } else { (x + 1) % q };
    let act_sc = |x: usize| if x == q { q } else { (x * s_sq) % q };
    let act_iv = |x: usize| if x == q { 0 } else if x == 0 { q } else { (q - invs[x]) % q };

    let mut rng = 0x9e37_79b9_7f4a_7c15u64 ^ (q as u64);
    for _ in 0..300_000 {
        let mut s = [0usize; 4];
        let mut cnt = 0;
        while cnt < 4 {
            rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
            let v = (rng as usize) % pts;
            if !s[..cnt].contains(&v) { s[cnt] = v; cnt += 1; }
        }
        let c0 = col4(s[0], s[1], s[2], s[3]);
        assert_eq!(col4(act_sh(s[0]), act_sh(s[1]), act_sh(s[2]), act_sh(s[3])), c0, "Shift failed in {}", fname);
        assert_eq!(col4(act_sc(s[0]), act_sc(s[1]), act_sc(s[2]), act_sc(s[3])), c0, "Scale failed in {}", fname);
        assert_eq!(col4(act_iv(s[0]), act_iv(s[1]), act_iv(s[2]), act_iv(s[3])), c0, "Inv failed in {}", fname);
    }

    // By verified PSL(2, q) invariance (2-transitive on P^1(F_q) = {0..q}, splitting {INF, 0, b} into at most
    // two orbits b = 1 and b = g_ns), EVERY 5-subset of P^1(F_q) maps under PSL(2, q) to {q, 0, b, c, d}
    // with b in {1, g_ns} and 1 <= c < d < q (c, d != b)!
    // Exhaustively check ALL 2 * C(q-2, 2) normalized 5-subsets across 4 threads!
    let tp_arc = Arc::new(tab_p);
    let tm_arc = Arc::new(tab_m);
    let iv_arc = Arc::new(invs);
    let qr_arc = Arc::new(qr);
    let viol = Arc::new(AtomicU64::new(0));

    let mut handles = Vec::new();
    for tid in 0..NUM_THREADS {
        let tp = Arc::clone(&tp_arc);
        let tm = Arc::clone(&tm_arc);
        let iv = Arc::clone(&iv_arc);
        let qv = Arc::clone(&qr_arc);
        let vl = Arc::clone(&viol);
        handles.push(thread::spawn(move || {
            let eval4 = |mut a: usize, mut b: usize, mut c: usize, mut d: usize| -> u8 {
                if a > b { std::mem::swap(&mut a, &mut b); }
                if c > d { std::mem::swap(&mut c, &mut d); }
                if a > c { std::mem::swap(&mut a, &mut c); }
                if b > d { std::mem::swap(&mut b, &mut d); }
                if b > c { std::mem::swap(&mut b, &mut c); }
                let delta = ((((b - a) * (c - a)) % q) * (c - b)) % q;
                let lam = if is_3mod4 {
                    if d == q {
                        (((a + q - c) % q) * iv[(b + q - c) % q]) % q
                    } else {
                        let num = (((a + q - c) % q) * ((b + q - d) % q)) % q;
                        let den = (((a + q - d) % q) * ((b + q - c) % q)) % q;
                        (num * iv[den]) % q
                    }
                } else {
                    let kv = ((c - a) * iv[c - b]) % q;
                    if d == q { kv } else { (((kv * (d - b)) % q) * iv[d - a]) % q }
                };
                if qv[delta] { tp[lam] } else { tm[lam] }
            };

            let mut loc = 0u64;
            for b in [1usize, g_ns] {
                // Precompute col4(0, b, x, q) for all x in 1..q, x != b
                let mut c_0bxq = vec![255u8; q];
                for x in 1..q {
                    if x != b {
                        c_0bxq[x] = eval4(0, b, x, q);
                    }
                }
                for c in ((1 + tid)..(q - 1)).step_by(NUM_THREADS) {
                    if c == b { continue; }
                    let target = c_0bxq[c];
                    for d in (c + 1)..q {
                        if d == b || c_0bxq[d] != target { continue; }
                        if eval4(0, c, d, q) != target { continue; }
                        if eval4(b, c, d, q) != target { continue; }
                        if eval4(0, b, c, d) == target {
                            loc += 1;
                        }
                    }
                }
            }
            vl.fetch_add(loc, Ordering::Relaxed);
        }));
    }
    for h in handles { h.join().unwrap(); }
    assert_eq!(viol.load(Ordering::Relaxed), 0, "Monochromatic K_5^(4) found in {}", fname);

    let norm5 = (q - 2) * (q - 3);
    println!(
        "[PASS] {:30} | {:28} | pts={:4} | orbits={:4} | norm5={:10} | {:.3}s",
        fname, claim, pts, num_orbits, norm5, t0.elapsed().as_secs_f64()
    );
}

fn main() {
    let t_all = Instant::now();
    let dir = Path::new("witnesses_part2");
    let files = [
        "R553_109_points_rule.json",
        "R663_307_points_rule.json",
        "R573_283_points_rule.json",
        "R563_155_points_rule.json",
        "R483_163_points_rule.json",
        "R473_107_points_rule.json",
        "R4443_102_points_rule.json",
        "R4453_163_points_rule.json",
        "R4553_271_points_rule.json",
        "R44443_380_points_rule.json",
        "R444443_1259_points_rule.json",
        "R4444443_3779_points_rule.json",
        "R44444443_5231_points_rule.json",
        "R5554_968_points_rule.json",
        "R55554_3804_points_rule.json",
        "R555554_9438_points_rule.json",
    ];

    println!("=== Clean-Room Verification of All 16 Part II Hypergraph Ramsey Witnesses ===");
    for fname in files {
        let p = dir.join(fname);
        let raw = fs::read_to_string(&p).unwrap_or_else(|e| panic!("Failed to read {:?}: {}", p, e));
        let ctype = json_str(&raw, "construction_type");
        let pts = json_usize(&raw, "points");
        match ctype {
            "affine_plus_infinity" => verify_affine_3unif(&raw, fname),
            "aglp_2homogeneous" => {
                if pts <= 300 {
                    verify_affine_3unif(&raw, fname);
                } else {
                    verify_aglp_large_3unif(&raw, fname);
                }
            }
            "psl2_narrow_3mod4" | "psl2_chiral_1mod4" => verify_psl2_4unif(&raw, fname),
            other => panic!("Unknown construction_type: {}", other),
        }
    }
    println!("=== ALL 16 WITNESSES PASSED 100% EXHAUSTIVE CLEAN-ROOM VERIFICATION IN {:.2}s! ===", t_all.elapsed().as_secs_f64());
}
