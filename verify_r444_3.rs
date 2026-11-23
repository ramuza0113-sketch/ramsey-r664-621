// Zero-shortcut, zero-symmetry clean-room Rust verifier for R(4, 4, 4; 3) >= n + 1!
// Reconstructs the explicit 3-colouring of ALL C(n, 3) triples, verifies group invariance on ALL group maps,
// and exhaustively checks EVERY SINGLE ONE of the C(n, 4) 4-subsets directly (no translation shortcut!).

use std::env;
use std::fs;
use std::time::Instant;

fn extract_usize_after(raw: &str, key: &str) -> usize {
    let idx = raw.find(key).unwrap();
    let rest = raw[idx + key.len()..].trim_start_matches(|c: char| c == ':' || c.is_whitespace());
    let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap();
    rest[..end].parse().unwrap()
}

fn main() {
    let t0 = Instant::now();
    let path = env::args().nth(1).expect("json path");
    let raw = fs::read_to_string(&path).unwrap();

    // Parse desc `"G(nm,a)[ord=k]+niinf"`, points, orbit_colors
    let d_idx = raw.find("\"G(").unwrap();
    let d_sub = &raw[d_idx + 3..d_idx + 40];
    let comma = d_sub.find(',').unwrap();
    let rpar = d_sub.find(')').unwrap();
    let plus = d_sub.find('+').unwrap();
    let inf_pos = d_sub.find("inf").unwrap();
    let nm: usize = d_sub[..comma].parse().unwrap();
    let a_gen: usize = d_sub[comma + 1..rpar].parse().unwrap();
    let ni: usize = d_sub[plus + 1..inf_pos].parse().unwrap();
    let pts = extract_usize_after(&raw, "\"points\"");
    assert_eq!(pts, nm + ni);

    let oc_idx = raw.find("\"orbit_colors\"").unwrap();
    let b1 = raw[oc_idx..].find('[').unwrap() + oc_idx;
    let b2 = raw[b1..].find(']').unwrap() + b1;
    let orb_cols: Vec<u8> = raw[b1 + 1..b2]
        .split(',')
        .map(|s| s.trim().parse::<u8>().unwrap())
        .collect();
    for &c in &orb_cols {
        assert!(c < 3, "Invalid colour >= 3!");
    }

    // Generate multiplier subgroup <a_gen> mod nm
    let mut mults = Vec::new();
    let mut x = 1usize;
    while !mults.contains(&x) {
        mults.push(x);
        x = (x * a_gen) % nm;
    }

    // Build all triples and assign orbits in canonical lexicographic order (identical to generator convention)
    let mut tri_id = vec![usize::MAX; pts * pts * pts];
    let mut triples = Vec::new();
    for a in 0..(pts - 2) {
        for b in (a + 1)..(pts - 1) {
            for c in (b + 1)..pts {
                tri_id[(a * pts + b) * pts + c] = triples.len();
                triples.push([a, b, c]);
            }
        }
    }

    let mut orb_of = vec![usize::MAX; triples.len()];
    let mut n_orbs = 0usize;
    for ti in 0..triples.len() {
        if orb_of[ti] != usize::MAX { continue; }
        let [a, b, c] = triples[ti];
        for &m in &mults {
            for sh in 0..nm {
                let map_pt = |p: usize| -> usize { if p < nm { (m * p + sh) % nm } else { p } };
                let mut im = [map_pt(a), map_pt(b), map_pt(c)];
                im.sort_unstable();
                let id2 = tri_id[(im[0] * pts + im[1]) * pts + im[2]];
                if orb_of[id2] != usize::MAX && orb_of[id2] != n_orbs {
                    panic!("Orbit collision!");
                }
                orb_of[id2] = n_orbs;
            }
        }
        n_orbs += 1;
    }
    assert_eq!(n_orbs, orb_cols.len(), "Orbit count mismatch!");

    // Build explicit flat table `col3[(a*pts + b)*pts + c]` for ALL ordered/unordered triples!
    let mut col3 = vec![0u8; pts * pts * pts];
    let mut cnt_c = [0u64; 3];
    for (ti, &[a, b, c]) in triples.iter().enumerate() {
        let cc = orb_cols[orb_of[ti]];
        cnt_c[cc as usize] += 1;
        col3[(a * pts + b) * pts + c] = cc;
    }

    // Exhaustively check ALL C(pts, 4) 4-subsets with ZERO symmetry assumptions!
    let mut total_4 = 0u64;
    for p0 in 0..(pts - 3) {
        for p1 in (p0 + 1)..(pts - 2) {
            let c01_base = p0 * pts + p1;
            for p2 in (p1 + 1)..(pts - 1) {
                let t012 = col3[c01_base * pts + p2];
                for p3 in (p2 + 1)..pts {
                    total_4 += 1;
                    let t013 = col3[c01_base * pts + p3];
                    if t013 != t012 { continue; }
                    let t023 = col3[(p0 * pts + p2) * pts + p3];
                    if t023 != t012 { continue; }
                    let t123 = col3[(p1 * pts + p2) * pts + p3];
                    if t123 == t012 {
                        panic!("VIOLATION: Monochromatic colour-{} 4-subset {{{}, {}, {}, {}}}!", t012, p0, p1, p2, p3);
                    }
                }
            }
        }
    }
    println!(
        "[CLEAN-ROOM ZERO-SYMMETRY PASS] pts={} (|H|={}, orbs={}), triples={:?}, ALL {} 4-subsets checked in {:.3}s -> R(4, 4, 4; 3) >= {} VERIFIED 100%!!",
        pts, mults.len(), n_orbs, cnt_c, total_4, t0.elapsed().as_secs_f64(), pts + 1
    );
}
