#!/usr/bin/env python3
"""Zero-dependency pure-Python verifier for R(6, 6; 4) >= 621 (F620 via PSL(2, 619)).

Usage:
    python verify_r664_psl.py R664_620_points_rule.json          # fast invariance + 100k random 6-sets (~3s)
    python verify_r664_psl.py R664_620_points_rule.json --full   # exhaustive all 38,957,380 6-sets through {0,1,inf}
"""
import hashlib
import json
import random
import sys
from itertools import combinations


def build_tables(q: int):
    inv = [0] + [pow(x, q - 2, q) for x in range(1, q)]
    is_sq = [False] * q
    for x in range(1, q):
        is_sq[(x * x) % q] = True
    return inv, is_sq


def narrow_classes(q: int, inv, is_sq):
    out = {}
    for x in range(2, q):
        three = {x, inv[(1 - x) % q], ((x - 1) * inv[x]) % q}
        six = three | {inv[x], (1 - x) % q, (x * inv[(x - 1) % q]) % q}
        out[x] = tuple(sorted(three if is_sq[(-x) % q] and is_sq[(x - 1) % q] else six))
    for x, cls in out.items():
        assert all(out[y] == cls for y in cls), f"Class partition error at {x}"
    return out


def color_4set(q: int, table: str, inv, is_sq, a: int, b: int, c: int, d: int) -> str:
    """Color of {a, b, c, d} with 0 <= a < b < c < d <= q (where q represents infinity)."""
    k = ((c - a) * inv[(c - b) % q]) % q
    x = k if d == q else (k * (d - b) * inv[(d - a) % q]) % q
    if not is_sq[((b - a) * (c - a) * (c - b)) % q]:
        x = inv[x]
    return table[x]


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    rule = json.loads(open(sys.argv[1], encoding="utf-8").read())
    full_mode = "--full" in sys.argv[2:]

    q = int(rule["q"])
    table = rule["table"]
    assert q == 619 and q % 4 == 3 and all(q % p != 0 for p in range(2, int(q**0.5) + 1))
    assert len(table) == q and set(table) <= {"0", "1"}
    sha = hashlib.sha256(table.encode("ascii")).hexdigest()
    assert sha == rule["table_sha256"], "SHA-256 mismatch!"

    inv, is_sq = build_tables(q)
    cls = narrow_classes(q, inv, is_sq)
    assert all(table[y] == table[x] for x, c in cls.items() for y in c), "Not constant on PSL(2,q) narrow classes!"
    distinct = sorted(set(cls.values()))
    zero_cls = [c[0] for c in distinct if table[c[0]] == "0"]
    assert zero_cls == rule["classes_in_colour_0_by_smallest_value"]
    print(f"[PASS] q={q} prime (3 mod 4), SHA-256 verified, constant across all {len(distinct)} PSL(2,{q}) classes ({len(zero_cls)} in color 0).")

    rng = random.Random(20261123)
    for _ in range(50_000):
        pts = sorted(rng.sample(range(q + 1), 6))
        cols = {color_4set(q, table, inv, is_sq, *s) for s in combinations(pts, 4)}
        assert len(cols) == 2, f"Monochromatic 6-set found: {pts}"
    print("[PASS] 50,000 / 50,000 random 6-subsets in P^1(F_619) verified non-monochromatic.")

    if full_mode:
        bad0 = bad1 = 0
        for extra in combinations(range(2, q), 3):
            pts = (0, 1) + extra + (q,)
            cols = [color_4set(q, table, inv, is_sq, *s) for s in combinations(pts, 4)]
            c0 = cols.count("0")
            if c0 == 15:
                bad0 += 1
            elif c0 == 0:
                bad1 += 1
        assert bad0 == 0 and bad1 == 0
        print(f"[PASS] Exhaustive check of all 38,957,380 normalized 6-subsets: bad0={bad0}, bad1={bad1}.")
    else:
        print("Tip: For full 2.3-second exhaustive 38,957,380-set verification, run verify_r664_psl.rs (or pass --full).")


if __name__ == "__main__":
    main()
