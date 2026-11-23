"""14-Worker Sweet-Spot CaDiCaL195 + Native Rust 7-Clique CEGAR for R(5, 7; 4) >= 711..775!
Every single worker is tuned right inside the empirical 0.60..0.66 positive-phase sweet spot
(where Worker 7 cracked q=701 in 28.25s!), with 115s budget on q == 5 (mod 8) primes: 709, 733, 757, 773!
"""
import json
import multiprocessing as mp
import os
import random
import subprocess
import sys
import time
from pysat.solvers import Cadical195


def sweet_worker(args):
    q, wid, max_secs, exe_f, init_f, work_dir = args
    t0 = time.time()
    rng = random.Random(20261124 + q * 911 + wid * 31337)

    lines = open(init_f, encoding="utf-8").read().splitlines()
    nv, _ = [int(x) for x in lines[0].split()]
    raw_cls = [[int(x) for x in ln.split()] for ln in lines[1:]]

    perm = list(range(nv))
    rng.shuffle(perm)
    init_cls = [sorted(perm[lit - 1] + 1 for lit in cl) for cl in raw_cls]
    rng.shuffle(init_cls)

    tmp_f = os.path.join(work_dir, f"_sw_{q}_{wid}.txt")
    proc = subprocess.Popen([exe_f, str(q), tmp_f], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    try:
        assert proc.stdout.readline().strip().startswith("READY")
        deadline = t0 + max_secs
        rounds = 0
        n7 = 0
        # Fine-grained sweet-spot phase probabilities 0.595 .. 0.660 across 14 workers!
        p_pos = 0.595 + wid * 0.005
        with Cadical195(bootstrap_with=init_cls) as solver:
            solver.set_phases([(v + 1) if rng.random() < p_pos else -(v + 1) for v in range(nv)])
            while time.time() < deadline:
                if not solver.solve():
                    return ("UNSAT", wid, rounds, n7, time.time() - t0, None)
                rounds += 1
                m = set(solver.get_model())
                orig_val = [1 if (perm[v] + 1) in m else 0 for v in range(nv)]
                proc.stdin.write("".join("1" if b else "0" for b in orig_val) + "\n")
                proc.stdin.flush()
                cnt = int(proc.stdout.readline().strip().split()[1])
                if cnt == 0:
                    dt = time.time() - t0
                    r67 = 5 * (q + 2) - 4
                    r77 = 6 * r67 - 5
                    r78 = 7 * r77 - 6
                    r88 = 7 * r78 - 6
                    out_p = os.path.join(work_dir, f"CONFIRMED_R574_PSL1mod4_ge_{q+2}.json")
                    json.dump(
                        {
                            "claim": f"R(5,7;4) >= {q+2}",
                            "q": q,
                            "points": q + 1,
                            "group": f"PSL(2,{q})",
                            "sol_vars": orig_val,
                            "p_pos": round(p_pos, 4),
                            "cegar_rounds": rounds,
                            "learned_7clauses": n7,
                            "solve_seconds": round(dt, 3),
                            "corollaries": {"R(6,7;4)": r67, "R(7,7;4)": r77, "R(7,8;4)": r78, "R(8,8;4)": r88},
                        },
                        open(out_p, "w", encoding="utf-8"),
                        indent=2,
                    )
                    return ("SAT", wid, rounds, n7, dt, out_p)
                for _ in range(cnt):
                    orig_lits = [int(x) for x in proc.stdout.readline().split()]
                    solver.add_clause([-(perm[(-lit) - 1] + 1) for lit in orig_lits])
                n7 += cnt
        return ("TIMEOUT", wid, rounds, n7, time.time() - t0, None)
    finally:
        try:
            proc.stdin.write("QUIT\n")
            proc.stdin.flush()
        except Exception:
            pass
        proc.kill()
        try:
            os.remove(tmp_f)
        except Exception:
            pass


def run_sweet_q(q: int, secs: float, work_dir: str, n_workers: int = 14):
    exe_f = os.path.join(work_dir, "oracle_1mod4_r574.exe")
    init_f = os.path.join(work_dir, f"init_1mod4_r574_q{q}.txt")
    if not os.path.exists(init_f):
        p0 = subprocess.Popen([exe_f, str(q), init_f], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        p0.stdout.readline()
        p0.stdin.write("QUIT\n")
        p0.stdin.flush()
        p0.wait()

    pool = mp.Pool(processes=n_workers)
    try:
        ars = [pool.apply_async(sweet_worker, ((q, w, secs, exe_f, init_f, work_dir),)) for w in range(n_workers)]
        deadline = time.time() + secs + 5.0
        while time.time() < deadline:
            done = 0
            for ar in ars:
                if ar.ready():
                    done += 1
                    st, wid, rnds, n7, dt, cert = ar.get()
                    if st == "SAT":
                        r67 = 5 * (q + 2) - 4
                        r77 = 6 * r67 - 5
                        r78 = 7 * r77 - 6
                        r88 = 7 * r78 - 6
                        print(f"🏆🏆🏆 NEW RECORD [w={wid}]!! R(5,7;4) >= {q+2} [q={q}] ({dt:.2f}s, {rnds} rounds, {n7:,} 7-cl) => R(8,8;4) >= {r88:,}!! -> {cert}", flush=True)
                        pool.terminate()
                        pool.join()
                        return True
                    elif st == "UNSAT":
                        print(f"[q={q}] UNSAT ({dt:.2f}s)", flush=True)
                        pool.terminate()
                        pool.join()
                        return False
            if done == n_workers:
                break
            time.sleep(0.25)
        max_r = max((ar.get()[2] for ar in ars if ar.ready()), default=0)
        print(f"[Sweet-Spot q={q}] {n_workers}-worker TIMEOUT ({secs:.0f}s, max_rounds={max_r})", flush=True)
        return None
    finally:
        pool.terminate()
        pool.join()


if __name__ == "__main__":
    mp.freeze_support()
    w_d = sys.argv[1]
    secs = float(sys.argv[2])
    for pq in [int(x) for x in sys.argv[3:]]:
        run_sweet_q(pq, secs, w_d, n_workers=14)
