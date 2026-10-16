"""Baselines without the mathematics of the paper: the degree of Q_0 attacked directly.

  maxsat : MaxSAT. Hard clauses v_C <-> (x_a + x_b + x_c != s(C)) (eight per line), soft clauses (not v_C) of weight 1;
           RC2 (PySAT) computes the least number of violated lines.
  card   : SAT. The same hard clauses and "at most 314 violated lines" (totalizer encoding); unsatisfiable iff the
           degree is at least 315.
Both are run with a time limit by sat_direct.sh. Usage: python sat_direct.py maxsat|card
"""
import sys
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
from pysat.solvers import Solver

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_facts import quadric_lines, quadric_points, sign_bit  # noqa: E402


def xor_clauses():
    P0 = quadric_points(0)
    L0 = sorted(tuple(sorted(k)) for k in quadric_lines(0))
    pid = {p: i + 1 for i, p in enumerate(P0)}
    out, vlits = [], []
    for j, k in enumerate(L0):
        v = 136 + j
        vlits.append(v)
        s = sign_bit(k[0], k[1])
        vs = [v] + [pid[p] for p in k]
        for m in range(16):
            bits = [(m >> i) & 1 for i in range(4)]
            if sum(bits) % 2 != s:
                out.append([-x if b else x for x, b in zip(vs, bits)])
    return out, vlits


def main():
    mode = sys.argv[1]
    hard, vlits = xor_clauses()
    t0 = time.time()
    if mode == "maxsat":
        w = WCNF()
        for c in hard:
            w.append(c)
        for v in vlits:
            w.append([-v], weight=1)
        print(f"MaxSAT: {len(hard)} hard clauses, {len(vlits)} soft clauses", flush=True)
        with RC2(w, verbose=0) as rc2:
            rc2.compute()
            print(f"optimum: {rc2.cost} violated lines ({time.time() - t0:.1f} s)")
    elif mode == "card":
        enc = CardEnc.atmost(lits=vlits, bound=314, top_id=1710, encoding=EncType.totalizer)
        cls = hard + enc.clauses
        print(f"SAT: {enc.nv} variables, {len(cls)} clauses (at most 314 violated lines)", flush=True)
        with Solver(name="cadical153", bootstrap_with=cls) as s:
            r = s.solve()
        print(f"{'SATISFIABLE' if r else 'UNSATISFIABLE'} ({time.time() - t0:.1f} s)")


if __name__ == "__main__":
    main()
