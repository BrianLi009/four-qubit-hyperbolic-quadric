"""Enumerate the violated sets of all optimal assignments of the real quadric Q_0 (the DW(5,2) theorem of the paper).

An assignment violates exactly 315 lines iff every doily of a family covering each line equally often has exactly
3 violated lines (the proposition on optimal assignments). We use the family of 2520 doilies of the Lean proof, which covers every line
24 times (24 * 315 = 3 * 2520): its data is read from lean/gen/order_perm.json and its 24-fold cover is checked here.

Variables: x_p (135 points), v_C (1575 lines) with v_C = x_a + x_b + x_c + s(C) (eight clauses each) and a
sequential-counter encoding of "exactly 3 of the 15 v_C" for each doily of the family, and the binary clauses
"not both" for any two intersecting lines of a common doily (implied for optimal assignments; --no-pairs omits them). The distinct violated sets are enumerated
with CaDiCaL (PySAT), blocking each one by the clause "not all of its lines are violated" (all sets have 315 lines).

Outputs: optimal_sets.json (each set as the sorted indices of its lines in the list `lines` stored with it) and,
with --cnf, the final formula (base + blocking clauses) in DIMACS for an independent DRAT check:
    cadical final.cnf final.drat ; drat-trim final.cnf final.drat
"""
import collections
import itertools
import json
import sys
import time
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from verify_facts import Q, quadric_lines, quadric_points, sign_bit, span, subspaces  # noqa: E402


def main():
    P0 = quadric_points(0)
    L0 = sorted(tuple(sorted(k)) for k in quadric_lines(0))
    pid = {p: i + 1 for i, p in enumerate(P0)}
    lid = {k: 136 + j for j, k in enumerate(L0)}
    fam = json.load(open(HERE.parent / "lean" / "gen" / "order_perm.json"))["doilies"]
    doilies = [[tuple(sorted((key // 256, key % 256, (key // 256) ^ (key % 256)))) for key in d] for d in fam]
    cover = collections.Counter(k for d in doilies for k in d)
    assert len(doilies) == 2520 and set(cover) == set(L0) and set(cover.values()) == {24}, "family is not a 24-fold cover"
    print("family: 2520 doilies covering each of the 1575 lines 24 times", flush=True)

    clauses = []
    for k in L0:
        s = sign_bit(k[0], k[1])
        vs = [lid[k]] + [pid[p] for p in k]
        for m in range(16):
            bits = [(m >> i) & 1 for i in range(4)]
            if sum(bits) % 2 != s:            # forbid v + x_a + x_b + x_c != s
                clauses.append([-x if b else x for x, b in zip(vs, bits)])
    # Redundant clauses (Proposition on doilies): in an optimal assignment the three violated lines of every doily
    # are pairwise disjoint, so two intersecting lines of a common doily are never both violated.
    pairs = set()
    if "--no-pairs" not in sys.argv:
        Lset = {frozenset(k) for k in L0}
        for rows in subspaces(8, 5):
            S = [v for v in span(rows) if v and Q(0, v) == 0]
            if len(S) != 15:
                continue
            ls = [tuple(sorted(t)) for t in itertools.combinations(S, 3) if frozenset(t) in Lset]
            if len(ls) == 15:
                pairs.update((k1, k2) for k1, k2 in itertools.combinations(sorted(ls), 2) if set(k1) & set(k2))
        clauses.extend([-lid[k1], -lid[k2]] for k1, k2 in sorted(pairs))
        print(f"{len(pairs)} pairs of intersecting lines sharing a doily", flush=True)
    top = 135 + 1575
    for d in doilies:
        enc = CardEnc.equals(lits=[lid[k] for k in d], bound=3, top_id=top, encoding=EncType.seqcounter)
        top = max(top, enc.nv)
        clauses.extend(enc.clauses)
    print(f"{len(clauses)} clauses, {top} variables", flush=True)

    sets, t0 = [], time.time()
    with Solver(name="cadical153", bootstrap_with=clauses) as solver:
        while solver.solve():
            model = solver.get_model()
            V = [j for j in range(1575) if model[135 + j] > 0]
            assert len(V) == 315
            sets.append(V)
            block = [-(136 + j) for j in V]
            clauses.append(block)
            solver.add_clause(block)
            if len(sets) % 20 == 0:
                print(f"  {len(sets)} sets, {time.time() - t0:.0f} s", flush=True)
    print(f"exactly {len(sets)} optimal violated sets ({time.time() - t0:.0f} s); the final formula is unsatisfiable")
    json.dump({"lines": L0, "sets": sets}, open(HERE / "optimal_sets.json", "w"))
    if "--cnf" in sys.argv:
        with open(HERE / "final.cnf", "w") as f:
            f.write(f"p cnf {top} {len(clauses)}\n")
            for c in clauses:
                f.write(" ".join(map(str, c)) + " 0\n")
        print("wrote final.cnf")


if __name__ == "__main__":
    main()
