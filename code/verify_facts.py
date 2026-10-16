"""Recompute every finite fact used in the paper for the four-qubit hyperbolic quadric Q+(7,2).

Points are encoded as integers v < 256: bit i is x_i and bit i+4 is z_i (qubit i carries I, X, Z, Y for
(x_i, z_i) = (0,0), (1,0), (0,1), (1,1)), as in the Lean development. Signs of contexts are computed from the
single-qubit Pauli multiplication rule and compared with products of 16 x 16 Pauli matrices (w72.py).

Usage:  python verify_facts.py [--brute]
  --brute also computes the exact degree (3) of every doily by brute force over its 2^15 assignments
          (a few minutes).
Exits with status 1 if any check fails.
"""
import collections
import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FAILED = []


def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + (f"  [{detail}]" if detail else ""), flush=True)
    if not cond:
        FAILED.append(name)


def xb(v, i): return (v >> i) & 1
def zb(v, i): return (v >> (i + 4)) & 1
def symp(u, v): return (bin((u & 15) & (v >> 4)).count("1") + bin((u >> 4) & (v & 15)).count("1")) & 1
def nY(v): return bin((v & 15) & (v >> 4)).count("1")
def Q(a, v): return (nY(v) + symp(a, v)) & 1          # the 256 quadratic forms polarising to symp


# single-qubit rule: sigma(x,z) sigma(x',z') = i^k sigma(x+x', z+z'); nonzero k only for X*Y, Y*Z, Z*X and reverses
P1 = {(1, 0, 1, 1): 1, (1, 1, 1, 0): 3, (1, 1, 0, 1): 1, (0, 1, 1, 1): 3, (0, 1, 1, 0): 1, (1, 0, 0, 1): 3}
def phase(u, v): return sum(P1.get((xb(u, i), zb(u, i), xb(v, i), zb(v, i)), 0) for i in range(4)) % 4
def sign_bit(a, b):
    """1 iff P(a) P(b) P(a+b) = -I (a, b commuting); P(a)P(b) = i^phase P(a+b)."""
    k = phase(a, b)
    assert k in (0, 2)
    return k // 2


def word(v): return "".join("IXZY"[xb(v, i) + 2 * zb(v, i)] for i in range(4))


def quadric_points(a): return [v for v in range(1, 256) if Q(a, v) == 0]
def quadric_lines(a):
    pts = set(quadric_points(a))
    return [frozenset((p, q, p ^ q)) for p in pts for q in pts if p < q < (p ^ q) and (p ^ q) in pts and not symp(p, q)]


def span(gens):
    S = {0}
    for g in gens:
        S |= {s ^ g for s in S}
    return S


def subspaces(n, k):
    """All k-dimensional subspaces of F_2^n, by reduced row echelon forms."""
    for piv in itertools.combinations(range(n), k):
        free = [(r, c) for r in range(k) for c in range(n) if c > piv[r] and c not in piv]
        for bits in itertools.product((0, 1), repeat=len(free)):
            rows = [1 << p for p in piv]
            for (r, c), b in zip(free, bits):
                if b:
                    rows[r] |= 1 << c
            yield rows


def grids_of(ls):
    """The 3 x 3 grids among the lines ls: three pairwise disjoint lines (a ruling) together with three pairwise
    disjoint lines each meeting all of them. Each grid is found from both of its rulings, hence the set."""
    n = len(ls)
    meet = [sum(1 << j for j in range(n) if j != i and ls[i] & ls[j]) for i in range(n)]
    out = set()
    for i, j, k in itertools.combinations(range(n), 3):
        if (meet[i] >> j) & 1 or (meet[i] >> k) & 1 or (meet[j] >> k) & 1:
            continue
        T = meet[i] & meet[j] & meet[k]
        t = [m for m in range(n) if (T >> m) & 1]
        if len(t) == 3 and not any((meet[a] >> b) & 1 for a, b in itertools.combinations(t, 2)):
            out.add(frozenset(ls[m] for m in (i, j, k, *t)))
    return list(out)


def main():
    brute = "--brute" in sys.argv
    # --- the space and its quadrics -------------------------------------------------------------
    hyp = [a for a in range(256) if len(quadric_points(a)) == 135]
    ell = [a for a in range(256) if len(quadric_points(a)) == 119]
    check("256 quadratic forms: 136 hyperbolic (135 points), 120 elliptic (119 points)", len(hyp) == 136 and len(ell) == 120)
    check("hyperbolic iff a = 0 or Q_0(a) = 0", set(hyp) == {0} | {a for a in range(1, 256) if Q(0, a) == 0})
    P0 = quadric_points(0)
    L0 = quadric_lines(0)
    sg = {k: sign_bit(*sorted(k)[:2]) for k in L0}
    check("Q_0 = observables with an even number of Y's = real symmetric Pauli operators", all(nY(v) % 2 == 0 for v in P0))
    check("Q_0: 135 points, 1575 lines, 35 lines per point", len(P0) == 135 and len(L0) == 1575
          and set(collections.Counter(p for k in L0 for p in k).values()) == {35})
    check("Q_0: 532 negative lines", sum(sg.values()) == 532, sum(sg.values()))
    # signs from matrices
    sys.path.insert(0, str(HERE))
    import w72
    enc = lambda t: sum(t[i] << i for i in range(8))
    msign = {frozenset(enc(p) for p in l[:3]): l[3] for l in w72.lines}
    check("signs from the phase rule agree with 16x16 matrix products", all(msign[k] == s for k, s in sg.items()))
    classes = collections.Counter()
    for a in hyp:
        La = quadric_lines(a)
        classes[sum(sign_bit(*sorted(k)[:2]) for k in La)] += 1
    check("negative lines over the 136 hyperbolic quadrics: 532 (81), 604 (54), 612 (1)",
          classes == collections.Counter({532: 81, 604: 54, 612: 1}), dict(classes))
    W = sum(1 for p in range(1, 256) for q in range(p + 1, 256) if not symp(p, q) and q < (p ^ q))
    check("W(7,2): 255 points, 5355 lines; each line on 40 hyperbolic quadrics",
          W == 5355 and all(sum(1 for a in hyp if Q(a, p) == 0 and Q(a, q) == 0) == 40
                            for p, q in [(1, 2), (3, 0x30), (0x11, 0x22)]))

    # --- doilies and grids of Q_0 ---------------------------------------------------------------
    Lset = set(L0)
    doilies = []
    for rows in subspaces(8, 5):
        S = [v for v in span(rows) if v and Q(0, v) == 0]
        if len(S) != 15:
            continue
        ls = [frozenset(t) for t in itertools.combinations(S, 3) if frozenset(t) in Lset]
        if len(ls) == 15 and set(collections.Counter(p for k in ls for p in k).values()) == {3}:
            doilies.append(ls)
    check("Q_0 contains 40320 doilies (parabolic sections Q(4,2) = GQ(2,2))", len(doilies) == 40320, len(doilies))
    cover = collections.Counter(k for ls in doilies for k in ls)
    check("every line of Q_0 lies in exactly 384 doilies (= 40320 * 15 / 1575)", set(cover.values()) == {384})
    all_grids = set()
    ok_ten = ok_four = ok_two = True
    for ls in doilies:
        G = grids_of(ls)
        all_grids.update(G)
        ok_ten &= len(G) == 10
        ok_four &= set(collections.Counter(k for g in G for k in g).values()) == {4}
        for k1, k2 in itertools.combinations(ls, 2):
            if k1 & k2:
                ok_two &= sum(1 for g in G if k1 in g and k2 in g) == 2
    check("every doily contains exactly 10 grids", ok_ten)
    check("every line of a doily lies in exactly 4 of its grids", ok_four)
    check("two intersecting lines of a doily lie in exactly 2 common grids", ok_two)
    odd = all(sum(sg[k] for k in g) % 2 == 1 for g in all_grids)
    noncol = all(symp(p, q) == 1 for g in all_grids for p, q in itertools.combinations({x for k in g for x in k}, 2)
                 if not any(p in k and q in k for k in g))
    check(f"Q_0 contains {len(all_grids)} grids; non-collinear points of a grid anticommute", noncol)
    check("every grid of Q_0 has an odd number of negative lines (Peres-Mermin)", odd)
    if brute:
        import numpy as np
        xs = np.arange(1 << 15, dtype=np.int64)
        degs = collections.Counter()
        for ls in doilies:
            idx = {p: i for i, p in enumerate(sorted({p for k in ls for p in k}))}
            viol = np.zeros(1 << 15, dtype=np.int64)
            for k in ls:
                a, b, c = (idx[p] for p in k)
                viol += (((xs >> a) ^ (xs >> b) ^ (xs >> c)) & 1) != sg[k]
            degs[int(viol.min())] += 1
        check("every doily of Q_0 has degree exactly 3 (brute force)", degs == collections.Counter({3: 40320}), dict(degs))

    # --- the witness ------------------------------------------------------------------------------
    w = json.load(open(HERE / "witness.json"))
    x = {enc(p): b for p, b in zip(w["points"], w["assignment"])}
    V = {k for k in L0 if (sum(x[p] for p in k) & 1) != sg[k]}
    check("the witness violates exactly 315 lines of Q_0", len(V) == 315)
    check("each point lies on exactly 7 violated lines", set(collections.Counter(p for k in V for p in k).values()) == {7})
    ruling = True
    for ls in doilies:
        Vd = [k for k in ls if k in V]
        ruling &= len(Vd) == 3 and all(not (k1 & k2) for k1, k2 in itertools.combinations(Vd, 2)) \
            and any(set(Vd) <= g for g in grids_of(ls))
    check("in every doily the witness violates exactly 3 lines, pairwise disjoint, lying in one grid", ruling)
    print("points with value 1 (outcome -1):", " ".join(sorted(word(v) for v in P0 if x[v])))

    # --- transport to every hyperbolic quadric --------------------------------------------------
    # For singular r (Q_0(r) = 0) the transvection t_r(v) = v + symp(v,r) r maps Q_r onto Q_0, and the Clifford
    # unitary (I + i P(r)) / sqrt 2 conjugates P(v) to P(v) or to i P(r) P(v) = +-P(v + r). Re-signing by those signs
    # transports the witness of Q_0 to an assignment of Q_r with the same violated lines.
    ok = True
    for r in hyp:
        if r == 0:
            continue
        def t(v): return v ^ r if symp(v, r) else v
        def tau(v):          # i P(r) P(v) = i^(1 + phase(r, v)) P(r + v)
            return 0 if not symp(v, r) else ((1 + phase(r, v)) % 4) // 2
        Lr = quadric_lines(r)
        # assignment of Q_r: y(v) = x(t v) + tau(v), where P(v) is carried to (-1)^tau(v) P(t v)
        y = {v: x[t(v)] ^ tau(v) for v in quadric_points(r)}
        nv = sum(1 for k in Lr if (sum(y[p] for p in k) & 1) != sign_bit(*sorted(k)[:2]))
        ok &= all(Q(0, t(v)) == 0 for v in quadric_points(r)) and nv == 315
    check("the transported witness violates exactly 315 lines on each of the 136 hyperbolic quadrics", ok)

    print()
    print("ALL CHECKS PASSED" if not FAILED else f"{len(FAILED)} CHECK(S) FAILED: {FAILED}")
    sys.exit(1 if FAILED else 0)


if __name__ == "__main__":
    main()
