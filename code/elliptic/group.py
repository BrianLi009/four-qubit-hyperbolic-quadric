"""Symmetries of the signed configuration Q-(7,2) fixing a vector v0 off the quadric.
Orthogonal reflections r_u(x) = x + B(x,u) u (Q(u) = 1, u ⊥ v0) preserve the quadric and v0; each acts on
assignments as x'_{g(p)} = x_p + c_p with a correction c solving s(g l) + s(l) = c_a + c_b + c_c for every line.
The correction is found by F2 elimination and the identity is checked on all 1071 lines."""
from __future__ import annotations

import random
from common import load, symp, N

pts, lines = load()
P = set(pts)
SIGN = {frozenset(l[:3]): l[3] for l in lines}


def Qform():
    """Quadratic form whose zeros are the points: Q(v) = |x & z| + B(v, a) (find a)."""
    m = (1 << N) - 1
    q0 = lambda v: bin((v >> N) & v & m).count("1") & 1
    for a in range(256):
        if all((q0(v) ^ symp(v, a)) == (0 if v in P else 1) for v in range(1, 256)):
            return lambda v, a=a: q0(v) ^ symp(v, a)
    raise ValueError


Q = Qform()


def solve_f2(rows, n):
    """rows: list of (mask over n unknowns, rhs). Return one solution or None."""
    piv = []
    for mask, rhs in rows:
        for pm, pr, pb in piv:
            if mask >> pb & 1:
                mask ^= pm; rhs ^= pr
        if mask == 0:
            if rhs:
                return None
            continue
        pb = mask.bit_length() - 1
        new = []
        for qm, qr, qb in piv:
            if qm >> pb & 1:
                qm ^= mask; qr ^= rhs
            new.append((qm, qr, qb))
        piv = new + [(mask, rhs, pb)]
    sol = 0
    for mask, rhs, pb in piv:  # fully reduced: each pivot row has only free vars besides pb; set free = 0
        if rhs:
            sol |= 1 << pb
    return sol


IDX = {p: i for i, p in enumerate(pts)}


def signed(g):
    """g: dict point -> point (a symmetry of the geometry). Return correction c as dict, verified."""
    rows = []
    for a, b, c, s in lines:
        t = SIGN[frozenset((g[a], g[b], g[c]))]
        rows.append(((1 << IDX[a]) | (1 << IDX[b]) | (1 << IDX[c]), s ^ t))
    sol = solve_f2(rows, len(pts))
    assert sol is not None, "no sign correction"
    c = {p: (sol >> IDX[p]) & 1 for p in pts}
    for a, b, cc, s in lines:
        assert SIGN[frozenset((g[a], g[b], g[cc]))] == s ^ c[a] ^ c[b] ^ c[cc]
    return c


def reflection(u):
    return {p: (p ^ u) if symp(p, u) else p for p in pts}


def generators(v0, k=6, seed=0):
    import os; seed = int(os.environ.get("GEN_SEED", seed))
    rng = random.Random(seed)
    us = [u for u in range(1, 256) if Q(u) == 1 and symp(u, v0) == 0 and u != v0]
    gens = []
    for u in rng.sample(us, k):
        g = reflection(u)
        assert all(g[p] in P for p in pts) and all(symp(g[p], v0) == symp(p, v0) for p in pts)
        gens.append((g, signed(g)))
    return gens
