"""An optimal configuration of Q-(7,2) built on the incidence graph of PG(2,2).

Take two disjoint generators (planes) U, W of the elliptic quadric, a basis u_i of U and the dual basis w_j of W
(B(u_i, w_j) = delta_ij), and the anisotropic line {e, f, e+f} = (U+W)^perp.  The group G = GL(3,2) x C_3 acts by
u -> A u, w -> A^{-T} w and by the rotation e -> f -> e+f; with the sign corrections of Lemma "clifford" it permutes
the unsatisfied configurations.  We list the G-invariant ones by linear algebra over F_2 on the line orbits and
check that the smallest have 315 lines: the 21 lines {a, b, a+b} with a in U, b in W, B(a, b) = 0 (the incidence
graph of PG(2,2), with the 21 midpoints a+b), one orbit of 126 lines through one midpoint, and one of 168 lines
through no point of U, W or the midpoints.  An explicit assignment violating exactly such a configuration is
computed and checked.  U and W are read off from the witness of witness_315.py, whose violated set has this shape.
    python invariant_elliptic.py"""
import itertools, sys
from collections import Counter
from group import signed, pts, lines, Q, IDX
from common import symp
from witness_315 import WITNESS

PS = set(pts)
one = set(WITNESS)
viol = [l for l in lines if (l[0] in one) ^ (l[1] in one) ^ (l[2] in one) ^ l[3]]
assert len(viol) == 315
deg = Counter(p for l in viol for p in l[:3])
assert sorted(Counter(deg.values()).items()) == [(3, 14), (7, 21), (9, 84)]


def closure(S):
    S = set(S)
    while True:
        n = S | {a ^ b for a in S for b in S if a != b}
        if n == S:
            return S
        S = n


A = [p for p in pts if deg[p] == 3]
U = closure({A[0]} | {b for b in A if b != A[0] and symp(A[0], b) == 0 and (A[0] ^ b) in set(A)})
W = set(A) - U
assert len(U) == 7 and len(W) == 7 and closure(W) == W
assert all(symp(a, b) == 0 for a in U for b in U) and all(symp(a, b) == 0 for a in W for b in W)
u = next(list(t) for t in itertools.combinations(sorted(U), 3) if len(closure(t)) == 7)
w = [next(x for x in sorted(W) if all(symp(u[j], x) == (i == j) for j in range(3))) for i in range(3)]
e, f = [x for x in range(1, 256) if all(symp(x, y) == 0 for y in u + w)][:2]
assert Q(e) == Q(f) == Q(e ^ f) == 1


def build(a, b, c, d):
    x = 0
    for i in range(3):
        x ^= u[i] * a[i] ^ w[i] * b[i]
    return x ^ e * c ^ f * d


coords = {}
for m in range(256):
    a = [m >> i & 1 for i in range(3)]; b = [m >> (3 + i) & 1 for i in range(3)]
    coords[build(a, b, m >> 6 & 1, m >> 7 & 1)] = (a, b, m >> 6 & 1, m >> 7 & 1)
assert len(coords) == 256


def mv(M, a):
    return [sum(M[i][j] & a[j] for j in range(3)) & 1 for i in range(3)]


def invT(M):
    for c in itertools.product([0, 1], repeat=9):
        N = [list(c[0:3]), list(c[3:6]), list(c[6:9])]
        if all(sum(M[i][k] & N[k][j] for k in range(3)) % 2 == (i == j) for i in range(3) for j in range(3)):
            return [[N[j][i] for j in range(3)] for i in range(3)]


gens = []
for M in ([[1, 1, 0], [0, 1, 0], [0, 0, 1]], [[0, 0, 1], [1, 0, 0], [0, 1, 0]]):   # generate GL(3,2)
    MT = invT(M)
    gens.append({p: build(mv(M, coords[p][0]), mv(MT, coords[p][1]), coords[p][2], coords[p][3]) for p in pts})
gens.append({p: build(coords[p][0], coords[p][1], coords[p][3], coords[p][2] ^ coords[p][3]) for p in pts})
for g in gens:
    assert sorted(g.values()) == sorted(pts)
    signed(g)                       # raises unless the signs are preserved up to re-signing

L = [frozenset(l[:3]) for l in lines]
Lid = {l: i for i, l in enumerate(L)}
orb, no = [-1] * len(L), 0
for i in range(len(L)):
    if orb[i] < 0:
        stack, orb[i] = [i], no
        while stack:
            j = stack.pop()
            for g in gens:
                k = Lid[frozenset(g[p] for p in L[j])]
                if orb[k] < 0:
                    orb[k] = no; stack.append(k)
        no += 1
size = Counter(orb)
# unknowns: y_O (orbit O in the configuration) and x_p; equations 1_Y(line) = s(line) + x_a + x_b + x_c
piv = []
for i, (a, b, c, s) in enumerate(lines):
    m, r = (1 << orb[i]) | (1 << (no + IDX[a])) | (1 << (no + IDX[b])) | (1 << (no + IDX[c])), s
    for pm, pr, pb in piv:
        if m >> pb & 1:
            m ^= pm; r ^= pr
    if m == 0:
        assert r == 0
        continue
    pb = m.bit_length() - 1
    piv = [(qm ^ m, qr ^ r, qb) if qm >> pb & 1 else (qm, qr, qb) for qm, qr, qb in piv] + [(m, r, pb)]
pivrow = {pb: (m, r) for m, r, pb in piv}
free = [k for k in range(no + len(pts)) if k not in pivrow]
configs = {}
for bits in range(1 << len(free)):
    val = {k: bits >> t & 1 for t, k in enumerate(free)}
    def value(k):
        if k in val:
            return val[k]
        m, r = pivrow[k]
        return r ^ (sum(val[j] for j in free if m >> j & 1) & 1)
    y = tuple(O for O in range(no) if value(O))
    x = {p for p in pts if value(no + IDX[p])}
    configs.setdefault(y, x)
sizes = sorted((sum(size[O] for O in y), y) for y in configs)
print(f"{no} line orbits of G, sizes {sorted(size.values())}")
print("invariant unsatisfied configurations, smallest sizes:", [s for s, _ in sizes[:6]])
smin, y = sizes[0]
assert smin == 315
x = configs[y]
V = [l for l in lines if (l[0] in x) ^ (l[1] in x) ^ (l[2] in x) ^ l[3]]
assert {frozenset(l[:3]) for l in V} == {L[i] for i in range(len(L)) if orb[i] in y}
mid = {a ^ b for a in U for b in W if symp(a, b) == 0}
kinds = Counter(sum((p in U | W) * 2 + (p in mid) for p in l[:3]) for l in V)
print("orbit sizes of the smallest:", sorted(size[O] for O in y))
print("its lines by points in U+W (weight 2) and midpoints (weight 1):", dict(kinds))
assert sorted(size[O] for O in y) == [21, 126, 168] and kinds == Counter({5: 21, 1: 126, 0: 168})
print("checked: an assignment violates exactly this configuration of 315 lines")
