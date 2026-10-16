"""All doilies (GQ(2,2) = parabolic sections Q(4,2)) inside a hyperbolic quadric Q+(7,2) of the 4-qubit
Pauli space; their line coverage and their exact contextuality degrees (brute force over 2^15)."""
import itertools, collections, time
import numpy as np
from w72 import points, lines, quadric, symp, N
a0 = next(a for a in itertools.product((0, 1), repeat=2 * N) if len(quadric(a)) == 135)
Q = quadric(a0)
Qlines = [l for l in lines if all(p in Q for p in l[:3])]
lineset = {frozenset(l[:3]): l for l in Qlines}
pt_index = {p: i for i, p in enumerate(points)}

def span(gens):
    S = {tuple([0] * (2 * N))}
    for g in gens:
        S |= {tuple((a + b) % 2 for a, b in zip(s, g)) for s in S}
    return S

# enumerate 5-dim subspaces via sets of 5 independent vectors in reduced echelon form
def rref_subspaces(n, k):
    for pivots in itertools.combinations(range(n), k):
        free = [(r, c) for r in range(k) for c in range(n) if c > pivots[r] and c not in pivots]
        for bits in itertools.product((0, 1), repeat=len(free)):
            M = [[0] * n for _ in range(k)]
            for r, p in enumerate(pivots): M[r][p] = 1
            for (r, c), b in zip(free, bits): M[r][c] = b
            yield [tuple(row) for row in M]

def degree15(pts, ls):
    idx = {p: i for i, p in enumerate(pts)}
    A = np.array([[(x >> idx[a]) & 1 ^ (x >> idx[b]) & 1 ^ (x >> idx[c]) & 1 for (a, b, c, s) in ls] for x in range(1 << 15)], dtype=np.uint8) if False else None
    xs = np.arange(1 << 15, dtype=np.int64)
    viol = np.zeros(1 << 15, dtype=np.int64)
    for (a, b, c, s) in ls:
        par = ((xs >> idx[a]) ^ (xs >> idx[b]) ^ (xs >> idx[c])) & 1
        viol += (par != s)
    return int(viol.min())


if __name__ == "__main__":
    t0 = time.time()
    doilies = []
    for gens in rref_subspaces(2 * N, 5):
        V = span(gens)
        sing = [v for v in V if any(v) and v in Q]
        if len(sing) != 15: continue
        ls = [lineset[frozenset(t)] for t in itertools.combinations(sing, 3) if frozenset(t) in lineset]
        if len(ls) != 15: continue
        # GQ(2,2): every point on exactly 3 lines
        deg = collections.Counter(p for l in ls for p in l[:3])
        if any(deg[p] != 3 for p in sing): continue
        doilies.append((sing, ls))
    print(len(doilies), "doilies inside Q+(7,2)", round(time.time() - t0, 1), "s")
    cover = collections.Counter(frozenset(l[:3]) for _, ls in doilies for l in ls)
    print("times each quadric line lies in a doily:", collections.Counter(cover[frozenset(l[:3])] for l in Qlines))

    t0 = time.time()
    degs = collections.Counter(degree15(p, l) for p, l in doilies)
    print("doily degrees:", degs, round(time.time() - t0, 1), "s")
