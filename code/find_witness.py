"""Find a +-1 assignment of the 135 quadric points violating as few lines as possible (local search)."""
import itertools, random, json
import numpy as np
from w72 import points, lines, quadric, N
a0 = next(a for a in itertools.product((0, 1), repeat=2 * N) if len(quadric(a)) == 135)
Q = sorted(quadric(a0)); idx = {p: i for i, p in enumerate(Q)}
L = [(idx[a], idx[b], idx[c], s) for (a, b, c, s) in lines if a in idx and b in idx and c in idx]
inc = [[] for _ in Q]
for k, (a, b, c, s) in enumerate(L):
    for p in (a, b, c): inc[p].append(k)
def viol(x): return sum((x[a] ^ x[b] ^ x[c]) != s for a, b, c, s in L)
rng = random.Random(1); best = None
for restart in range(200):
    x = [rng.randint(0, 1) for _ in Q]
    v = viol(x); improved = True
    while improved:
        improved = False
        for p in rng.sample(range(len(Q)), len(Q)):
            d = sum(1 if (x[L[k][0]] ^ x[L[k][1]] ^ x[L[k][2]]) == L[k][3] else -1 for k in inc[p])   # flipping p: satisfied->violated (+1)
            if d < 0: x[p] ^= 1; v += d; improved = True
    if best is None or v < best[0]:
        best = (v, list(x))
        if v <= 315: break
v, x = best
assert v == viol(x)
print("best assignment violates", v, "of", len(L), "lines")
json.dump({"quadric_a": list(a0), "points": [list(p) for p in Q], "assignment": x, "violated": v}, open("witness_found.json", "w"))
