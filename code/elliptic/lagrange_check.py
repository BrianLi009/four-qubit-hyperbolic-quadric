"""Separately written check of inner_bb.c on sampled leaves: the inner problem is rebuilt from the instance lines
(leafinfo.py, not zdata.txt), and the Lagrangian bound over the doily family of hdata.txt is recomputed in NumPy
with its own subgradient loop.  A leaf counts as confirmed when the bound exceeds TARGET - 1.
    python lagrange_check.py hdata.txt leaves.txt N_SAMPLES [TARGET]"""
import sys, random
import numpy as np
from leafinfo import HL, unary

hd = open(sys.argv[1]).read().split("\n")
nH, nL, nD = map(int, hd[0].split())
fam = []
for row in hd[1 + nL:1 + nL + nD]:
    t = list(map(int, row.split()))
    fam.append((t[:15], t[15:]))
TARGET = int(sys.argv[4]) if len(sys.argv) > 4 else 315
lc = np.zeros(nL); pc = np.zeros(nH)
for p, l in fam:
    lc[l] += 1; pc[p] += 1
assert lc.min() == lc.max() and pc.min() == pc.max()
lam = 1 / lc[0]
X = np.arange(1 << 15)
bits = ((X[:, None] >> np.arange(15)) & 1).astype(np.float64)
VI = np.zeros((nD, 1 << 15))
P = np.array([p for p, l in fam])
for j, (p, l) in enumerate(fam):
    pi = {q: k for k, q in enumerate(p)}
    for li in l:
        a, b, c, s = HL[li]
        VI[j] += ((X >> pi[a]) ^ (X >> pi[b]) ^ (X >> pi[c]) ^ s) & 1
assert VI.min(1).min() == 3          # every doily has degree 3
VI *= lam


def bound(z, rm, iters=300):
    u = unary(z, rm)
    c0 = np.array([a[0] for a in u], float); c1 = np.array([a[1] for a in u], float)
    beta = (c1 - c0)[P] / pc[0]
    best = -1e9
    for it in range(iters):
        val = VI + beta @ bits.T
        am = val.argmin(1)
        lb = c0.sum() + val[np.arange(nD), am].sum()
        best = max(best, lb)
        if best > TARGET - 1 + 1e-6:
            break
        xs = bits[am]
        tot = np.zeros(nH); np.add.at(tot, P, xs)
        g = xs - (tot / pc[0])[P]
        n2 = (g ** 2).sum()
        if n2 == 0:
            break
        beta += max((TARGET + 3 - lb) / n2, 1e-4) * g
    return best


rows = [tuple(map(int, x.split()[:3])) for x in open(sys.argv[2])]
random.seed(3)
sample = random.sample(rows, min(int(sys.argv[3]), len(rows)))
bad = 0
for z, rm, f in sample:
    lb = bound(z, rm)
    ok = lb > TARGET - 1 + 1e-6
    bad += not ok
    print(z, rm, f, round(lb, 4), "confirmed" if ok else "NOT confirmed", flush=True)
print(f"{len(sample)} leaves, not confirmed: {bad}")
sys.exit(1 if bad else 0)
