"""Independent check of the leaf list of zcount.c: for orbit representatives z, count by brute force over all 2^21
gauge classes of r (gauge fixed on other representatives than zcount.c) the r with
sum_a min(k_a, 12 - k_a) <= 251, computed directly from the instance lines, and compare with zcount's count.
    python brute_count.py V0 orbits_file zcount_perorbit.txt [n_orbits]      (all orbits if n_orbits is omitted)"""
import sys, random
import numpy as np
from common import load, symp

import numpy as np
from common import load, symp

pts, lines = load(); P = set(pts)
v0 = int(sys.argv[1])
H = [p for p in pts if symp(p, v0) == 0]; Hs = set(H)
O = [p for p in pts if symp(p, v0) == 1]
reps, seen = [], set()
for b in O:                       # same coordinate convention as mkz.py (rep = first of the pair met)
    if b not in seen:
        reps.append(b); seen |= {b, b ^ v0}
pairof = {}
for k, b in enumerate(reps):
    pairof[b] = (k, 0); pairof[b ^ v0] = (k, 1)
# gauge: functionals with l(v0)=0 zero r on 7 reps independent mod v0; choose them from the END of the list
def indep(vecs):
    rows, ch = {}, []
    for p in vecs:
        v = p
        while v:
            h = v.bit_length() - 1
            if h in rows: v ^= rows[h]
            else: rows[h] = v; ch.append(p); break
    return ch
fixed = [reps.index(b) for b in indep([v0] + reps[::-1])[1:]]
assert len(fixed) == 7
free = [k for k in range(28) if k not in fixed]
comp = []
for a, b, c, s in lines:
    ins = [q for q in (a, b, c) if q in Hs]
    if len(ins) == 1:
        u, w = [q for q in (a, b, c) if q not in Hs]
        comp.append((H.index(ins[0]), u, w, s))
assert len(comp) == 756

def exact_min(z):
    best = 10 ** 9
    CH = 1 << 17
    for start in range(0, 1 << 21, CH):
        idx = np.arange(start, start + CH, dtype=np.uint32)
        r = np.zeros((28, CH), dtype=np.uint8)
        for j, k in enumerate(free):
            r[k] = (idx >> j) & 1
        def y(p):
            k, t = pairof[p]
            return r[k] ^ (((z >> k) & 1) if t else 0)
        cnt = np.zeros((len(H), CH), dtype=np.uint8)
        for ai, u, w, s in comp:
            cnt[ai] += (y(u) ^ y(w) ^ s).astype(np.uint8)
        cost = np.minimum(cnt, 12 - cnt).sum(axis=0)
        best = min(best, int(cost.min()))
    return best



def count(z, B=251):
    tot, CH = 0, 1 << 17
    for start in range(0, 1 << 21, CH):
        idx = np.arange(start, start + CH, dtype=np.uint32)
        r = np.zeros((28, CH), dtype=np.uint8)
        for j, k in enumerate(free):
            r[k] = (idx >> j) & 1
        def y(p):
            k, t = pairof[p]
            return r[k] ^ (((z >> k) & 1) if t else 0)
        cnt = np.zeros((len(H), CH), dtype=np.uint8)
        for ai, u, w, s in comp:
            cnt[ai] += (y(u) ^ y(w) ^ s).astype(np.uint8)
        tot += int((np.minimum(cnt, 12 - cnt).sum(axis=0) <= B).sum())
    return tot


per = {int(l.split()[1]): int(l.split()[9]) for l in open(sys.argv[3]) if l.startswith("z ")}
zs = sorted(per)
if len(sys.argv) > 4:
    random.seed(5); zs = random.sample(zs, int(sys.argv[4]))
bad = 0
for z in zs:
    c = count(z)
    bad += c != per[z]
    print(z, "zcount", per[z], "brute", c, "OK" if c == per[z] else "MISMATCH", flush=True)
print(f"{len(zs)} orbits, {sum(per[z] for z in zs)} leaves, mismatches: {bad}")
sys.exit(1 if bad else 0)
