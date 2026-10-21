"""Independent check of zorb.c on sampled orbits: for a pair-parity vector z, brute-force
min over all y with y_b ^ y_{b^v0} = z_pair of  sum_{a in H} min(k_a, 12 - k_a),
computed directly from the instance lines (no edge data, no pair formula).  The 7 gauge bits are fixed on a
different independent set of reps than zorb.c uses.
    python brute_check.py V0 orbits_file [n_samples]"""
import sys, random
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

rows = [tuple(map(int, l.split())) for l in open(sys.argv[2])]
n = int(sys.argv[3]) if len(sys.argv) > 3 else 6
rng = random.Random(5)
sample = sorted(rows, key=lambda t: t[1] + 2 * t[2])[:3] + rng.sample(rows, n - 3)
bad = 0
for z, Pz, G, size in sample:
    m = exact_min(z)
    ok = m == Pz + 2 * G
    bad += not ok
    print(f"z={z:10d} zorb P+2G={Pz + 2 * G:4d} brute={m:4d} {'OK' if ok else 'MISMATCH'}", flush=True)
# global flip: z and its complement must have the same minimum
z = sample[0][0]; zc = z ^ ((1 << 28) - 1)
m1, m2 = exact_min(z), exact_min(zc)
print(f"flip check: min(z)={m1} min(~z)={m2} {'OK' if m1 == m2 else 'MISMATCH'}")
print("BRUTE CHECK", "PASSED" if bad == 0 and m1 == m2 else "FAILED")
sys.exit(0 if bad == 0 and m1 == m2 else 1)
