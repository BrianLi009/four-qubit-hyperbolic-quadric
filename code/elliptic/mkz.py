"""Data for zorb.c: the parabolic complement in pair coordinates, plus signed group generators fixing v0.
Off-H points come in antipodal pairs {b, b^v0}; y_b = r_pair + (z_pair if b is the partner else 0).
Output (whitespace separated):
  NPAIR NH
  for each H point a: 12 edges as (pair_b, partner_b, pair_c, partner_c, sign)
  NGEN; for each generator: for each off-H point i (rep of pair k = i < 28, partner = i >= 28 at k-28):
        image index and correction bit
"""
import sys
from group import pts, lines, P, symp, generators, Q

v0 = int(sys.argv[1]) if len(sys.argv) > 1 else min(v for v in range(1, 256) if v not in P)
ngen = int(sys.argv[2]) if len(sys.argv) > 2 else 8
H = [p for p in pts if symp(p, v0) == 0]
O = [p for p in pts if symp(p, v0) == 1]
reps = []
seen = set()
for b in O:
    if b in seen: continue
    assert (b ^ v0) in set(O)
    reps.append(b); seen |= {b, b ^ v0}
pair = {}
for k, b in enumerate(reps):
    pair[b] = (k, 0); pair[b ^ v0] = (k, 1)
order = reps + [b ^ v0 for b in reps]           # index i: i<28 rep, i>=28 partner of pair i-28
pos = {p: i for i, p in enumerate(order)}
Hs = set(H)
edges = {a: [] for a in H}
for a, b, c, s in lines:
    ins = [q for q in (a, b, c) if q in Hs]
    if len(ins) == 1:
        u, w = [q for q in (a, b, c) if q not in Hs]
        edges[ins[0]].append((*pair[u], *pair[w], s))
out = [f"{len(reps)} {len(H)}"]
for a in H:
    assert len(edges[a]) == 12
    out.append(" ".join(" ".join(map(str, e)) for e in edges[a]))
# gauge on reps: linear functionals with l(v0) = 0 can zero r on 7 reps independent modulo v0
from common import basis
fix = [reps.index(b) for b in basis([v0] + reps)[1:]]
assert len(fix) == 7
out.append(" ".join(map(str, fix)))
gens = generators(v0, ngen)
out.append(str(len(gens)))
for g, c in gens:
    out.append(" ".join(f"{pos[g[p]]} {c[p]}" for p in order))
print("\n".join(out))
