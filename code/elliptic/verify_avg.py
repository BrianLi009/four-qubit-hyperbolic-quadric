"""Checks for the averaging step.
 (1) every line of Q-(7,2) lies outside exactly 96 of the 136 parabolic hyperplanes v^perp (v off the quadric);
 (2) signed reflections (sign correction found and checked on all 1071 lines) map v0 to all 136 such v,
     so the 136 complements are equivalent signed configurations and have equal degree;
 (3) in W(7,2): signed symplectic transvections map this quadric to all 120 elliptic quadrics, each line of
     W(7,2) lies in exactly 24 of them, and the inherited signs are those of W(7,2)."""
from collections import Counter
import numpy as np
from common import load, symp, INST
import group
from group import pts, lines, P, Q, signed, reflection, solve_f2

off = [v for v in range(1, 256) if v not in P]
assert len(off) == 136 and all(Q(v) == 1 for v in off)
cnt = Counter(sum(1 for v in off if any(symp(p, v) for p in l[:3])) for l in lines)
print("(1) lines outside k sections:", dict(cnt))
assert cnt == Counter({96: 1071})

v0 = min(off)
reach, frontier = {v0}, [v0]
refl_ok = {}
while frontier:
    v = frontier.pop()
    for u in off:
        w = v ^ u if symp(v, u) else v
        if w not in reach:
            if u not in refl_ok:
                signed(reflection(u)); refl_ok[u] = True   # asserts the sign correction exists and is exact
            reach.add(w); frontier.append(w)
print("(2) orbit of v0 under signed reflections:", len(reach), "reflections verified:", len(refl_ok))
assert reach == set(off)

# (3) W(7,2)
wp = [int(p) for p in np.load(INST / "w4_full.points.npy")]
raw = np.loadtxt(INST / "w4_full.txt", skiprows=1, dtype=np.int64)
wl = [(wp[a], wp[b], wp[c], int(s)) for a, b, c, s in raw]
WS = {frozenset(l[:3]): l[3] for l in wl}
widx = {p: i for i, p in enumerate(wp)}
# our quadric's restriction of W signs must equal the w4_ell signs (same generator) up to gauge: check equality
for a, b, c, s in lines:
    assert WS[frozenset((a, b, c))] == s
m = 15
q0 = lambda v: bin((v >> 4) & v & m).count("1") & 1
quad = lambda a: frozenset(v for v in range(1, 256) if (q0(v) ^ symp(v, a)) == 0)
ell = [a for a in range(256) if len(quad(a)) == 119]
print("(3) elliptic quadrics:", len(ell))
assert len(ell) == 120
cov = Counter(sum(1 for a in ell if l[0] in Qs and l[1] in Qs and l[2] in Qs) for l in wl for Qs in [None] if False)
qsets = [quad(a) for a in ell]
cov = Counter(sum(1 for S in qsets if l[0] in S and l[1] in S and l[2] in S) for l in wl)
print("    W lines in k elliptic quadrics:", dict(cov))
assert cov == Counter({24: 5355})
def wsigned(u):
    g = {p: (p ^ u) if symp(p, u) else p for p in wp}
    rows = [((1 << widx[a]) | (1 << widx[b]) | (1 << widx[c]), s ^ WS[frozenset((g[a], g[b], g[c]))]) for a, b, c, s in wl]
    sol = solve_f2(rows, len(wp)); assert sol is not None
    cc = {p: (sol >> widx[p]) & 1 for p in wp}
    for a, b, c, s in wl:
        assert WS[frozenset((g[a], g[b], g[c]))] == s ^ cc[a] ^ cc[b] ^ cc[c]
    return g
start = frozenset(P)
seenq, frontier, tv = {start}, [start], {}
while frontier:
    S = frontier.pop()
    for u in range(1, 256):
        if u not in tv:
            tv[u] = wsigned(u)
        T = frozenset(tv[u][p] for p in S)
        if T not in seenq:
            seenq.add(T); frontier.append(T)
print("    orbit of our quadric under signed transvections:", len(seenq), "transvections verified:", len(tv))
assert seenq == set(qsets)
print("ALL AVERAGING CHECKS PASSED")
