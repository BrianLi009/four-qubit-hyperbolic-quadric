"""Lower bounds for the five-qubit quadrics by averaging over their elliptic sections Q-(7,2).

For Q^eps(9,2), a section is H = K^perp for a nondegenerate plane K such that Q restricted to H is elliptic
(K elliptic for eps = +, K hyperbolic for eps = -). For every section the script
  * maps H onto F_2^8 by a symplectic basis and checks that its 119 points form one of the 120 elliptic
    quadrics of W(7,2);
  * checks that the five-qubit signs of its 1071 lines agree with the signs of W(7,2) (instance w4_full of
    ../elliptic) up to a relabelling of the points, by solving the F2 coboundary system;
  * counts, for every line of Q^eps(9,2), the sections that contain it.
../elliptic/verify_avg.py shows that each elliptic quadric of W(7,2), with these signs, is equivalent to the
instance w4_ell, of degree 315 (../elliptic). Hence deg Q^eps(9,2) >= #sections * 315 / r.
For eps = +, it also counts the lines of the invariant configuration (invariant_N5.txt) in every section.

    python sections.py + | -          (about 2 minutes for +, 4 minutes for -)
"""
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
import numpy as np
from pauli import Space, coboundary_solvable

EPS = sys.argv[1]
sp = Space(5, EPS)
pts, lines = sp.quadric()
L = len(lines)
print(f"Q{EPS}(9,2): {len(pts)} points, {L} lines")
INST = Path(__file__).resolve().parent.parent / "elliptic" / "instances"
wp = [int(p) for p in np.load(INST / "w4_full.points.npy")]
raw = np.loadtxt(INST / "w4_full.txt", skiprows=1, dtype=np.int64)
WS = {frozenset((wp[a], wp[b], wp[c])): int(s) for a, b, c, s in raw}
four = Space(4)
ELL = {frozenset(v for v in range(1, 256) if (four.Q(v) ^ four.symp(v, a)) == 0) for a in range(256)}
ELL = {E for E in ELL if len(E) == 119}
assert len(ELL) == 120
inv = None
if EPS == "+" and Path("invariant_N5.txt").exists():
    inv = [frozenset(map(int, s.split())) for s in open("invariant_N5.txt")]

want = 1 if EPS == "+" else 0
Ks = {frozenset((a, b, a ^ b)) for a in range(1, 1024) for b in range(a + 1, 1024)
      if sp.symp(a, b) and sp.Q(a) == want and sp.Q(b) == want and (EPS == "-" or sp.Q(a ^ b) == 1)}
print("sections:", len(Ks))
cover, inv_count = Counter(), Counter()
for K in Ks:
    a, b = sorted(K)[:2]
    H = [v for v in range(1, 1024) if not sp.symp(v, a) and not sp.symp(v, b)]
    pool, E, F = set(H), [], []
    while pool:                                     # symplectic basis e_i, f_i of H
        e = min(pool)
        f = next(v for v in pool if sp.symp(e, v))
        E.append(e); F.append(f)
        pool = {v for v in pool if not sp.symp(v, e) and not sp.symp(v, f)}
    assert len(E) == 4
    phi = {v: sum(sp.symp(v, F[i]) << i for i in range(4)) | sum(sp.symp(v, E[i]) << (i + 4) for i in range(4))
           for v in H}
    hp = [v for v in H if sp.Q(v) == 0]
    hs = set(hp)
    assert frozenset(phi[v] for v in hp) in ELL
    sec = [l for l in lines if l[0] in hs and l[1] in hs and l[2] in hs]
    assert len(sec) == 1071
    hidx = {v: i for i, v in enumerate(hp)}
    rows = [(1 << (hidx[x] + 1)) | (1 << (hidx[y] + 1)) | (1 << (hidx[z] + 1)) | (s ^ WS[frozenset((phi[x], phi[y], phi[z]))])
            for x, y, z, s in sec]
    assert coboundary_solvable(rows), "sign classes differ"
    for l in sec:
        cover[l[:3]] += 1
    if inv is not None:
        inv_count[sum(1 for l in inv if l <= hs)] += 1
assert len(cover) == L
cnt = Counter(cover.values())
assert len(cnt) == 1
r = next(iter(cnt))
print(f"every section: elliptic, signs equivalent to W(7,2); every line lies in {r} sections")
bound = Fraction(len(Ks) * 315, r)
print(f"  deg Q{EPS}(9,2) >= {len(Ks)}*315/{r} = {bound}, so >= {-(-bound.numerator // bound.denominator)}")
if inv is not None:
    print("lines of the invariant configuration per section:", dict(inv_count))
