"""Map zcount leaves (z, r) back to assignments on the 56 points outside v0^perp and build the inner problem
on the parabolic section H (63 points, 315 lines): minimise sum_a u_a(x_a) + #violated lines of H."""
from group import pts, lines, P, symp
import os
v0 = int(os.environ.get("V0", min(v for v in range(1, 256) if v not in P)))
H = [p for p in pts if symp(p, v0) == 0]
O = [p for p in pts if symp(p, v0) == 1]
reps, seen = [], set()
for b in O:
    if b in seen: continue
    reps.append(b); seen |= {b, b ^ v0}
Hs = set(H); Hidx = {a: i for i, a in enumerate(H)}
HL = [(Hidx[a], Hidx[b], Hidx[c], s) for a, b, c, s in lines if a in Hs and b in Hs and c in Hs]
CL = []   # (h index, b, c, s) complement lines
for a, b, c, s in lines:
    ins = [q for q in (a, b, c) if q in Hs]
    if len(ins) == 1:
        u, w = [q for q in (a, b, c) if q not in Hs]
        CL.append((Hidx[ins[0]], u, w, s))
assert len(HL) == 315 and len(CL) == 756
def outside(z, rm):
    y = {}
    for k, b in enumerate(reps):
        y[b] = rm >> k & 1; y[b ^ v0] = (rm >> k & 1) ^ (z >> k & 1)
    return y
def unary(z, rm):
    """u[a] = (violated complement lines at a if x_a = 0, ... if x_a = 1)"""
    y = outside(z, rm); u = [[0, 0] for _ in H]
    for a, b, c, s in CL:
        t = y[b] ^ y[c] ^ s
        u[a][t] += 1          # x_a = t violates (x_a ^ y_b ^ y_c ^ s = 1 iff x_a != t)... fixed below
    return [[u0[1], u0[0]] for u0 in u]   # x_a = 0 violated iff t = 1
def total(z, rm, xH):
    y = outside(z, rm); x = dict(y); x.update({a: xH[i] for i, a in enumerate(H)})
    return sum(x[a] ^ x[b] ^ x[c] ^ s for a, b, c, s in lines)
