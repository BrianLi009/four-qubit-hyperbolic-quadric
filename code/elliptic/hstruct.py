"""Doilies of the parabolic section H = Q(6,2) of Q-(7,2) cut out by v0^perp (63 points, 315 lines), and the input
file of inner_bb.c.  H is isomorphic to W(5,2) = v0^perp / <v0>; its linear doilies are the 336 subspaces U with
v0 in U and U/<v0> nondegenerate of dimension 4, its quadratic doilies the 1008 parabolic sections of the
5-dimensional subspaces of the quotient (16 for each nucleus).

    V0=v python hstruct.py lin|quad > hdata.txt      (v0 defaults to the vector used by mkz.py)"""
import sys
from leafinfo import H, HL, v0, symp
from common import basis

Hidx = {a: i for i, a in enumerate(H)}


def span(gs):
    s = [0]
    for g in gs:
        s += [t ^ g for t in s]
    return s


def linear():
    V = [w for w in range(256) if symp(w, v0) == 0]
    out, seen = [], set()
    for e1 in V:
        for f1 in V:
            if not symp(e1, f1):
                continue
            R = [w for w in V if not symp(w, e1) and not symp(w, f1)]
            for e2 in R:
                for f2 in R:
                    if not symp(e2, f2):
                        continue
                    U = frozenset(span([v0, e1, f1, e2, f2]))
                    if U in seen:
                        continue
                    seen.add(U)
                    ps = {Hidx[p] for p in U if p in Hidx}
                    out.append(ps)
    return out


def quadratic():
    V = [w for w in range(256) if symp(w, v0) == 0]
    cb = basis([v0] + [w for w in V if w and w != v0])[1:]
    assert len(cb) == 6
    def vec(m):
        t = 0
        for i in range(6):
            if m >> i & 1:
                t ^= cb[i]
        return t
    lift = {}
    for m in range(1, 64):          # each quotient point has exactly one singular lift in H
        t = vec(m)
        lift[m] = Hidx[t] if t in Hidx else Hidx[t ^ v0]
    qs = lambda m1, m2: symp(vec(m1), vec(m2))
    out = []
    for P in range(1, 64):
        Pp = next(m for m in range(1, 64) if qs(m, P))
        D5 = [m for m in range(1, 64) if not qs(m, P) and not qs(m, Pp)]
        e1 = D5[0]; f1 = next(m for m in D5 if qs(e1, m))
        R = [m for m in D5 if not qs(m, e1) and not qs(m, f1)]
        e2 = R[0]; f2 = next(m for m in R if qs(e2, m))
        bas = [P, e1, f1, e2, f2]
        for q in range(16):          # quadratic forms with polar form B and Q(P) = 1
            qv = [1] + [q >> i & 1 for i in range(4)]
            Qv, vecs = {0: 0}, [0]
            for bi, qb in zip(bas, qv):
                new = []
                for w in vecs:
                    t = w ^ bi; Qv[t] = Qv[w] ^ qb ^ qs(w, bi); new.append(t)
                vecs += new
            out.append({lift[w] for w in vecs if w and Qv[w] == 0})
    return out


def lines_of(ps):
    return [i for i, (a, b, c, s) in enumerate(HL) if a in ps and b in ps and c in ps]


if __name__ == "__main__":
    fam = linear() if sys.argv[1] == "lin" else quadratic()
    print(f"{len(H)} {len(HL)} {len(fam)}")
    for a, b, c, s in HL:
        print(a, b, c, s)
    for ps in fam:
        ls = lines_of(ps)
        assert len(ps) == 15 and len(ls) == 15
        print(" ".join(map(str, sorted(ps))), " ".join(map(str, ls)))
    print(f"v0 = {v0}: {len(fam)} doilies", file=sys.stderr)
