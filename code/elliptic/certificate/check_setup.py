"""Independent checker for deg Q-(7,2) >= 315, part 1: the setup, written without the code of the search.

It builds the signed configurations from 2x2 Pauli matrices and checks everything the search assumes:
  * Q-(7,2) = {v : |x & z| + B(v, a) = 0}, a = 17, has 119 points and 1071 lines; W(7,2) has 255 and 5355;
    the sign of a line {p, q, p+q} is the scalar P(p) P(q) P(p+q) = +-I, computed qubit by qubit;
  * the witnesses violate 315 lines of Q-(7,2) and 1575 lines of W(7,2) (upper bounds);
  * v0 = 1 has Q(v0) = 1; its section H (63 points, 315 lines) and the 28 pairs {b, b + v0} outside;
  * v0 and the representatives b_k, k in K, form a basis, so a linear functional vanishing at v0 can make r_K = 0;
  * each reflection r_u (Q(u) = 1, u in v0^perp, u != v0) is induced by the Clifford unitary (I + i P(u)) / sqrt 2,
    and with the resulting sign corrections tau it maps every line l to a line with sign s(l) + tau(l), so
    x'(r_u p) = x(p) + tau(p) violates exactly the lines that x violates;
  * the doilies: every line of H lies in exactly LCV of them and every point in exactly PC.
It writes setup.txt for check_cert.c, which does the exhaustive parts.

    python check_setup.py ../hdata_v1_lin.txt ../zdata.txt > setup.txt
"""
import sys
from pathlib import Path

N, A, V0, TARGET = 4, 17, 1, 315
HERE = Path(__file__).resolve().parent

# single-qubit Paulis as 2x2 complex matrices (lists), indexed by (x, z)
I2 = [[1, 0], [0, 1]]
X2 = [[0, 1], [1, 0]]
Z2 = [[1, 0], [0, -1]]
Y2 = [[0, -1j], [1j, 0]]
LETTER = {(0, 0): I2, (1, 0): X2, (0, 1): Z2, (1, 1): Y2}


def mat(m1, m2):
    return [[sum(m1[i][k] * m2[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def letter(v, j):
    return LETTER[((v >> N) >> j & 1, v >> j & 1)]          # x part in the high bits, z part in the low bits


def scalar(*vs):
    """The product P(v1) P(v2) ... as a scalar, assuming it is one (checked qubit by qubit)."""
    c = 1
    for j in range(N):
        m = I2
        for v in vs:
            m = mat(m, letter(v, j))
        assert m[0][1] == 0 and m[1][0] == 0 and m[0][0] == m[1][1], "not a scalar"
        c *= m[0][0]
    return c


def B(u, v):
    return (bin((u >> N) & v).count("1") + bin(u & (v >> N)).count("1")) & 1


def Q(v):
    return (bin((v >> N) & v & ((1 << N) - 1)).count("1") + B(v, A)) & 1


def lines_of(points):
    ps, out = set(points), []
    for p in points:
        for q in points:
            if p < q < p ^ q and (p ^ q) in ps and B(p, q) == 0:
                c = scalar(p, q, p ^ q)
                assert c in (1, -1)
                out.append((p, q, p ^ q, int(c == -1)))
    return out


def violated(lines, one):
    return sum(((a in one) ^ (b in one) ^ (c in one) ^ s) for a, b, c, s in lines)


def main():
    hfile, zfile = sys.argv[1], sys.argv[2]
    pts = [v for v in range(1, 1 << 2 * N) if Q(v) == 0]
    L = lines_of(pts)
    assert len(pts) == 119 and len(L) == 1071, "not the elliptic quadric"
    sign = {frozenset(l[:3]): l[3] for l in L}
    # upper bounds
    wq = [int(t) for t in open(HERE.parent / "witness_315.py").read().split("WITNESS = [")[1].split("]")[0].replace("\n", " ").split(",")]
    assert violated(L, set(wq)) == 315
    LW = lines_of(list(range(1, 1 << 2 * N)))
    assert len(LW) == 5355
    ww = [int(t) for t in open(HERE / "witness_W72.txt").read().split("\n", 1)[1].split()]
    assert violated(LW, set(ww)) == 1575
    print("witnesses: 315 violated lines of Q-(7,2), 1575 of W(7,2)", file=sys.stderr)

    # the section and the pairs
    assert Q(V0) == 1
    H = [p for p in pts if B(p, V0) == 0]
    O = [p for p in pts if B(p, V0) == 1]
    reps = []
    for b in O:
        if b not in reps and (b ^ V0) not in reps:
            reps.append(b)
    assert len(H) == 63 and len(O) == 56 and len(reps) == 28 and all((b ^ V0) in O for b in reps)
    hidx = {a: i for i, a in enumerate(H)}
    where = {}
    for k, b in enumerate(reps):
        where[b], where[b ^ V0] = (k, 0), (k, 1)
    HL = [(hidx[a], hidx[b], hidx[c], s) for a, b, c, s in L if a in hidx and b in hidx and c in hidx]
    comp = {i: [] for i in range(63)}
    for a, b, c, s in L:
        inside = [p for p in (a, b, c) if p in hidx]
        if len(inside) == 1:
            u, w = [p for p in (a, b, c) if p not in hidx]
            comp[hidx[inside[0]]].append((*where[u], *where[w], s))
    assert len(HL) == 315 and all(len(e) == 12 for e in comp.values())

    # gauge: K from zdata, checked to complete v0 to a basis
    zl = open(zfile).read().split("\n")
    K = [int(t) for t in zl[1 + 63].split()]
    rows, rank = {}, 0
    for v in [V0] + [reps[k] for k in K]:
        while v:
            h = v.bit_length() - 1
            if h in rows:
                v ^= rows[h]
            else:
                rows[h] = v; rank += 1; break
    assert len(K) == 7 and rank == 8

    # generators: all reflections fixing v0, with Clifford sign corrections
    gens = []
    for u in range(1, 1 << 2 * N):
        if Q(u) != 1 or B(u, V0) != 0 or u == V0:
            continue
        g, tau = {}, {}
        for p in pts:
            if B(p, u):
                c = 1j * scalar(u, p, p ^ u)       # i P(u) P(p) = c P(p + u)
                assert c in (1, -1)
                g[p], tau[p] = p ^ u, int(c == -1)
            else:
                g[p], tau[p] = p, 0
        assert sorted(g.values()) == pts
        for a, b, c, s in L:
            assert sign[frozenset((g[a], g[b], g[c]))] == s ^ tau[a] ^ tau[b] ^ tau[c]
        perm, add = [0] * 28, [0] * 28
        for k, b in enumerate(reps):
            k2, _ = where[g[b]]
            assert where[g[b ^ V0]][0] == k2
            perm[k], add[k] = k2, tau[b] ^ tau[b ^ V0]
        gens.append((perm, add))
    assert len(gens) == 63

    # doilies
    hd = open(hfile).read().split("\n")
    nh, nl, nd = map(int, hd[0].split())
    assert (nh, nl) == (63, 315)
    D = [[int(t) for t in hd[1 + 315 + d].split()[:15]] for d in range(nd)]
    lcv, pc = nd * 15 // 315, nd * 15 // 63
    lc, pcnt = [0] * 315, [0] * 63
    for pset in D:
        ps = set(pset); assert len(ps) == 15
        for i, l in enumerate(HL):
            if set(l[:3]) <= ps:
                lc[i] += 1
        for a in ps:
            pcnt[a] += 1
    assert all(c == lcv for c in lc) and all(c == pc for c in pcnt), "doilies do not cover uniformly"
    print(f"setup checked: {len(gens)} signed reflections, {nd} doilies covering lines {lcv}, points {pc} times", file=sys.stderr)

    out = [f"28 63 {nd} {lcv} {pc} {TARGET}"]
    for a in range(63):
        out.append(" ".join(" ".join(map(str, e)) for e in comp[a]))
    out += [" ".join(map(str, l)) for l in HL]
    out += [" ".join(map(str, d)) for d in D]
    out.append(" ".join(map(str, K)))
    out.append(str(len(gens)))
    out += [" ".join(f"{p} {q}" for p, q in zip(*g)) for g in gens]
    print("\n".join(out))


if __name__ == "__main__":
    main()
