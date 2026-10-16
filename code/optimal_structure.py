"""Structure of the optimal violated sets of the real quadric Q_0 (the DW(5,2) theorem of the paper).

1. Orbit: the orbit of the witness's violated set under the 120 transvections t_r(v) = v + B(v,r) r with
   Q_0(r) = 1, which generate the orthogonal group O+(8,2) of Q_0.
2. Realisability: every set in the orbit is the violated set of an assignment (linear algebra over F_2), so it is
   optimal; nothing here relies on the SAT solver.
3. Comparison with the SAT enumeration (optimal_sets.json from enumerate_optimal.py): the same 240 sets.
4. DW(5,2): the explicit isomorphism stored in dw52_isomorphism.json (planes of W(5,2) -> points of Q_0) is
   checked to be a bijection that maps the 315 lines of W(5,2) onto the 315 violated lines of the witness.
   With --find it is recomputed by a backtracking search and written. The search is also run on every one of the
   240 sets, and each isomorphism found is checked.
Exits with status 1 if a check fails.
"""
import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from verify_facts import Q, quadric_lines, quadric_points, sign_bit, symp, word  # noqa: E402

FAILED = []


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name, flush=True)
    if not cond:
        FAILED.append(name)


def gf2_rank_with(rows_int, target=None):
    """Rank of a list of bit-vectors (Python ints); if target is given, whether it lies in their span."""
    basis = {}
    def reduce(v):
        while v:
            h = v.bit_length() - 1
            if h not in basis:
                return v, h
            v ^= basis[h]
        return 0, None
    for r in rows_int:
        v, h = reduce(r)
        if v:
            basis[h] = v
    if target is None:
        return len(basis)
    return reduce(target)[0] == 0


def find_isomorphism(n, lines1, pts2, lines2):
    """A bijection phi from range(n) onto pts2 that maps the lines lines1 (triples of indices) onto the lines lines2
    (triples of points), or None. Backtracking over the points in BFS order: an image must preserve collinearity
    with every point already mapped, and is forced when two collinear points of its line are already mapped."""
    def thirds(lines):
        t = {}
        for a, b, c in lines:
            for u, v, w in ((a, b, c), (a, c, b), (b, c, a)):
                t[u, v] = t[v, u] = w
        return t
    third1, third2 = thirds(lines1), thirds([tuple(k) for k in lines2])
    adj = {u: sorted(v for (a, v) in third1 if a == u) for u in range(n)}
    order, seen = [0], {0}
    for u in order:
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                order.append(v)
    if len(order) != n:
        return None
    phi, used = {}, set()

    def consistent(u, img):
        for w, iw in phi.items():
            if ((u, w) in third1) != ((img, iw) in third2):
                return False
            if (u, w) in third1 and third1[u, w] in phi and phi[third1[u, w]] != third2[img, iw]:
                return False
        return True

    def candidates(u):
        for w in phi:
            if (u, w) in third1 and third1[u, w] in phi:
                return [third2.get((phi[w], phi[third1[u, w]]))]
        return [p for p in pts2 if p not in used]

    def rec(k):
        if k == n:
            return True
        u = order[k]
        for img in candidates(u):
            if img is None or img in used or not consistent(u, img):
                continue
            phi[u] = img
            used.add(img)
            if rec(k + 1):
                return True
            del phi[u]
            used.discard(img)
        return False

    sys.setrecursionlimit(max(10000, 4 * n))
    return dict(phi) if rec(0) else None


def main():
    P0 = quadric_points(0)
    L0 = sorted(tuple(sorted(k)) for k in quadric_lines(0))
    lindex = {k: j for j, k in enumerate(L0)}
    sg = [sign_bit(k[0], k[1]) for k in L0]
    w = json.load(open(HERE / "witness.json"))
    enc = lambda t: sum(t[i] << i for i in range(8))
    x = {enc(p): b for p, b in zip(w["points"], w["assignment"])}
    V0 = frozenset(j for j, k in enumerate(L0) if (x[k[0]] ^ x[k[1]] ^ x[k[2]]) != sg[j])
    check("the witness violates 315 lines", len(V0) == 315)

    # 1. orbit under the transvections of O+(8,2)
    gens = [r for r in range(1, 256) if Q(0, r) == 1]
    perms = []
    for r in gens:
        t = lambda v: v ^ r if symp(v, r) else v
        perms.append([lindex[tuple(sorted(t(p) for p in k))] for k in L0])
    orbit, frontier = {V0}, [V0]
    while frontier:
        new = []
        for S in frontier:
            for pm in perms:
                T = frozenset(pm[j] for j in S)
                if T not in orbit:
                    orbit.add(T)
                    new.append(T)
        frontier = new
    check(f"orbit of the witness's violated set under O+(8,2): {len(orbit)} sets", len(orbit) == 240)
    check("|O+(8,2)| / 240 = 1451520 = |Sp(6,2)|", 348364800 // 240 == 1451520 and 348364800 % 240 == 0)

    # 2. realisability: 1_V + s must be in the span of the columns of the line-point incidence matrix,
    #    i.e. there is x with x(a)+x(b)+x(c) = 1_V(C) + s(C) on every line C.
    pidx = {p: i for i, p in enumerate(P0)}
    cols = [sum(1 << j for j, k in enumerate(L0) if p in k) for p in P0]
    rank = gf2_rank_with(cols)
    check(f"incidence matrix has rank {rank} over F_2, so each violated set comes from 2^{135 - rank} = 256 assignments",
          rank == 127)
    s_vec = sum(1 << j for j in range(1575) if sg[j])
    check("every set in the orbit is the violated set of some assignment",
          all(gf2_rank_with(cols, s_vec ^ sum(1 << j for j in S)) for S in orbit))
    del pidx

    # 3. comparison with the SAT enumeration
    f = HERE / "optimal_sets.json"
    if f.exists():
        d = json.load(open(f))
        assert [tuple(k) for k in d["lines"]] == L0
        sat = {frozenset(S) for S in d["sets"]}
        check(f"SAT enumeration found {len(d['sets'])} distinct sets, equal to the orbit", len(sat) == len(d["sets"]) == 240 and sat == orbit)
    else:
        print("(optimal_sets.json not found: run enumerate_optimal.py to compare with the SAT enumeration)")

    # 4. isomorphism with DW(5,2)
    def B3(u, v): return (bin((u & 7) & (v >> 3)).count("1") + bin((u >> 3) & (v & 7)).count("1")) & 1
    planes = sorted({frozenset({a, b, c, a ^ b, a ^ c, b ^ c, a ^ b ^ c}) for a, b, c in itertools.combinations(range(1, 64), 3)
                     if not (B3(a, b) or B3(a, c) or B3(b, c)) and len({a, b, c, a ^ b, a ^ c, b ^ c, a ^ b ^ c}) == 7},
                    key=sorted)
    wlines = sorted({frozenset({a, b, a ^ b}) for a in range(1, 64) for b in range(1, 64) if a != b and not B3(a, b)}, key=sorted)
    check("W(5,2) has 135 planes and 315 lines", len(planes) == 135 and len(wlines) == 315)
    Vlines = [L0[j] for j in sorted(V0)]
    lines1 = [tuple(i for i, P in enumerate(planes) if l <= P) for l in wlines]
    def is_iso(phi, target):
        return (phi is not None and sorted(phi.values()) == sorted(P0)
                and {frozenset(phi[i] for i in l) for l in lines1} == {frozenset(k) for k in target})
    iso_file = HERE / "dw52_isomorphism.json"
    if "--find" in sys.argv or not iso_file.exists():
        phi = find_isomorphism(135, lines1, P0, Vlines)
        iso = {",".join(map(str, sorted(planes[i]))): word(phi[i]) for i in range(135)}
        json.dump(iso, open(iso_file, "w"), indent=0)
    allsets = [[L0[j] for j in S] for S in orbit]
    check("each of the 240 sets in the orbit is isomorphic to DW(5,2) (an isomorphism found by search and checked)",
          all(is_iso(find_isomorphism(135, lines1, P0, T), T) for T in allsets))
    iso = json.load(open(iso_file))
    wtoint = {word(v): v for v in P0}
    phi = {frozenset(map(int, key.split(","))): wtoint[val] for key, val in iso.items()}
    image_lines = {frozenset(phi[P] for P in planes if l <= P) for l in wlines}
    check("stored map is a bijection from the 135 planes of W(5,2) onto the 135 points of Q_0",
          set(phi) == set(planes) and sorted(phi.values()) == sorted(P0))
    check("it maps the 315 lines of DW(5,2) onto the 315 violated lines of the witness",
          image_lines == {frozenset(k) for k in Vlines})

    print()
    print("ALL CHECKS PASSED" if not FAILED else f"{len(FAILED)} CHECK(S) FAILED: {FAILED}")
    sys.exit(1 if FAILED else 0)


if __name__ == "__main__":
    main()
