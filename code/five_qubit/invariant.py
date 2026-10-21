"""Unsatisfied configurations of Q+(2N-1,2) invariant under GL(N,2) (and the swap X <-> Z).

The X-type and the Z-type observables span two opposite generators U and W of the hyperbolic quadric
Q(x|z) = x.z. A matrix A in GL(N,2) acts by (x|z) -> (Ax | A^{-T} z); this is the action of CNOT circuits.
Signs are preserved up to a relabelling of the points (the action is realised by Clifford unitaries), so the
set of unsatisfied configurations, a coset of the image of the line-point incidence map, is invariant.
The script computes the orbits on lines, finds which unions of orbits are unsatisfied configurations (F2
elimination with the point variables eliminated first), and prints the smallest ones.

    python invariant.py N [--no-swap]    (N = 3, 4, 5, 6; N = 6 takes about ten seconds)
--no-swap uses GL(N,2) alone; the minimum is the same for N = 3, 4, 5.
"""
import itertools
import sys
from pauli import Space

N = int(sys.argv[1])
sp = Space(N)
pts, lines = sp.quadric()
idx = {p: i for i, p in enumerate(pts)}
lid = {frozenset(l[:3]): i for i, l in enumerate(lines)}
print(f"Q+({2 * N - 1},2): {len(pts)} points, {len(lines)} lines")


def mat_apply(cols, v):
    r = 0
    for i in range(N):
        if (v >> i) & 1:
            r ^= cols[i]
    return r


def inverse_transpose(cols):
    A = [[(cols[j] >> i) & 1 for j in range(N)] + [int(i == j) for j in range(N)] for i in range(N)]
    for c in range(N):
        p = next(r for r in range(c, N) if A[r][c])
        A[c], A[p] = A[p], A[c]
        for r in range(N):
            if r != c and A[r][c]:
                A[r] = [a ^ b for a, b in zip(A[r], A[c])]
    inv = [row[N:] for row in A]
    return [sum(inv[j][i] << i for i in range(N)) for j in range(N)]


def gl_element(cols):
    B = inverse_transpose(cols)
    return lambda v: mat_apply(cols, sp.x(v)) | (mat_apply(B, sp.z(v)) << N)


gens = [gl_element([1 << ((i + 1) % N) for i in range(N)]),            # cyclic permutation of the qubits
        gl_element([1, 3] + [1 << i for i in range(2, N)]),             # a transvection (one CNOT)
        lambda v: sp.z(v) | (sp.x(v) << N)]                             # X <-> Z on every qubit
if "--no-swap" in sys.argv:
    gens.pop()
parent = list(range(len(lines)))


def find(i):
    while parent[i] != i:
        parent[i] = parent[parent[i]]
        i = parent[i]
    return i


for g in gens:
    for i, l in enumerate(lines):
        a, b = find(i), find(lid[frozenset(g(p) for p in l[:3])])
        if a != b:
            parent[a] = b
orbits = {}
for i in range(len(lines)):
    orbits.setdefault(find(i), []).append(i)
orbits = sorted(orbits.values(), key=len)
k = len(orbits)


def kind(l):
    """X: point of U, Z: point of W, m: a 'midpoint' (neither)."""
    return "".join(sorted("X" if sp.z(p) == 0 else "Z" if sp.x(p) == 0 else "m" for p in l[:3]))


print("orbits:", [(len(o), kind(lines[o[0]])) for o in orbits])
# unknowns: bit 0 rhs (sign), bits 1..k orbit indicators c_j, bits k+1.. point values f_p (eliminated first)
orb_of = {i: j for j, o in enumerate(orbits) for i in o}
piv = {}
for i, (a, b, c, s) in enumerate(lines):
    r = s | (1 << (1 + orb_of[i]))
    for p in (a, b, c):
        r ^= 1 << (1 + k + idx[p])
    while r:
        h = r.bit_length() - 1
        if h in piv:
            r ^= piv[h]
        else:
            piv[h] = r
            break
assert 0 not in piv
cons = sorted((piv[h] for h in piv if 1 <= h <= k), key=lambda r: r.bit_length())
free = [j for j in range(k) if (j + 1) not in piv]
sols = []
for bits in itertools.product((0, 1), repeat=len(free)):
    c = dict(zip(free, bits))
    for r in cons:
        j = r.bit_length() - 2
        c[j] = (r & 1) ^ (sum(c[t] for t in range(j) if (r >> (t + 1)) & 1) & 1)
    chosen = [j for j in range(k) if c[j]]
    sols.append((sum(len(orbits[j]) for j in chosen), chosen))
sols.sort()
print("invariant unsatisfied configurations, smallest first:")
for w, chosen in sols[:4]:
    print(f"  {w:>7}  =", " + ".join(f"{len(orbits[j])} ({kind(lines[orbits[j][0]])})" for j in chosen))
w, chosen = sols[0]
best = {i for j in chosen for i in orbits[j]}
on = {}
for i in best:
    for p in lines[i][:3]:
        on[p] = on.get(p, 0) + 1
deg = {}
for p in pts:
    deg.setdefault(kind((p,)), set()).add(on.get(p, 0))
print("lines of the smallest one through each point, by point kind:", {t: sorted(v) for t, v in deg.items()})
with open(f"invariant_N{N}.txt", "w") as f:
    for i in sorted(best):
        f.write("%d %d %d\n" % lines[i][:3])
# an explicit assignment whose violated lines are exactly this configuration, checked directly
rows = []
for i, (a, b, c, s) in enumerate(lines):
    rows.append(((1 << idx[a]) | (1 << idx[b]) | (1 << idx[c]), s ^ (i in best)))
piv = {}
for mask, rhs in rows:
    while mask:
        h = mask.bit_length() - 1
        if h not in piv:
            piv[h] = (mask, rhs)
            break
        mask ^= piv[h][0]
        rhs ^= piv[h][1]
    else:
        assert rhs == 0
f = {}
for h in sorted(piv):                       # pivot rows only involve lower-indexed unknowns
    mask, rhs = piv[h]
    f[h] = rhs ^ (sum(f.get(t, 0) for t in range(h) if (mask >> t) & 1) & 1)
viol = {i for i, (a, b, c, s) in enumerate(lines) if f.get(idx[a], 0) ^ f.get(idx[b], 0) ^ f.get(idx[c], 0) ^ s}
assert viol == best
print(f"witness assignment checked: it violates exactly these {len(viol)} lines")
with open(f"witness_N{N}.txt", "w") as fh:
    fh.write("".join(str(f.get(i, 0)) for i in range(len(pts))) + "\n")
