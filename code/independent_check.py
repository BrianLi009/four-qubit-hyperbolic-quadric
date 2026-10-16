"""Independent re-check of the degree 315 of Q+(7,2), written without importing the other scripts.
Signs of contexts come from the Pauli multiplication table (phases i^k), not from matrices."""
import sys
import itertools, json, collections
import numpy as np
N = 4
# single-qubit Pauli product: P*Q = phase * R, letters as (x,z) bits; phase in units of i
MUL = {}
L = {(0,0):"I",(1,0):"X",(1,1):"Y",(0,1):"Z"}
table = {("I","I"):(0,"I"),("I","X"):(0,"X"),("I","Y"):(0,"Y"),("I","Z"):(0,"Z"),
         ("X","I"):(0,"X"),("X","X"):(0,"I"),("X","Y"):(1,"Z"),("X","Z"):(3,"Y"),
         ("Y","I"):(0,"Y"),("Y","X"):(3,"Z"),("Y","Y"):(0,"I"),("Y","Z"):(1,"X"),
         ("Z","I"):(0,"Z"),("Z","X"):(1,"Y"),("Z","Y"):(3,"X"),("Z","Z"):(0,"I")}
def mul(p, q):   # words, returns (phase mod 4, word)
    ph, w = 0, ""
    for a, b in zip(p, q):
        k, r = table[(a, b)]; ph += k; w += r
    return ph % 4, w
words = ["".join(t) for t in itertools.product("IXYZ", repeat=N) if set(t) != {"I"}]
def commute(p, q):
    return sum(1 for a, b in zip(p, q) if a != "I" and b != "I" and a != b) % 2 == 0
# quadric: Q_a(P) = (#Y + <a,P>) mod 2 with a = the quadric used before
qa = json.load(open("witness.json"))["quadric_a"]
aw = "".join(L[(qa[i], qa[N + i])] for i in range(N))
def inquad(p): return (p.count("Y") + (0 if commute(p, aw) else 1)) % 2 == 0
Q = [w for w in words if inquad(w)]
lines = {}
for p, q in itertools.combinations(Q, 2):
    if not commute(p, q): continue
    ph, r = mul(p, q)
    if r not in Q and r != "I" * N: continue
    if r == "I" * N or r not in Q: continue
    key = frozenset((p, q, r))
    if key in lines: continue
    ph2, ident = mul(mul(p, q)[1], r)            # (pq) r with phase
    total = (ph + ph2) % 4                         # p q r = i^total * I
    assert ident == "I" * N and total in (0, 2)
    lines[key] = 0 if total == 0 else 1            # 1 = product -I
print("points", len(Q), "lines", len(lines), "negative lines", sum(lines.values()))
# upper bound: re-evaluate the stored assignment
d = json.load(open("witness.json"))
assign = {}
for v, x in zip(d["points"], d["assignment"]):
    assign["".join(L[(v[i], v[N + i])] for i in range(N))] = x
viol = sum(1 for k, s in lines.items() if (sum(assign[p] for p in k) % 2) != s)
print("stored assignment violates", viol)
# doilies: 15-point sets closed as GQ(2,2) inside Q found from scratch as 5-dim subspaces' singular parts
vec = {w: tuple([1 if c in "XY" else 0 for c in w] + [1 if c in "ZY" else 0 for c in w]) for w in words}
wor = {v: w for w, v in vec.items()}
lineset = set(lines)
deg_hist = collections.Counter(); cover = collections.Counter(); count = 0
def gf2_span(gs):
    S = {tuple([0] * 8)}
    for g in gs: S |= {tuple((a + b) % 2 for a, b in zip(s, g)) for s in S}
    return S
# doilies: the 15 singular points of a 5-dim subspace carrying 15 lines of the quadric, 3 through each point
def rref_subspaces(n, k):
    for pivots in itertools.combinations(range(n), k):
        free = [(rr, c) for rr in range(k) for c in range(n) if c > pivots[rr] and c not in pivots]
        for bits in itertools.product((0, 1), repeat=len(free)):
            M = [[0] * n for _ in range(k)]
            for rr, pv in enumerate(pivots): M[rr][pv] = 1
            for (rr, c), b in zip(free, bits): M[rr][c] = b
            yield [tuple(row) for row in M]
Qset = set(Q)
for gens in rref_subspaces(8, 5):
    V = gf2_span(gens)
    sing = [wor[v] for v in V if any(v) and wor[v] in Qset]
    if len(sing) != 15: continue
    ls = [k for k in itertools.combinations(sing, 3) if frozenset(k) in lineset]
    if len(ls) != 15: continue
    pc = collections.Counter(x for k in ls for x in k)
    if any(pc[x] != 3 for x in sing): continue
    count += 1
    for k in ls: cover[frozenset(k)] += 1
    idx = {x: i for i, x in enumerate(sing)}
    xs = np.arange(1 << 15)
    v = np.zeros(1 << 15, dtype=np.int32)
    for k in ls:
        par = (xs >> idx[k[0]] ^ xs >> idx[k[1]] ^ xs >> idx[k[2]]) & 1
        v += (par != lines[frozenset(k)])
    deg_hist[int(v.min())] += 1
print("doilies", count, "coverage", collections.Counter(cover[k] for k in lines), "degrees", deg_hist)
print("lower bound", count * min(deg_hist) / min(cover.values()))
ok = viol == 315 and count * min(deg_hist) / min(cover.values()) == 315 and len(set(cover.values())) == 1
print("independent check of degree 315:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
