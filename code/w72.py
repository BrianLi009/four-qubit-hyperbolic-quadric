"""4-qubit Pauli geometry W(7,2): points = 255 non-identity Pauli operators (up to sign), lines = triples
{a, b, ab} of pairwise commuting operators; each line carries the sign s with A*B*(AB) = s*I (s = +1/-1)
computed from actual Pauli matrices (Hermitian representatives XYZ with real phases).
Quadrics: Q_a(x) = Q0(x) + <a,x>, Q0 = number of Y's mod 2 (hyperbolic for a singular/Q0(a)=0 ... see counts)."""
import itertools, functools
import numpy as np

N = 4
PAULI = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]), "Y": np.array([[0, -1j], [1j, 0]]), "Z": np.array([[1, 0], [0, -1]])}
LET = "IXYZ"

def vec(word):   # symplectic vector (x|z)
    x = [1 if c in "XY" else 0 for c in word]; z = [1 if c in "ZY" else 0 for c in word]
    return tuple(x + z)

def word(v):
    return "".join(LET[(v[i]) + 2 * v[N + i]] if False else {(0,0):"I",(1,0):"X",(1,1):"Y",(0,1):"Z"}[(v[i], v[N+i])] for i in range(N))

def symp(u, v):
    return sum(u[i] * v[N + i] + u[N + i] * v[i] for i in range(N)) % 2

def add(u, v):
    return tuple((a + b) % 2 for a, b in zip(u, v))

def Q0(v):  # number of Y's mod 2
    return sum(v[i] * v[N + i] for i in range(N)) % 2

@functools.lru_cache(None)
def mat(w):
    m = np.array([[1]])
    for c in w:
        m = np.kron(m, PAULI[c])
    return m

points = [v for v in itertools.product((0, 1), repeat=2 * N) if any(v)]
lines = []
seen = set()
for a, b in itertools.combinations(points, 2):
    if symp(a, b): continue
    c = add(a, b)
    key = frozenset((a, b, c))
    if key in seen: continue
    seen.add(key)
    prod = mat(word(a)) @ mat(word(b)) @ mat(word(c))
    s = prod[0, 0] if abs(prod[0, 0]) > 0.5 else None
    assert s is not None and np.allclose(prod, s * np.eye(2 ** N)) and abs(abs(s) - 1) < 1e-9 and abs(s.imag) < 1e-9
    lines.append((a, b, c, 0 if s.real > 0 else 1))     # sign bit 1 = product -I

def quadric(a):
    return {v for v in points if (Q0(v) + symp(a, v)) % 2 == 0}

if __name__ == "__main__":
    print("points", len(points), "lines", len(lines), "negative lines", sum(l[3] for l in lines))
    quads = [(a, quadric(a)) for a in itertools.product((0, 1), repeat=2 * N)]
    sizes = sorted({len(q) for _, q in quads})
    hyp = [(a, q) for a, q in quads if len(q) == 135]; ell = [(a, q) for a, q in quads if len(q) == 119]
    print("quadric sizes", sizes, "hyperbolic", len(hyp), "elliptic", len(ell))
    def qlines(q): return [l for l in lines if l[0] in q and l[1] in q and l[2] in q]
    print("lines on a hyperbolic quadric", len(qlines(hyp[0][1])), "on an elliptic", len(qlines(ell[0][1])))
