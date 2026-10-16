"""The doily lower bound deg >= ceil(L/5) for the quadrics and the whole space of N qubits (the general theorem of the paper).

Point and line counts come from the formulas in the paper; for N <= 5 they are also counted directly.
The upper bounds are those reported by Muller et al., arXiv:2407.02928, Table 3 (quadrics) and Table 1 (W).
"""
import itertools
import sys

UPPER = {  # N: (hyperbolic, elliptic) upper bounds from arXiv:2407.02928, Table 3
    3: (21, 9), 4: (315, 315), 5: (6975, 7087), 6: (132391, 131700), 7: (2331191, 2294580)}
EXACT = {(3, "+"): 21, (3, "-"): 9}   # exact values known before (de Boutray et al. 2022)


def npts(N, eps):     # points of Q^eps(2N-1, 2)
    return (2 ** N - eps) * (2 ** (N - 1) + eps)


def nlines(N, eps):   # each point lies on as many lines as Q^eps(2N-3, 2) has points
    return npts(N, eps) * npts(N - 1, eps) // 3


def direct(N, eps):
    """Count points and lines of Q(v) = sum x_i z_i (+ x_1^2 + x_1 z_1 + z_1^2 for eps = -1) directly."""
    def Qf(v):
        x, z = v & ((1 << N) - 1), v >> N
        q = bin(x & z).count("1")
        if eps < 0:
            q += (x & 1) + (z & 1)        # x1^2 + z1^2 = x1 + z1 over F_2: makes the first plane elliptic
        return q & 1
    def B(u, v): return Qf(u ^ v) ^ Qf(u) ^ Qf(v)
    P = [v for v in range(1, 1 << (2 * N)) if Qf(v) == 0]
    S = set(P)
    L = sum(1 for a in P for b in P if a < b < (a ^ b) and (a ^ b) in S and not B(a, b))
    return len(P), L


def main():
    ok = True
    print(f"{'N':>2} {'type':>4} {'points':>8} {'lines':>9} {'ceil(L/5)':>10} {'known upper':>12}")
    for N in range(3, 8):
        for eps, name in ((1, "+"), (-1, "-")):
            p, L = npts(N, eps), nlines(N, eps)
            if N <= 5:
                dp, dL = direct(N, eps)
                ok &= (dp, dL) == (p, L)
            lb = -(-L // 5)
            ub = UPPER[N][0 if eps > 0 else 1]
            tag = " (exact)" if (N, name) in EXACT or (N, name) == (4, "+") else ""
            print(f"{N:>2} {('Q' + name):>4} {p:>8} {L:>9} {lb:>10} {ub:>12}{tag}")
        Wl = (4 ** N - 1) * (4 ** (N - 1) - 1) // 3
        print(f"{N:>2} {'W':>4} {4 ** N - 1:>8} {Wl:>9} {-(-Wl // 5):>10}")
    print("direct counts agree with the formulas for N <= 5:", ok)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
