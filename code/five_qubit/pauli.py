"""Signed line configurations of N-qubit quadrics.

A point is an integer v < 4^N: bit i is x_i and bit i+N is z_i (qubit i carries I, X, Z, Y for (x_i, z_i) =
(0,0), (1,0), (0,1), (1,1)). A line {a, b, a+b} has sign bit 1 iff P(a) P(b) P(a+b) = -I.
"""
P1 = {(1, 0, 1, 1): 1, (1, 1, 1, 0): 3, (1, 1, 0, 1): 1, (0, 1, 1, 1): 3, (0, 1, 1, 0): 1, (1, 0, 0, 1): 3}


class Space:
    def __init__(self, N, eps="+"):
        self.N, self.eps, self.m = N, eps, (1 << N) - 1

    def x(self, v): return v & self.m
    def z(self, v): return v >> self.N

    def symp(self, u, v):
        return (bin(self.x(u) & self.z(v)).count("1") + bin(self.z(u) & self.x(v)).count("1")) & 1

    def Q(self, v):
        """Sum x_i z_i, plus x_1 + z_1 for the elliptic quadric (this makes the first plane elliptic)."""
        q = bin(self.x(v) & self.z(v)).count("1")
        if self.eps == "-":
            q += (v & 1) + ((v >> self.N) & 1)
        return q & 1

    def phase(self, u, v):
        N = self.N
        return sum(P1.get(((u >> i) & 1, (u >> (i + N)) & 1, (v >> i) & 1, (v >> (i + N)) & 1), 0)
                   for i in range(N)) % 4

    def quadric(self):
        pts = [v for v in range(1, 1 << (2 * self.N)) if self.Q(v) == 0]
        S = set(pts)
        lines = []
        for a in pts:
            for b in pts:
                c = a ^ b
                if a < b < c and c in S and not self.symp(a, b):
                    k = self.phase(a, b)
                    assert k in (0, 2)
                    lines.append((a, b, c, k // 2))
        return pts, lines


def coboundary_solvable(rows):
    """rows: ints, bit 0 the right-hand side, higher bits the unknowns. True iff the F2 system is consistent."""
    piv = {}
    for r in rows:
        while r:
            h = r.bit_length() - 1
            if h in piv:
                r ^= piv[h]
            else:
                piv[h] = r
                break
    return 0 not in piv
