"""The upper bound deg Q-(7,2) <= 315 (first shown by Muller et al.): an explicit assignment of the elliptic
quadric instance w4_ell violating exactly 315 of its 1071 lines.  With --search, find one by simulated
annealing (seeded) and print it; otherwise check the stored one.
    python witness_315.py [--search]"""
import sys, random, math
from common import load

pts, lines = load("w4_ell")
idx = {p: i for i, p in enumerate(pts)}
WITNESS = [4, 6, 8, 10, 14, 32, 43, 44, 47, 50, 51, 62, 63, 64, 66, 69, 79, 92, 93, 94, 95, 99, 102, 104, 107, 114,
           117, 123, 124, 132, 134, 139, 143, 153, 155, 156, 158, 163, 169, 178, 184, 185, 189, 194, 201, 203,
           204, 213, 216, 217, 218, 227, 234, 242, 243]   # points (as integers, bit i = x_i, bit i+4 = z_i) with value 1


def violated(one):
    return sum((a in one) ^ (b in one) ^ (c in one) ^ s for a, b, c, s in lines)


def search(seed=1, steps=400000):
    rng = random.Random(seed)
    inc = {p: [] for p in pts}
    for i, (a, b, c, s) in enumerate(lines):
        for q in (a, b, c): inc[q].append(i)
    x = {p: rng.random() < 0.5 for p in pts}
    v = [x[a] ^ x[b] ^ x[c] ^ s for a, b, c, s in lines]
    cur = sum(v); best, bx = cur, dict(x)
    for t in range(steps):
        T = 3.0 * (0.05 / 3.0) ** (t / steps)
        p = pts[rng.randrange(len(pts))]
        d = sum(-1 if v[i] else 1 for i in inc[p])
        if d <= 0 or rng.random() < math.exp(-d / T):
            x[p] = not x[p]; cur += d
            for i in inc[p]: v[i] ^= 1
            if cur < best: best, bx = cur, dict(x)
    return best, sorted(p for p in pts if bx[p])


if __name__ == "__main__":
    if "--search" in sys.argv:
        best, one = search()
        print(best, one)
    else:
        n = violated(set(WITNESS))
        print(f"witness violates {n} of {len(lines)} lines")
        sys.exit(0 if n == 315 else 1)
