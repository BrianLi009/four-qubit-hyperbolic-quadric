"""Line configurations of the N-qubit symplectic polar space W(2N-1,2) and of its quadrics, with signs.

Points are the 4^N - 1 non-identity Pauli operators (x|z) in F_2^{2N}; a line is {a, b, a+b} with a, b
commuting. With Hermitian representatives P(x|z) = i^{x.z} X^x Z^z, the product P(a) P(b) P(a+b) equals
i^e I with e = |xa&za| + |xb&zb| - |xc&zc| + 2|za&xb| (mod 4), e in {0, 2}; the line is negative when e = 2.
Quadric Q_a = {v : |xv&zv| + <a, v> = 0 mod 2}; hyperbolic or elliptic by its number of points.

    python gen_instances.py 5 full|hyp|ell     ->  instances/w5_full.txt  (header "points lines", then
                                                   one line per context: three point indices and the sign bit)
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
POP = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)


def popcount(a: np.ndarray) -> np.ndarray:
    a = a.astype(np.int64)
    return POP[a & 0xFFFF] + POP[(a >> 16) & 0xFFFF]


def split(v: np.ndarray, n: int):
    return v >> n, v & ((1 << n) - 1)          # x part (high bits), z part (low bits)


def symp(u: np.ndarray, v: np.ndarray, n: int) -> np.ndarray:
    xu, zu = split(u, n)
    xv, zv = split(v, n)
    return (popcount(xu & zv) + popcount(zu & xv)) & 1


def lines_of(n: int, pts: np.ndarray):
    """All lines {a<b<c} inside the point set pts (assumed closed enough; we test membership)."""
    member = np.zeros(1 << (2 * n), dtype=bool)
    member[pts] = True
    index = -np.ones(1 << (2 * n), dtype=np.int64)
    index[pts] = np.arange(len(pts))
    out = []
    for i, a in enumerate(pts):
        b = pts[i + 1:]
        b = b[symp(np.full(len(b), a), b, n) == 0]
        c = a ^ b
        keep = (c > b) & member[c]
        b, c = b[keep], c[keep]
        if len(b) == 0:
            continue
        xa, za = a >> n, a & ((1 << n) - 1)
        xb, zb = split(b, n)
        xc, zc = split(c, n)
        e = (popcount(np.full(len(b), xa & za)) + popcount(xb & zb) - popcount(xc & zc) + 2 * popcount(za & xb)) % 4
        assert np.all((e == 0) | (e == 2)), "phase must be real"
        out.append(np.stack([np.full(len(b), index[a]), index[b], index[c], (e == 2).astype(np.int64)], axis=1))
    return np.concatenate(out)


def points_of(n: int, kind: str) -> np.ndarray:
    allv = np.arange(1, 1 << (2 * n), dtype=np.int64)
    if kind == "full":
        return allv
    x, z = split(allv, n)
    q0 = popcount(x & z) & 1
    hyp_size = (2 ** n - 1) * (2 ** (n - 1) + 1)
    for a in range(1 << (2 * n)):              # first quadric of the requested type, in a fixed order
        pts = allv[((q0 + symp(np.full(len(allv), a), allv, n)) & 1) == 0]
        if (kind == "hyp") == (len(pts) == hyp_size):
            return pts
    raise ValueError(kind)


def write(n: int, kind: str) -> Path:
    pts = points_of(n, kind)
    ls = lines_of(n, pts)
    path = HERE / "instances" / f"w{n}_{kind}.txt"
    path.parent.mkdir(exist_ok=True)
    with path.open("w") as f:
        f.write(f"{len(pts)} {len(ls)}\n")
        np.savetxt(f, ls, fmt="%d")
    np.save(path.with_suffix(".points.npy"), pts)
    print(f"N={n} {kind}: {len(pts)} points, {len(ls)} lines, {int(ls[:, 3].sum())} negative -> {path.name}")
    return path


if __name__ == "__main__":
    write(int(sys.argv[1]), sys.argv[2])
