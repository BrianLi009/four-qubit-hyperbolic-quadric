"""Shared helpers for the Q-(7,2) lower bound: load the signed configuration, sub-configurations, F2 basis."""
from __future__ import annotations

from pathlib import Path

import numpy as np

INST = Path(__file__).resolve().parent / "instances"
N = 4


def load(name="w4_ell"):
    pts = [int(p) for p in np.load(INST / f"{name}.points.npy")]
    raw = np.loadtxt(INST / f"{name}.txt", skiprows=1, dtype=np.int64)
    lines = [(pts[a], pts[b], pts[c], int(s)) for a, b, c, s in raw]
    return pts, lines


def symp(u, v, n=N):
    m = (1 << n) - 1
    return (bin((u >> n) & v & m).count("1") + bin(u & m & (v >> n)).count("1")) & 1


def restrict(lines, pset):
    return [l for l in lines if l[0] in pset and l[1] in pset and l[2] in pset]


def basis(points):
    """A maximal F2-independent subset of the points (greedy, with reduced forms)."""
    rows, chosen = {}, []
    for p in points:
        v = p
        while v:
            h = v.bit_length() - 1
            if h in rows:
                v ^= rows[h]
            else:
                rows[h] = v
                chosen.append(p)
                break
    return chosen
