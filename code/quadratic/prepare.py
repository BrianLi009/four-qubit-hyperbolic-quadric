"""Write lines.txt for search.c: the 1575 lines of Q_0 with the coordinates of beta(u, v) and their signs."""
import itertools
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify_facts import quadric_lines, sign_bit  # noqa: E402

pairs = list(itertools.combinations(range(8), 2))
L = sorted(tuple(sorted(k)) for k in quadric_lines(0))
with open(Path(__file__).resolve().parent / "lines.txt", "w") as f:
    f.write(f"{len(L)} {len(pairs)}\n")
    for a, b, _ in L:
        bits = [((a >> i) & 1) * ((b >> j) & 1) ^ ((a >> j) & 1) * ((b >> i) & 1) for i, j in pairs]
        f.write(" ".join(map(str, bits)) + f" {sign_bit(a, b)}\n")
print(f"wrote lines.txt ({len(L)} lines, {sum(sign_bit(a, b) for a, b, _ in L)} negative)")
