"""Write the signed lines of Q^eps(2N-1,2) for anneal.c: header "points lines", then "i j k sign" per line.

    python dump_instance.py 5 + > q9plus.txt
"""
import sys
from pauli import Space

pts, lines = Space(int(sys.argv[1]), sys.argv[2]).quadric()
idx = {p: i for i, p in enumerate(pts)}
print(len(pts), len(lines))
for a, b, c, s in lines:
    print(idx[a], idx[b], idx[c], s)
