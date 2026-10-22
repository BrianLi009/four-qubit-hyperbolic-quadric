#!/bin/sh
# Reproduces Theorem "elliptic" (deg Q-(7,2) >= 306, deg W(7,2) >= 1530). About 20 minutes on one core.
set -e
cd "$(dirname "$0")"
python3 gen_instances.py 4 ell
python3 gen_instances.py 4 full
cc -O3 -o zorb zorb.c
# run 1: v = 1, 8 generators; must reproduce the stored input exactly
python3 mkz.py > zdata.new && cmp zdata.new zdata.txt && rm zdata.new
nice -n 5 ./zorb zdata.txt 100000 orbits.txt > zorb.out 2> zorb.err
grep DONE zorb.out
python3 -c "
rows = [tuple(map(int, l.split())) for l in open('orbits.txt')]
f = sorted(p + 2 * g for _, p, g, _ in rows)
assert len(rows) == 467 and f[0] == 216 and f[1] == 220, (len(rows), f[:3])
print('orbits', len(rows), 'minimum', f[0], 'attained by', f.count(216), 'orbit; next value', f[1])"
# run 2: v = 253, 12 other generators, search for f <= 216 only
GEN_SEED=11 python3 mkz.py 253 12 > zdata_v253.txt
nice -n 5 ./zorb zdata_v253.txt 217 > zorb_v253.out 2> zorb_v253.err
grep DONE zorb_v253.out
# independent brute force on six orbits, and the averaging and transport checks
python3 brute_check.py 1 orbits.txt > brute_check.log && tail -1 brute_check.log
python3 verify_avg.py > verify_avg.log && tail -1 verify_avg.log
