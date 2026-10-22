#!/bin/sh
# Reproduces deg Q-(7,2) >= 315 (Theorem "elliptic").  Needs the files of run.sh (orbits.txt, zdata_v253.txt).
# Run 1 (v0 = 1, 336 linear doilies): a few hours on 3 cores.  Run 2 (v0 = 253, 1008 quadratic doilies): about 3x
# longer.  Set CORES to change the number of parallel processes.
set -e
cd "$(dirname "$0")"
CORES=${CORES:-3}
cc -O3 -o zcount zcount.c
cc -O3 -o inner_bb inner_bb.c -lm
cc -O3 -DND=1008 -o inner_bb_q inner_bb.c -lm
check() {   # $1 = tag; all leaves must have status P
    n=$(cat leaves_$1.txt | wc -l)
    cat out_$1_*.txt | awk -v n="$n" '{c[$4]++; t++} END {print t, "leaves:", (c["P"]+0), "P,", (c["U"]+0), "U,", (c["C"]+0), "C"; exit !(t == n && c["P"] == n)}'
}
run() {     # $1 = tag, $2 = zdata, $3 = orbits, $4 = hdata, $5 = solver
    ./zcount "$2" 251 "$3" leaves_$1.txt | grep -E "^z |TOTAL" > zcount_$1.log
    tail -1 zcount_$1.log
    rm -f out_$1_*.txt
    awk -v k="$CORES" -v t="$1" '{print > ("part_" t "_" (NR % k))}' leaves_$1.txt
    for f in part_$1_*; do nice -n 10 ./$5 "$2" "$4" "$f" 315 300 > out_$1_${f##*_}.txt & done
    wait
    rm -f part_$1_*
    check $1
}
# run 1
python3 hstruct.py lin > hdata_v1_lin.txt
run v1 zdata.txt orbits.txt hdata_v1_lin.txt inner_bb
# run 2: other vector, other generators (zdata_v253.txt from run.sh), quadratic doilies
nice -n 5 ./zorb zdata_v253.txt 252 orbits_v253.txt > /dev/null 2>&1
V0=253 python3 hstruct.py quad > hdata_v253_quad.txt
run v253 zdata_v253.txt orbits_v253.txt hdata_v253_quad.txt inner_bb_q
# upper bound: an explicit assignment with 315 violated lines
python3 witness_315.py
# separately written checks
python3 brute_count.py 1 orbits.txt zcount_v1.log > brute_count.log && tail -1 brute_count.log
awk '$8 != "0" && $7 == 1' out_v1_*.txt > leaves_v1_hard.txt   # leaves settled at the root after >= 1 subgradient step
python3 lagrange_check.py hdata_v1_lin.txt leaves_v1_hard.txt 1000 > lagrange_check.log && tail -1 lagrange_check.log
