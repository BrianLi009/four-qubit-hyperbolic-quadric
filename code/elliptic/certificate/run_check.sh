#!/bin/sh
# Certificate for deg Q-(7,2) >= 315, checked by programs that share no code with the search.
# Needs the files of run_exact.sh run 1 (leaves_v1.txt, out_v1_*.txt, hdata_v1_lin.txt) and of run.sh (orbits.txt, zdata.txt).
# 1. generate the certificate: rerun inner_bb, with a margin of 2e-4, on the leaves the uniform split does not settle,
#    writing the multipliers of every node in integers (about 320 MB, not kept in the repository);
# 2. check_setup.py: signs from Pauli matrices, witnesses, symmetries, gauge, doily cover;
# 3. check_cert: orbit coverage, doily degree and leaf completeness, and the bound of every leaf in exact integers.
set -e
cd "$(dirname "$0")"
CORES=${CORES:-3}
cc -O3 -o check_cert check_cert.c
cc -O3 -o ../inner_bb ../inner_bb.c -lm
awk '$8 != "0" || $7 > 1 {print $1, $2, $3}' ../out_v1_*.txt > leaves_cert.txt
awk -v k="$CORES" '{print > ("part_cert_" (NR % k))}' leaves_cert.txt
for f in part_cert_*; do nice -n 10 ../inner_bb ../zdata.txt ../hdata_v1_lin.txt "$f" 315 300 cert_${f##*_}.bin > /dev/null & done
wait
rm -f part_cert_*
python3 check_setup.py ../hdata_v1_lin.txt ../zdata.txt > setup_v1.txt
./check_cert setup_v1.txt ../orbits.txt ../leaves_v1.txt orbits
./check_cert setup_v1.txt ../orbits.txt ../leaves_v1.txt leaves
k=0
while [ $k -lt "$CORES" ]; do
    nice -n 10 ./check_cert setup_v1.txt ../orbits.txt ../leaves_v1.txt bounds $k "$CORES" cert_*.bin > bounds_$k.log &
    k=$((k + 1))
done
wait
cat bounds_*.log && shasum -a 256 cert_*.bin
grep -q FAIL bounds_*.log && exit 1
echo "CERTIFICATE CHECKED: every assignment of Q-(7,2) violates at least 315 lines"
