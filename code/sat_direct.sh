#!/bin/sh
# Baselines without the mathematics of the paper (MaxSAT and SAT with a global cardinality constraint), each with a
# time limit of 30 minutes. Output: sat_direct.log.
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
for mode in maxsat card; do
  echo "=== $mode"
  start=$(date +%s)
  timeout 1800 nice -n 15 $PY -u sat_direct.py $mode 2>&1 || echo "(stopped by the time limit)"
  echo "wall $(( $(date +%s) - start )) s (limit 1800 s)"
done
