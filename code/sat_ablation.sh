#!/bin/sh
# The encoding comparison of the paper: the four combinations of doily family and pair clauses, each with a time
# limit of 30 minutes (wall clock), one after the other. Output: sat_ablation.log.
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
for cfg in "--family=lean --no-pairs" "--family=all --no-pairs" "--family=lean" "--family=all"; do
  echo "=== $cfg"
  start=$(date +%s)
  timeout 1800 nice -n 15 $PY -u enumerate_optimal.py $cfg 2>&1 || true
  echo "wall $(( $(date +%s) - start )) s (limit 1800 s)"
done
