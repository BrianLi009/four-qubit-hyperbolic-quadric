#!/bin/sh
# DRAT check of the final formula of enumerate_optimal.py (the SAT enumeration of the optimal violated sets).
# Needs cadical and drat-trim (https://github.com/marijnheule/drat-trim) on the PATH.
# If cake_lpr (https://github.com/tanyongkiam/cake_lpr) is on the PATH, the proof is also converted
# to LRAT by drat-trim and checked by this verified checker.
set -e
cd "$(dirname "$0")/.."
[ -f final.cnf ] || python3 enumerate_optimal.py --cnf
shasum -a 256 final.cnf
cadical -q --no-binary final.cnf final.drat || [ $? -eq 20 ]     # exit code 20 = UNSATISFIABLE
drat-trim final.cnf final.drat
if command -v cake_lpr >/dev/null 2>&1; then
  drat-trim final.cnf final.drat -L final.lrat > /dev/null
  cake_lpr --CML_HEAP_SIZE=4000 --CML_STACK_SIZE=1000 final.cnf final.lrat
fi
