#!/bin/sh
# DRAT check of the final formula of enumerate_optimal.py (the SAT enumeration of the optimal violated sets).
# Needs cadical and drat-trim (https://github.com/marijnheule/drat-trim) on the PATH.
set -e
cd "$(dirname "$0")/.."
[ -f final.cnf ] || python3 enumerate_optimal.py --cnf
shasum -a 256 final.cnf
cadical -q --no-binary final.cnf final.drat || [ $? -eq 20 ]     # exit code 20 = UNSATISFIABLE
drat-trim final.cnf final.drat
