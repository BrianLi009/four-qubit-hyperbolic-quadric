#!/bin/sh
# Exhaustive search over quadratic assignments (a few seconds).
cd "$(dirname "$0")" && python3 prepare.py && cc -O3 -o search search.c && ./search
