# Code

Requirements: Python 3.10 or later, with `numpy` and `python-sat` (`pip install -r requirements.txt`). A C compiler is needed for `quadratic/`. CaDiCaL and drat-trim are needed only for the DRAT check.

Every script exits with a non-zero status if a check fails.

| File | What it checks or computes | Time |
|---|---|---|
| `verify_facts.py` | Every finite fact used in the paper: counts of quadrics, points, lines and negative lines; signs from the phase rule and from 16×16 matrix products; the 40 320 doilies of `Q_0` and their 384-fold cover; the 10 grids of each doily, 4 through each line, 2 through two intersecting lines; oddness of all 67 200 grids; the witness and its structure; transport of the witness to all 136 hyperbolic quadrics. `--brute` also computes the degree 3 of every doily over its 2^15 assignments. | < 1 min (+ a few min with `--brute`) |
| `independent_check.py` | A second implementation, written separately, of the counts, the doily bound (by brute force) and the witness. Signs come from the Pauli multiplication table. | ~1 min |
| `w72.py`, `doilies.py` | The four-qubit space W(7,2) with signs from Pauli matrices, and the doilies of a hyperbolic quadric with their exact degrees | |
| `find_witness.py` | Local search for an assignment with 315 violated lines. It writes `witness_found.json` (the committed witness is `witness.json`) | seconds |
| `witness.json` | The witness: an assignment of the 135 points of `Q_0` violating exactly 315 lines | |
| `enumerate_optimal.py` | SAT enumeration of all optimal violated sets. It writes `optimal_sets.json`, and with `--cnf` the final formula `final.cnf` for a DRAT check | < 1 min |
| `optimal_structure.py` | Orbit of the witness's violated set under O⁺(8,2) (240 sets), realisability of each by linear algebra, equality with the SAT list, an isomorphism with DW(5,2) found and checked for each of the 240 sets, and a check of the stored isomorphism `dw52_isomorphism.json` for the witness (`--find` recomputes it) | seconds |
| `optimal_sets.json`, `dw52_isomorphism.json` | Outputs of the two scripts above | |
| `drat/` | The DRAT check of the final unsatisfiable formula: `check.sh` and its output `check.log` (CaDiCaL proof, verified by drat-trim) | ~1 min |
| `general_bounds.py` | The table of the lower bounds ⌈L/5⌉ for all quadrics, N = 3..7, with direct counts for N ≤ 5 | < 1 s |
| `quadratic/` | Exhaustive search over the 2^28 quadratic assignments: none violates fewer than 532 lines (`./run.sh`) | seconds |

Run the scripts from this folder. `verify_facts.py`, `enumerate_optimal.py`, `optimal_structure.py` and `quadratic/prepare.py` share the integer encoding of `verify_facts.py`. `w72.py`, `doilies.py`, `independent_check.py` and `find_witness.py` use tuples, as does `witness.json`.
