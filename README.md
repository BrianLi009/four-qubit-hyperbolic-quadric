# The four-qubit hyperbolic quadric has contextuality degree 315

This repository contains the paper, the code and the Lean proof for the following results.

- **Main theorem.** Every hyperbolic quadric Q⁺(7,2) of the four-qubit Pauli space, with its 1575 lines as contexts, has contextuality degree exactly **315**. This proves a conjecture of Muller, Saniga, Giorgetti, Holweck and Kelleher (arXiv:2407.02928).
- **Optimal assignments.** In every optimal assignment, each of the 40 320 doilies of the quadric fails on exactly one ruling of one of its grids. There are exactly **240** optimal sets of violated lines. They form one orbit of O⁺(8,2), and each is isomorphic to the dual polar space **DW(5,2)**, which proves the second half of the same conjecture. This part is computer-assisted (SAT enumeration with a DRAT certificate).
- **All quadrics.** For N ≥ 3, every hyperbolic or elliptic quadric of the N-qubit space with L lines has degree at least ⌈L/5⌉.
- **Beyond the doily bound (computer-assisted).** The four-qubit elliptic quadric Q⁻(7,2) has degree at least **306** (was 215), and W(7,2) at least **1530** (was 1071). Averaging over Q⁻(7,2) sections then gives ⌈2L/7⌉ for every quadric with N ≥ 5 and every W(2N−1,2) with N ≥ 4.
- **Five qubits.** **6776 ≤ deg Q⁺(9,2) ≤ 6975**, so the doily bound 4743 is not tight. The upper bound is attained by the smallest unsatisfied configuration invariant under the CNOT group GL(5,2), built on the point–hyperplane incidence graph of PG(4,2). If deg Q⁻(7,2) = 315, then deg Q⁺(9,2) = 6975.
- **Physics.** The 1575 contexts give a state-independent noncontextuality inequality: the classical bound is exactly 945 and the quantum value is 1575.

The lower bound has a short proof with no computation: Peres–Mermin parity, Sylvester's model of GQ(2,2) and Witt's theorem. The theorem for the real quadric, i.e. the observables with an even number of Y's, is kernel-checked in Lean 4.

## Layout

| Path | What it is |
|---|---|
| `main.tex`, `refs.bib` | The paper (build with `tectonic -X compile main.tex`, or with pdflatex + bibtex) |
| `code/` | Python checks of every finite fact in the paper, the witness, and the SAT enumeration of the optimal assignments (see `code/README.md`) |
| `lean/` | The Lean 4 proof of `degree 0 = 315` and the scripts that generate its data files (see `lean/README.md`) |

## Building the paper (Overleaf or locally)

The paper is the single LaTeX root `main.tex`, with its bibliography `refs.bib`, both at the top level. No other `.tex`, `.cls` or `.sty` files are in the repository, so Overleaf detects the main document automatically.

- **Overleaf:** New Project → Import from GitHub → this repository. Use the default compiler, pdfLaTeX. The `code/` and `lean/` folders come along as ordinary files and do not affect the build.
- **Locally:** `latexmk -pdf main.tex` (pdfLaTeX + BibTeX), or `tectonic -X compile main.tex`.

Packages used: amsmath, amssymb, amsthm, booktabs, graphicx, enumitem, xcolor, hyperref, cleveref and geometry, all standard in TeX Live.

## Quick start

```shell
python3 -m venv .venv && .venv/bin/pip install -r code/requirements.txt
cd code
../.venv/bin/python verify_facts.py          # all finite facts used in the paper (under a minute)
../.venv/bin/python independent_check.py     # a second, separately written check of the bound and the witness
../.venv/bin/python enumerate_optimal.py     # the 240 optimal violated sets (under a minute)
../.venv/bin/python optimal_structure.py     # orbit, realisability, comparison with the SAT list, DW(5,2) isomorphism
../.venv/bin/python general_bounds.py        # the table of lower bounds for all quadrics
sh elliptic/run.sh                            # deg Q-(7,2) >= 306 and deg W(7,2) >= 1530 (about 20 minutes)
cd five_qubit
../../.venv/bin/python invariant.py 5         # the GL(5,2)-invariant configuration with 6975 lines (seconds)
../../.venv/bin/python sections.py +          # deg Q+(9,2) >= 6776 by averaging over 19 840 sections (2 minutes)
```

Lean (about 10 minutes and under 3 GB on a laptop, after downloading the Mathlib cache):

```shell
cd lean
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean scripts/AxiomReport.lean       # only propext, Classical.choice, Quot.sound
```

Running times of every computation, the SAT encodings and a comparison of encodings are in the section "Computations" of the paper. Everything except the Lean build reruns in a few minutes on a laptop.

## Conventions

A Pauli observable on four qubits is encoded as an integer `v < 256`. Bit `i` is `x_i` and bit `i+4` is `z_i`; qubit `i` carries I, X, Z, Y for `(x_i, z_i) = (0,0), (1,0), (0,1), (1,1)`. The real quadric is `Q_0(v) = number of Y's mod 2`. An assignment gives each observable a bit, and bit 1 means outcome −1. The same conventions are used in the paper, the Python code and Lean. The scripts in `code/five_qubit` use the same convention for N qubits (bit `i+N` is `z_i`); the instance files of `code/elliptic` put `x` in the high bits and `z` in the low bits.

## License

MIT (see `LICENSE`).
