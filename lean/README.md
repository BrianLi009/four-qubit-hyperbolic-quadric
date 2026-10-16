# Lean proof: the real four-qubit quadric has degree 315

```lean
theorem Contextuality.Pauli.Q8Plus.degree_eq_315 : Contextuality.Pauli.degree 0 = 315
```

`degree 0` is the least number of violated contexts, over all assignments, of the quadric `Q_0`: the 135 four-qubit Pauli observables with an even number of Y's, and their 1575 lines. The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound` (`scripts/axiom_report.txt`). It uses no `sorry`, no `native_decide` and no added axioms. Every finite check is done by `decide +kernel`.

Toolchain: Lean `v4.35.0-rc2`, Mathlib at commit `045acef0` (pinned in `lakefile.toml` and `lake-manifest.json`).

## Files

| File | Content |
|---|---|
| `QuadricDegree/Basic.lean` | Points (integers `< 256`), symplectic form, the quadratic forms `Q_w`, the phase rule, the contexts (computed inside Lean by filtering pairs of points), their signs, violation and `degree` |
| `QuadricDegree/OddSets.lean` | Every assignment violates a context of every odd set (the parity lemma) |
| `QuadricDegree/PhaseMatrix.lean` | The phase rule holds for the actual 16×16 Pauli matrices over ℂ (`pauliMat_mul`), so the sign of every context is the sign of the matrix product (`context_product`) |
| `QuadricDegree/Q8PlusData.lean` | Generated data: 2520 doilies covering every context 24 times, the 10 grids of GQ(2,2) as positions, the witness |
| `QuadricDegree/Q8PlusContexts.lean` | Generated: the 1575 contexts in 64 literal chunks, each checked against the definition (`contexts_eq`) |
| `QuadricDegree/Q8PlusChecks.lean` | Generated kernel checks: the cover (in chunks), the oddness of every grid of every doily |
| `QuadricDegree/Q8Plus.lean` | The proof: the cover is a permutation of the contexts with multiplicity 24 (`keys_perm`), each doily has at least 3 violated contexts, `24·|V| ≥ 3·2520`, the witness, `degree_eq_315` |
| `scripts/AxiomReport.lean` | `#print axioms` for the main theorems |
| `gen/` | Python scripts that produce the data, and `mirror.py`, which re-checks in Python every property that Lean checks |

None of the generated data is trusted. Every property the proof uses is re-evaluated by the kernel, including the sorting of the 37 800 doily keys.

## Build

```shell
lake exe cache get                 # download the compiled Mathlib
LEAN_NUM_THREADS=1 lake build      # about 10 minutes, at most about 3 GB of memory
lake env lean scripts/AxiomReport.lean
```

Evaluating the checks in one piece needs about 10 GB of memory. They are therefore split into chunks, which are combined by permutation lemmas. Build one module at a time (`lake build QuadricDegree.Q8PlusChecks`, …) to keep a single Lean process alive.

## Regenerating the data

```shell
cd gen
python gen0.py                                # all 40320 doilies of Q_0 -> doil.pkl
python orb2.py perm 24                        # a 24-fold cover by S4-orbits (MILP, scipy) -> sel_perm.pkl
python order.py sel_perm.pkl                  # GQ(2,2) labelling of each doily -> order.json (= order_perm.json)
python emit.py order_perm.json 24 ../QuadricDegree/Q8PlusData.lean
python emit_ctx.py ../QuadricDegree/Q8PlusContexts.lean
python emit_checks.py ../QuadricDegree/Q8PlusChecks.lean
python mirror.py order_perm.json              # the same checks in Python
```

The last four commands reproduce the committed files byte for byte. `gen0.py` and `mirror.py` import `../code/doilies.py` and `../code/w72.py` and read `../code/witness.json`. `orb2.py` needs `scipy`.
