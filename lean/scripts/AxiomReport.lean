/-
Axioms of the main theorems. Run from `lean/` after `lake build`:
  lake env lean scripts/AxiomReport.lean
Every line must list only propext, Classical.choice and Quot.sound (no sorryAx, no Lean.ofReduceBool).
-/
import QuadricDegree

#print axioms Contextuality.Pauli.Q8Plus.degree_eq_315
#print axioms Contextuality.Pauli.Q8Plus.le_numViolated
#print axioms Contextuality.Pauli.Q8Plus.witness_check
#print axioms Contextuality.Pauli.Q8Plus.contexts_length
#print axioms Contextuality.Pauli.context_product
#print axioms Contextuality.Pauli.pauliMat_mul
