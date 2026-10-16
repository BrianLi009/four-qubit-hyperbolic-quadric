/-
Released under the GNU GPLv3 license.
-/
import QuadricDegree.Q8PlusContexts
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The phase rule agrees with the multiplication of Pauli matrices

`pauliMat v` is the four-qubit Pauli matrix `σ(x₀,z₀) ⊗ σ(x₁,z₁) ⊗ σ(x₂,z₂) ⊗ σ(x₃,z₃)` over `ℂ`,
with `σ(0,0) = I`, `σ(1,0) = X`, `σ(1,1) = Y`, `σ(0,1) = Z`.

* `pauliMat_mul`: `P(u) P(v) = i ^ phase u v • P(u ^^^ v)`.
* `context_product`: for every context `(a, b)` of a quadric `Q_w`,
  `P(a) P(b) P(a ^^^ b) = (-1) ^ [negB a b] • 1`, so `negB` is the sign of the context computed
  from the actual Pauli matrices.
-/

namespace Contextuality.Pauli

open Matrix Complex
open scoped Kronecker

/-- The single-qubit Pauli matrices. -/
def sigma : Bool → Bool → Matrix (Fin 2) (Fin 2) ℂ
  | false, false => 1
  | true, false => !![0, 1; 1, 0]
  | true, true => !![0, -I; I, 0]
  | false, true => !![1, 0; 0, -1]

lemma sigma_mul (x₁ z₁ x₂ z₂ : Bool) :
    sigma x₁ z₁ * sigma x₂ z₂ = I ^ phase1 x₁ z₁ x₂ z₂ • sigma (x₁ ^^ x₂) (z₁ ^^ z₂) := by
  cases x₁ <;> cases z₁ <;> cases x₂ <;> cases z₂ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [sigma, phase1, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- The four-qubit Pauli matrix of `v < 256`. -/
noncomputable def pauliMat (v : ℕ) :
    Matrix (((Fin 2 × Fin 2) × Fin 2) × Fin 2) (((Fin 2 × Fin 2) × Fin 2) × Fin 2) ℂ :=
  sigma (xbit v 0) (zbit v 0) ⊗ₖ sigma (xbit v 1) (zbit v 1) ⊗ₖ sigma (xbit v 2) (zbit v 2) ⊗ₖ
    sigma (xbit v 3) (zbit v 3)

lemma xbit_xor (u v i : ℕ) : xbit (u ^^^ v) i = (xbit u i ^^ xbit v i) := by
  simp [xbit, Nat.testBit_xor]

lemma zbit_xor (u v i : ℕ) : zbit (u ^^^ v) i = (zbit u i ^^ zbit v i) := by
  simp [zbit, Nat.testBit_xor]

lemma I_pow_mod (n : ℕ) : I ^ (n % 4) = I ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, I_pow_four, one_pow, one_mul]

/-- The phase rule: `P(u) P(v) = i ^ phase u v • P(u ^^^ v)`. -/
theorem pauliMat_mul (u v : ℕ) : pauliMat u * pauliMat v = I ^ phase u v • pauliMat (u ^^^ v) := by
  simp only [pauliMat, ← mul_kronecker_mul, sigma_mul, smul_kronecker, kronecker_smul, smul_smul,
    xbit_xor, zbit_xor, phase, I_pow_mod]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_add]
  congr 1
  ring

lemma sigma_mul_self (x z : Bool) : sigma x z * sigma x z = 1 := by
  rw [sigma_mul]; cases x <;> cases z <;> simp [phase1, sigma]

lemma pauliMat_mul_self (v : ℕ) : pauliMat v * pauliMat v = 1 := by
  simp only [pauliMat, ← mul_kronecker_mul, sigma_mul_self, one_kronecker_one]

/-- On every context the phase is `0` or `2` (the operators commute). -/
lemma phase_of_context : ∀ t ∈ contexts 0, phase t.1 t.2 = 0 ∨ phase t.1 t.2 = 2 := by
  have h : ((List.range 64).flatMap Q8Plus.cchunk).all
      (fun t => phase t.1 t.2 == 0 || phase t.1 t.2 == 2) = true := by
    decide +kernel
  intro t ht
  rw [Q8Plus.contexts_eq] at ht
  simpa using List.all_eq_true.1 h t ht

/-- The sign of a context of `Q⁺(7,2)` is the sign of the product of its three Pauli matrices. -/
theorem context_product {a b : ℕ} (h : (a, b) ∈ contexts 0) :
    pauliMat a * pauliMat b * pauliMat (a ^^^ b) = (if negB a b then -1 else 1 : ℂ) • 1 := by
  rw [pauliMat_mul, smul_mul_assoc, pauliMat_mul_self]
  rcases phase_of_context _ h with h0 | h2
  · simp only at h0; simp [negB, h0]
  · simp only at h2; simp [negB, h2, pow_two]

end Contextuality.Pauli
