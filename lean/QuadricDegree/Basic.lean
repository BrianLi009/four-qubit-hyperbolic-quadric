/-
Released under the MIT license (see LICENSE).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Four-qubit Pauli geometry: points, symplectic form, quadrics, contexts and their signs

A non-identity four-qubit Pauli operator, up to sign, is a nonzero vector `(x | z)` of `𝔽₂⁸`. We
encode it as a natural number `v < 256` whose bit `i` is `xᵢ` and whose bit `i + 4` is `zᵢ`
(`i < 4`): on qubit `i` the operator is `I, X, Z, Y` for `(xᵢ, zᵢ) = (0,0), (1,0), (0,1), (1,1)`.
Addition of vectors is `^^^` (bitwise xor).

* `symp u v`: the symplectic form `Σᵢ xᵢ(u) zᵢ(v) + zᵢ(u) xᵢ(v)` (a bit, `true = 1`); the
  operators commute iff it is `0`.
* `quadForm w v`: the quadratic form `Q_w(v) = #Y(v) + ⟨w, v⟩ (mod 2)` (a bit) whose polarisation is
  `symp`. `Q_0` is the hyperbolic quadric `Q⁺(7,2)` of `135` points.
* `phase u v`: the exponent `k mod 4` in the Pauli multiplication rule
  `P(u) P(v) = iᵏ P(u + v)` for the Hermitian representatives `P(v) = ⊗ᵢ σ(xᵢ, zᵢ)`; it is the sum
  over the qubits of the single-qubit exponents (`XY = iZ`, `YZ = iX`, `ZX = iY` and the reverse
  products with `-i`). The file `QuadricDegree/PhaseMatrix.lean` proves this rule for the actual Pauli
  matrices.
* A *context* (line) of the quadric is a triple `{a, b, a + b}` of pairwise commuting points of
  the quadric. We list each one once, as `(a, b)` with `a < b < a ^^^ b`.
* `negBit a b`: the sign of the context, `1` when `P(a) P(b) P(a + b) = -I` and `0` when it is
  `+I`, read off from the phase rule (`P(a) P(b) P(a+b) = i^{phase a b} P(a+b)² = i^{phase a b} I`).
* `numViolated x`: for an assignment `x` of values in `ZMod 2` to the points (`x p = 1` stands for
  the outcome `-1`), the number of contexts `(a, b)` with `x a + x b + x (a + b) ≠ negBit a b`.
-/

namespace Contextuality.Pauli

/-- The `x`-bit of qubit `i`. -/
def xbit (v i : ℕ) : Bool := v.testBit i

/-- The `z`-bit of qubit `i`. -/
def zbit (v i : ℕ) : Bool := v.testBit (i + 4)

/-- A bit as an element of `ZMod 2`. -/
def b2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The parity of a list of bits (their sum in `𝔽₂`, with `true = 1`). -/
def parity (l : List Bool) : Bool := l.foldr (· ^^ ·) false

/-- The symplectic form `Σᵢ xᵢ(u) zᵢ(v) + zᵢ(u) xᵢ(v)` on `𝔽₂⁸` (`true = 1`); two Pauli operators
commute iff it vanishes. -/
def symp (u v : ℕ) : Bool :=
  parity ((List.range 4).map fun i => (xbit u i && zbit v i) ^^ (zbit u i && xbit v i))

/-- The quadratic form `Q_w(v) = (number of Y's in v) + ⟨w, v⟩` on `𝔽₂⁸` (`true = 1`). -/
def quadForm (w v : ℕ) : Bool :=
  parity ((List.range 4).map fun i => xbit v i && zbit v i) ^^ symp w v

/-- Single-qubit phase rule: `σ(x₁,z₁) σ(x₂,z₂) = i ^ phase1 x₁ z₁ x₂ z₂ • σ(x₁+x₂, z₁+z₂)` with
`σ(1,0) = X`, `σ(1,1) = Y`, `σ(0,1) = Z`. -/
def phase1 : Bool → Bool → Bool → Bool → ℕ
  | true, false, true, true => 1   -- X Y = i Z
  | true, false, false, true => 3  -- X Z = -i Y
  | true, true, true, false => 3   -- Y X = -i Z
  | true, true, false, true => 1   -- Y Z = i X
  | false, true, true, false => 1  -- Z X = i Y
  | false, true, true, true => 3   -- Z Y = -i X
  | _, _, _, _ => 0

/-- Four-qubit phase rule: `P(u) P(v) = i ^ phase u v • P(u ^^^ v)`. -/
def phase (u v : ℕ) : ℕ :=
  ((List.range 4).map fun i => phase1 (xbit u i) (zbit u i) (xbit v i) (zbit v i)).sum % 4

/-- The sign of the context `{a, b, a ^^^ b}`: `true` iff `P(a) P(b) P(a ^^^ b) = -I`. -/
def negB (a b : ℕ) : Bool := phase a b == 2

/-- The sign bit of the context `{a, b, a ^^^ b}` in `ZMod 2`: `1` iff
`P(a) P(b) P(a ^^^ b) = -I`. -/
def negBit (a b : ℕ) : ZMod 2 := b2 (negB a b)

/-- The points of the quadric `Q_w`: nonzero vectors of `𝔽₂⁸` on which `Q_w` vanishes. -/
def IsQuadricPoint (w v : ℕ) : Prop := 0 < v ∧ v < 256 ∧ quadForm w v = false

instance (w v : ℕ) : Decidable (IsQuadricPoint w v) := by unfold IsQuadricPoint; infer_instance

/-- `(a, b)` is a context of the quadric `Q_w`, listed in its normal form `a < b < a ^^^ b`:
`a`, `b`, `a ^^^ b` are points of the quadric and `a`, `b` commute. -/
def IsContext (w : ℕ) (t : ℕ × ℕ) : Prop :=
  t.1 < t.2 ∧ t.2 < t.1 ^^^ t.2 ∧ IsQuadricPoint w t.1 ∧ IsQuadricPoint w t.2 ∧
    IsQuadricPoint w (t.1 ^^^ t.2) ∧ symp t.1 t.2 = false

instance (w : ℕ) (t : ℕ × ℕ) : Decidable (IsContext w t) := by unfold IsContext; infer_instance

/-- All contexts of the quadric `Q_w`, each once, in lexicographic order. -/
def contexts (w : ℕ) : List (ℕ × ℕ) :=
  (List.range 256).flatMap fun a => ((List.range 256).map fun b => (a, b)).filter (IsContext w ·)

lemma mem_contexts {w : ℕ} {t : ℕ × ℕ} : t ∈ contexts w ↔ IsContext w t := by
  obtain ⟨a, b⟩ := t
  simp only [contexts, List.mem_flatMap, List.mem_range, List.mem_filter, List.mem_map,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a', -, ⟨b', -, h⟩, hc⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hc
  · intro h
    have ha : a < 256 := h.2.2.1.2.1
    have hb : b < 256 := h.2.2.2.1.2.1
    exact ⟨a, ha, ⟨b, hb, rfl⟩, h⟩

/-- The contexts violated by an assignment `x` (with values in `ZMod 2`, `1` meaning `-1`). -/
def Violated (x : ℕ → ZMod 2) (t : ℕ × ℕ) : Prop :=
  x t.1 + x t.2 + x (t.1 ^^^ t.2) ≠ negBit t.1 t.2

instance (x : ℕ → ZMod 2) (t : ℕ × ℕ) : Decidable (Violated x t) := by
  unfold Violated; infer_instance

/-- The number of contexts of `Q_w` violated by the assignment `x`. -/
def numViolated (w : ℕ) (x : ℕ → ZMod 2) : ℕ := ((contexts w).filter (Violated x ·)).length

/-- The contextuality degree of the quadric `Q_w`: the least number of contexts violated by an
assignment of `±1` values (elements of `ZMod 2`) to the points. Assignments are given on all of
`ℕ`; the values off the points of the quadric play no role. -/
noncomputable def degree (w : ℕ) : ℕ := sInf (Set.range (numViolated w))

/-- To show `degree w = d` it suffices to give a lower bound for all assignments and a witness. -/
lemma degree_eq {w d : ℕ} (hlow : ∀ x, d ≤ numViolated w x) (hwit : ∃ x, numViolated w x = d) :
    degree w = d := by
  obtain ⟨x, hx⟩ := hwit
  apply le_antisymm
  · exact hx ▸ Nat.sInf_le ⟨x, rfl⟩
  · exact le_csInf ⟨_, ⟨x, rfl⟩⟩ (by rintro _ ⟨y, rfl⟩; exact hlow y)

end Contextuality.Pauli
