/-
Released under the MIT license (see LICENSE).
-/
import QuadricDegree.Basic

/-!
# Odd sets of contexts, and a merge that the kernel can run

* An *odd set* of contexts is a list of contexts in which every point occurs an even number of
  times and whose signs add up to `1`. Every assignment violates one of its contexts
  (`exists_violated_of_odd`): the sum over the list of `x a + x b + x (a + b)` is `0`, the sum of
  the signs is `1`. Evenness is checked through point masks: the context `(a, b)` has the mask
  `2^a ^^^ 2^b ^^^ 2^(a ^^^ b)`, and every point occurs an even number of times iff the xor of the
  masks is `0`.
* `mergeF`: a structurally recursive merge of lists of naturals. Whatever its input, its output is
  a permutation of the concatenation of its inputs (`mergeF_perm`), so it can be used to compare
  multisets by a kernel computation without trusting that the inputs are sorted.
-/

namespace Contextuality.Pauli

open Finset

/-- The point mask of a context. -/
def lmask (t : ℕ × ℕ) : ℕ := 2 ^ t.1 ^^^ 2 ^ t.2 ^^^ 2 ^ (t.1 ^^^ t.2)

/-- The xor of the masks of a list of contexts. -/
def xmask (S : List (ℕ × ℕ)) : ℕ := (S.map lmask).foldr (· ^^^ ·) 0

/-- The sum of the values of `x` on the points of the mask `m` (below `256`). -/
def evalMask (x : ℕ → ZMod 2) (m : ℕ) : ZMod 2 :=
  ∑ p ∈ range 256, if m.testBit p then x p else 0

lemma ite_xor_zmod2 (a b : Bool) (v : ZMod 2) :
    (if (a ^^ b) = true then v else 0) =
      (if a = true then v else 0) + (if b = true then v else 0) := by
  have h : v + v = 0 := by fin_cases v <;> decide
  cases a <;> cases b <;> simp [h]

lemma evalMask_xor (x : ℕ → ZMod 2) (m m' : ℕ) :
    evalMask x (m ^^^ m') = evalMask x m + evalMask x m' := by
  simp only [evalMask, ← sum_add_distrib, Nat.testBit_xor, ite_xor_zmod2]

lemma evalMask_zero (x : ℕ → ZMod 2) : evalMask x 0 = 0 := by simp [evalMask]

lemma evalMask_pow (x : ℕ → ZMod 2) {a : ℕ} (ha : a < 256) : evalMask x (2 ^ a) = x a := by
  simp only [evalMask, Nat.testBit_two_pow]
  rw [sum_eq_single a]
  · simp
  · intro p _ hp; simp [Ne.symm hp]
  · intro h; exact absurd (mem_range.2 ha) h

lemma evalMask_lmask (x : ℕ → ZMod 2) {t : ℕ × ℕ} (h1 : t.1 < 256) (h2 : t.2 < 256)
    (h3 : t.1 ^^^ t.2 < 256) : evalMask x (lmask t) = x t.1 + x t.2 + x (t.1 ^^^ t.2) := by
  simp only [lmask, evalMask_xor, evalMask_pow x h1, evalMask_pow x h2, evalMask_pow x h3]

lemma b2_xor (a b : Bool) : b2 (a ^^ b) = b2 a + b2 b := by
  cases a <;> cases b <;> decide

lemma sum_map_b2 (l : List Bool) : (l.map b2).sum = b2 (parity l) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [parity, ih, b2_xor]

/-- Every assignment violates some context of an odd set. -/
theorem exists_violated_of_odd (x : ℕ → ZMod 2) (S : List (ℕ × ℕ))
    (hS : ∀ t ∈ S, t.1 < 256 ∧ t.2 < 256 ∧ t.1 ^^^ t.2 < 256)
    (hmask : xmask S = 0) (hsign : (S.map fun t => negBit t.1 t.2).sum = 1) :
    ∃ t ∈ S, Violated x t := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have key : ∀ S' : List (ℕ × ℕ), (∀ t ∈ S', t.1 < 256 ∧ t.2 < 256 ∧ t.1 ^^^ t.2 < 256) →
      (∀ t ∈ S', ¬ Violated x t) →
      evalMask x (xmask S') = (S'.map fun t => negBit t.1 t.2).sum := by
    intro S' hb hv
    induction S' with
    | nil => simp [xmask, evalMask_zero]
    | cons t S' ih =>
      have hb' := hb t (List.mem_cons_self ..)
      have hvt := hv t (List.mem_cons_self ..)
      simp only [Violated, not_not] at hvt
      have ih' := ih (fun t' ht' => hb t' (List.mem_cons_of_mem _ ht'))
        (fun t' ht' => hv t' (List.mem_cons_of_mem _ ht'))
      simp only [xmask, List.map_cons, List.foldr_cons, List.sum_cons] at ih' ⊢
      rw [evalMask_xor, evalMask_lmask x hb'.1 hb'.2.1 hb'.2.2, hvt, ih']
  have := key S hS hno
  rw [hmask, evalMask_zero, hsign] at this
  exact absurd this (by decide)

/-! ### A merge for the kernel -/

/-- Merge two lists (sorted, for the result to be sorted), with fuel. -/
def mergeF : ℕ → List ℕ → List ℕ → List ℕ
  | 0, l₁, l₂ => l₁ ++ l₂
  | _ + 1, [], l₂ => l₂
  | _ + 1, a :: l₁, [] => a :: l₁
  | n + 1, a :: l₁, b :: l₂ =>
    if a ≤ b then a :: mergeF n l₁ (b :: l₂) else b :: mergeF n (a :: l₁) l₂

lemma mergeF_perm : ∀ (n : ℕ) (l₁ l₂ : List ℕ), (mergeF n l₁ l₂).Perm (l₁ ++ l₂)
  | 0, l₁, l₂ => by simp [mergeF]
  | _ + 1, [], l₂ => by simp [mergeF]
  | _ + 1, a :: l₁, [] => by simp [mergeF]
  | n + 1, a :: l₁, b :: l₂ => by
    unfold mergeF
    split_ifs
    · exact (mergeF_perm n l₁ (b :: l₂)).cons a
    · refine ((mergeF_perm n (a :: l₁) l₂).cons b).trans ?_
      simpa using (List.perm_middle (a := b) (l₁ := a :: l₁) (l₂ := l₂)).symm

/-- Merge the lists of a family two by two. -/
def mergePairs : List (List ℕ) → List (List ℕ)
  | l₁ :: l₂ :: L => mergeF (l₁.length + l₂.length) l₁ l₂ :: mergePairs L
  | L => L

lemma mergePairs_perm : ∀ L : List (List ℕ), (mergePairs L).flatten.Perm L.flatten
  | [] => by simp [mergePairs]
  | [l] => by simp [mergePairs]
  | l₁ :: l₂ :: L => by
    simp only [mergePairs, List.flatten_cons, ← List.append_assoc]
    exact (mergeF_perm _ _ _).append (mergePairs_perm L)

/-- Merge a family of lists by `n` rounds of pairwise merging, then concatenate. -/
def mergeTree : ℕ → List (List ℕ) → List ℕ
  | 0, L => L.flatten
  | n + 1, L => mergeTree n (mergePairs L)

lemma mergeTree_perm : ∀ (n : ℕ) (L : List (List ℕ)), (mergeTree n L).Perm L.flatten
  | 0, L => by simp [mergeTree]
  | n + 1, L => (mergeTree_perm n (mergePairs L)).trans (mergePairs_perm L)

/-- Sort each list of a family (by insertion) and merge them all in `n` rounds. -/
def sortMerge (n : ℕ) (L : List (List ℕ)) : List ℕ :=
  mergeTree n (L.map fun D => D.insertionSort (· ≤ ·))

lemma sortMerge_perm (n : ℕ) (L : List (List ℕ)) : (sortMerge n L).Perm L.flatten := by
  refine (mergeTree_perm n _).trans ?_
  induction L with
  | nil => simp
  | cons D L ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact (List.perm_insertionSort _ D).append ih

end Contextuality.Pauli
