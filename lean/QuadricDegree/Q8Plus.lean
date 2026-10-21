/-
Released under the MIT license (see LICENSE).
-/
import QuadricDegree.Q8PlusChecks

/-!
# The contextuality degree of the four-qubit hyperbolic quadric `Q⁺(7,2)` is `315`

The quadric `Q_0` (Pauli operators with an even number of `Y`s) has `135` points and `1575`
contexts (`contexts_length`). We prove that every assignment violates at least `315` of them and
that some assignment violates exactly `315`, so its contextuality degree is `315` (`degree_eq_315`).

## The lower bound

A double counting. The data file lists `numDoilies` doilies (subconfigurations isomorphic to the
generalised quadrangle `GQ(2,2)`), each as `15` context keys in the order of a fixed labelling of
`GQ(2,2)`. The kernel checks (in `QuadricDegree/Q8PlusChecks.lean`, chunk by chunk):

* `sortOK_all`, `bucketOK_all`: the keys of all doilies are a permutation of the contexts of the
  quadric, each repeated `mult` times (`keys_perm`). The merges only permute their input
  (`mergeTree_perm`), so nothing about the sorting is trusted. So every context lies in exactly
  `mult` of the doilies (counted with multiplicity), and every key in a doily is a context.
* `gridChk_all`: in every doily, each of the `10` grids of `GQ(2,2)` (`6` lines through `9`
  points, each point on two of them) is an odd set: the xor of the point masks of its `6` contexts
  is `0` and the sum of their signs is `1`. So every assignment violates a context of every grid
  (`exists_violated_of_odd`).
* each line of `GQ(2,2)` lies in exactly `4` grids (`sum_gridPos`).

So an assignment violates at least `⌈10 / 4⌉ = 3` contexts of every doily, and
`mult · numViolated x = Σ_doilies (violated contexts in the doily) ≥ 3 · numDoilies`,
which gives `numViolated x ≥ 3 · 2520 / 24 = 315`.

## The upper bound

`witness` violates exactly `315` contexts, by a kernel computation (`witness_check`).
-/

namespace Contextuality.Pauli.Q8Plus

lemma ofKey_keyOf {t : ℕ × ℕ} (h : t.2 < 256) : ofKey (keyOf t) = t := by
  obtain ⟨a, b⟩ := t
  simp only [ofKey, keyOf, Prod.mk.injEq]
  constructor <;> omega

/-- The doilies, as lists of `15` context keys. -/
def doilies : List (List ℕ) := (List.range numChunks).flatMap fun i => (dchunk i).map unpack

/-- Every context of the quadric, `mult` times each. -/
def contextKeys : List ℕ := (contexts 0).flatMap rep

/-! ### The kernel checks on the whole quadric -/

theorem numDoilies_eq : doilies.length = numDoilies := by decide +kernel

theorem contexts_length : (contexts 0).length = 1575 := by
  rw [contexts_eq]; decide +kernel

/-! ### The keys of the doilies are the contexts, each `mult` times -/

lemma flatMap_append_perm {α β : Type*} (C : List α) (g h : α → List β) :
    (C.flatMap fun c => g c ++ h c).Perm (C.flatMap g ++ C.flatMap h) := by
  classical
  rw [List.perm_iff_count]
  intro a
  induction C with
  | nil => simp
  | cons c C ih => simp only [List.flatMap_cons, List.count_append] at ih ⊢; omega

/-- Two `flatMap`s commute up to permutation. -/
lemma flatMap_comm_perm {α β γ : Type*} (I : List α) (C : List β)
    (f : α → β → List γ) :
    (I.flatMap fun i => C.flatMap (f i)).Perm (C.flatMap fun c => I.flatMap fun i => f i c) := by
  induction I with
  | nil => simp
  | cons i I ih =>
    simp only [List.flatMap_cons]
    exact (ih.append_left _).trans (flatMap_append_perm C (f i) _).symm

lemma flatten_flatMap {α β : Type*} (L : List α) (f : α → List (List β)) :
    (L.flatMap f).flatten = L.flatMap fun a => (f a).flatten := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.flatMap_cons, List.flatten_append, ih]

lemma mergeTree_singletons_perm (n : ℕ) (l : List ℕ) :
    (mergeTree n (l.map fun k => [k])).Perm l := by
  have := mergeTree_perm n (l.map fun k => [k])
  rwa [← List.flatMap_def, List.flatMap_singleton'] at this

/-- The keys of all doilies are a permutation of the contexts, each repeated `mult` times. -/
theorem keys_perm : doilies.flatten.Perm contextKeys := by
  have e1 : doilies.flatten = (List.range numChunks).flatMap chunkKeys := by
    rw [doilies, flatten_flatMap]; rfl
  have p1 : ((List.range numChunks).flatMap chunkKeys).Perm
      ((List.range numChunks).flatMap fun i => (List.range 64).flatMap (bucket i)) := by
    refine List.Perm.flatMap_left _ fun i hi => ?_
    have h := of_decide_eq_true (sortOK_all i hi)
    exact h ▸ (mergeTree_singletons_perm 11 (chunkKeys i)).symm
  have p2 :
      ((List.range 64).flatMap fun c => (List.range numChunks).flatMap fun i => bucket i c).Perm
      ((List.range 64).flatMap fun c => (cchunk c).flatMap rep) := by
    refine List.Perm.flatMap_left _ fun c hc => ?_
    have h := of_decide_eq_true (bucketOK_all c hc)
    have := mergeTree_perm 5 ((List.range numChunks).map fun i => bucket i c)
    rw [h, ← List.flatMap_def] at this
    exact this.symm
  have e3 : ((List.range 64).flatMap fun c => (cchunk c).flatMap rep) = contextKeys := by
    rw [contextKeys, contexts_eq, List.flatMap_assoc]
  rw [e1, ← e3]
  exact (p1.trans (flatMap_comm_perm _ _ _)).trans p2

/-- Each line of `GQ(2,2)` lies in exactly `4` of its `10` grids. -/
lemma sum_gridPos (g : ℕ → ℕ) :
    (gridPos.map fun G => (G.map g).sum).sum = 4 * ((List.range 15).map g).sum := by
  simp [gridPos, List.range_succ]
  ring

/-! ### The lower bound -/

/-- `1` for a violated context, `0` otherwise. -/
def viol (x : ℕ → ZMod 2) (t : ℕ × ℕ) : ℕ := if Violated x t then 1 else 0

lemma numViolated_eq_sum (x : ℕ → ZMod 2) :
    numViolated 0 x = ((contexts 0).map (viol x)).sum := by
  unfold numViolated
  induction contexts 0 with
  | nil => simp
  | cons t L ih =>
    by_cases h : Violated x t <;> simp [h, viol, ih]; omega

lemma length_le_sum {α : Type*} (k : ℕ) (L : List α) (f : α → ℕ) (h : ∀ a ∈ L, k ≤ f a) :
    k * L.length ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.mul_succ]
    have := h a (List.mem_cons_self ..)
    have := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    omega

/-- Every key of a doily is the key of a context. -/
lemma mem_contexts_of_mem {D : List ℕ} (hD : D ∈ doilies) {k : ℕ} (hk : k ∈ D) :
    ofKey k ∈ contexts 0 := by
  have h1 : k ∈ doilies.flatten := List.mem_flatten.2 ⟨D, hD, hk⟩
  have h2 : k ∈ contextKeys := keys_perm.subset h1
  simp only [contextKeys, rep, List.mem_flatMap, List.mem_replicate] at h2
  obtain ⟨t, ht, -, rfl⟩ := h2
  have hb : t.2 < 256 := (mem_contexts.1 ht).2.2.2.1.2.1
  rwa [ofKey_keyOf hb]

lemma bounds_of_mem {t : ℕ × ℕ} (ht : t ∈ contexts 0) :
    t.1 < 256 ∧ t.2 < 256 ∧ t.1 ^^^ t.2 < 256 := by
  have h := mem_contexts.1 ht
  exact ⟨h.2.2.1.2.1, h.2.2.2.1.2.1, h.2.2.2.2.1.2.1⟩

/-- Every assignment violates at least `3` contexts of every doily. -/
theorem three_le_doily (x : ℕ → ZMod 2) {D : List ℕ} (hD : D ∈ doilies) :
    3 ≤ (D.map fun k => viol x (ofKey k)).sum := by
  obtain ⟨i, hi, hD'⟩ := List.mem_flatMap.1 hD
  have hgrid := List.all_eq_true.1 (gridChk_all i hi) _ hD'
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hD'
  set g : ℕ → ℕ := fun j => viol x (ofKey ((unpack n).getD j 0)) with hg
  have hsum : ((unpack n).map fun k => viol x (ofKey k)).sum = ((List.range 15).map g).sum := by
    simp only [unpack, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    simp only [Function.comp, hg]
    rw [unpack, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (List.mem_range.1 hj)]
    rfl
  have hone : ∀ G ∈ gridPos, 1 ≤ (G.map g).sum := by
    intro G hG
    have hok := List.all_eq_true.1 (hgrid) G hG
    simp only [gridOK, Bool.and_eq_true, beq_iff_eq] at hok
    have hsign : ((G.map fun j => ofKey ((unpack n).getD j 0)).map
        fun t => negBit t.1 t.2).sum = 1 := by
      have := sum_map_b2 ((G.map fun j => ofKey ((unpack n).getD j 0)).map fun t => negB t.1 t.2)
      rw [hok.2, List.map_map] at this
      exact this
    have hS : ∀ t ∈ G.map (fun j => ofKey ((unpack n).getD j 0)),
        t.1 < 256 ∧ t.2 < 256 ∧ t.1 ^^^ t.2 < 256 := by
      intro t ht
      obtain ⟨j, hjG, rfl⟩ := List.mem_map.1 ht
      apply bounds_of_mem
      by_cases hj : j < (unpack n).length
      · exact mem_contexts_of_mem hD (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj)
      · have : (unpack n).length = 15 := by simp [unpack]
        rw [this] at hj
        have hG' : ∀ G ∈ gridPos, ∀ j ∈ G, j < 15 := by decide
        exact absurd (hG' G hG j hjG) hj
    obtain ⟨t, ht, hv⟩ := exists_violated_of_odd x _ hS hok.1 hsign
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
    have : g j = 1 := by rw [hg]; exact ite_eq_left_iff.2 fun h => absurd hv h
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := g) hj)
    omega
  have h10 := length_le_sum 1 gridPos (fun G => (G.map g).sum) hone
  rw [sum_gridPos] at h10
  have : gridPos.length = 10 := rfl
  omega

lemma sum_viol_flatMap_rep (x : ℕ → ZMod 2) (L : List (ℕ × ℕ)) (hL : ∀ t ∈ L, t.2 < 256) :
    ((L.flatMap rep).map fun k => viol x (ofKey k)).sum = mult * (L.map (viol x)).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append,
      ih fun t' ht' => hL t' (List.mem_cons_of_mem _ ht'), rep, List.map_replicate,
      List.sum_replicate, ofKey_keyOf (hL t (List.mem_cons_self ..)), smul_eq_mul,
      List.map_cons, List.sum_cons, Nat.mul_add]

/-- Every assignment violates at least `315` contexts of the quadric. -/
theorem le_numViolated (x : ℕ → ZMod 2) : 315 ≤ numViolated 0 x := by
  have hcount : (doilies.map fun D => (D.map fun k => viol x (ofKey k)).sum).sum =
      mult * numViolated 0 x := by
    have e1 : (doilies.map fun D => (D.map fun k => viol x (ofKey k)).sum).sum =
        (doilies.flatten.map fun k => viol x (ofKey k)).sum := by
      simp [List.map_flatten, List.sum_flatten, Function.comp_def]
    have e2 := (keys_perm.map fun k => viol x (ofKey k)).sum_eq
    rw [e1, e2, numViolated_eq_sum, contextKeys]
    exact sum_viol_flatMap_rep x _ fun t ht => (bounds_of_mem ht).2.1
  have hlow : 3 * doilies.length ≤
      (doilies.map fun D => (D.map fun k => viol x (ofKey k)).sum).sum := by
    exact length_le_sum 3 doilies _ fun D hD => three_le_doily x hD
  rw [hcount, numDoilies_eq] at hlow
  simp only [numDoilies, mult] at hlow
  omega

/-! ### The upper bound and the degree -/

/-- The witness assignment violates exactly `315` contexts. -/
theorem witness_check : numViolated 0 (fun p => b2 (witness.testBit p)) = 315 := by
  unfold numViolated
  rw [contexts_eq]
  decide +kernel

/-- **The contextuality degree of the four-qubit hyperbolic quadric `Q⁺(7,2)` is `315`.** -/
theorem degree_eq_315 : degree 0 = 315 :=
  degree_eq le_numViolated ⟨_, witness_check⟩

end Contextuality.Pauli.Q8Plus
