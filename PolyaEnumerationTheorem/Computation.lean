import PolyaEnumerationTheorem.PermutationAuxiliary
import PolyaEnumerationTheorem.ReductionToFin

/-!
# Computation of the number of distinct colorings

Evaluating the number of distinct colorings with the `#eval` command is generally slow. Here, we define a function
`computeNumDistinctColorings` for fast computation of the number of distinct colorings, along with a proof of its correctness:
`computeNumDistinctColorings_eq_numDistinctColorings`.

We prove some auxiliary results about arrays.

We define a function `visitCycle` that takes a permutation `f : Fin n → Fin n`, an element `x : Fin n`, and an array of length `n`. It
returns an identical array except that it is set to `true` at all indices belonging to the same cycle of the permutation `f` as `x`. It
first stores `x` as the `final` element, then repeatedly sets the array at index `x` to `true` and updates `x := f x` until `x` equals
`final`.

We define a function `computeNumCyclesOfPerm` that takes a permutation `f : Fin n → Fin n` and computes its number of cycles. It first
creates a boolean array of size `n` initialized to `false`, then iterates through values `n - 1, n - 2, ..., 0`. For each value, it checks
if the array is already set to `true` at its index. If so, it proceeds to the next value. Otherwise, it increments the number of cycles,
sets the array to `true` at all indices in the same cycle as the current value using `visitCycle`, and proceeds to the next value.

We define a function `computeNumDistinctColorings` for fast computation of the number of distinct colorings. It requires a bijection
`X → Fin n` to reduce the problem of computing the number of distinct colorings of `X` with colors in `Y` under the group action of `G` on
`X` to the problem of computing the number of distinct colorings of `Fin n` with colors in `Y` under the induced group action of `G` on
`Fin n`. It uses `computeNumCyclesOfPerm` to compute the number of cycles of elements in the group. The proof
`computeNumDistinctColorings_eq_numDistinctColorings` establishes its correctness using *Pólya’s enumeration theorem*.
-/

universe u v w

namespace ArrayAuxiliary

variable {X : Type u} [Inhabited X] {array : Array X}

/-- Setting an array at index `i` to a value `v` and then retrieving the value at index `i` results in `v`. -/
@[simp]
lemma setD_getElem!_eq (i : Fin array.size) (v : X) : (array.setD i.1 v)[i.1]! = v := by
  rw [Array.setD, dif_pos i.2, getElem!_pos, Array.getElem_set]
  repeat simp

/-- If an array has value `v` at index `i`, then after setting the value at some index to `v`, the value at index `i` remains `v`. -/
lemma setD_getElem!_eq_of_getElem!_eq (i : Fin array.size) {j : Fin array.size} {v : X} (h : array[j.1]! = v) :
  (array.setD i.1 v)[j.1]! = v := by
  by_cases hcases : i.1 = j.1
  · simp [hcases]
  · rw [Array.setD, dif_pos i.2, getElem!_pos, Array.getElem_set]
    · simp [← h, hcases, getElem!_pos]
    · simp

/-- If `i` and `j` are not in the same cycle of a permutation, then they are distinct, and setting the value at index `i` does not affect
    the value at index `j`. -/
lemma setD_getElem!_eq_of_not_SameCycle {i j : Fin array.size} (v : X) {f : Equiv.Perm (Fin array.size)} (h : ¬f.SameCycle i j) :
  (array.setD i.1 v)[j.1]! = array[j.1]! := by
  rw [Array.setD, dif_pos i.2, getElem!_pos, Array.getElem_set, if_neg, getElem!_pos]
  · by_contra hcontra
    apply h
    rw [← Fin.eq_of_val_eq hcontra]
  · simp

end ArrayAuxiliary


namespace ComputationNumberOfCycles

open ArrayAuxiliary PowersOfPermutation CyclesOfPermutation

variable {n i : ℕ}

/-- Auxiliary function for `visitCycle`.
    It sets the array `visited` to `true` at indices `{x, f x, f² x, ..., f⁻¹ final}`.
    To ensure termination, it requires a proof that iterating `f` on `x` eventually results in `final`.
    The proof `visitCycleAux_spec` establishes the correctness of this function. -/
def visitCycleAux {f : Equiv.Perm (Fin n)} {final x : Fin n} (visited : Array Bool) (htermination : ∃ m, (f ^ (m + 1)) x = final) :
  Array Bool :=
  let new_visited := visited.set! x true
  let next := f x
  if h : next = final
  then new_visited
  else visitCycleAux new_visited (by
    rcases htermination with ⟨m, hm⟩
    cases' m with m
    · contradiction
    · use m
      exact hm)
  termination_by
    Nat.find htermination
  decreasing_by
    simp
    intro m hm hm'
    cases' m with m
    · contradiction
    · exact (hm m (by simp)) hm'

/-- `visitCycleAux visited _` returns an array that is `true` at all indices where `visited` is `true`. -/
lemma visitCycleAux_get!_true_of_get!_true {visited : Array Bool} {f : Equiv.Perm (Fin visited.size)} {final x y : Fin visited.size}
  (hf : ∃ m, (f ^ (m + 1)) x = final) (hy : visited.get! y) : (visitCycleAux visited hf).get! y := by
  rcases hf with ⟨m, hm⟩
  simp at hy
  induction' m with _ hinduction generalizing x visited
  · simp at hm
    simp [visitCycleAux, hm]
    exact setD_getElem!_eq_of_getElem!_eq x hy
  · unfold visitCycleAux
    by_cases hcases : f x = final
    · simp [hcases]
      exact setD_getElem!_eq_of_getElem!_eq x hy
    · rw [dif_neg]
      apply (Array.size_setD _ _ _) ▸ @hinduction _
      · exact hm
      · exact setD_getElem!_eq_of_getElem!_eq x hy
      · exact hcases

/-- `visitCycleAux visited _` returns an array identical to `visited` at all indices not in the same cycle as `x`, and set to `true` at all
    indices in `{x, f x, f² x, ..., fⁱ x} = {x, f x, f² x, ..., f⁻¹ final}`. It has the same size as `visited`. -/
lemma visitCycleAux_spec {visited : Array Bool} {f : Equiv.Perm (Fin visited.size)} {final x : Fin visited.size}
  (hi : (f ^ (i + 1)) x = final) (hi' : ∀ l < i, (f ^ (l + 1)) x ≠ final) :
  (∀ l < i + 1, (visitCycleAux visited (by use i)).get! ((f ^ l) x))
  ∧
  (∀ y, ¬f.SameCycle final y → (visitCycleAux visited (by use i)).get! y = visited.get! y)
  ∧
  ((visitCycleAux visited (by use i)).size = visited.size) := by
  induction' i with i hinduction generalizing x visited
  repeat' unfold visitCycleAux
  · simp at hi
    simp [hi]
    intro y hy
    exact setD_getElem!_eq_of_not_SameCycle _ (by
      by_contra hcontra
      exact hy (Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm ⟨1, hi⟩) hcontra))
  · rcases ((Array.size_setD _ _ _) ▸ @hinduction (visited.set! x _)) hi (fun l hl ↦ hi' (l + 1) (Nat.add_lt_add_right hl 1))
      with ⟨h1, h2, h3⟩
    rw [dif_neg (by exact hi' 0 (by linarith))]
    constructor
    · intro l _
      cases' l with l
      · apply (Array.size_setD _ _ _) ▸ @visitCycleAux_get!_true_of_get!_true _
        simp
      · exact h1 l (by linarith)
    constructor
    · intro y hy
      rw [h2 y hy]
      simp
      exact setD_getElem!_eq_of_not_SameCycle _ (by
        by_contra hcontra
        exact hy (Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm (by use i + 1 + 1; exact hi)) hcontra))
    · exact h3

/-- A function that sets the array `visited` to `true` at indices in the same cycle of permutation `f` as `x`.
    The proof `visitCycle_spec` establishes its correctness. -/
def visitCycle (f : Equiv.Perm (Fin n)) (x : Fin n) (visited : Array Bool) : Array Bool :=
  visitCycleAux visited (exists_perm_pow f x)

/-- `visitCycle f x visited` returns an array identical to `visited`, except that it is set to `true` at all indices that belong to the
    same cycle of the permutation `f` as `x`. -/
lemma visitCycle_spec {visited : Array Bool} (f : Equiv.Perm (Fin visited.size)) (x : Fin visited.size) :
  (∀ y, f.SameCycle x y → (visitCycle f x visited).get! y)
  ∧
  (∀ y, ¬f.SameCycle x y → (visitCycle f x visited).get! y = visited.get! y)
  ∧
  ((visitCycle f x visited).size = visited.size) := by
  let htermination := exists_perm_pow f x
  rcases visitCycleAux_spec (Nat.find_spec htermination) (fun k hk ↦ @Nat.find_min _ _ htermination k hk) with ⟨h1, h2, h3⟩
  constructor
  · rintro _ ⟨k, rfl⟩
    rcases forall_exists_lt_perm_pow_eq_perm_pow (Nat.find_spec htermination) k with ⟨l, hl, hl'⟩
    rw [hl']
    exact h1 l hl
  · use h2, h3

/-- Auxiliary function for `computeNumCyclesOfPerm`.
    Returns `count` incremented by the number of cycles of `f` that contain a value in `{m ∈ {0, ..., i - 1} | visited[m] = false}`.
    The proof `computeNumCyclesOfPermAux_exists_representatives` establishes its correctness. -/
def computeNumCyclesOfPermAux {i : ℕ} (f : Equiv.Perm (Fin n)) (visited : Array Bool) (count : ℕ) (hi : i ≤ n) : ℕ :=
  match i with
  | 0 => count
  | m + 1 =>
      if visited.get! m
      then computeNumCyclesOfPermAux f visited count (Nat.le_of_succ_le hi)
      else computeNumCyclesOfPermAux f (visitCycle f ⟨m, hi⟩ visited) (count + 1) (Nat.le_of_succ_le hi)

/-- `computeNumCyclesOfPermAux` takes a permutation `f`, an array `visited` that is set to `true` at indices in the same cycle of `f` as
    some element in `{i, ..., n - 1}`, and a number `count` representing the cardinality of some set of representatives of those cycles of
    `f` containing some element in `{i, ..., n - 1}`. It computes the cardinality of some set of representatives of cycles of `f`. -/
lemma computeNumCyclesOfPermAux_exists_representatives {visited : Array Bool} {f : Equiv.Perm (Fin visited.size)} (count : ℕ)
  (hi : i ≤ visited.size) (h1 : ∀ x : Fin visited.size, x ≥ i → ∀ y : Fin visited.size, f.SameCycle x y → visited.get! y.1)
  (h2 : ∀ x : Fin visited.size, visited.get! x.1 → ∃ y : Fin visited.size, y ≥ i ∧ f.SameCycle x y)
  (h3 :
    ∃ s : Finset (Fin visited.size),
      (∀ x ∈ s, x ≥ i)
      ∧
      (∀ x ∈ s, ∀ y ∈ s, f.SameCycle x y → x = y)
      ∧
      (∀ x : Fin visited.size, x ≥ i → ∃ y ∈ s, f.SameCycle x y)
      ∧
      (count = s.card)) :
  (∃ s : Finset (Fin visited.size),
    (∀ x ∈ s, ∀ y ∈ s, f.SameCycle x y → x = y)
    ∧
    (∀ x : Fin visited.size, ∃ y ∈ s, f.SameCycle x y)
    ∧
    (computeNumCyclesOfPermAux f visited count hi = s.card)) := by
  induction' i with i hinduction generalizing visited count
  · simp at h3
    exact h3
  · unfold computeNumCyclesOfPermAux
    by_cases h : visited.get! i = true
    · rw [if_pos h]
      apply hinduction
      · intro x hx y hxy
        by_cases hcases : i = x.1
        · rcases h2 x (by rw [← hcases] ; exact h) with ⟨z, hz, hz'⟩
          exact h1 z hz y (Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm hz') hxy)
        · exact h1 x (Nat.lt_of_le_of_ne hx hcases) y hxy
      · intro x hx
        rcases h2 x hx with ⟨y, _, hxy⟩
        use y
        constructor
        · linarith
        · exact hxy
      · rcases h3 with ⟨s, hs1, hs2, hs3, hs4⟩
        use s, fun x hx ↦ Nat.le_of_succ_le (hs1 x hx), hs2
        constructor
        · intro x hx
          by_cases hcases : i = x.1
          · rw [hcases] at h
            rcases h2 x h with ⟨y, hy, hy'⟩
            rcases hs3 y hy with ⟨z, hz, hz'⟩
            use z, hz
            exact Equiv.Perm.SameCycle.trans hy' hz'
          · exact hs3 x (Nat.lt_of_le_of_ne hx hcases)
        · exact hs4
    · rw [if_neg h]
      rcases visitCycle_spec f ⟨i, (by linarith)⟩ with ⟨hv1, hv2, hv3⟩
      apply hv3 ▸ @hinduction _
      · intro x hx y hxy
        by_cases hcases : i = x.1
        · apply hv1
          simp [hcases]
          exact hxy
        · by_cases hcases' : f.SameCycle ⟨i, hi⟩ y
          · apply hv1
            exact hcases'
          · rw [← h1 x (Nat.lt_of_le_of_ne hx hcases) y hxy]
            apply hv2
            exact hcases'
      · intro x hx
        by_cases hcases : f.SameCycle ⟨i, hi⟩ x
        · use ⟨i, hi⟩
          simp
          exact Equiv.Perm.SameCycle.symm hcases
        · rw [hv2 x hcases] at hx
          rcases h2 x hx with ⟨y, _, hy'⟩
          use y
          constructor
          · linarith
          · exact hy'
      · rcases h3 with ⟨s, hs1, hs2, hs3, hs4⟩
        use s ∪ {⟨i, hi⟩}
        simp
        constructor
        · rintro x (hx | hx)
          · linarith [hs1 x hx]
          · rw [Fin.val_eq_of_eq hx]
        constructor
        · rintro x (hx | hx) y (hy | hy) hxy
          · exact hs2 x hx y hy hxy
          · specialize h1 x (hs1 x hx) y hxy
            rw [hy] at h1
            contradiction
          · specialize h1 y (hs1 y hy) x (Equiv.Perm.SameCycle.symm hxy)
            rw [hx] at h1
            contradiction
          · rw [hx, hy]
        constructor
        · intro x hx
          by_cases hcases : i = x.1
          · use x
            simp [hcases]
            rfl
          · rcases hs3 x (Nat.lt_of_le_of_ne hx hcases) with ⟨y, hy, hy'⟩
            use y
            constructor
            · left
              exact hy
            · exact hy'
        · rw [hs4, Finset.card_union_of_disjoint]
          · rfl
          · simp
            by_contra hcontra
            linarith [hs1 ⟨i, hi⟩ hcontra]

/-- Computes the number of cycles of a permutation `f : Fin n → Fin n`.
    The proof `computeNumCyclesOfPerm_eq_numCyclesOfPerm` establishes its correctness. -/
def computeNumCyclesOfPerm (f : Equiv.Perm (Fin n)) : ℕ :=
  computeNumCyclesOfPermAux f (Array.mkArray n false) 0 (Nat.le_refl n)

/-- `computeNumCyclesOfPerm f` computes the cardinality of some set of representatives of cycles of `f`, which is a set containing exactly
    one element from each cycle of `f`. -/
lemma computeNumCyclesOfPerm_exists_representatives (f : Equiv.Perm (Fin n)) :
  ∃ s : Finset (Fin n),
    (∀ x ∈ s, ∀ y ∈ s, f.SameCycle x y → x = y)
    ∧
    (∀ (x : Fin n), ∃ y ∈ s, f.SameCycle x y)
    ∧
    (computeNumCyclesOfPerm f = s.card) :=
  ((Array.size_mkArray n _) ▸ @computeNumCyclesOfPermAux_exists_representatives n _) 0 _ (by simp) (by
    intro x hx
    simp [Array.get!, Array.getD] at hx) (by
    use ∅
    simp)

/-- `computeNumCyclesOfPerm f` computes the number of cycles of the permutation `f`. -/
lemma computeNumCyclesOfPerm_eq_numCyclesOfPerm (f : Equiv.Perm (Fin n)) : computeNumCyclesOfPerm f = numCyclesOfPerm f := by
  rcases computeNumCyclesOfPerm_exists_representatives f with ⟨_, h1, h2, h3⟩
  rw [h3]
  symm
  exact numCyclesOfPerm_eq_card h1 h2

end ComputationNumberOfCycles


namespace ComputationNumberOfDistinctColorings

open ComputationNumberOfCycles DistinctColorings

variable (X : Type u) (Y : Type v) (G : Type w) [Group G] [MulAction G X] [Fintype Y] [Fintype G] [enum : FinEnum X]

/-- Computes the number of distinct colorings of `X` with colors in `Y` under the group action of `G` on `X`.
    The proof `computeNumDistinctColorings_eq_numDistinctColorings` establishes its correctness. -/
def computeNumDistinctColorings : ℕ :=
  (∑ g : G, (Fintype.card Y) ^ (computeNumCyclesOfPerm (@MulAction.toPerm _ (Fin enum.card) _ _ g))) / (Fintype.card G)

/-- `computeNumDistinctColorings X Y G` computes the number of distinct colorings of `X` with colors in `Y` under the group action of `G`
    on `X`. -/
@[simp]
lemma computeNumDistinctColorings_eq_numDistinctColorings [Fintype (Quotient (MulAction.orbitRel G (X → Y)))]
  [(g : G) → Fintype (MulAction.fixedBy (Fin (FinEnum.card X) → Y) g)] :
  computeNumDistinctColorings X Y G = numDistinctColorings X Y G := by
    rw [computeNumDistinctColorings, ReductionToFin.numDistinctColorings_eq_numDistinctColorings_of_Fin,
      Theorem.numDistinctColorings_eq_sum_card_pow_numCyclesOfGroup_div_card_group] -- Pólya's enumeration theorem
    congr
    ext g
    congr
    exact computeNumCyclesOfPerm_eq_numCyclesOfPerm (MulAction.toPerm g)

end ComputationNumberOfDistinctColorings
