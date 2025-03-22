import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Linarith.Frontend

/-!
# Auxiliary results on permutations
-/

universe u

variable {X : Type u}

namespace CyclesOfPermutation

/-!
## Cycles of a permutation

The cycles of a permutation `f : X → X` are defined as the equivalence classes of `X` quotiented by the equivalence relation of being in
the same cycle: `x₁ ∼ x₂ ↔ ∃ k : ℤ, fᵏ x₁ = x₂`.

To avoid working with cardinalities of quotients, we introduce a lemma that enables us to work with cardinalities of finite sets instead.
For a permutation `f`, we can construct a set of representatives of its cycles, that is, a set that contains exactly one element of `X`
from every cycle of `f`. The number of cycles of `f` is equal to the cardinality of any such set of representatives of its cycles.
-/

/-- The number of cycles in the permutation `f`. Cycles with only a single element are also counted,
    e.g., `c[0, 1] : Equiv.Perm (Fin 3)` has two cycles. -/
abbrev numCyclesOfPerm (f : Equiv.Perm X) [Fintype (Quotient (Equiv.Perm.SameCycle.setoid f))] : ℕ :=
  Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid f))

/-- The number of cycles of a permutation `f : X → X` is equal to the cardinality of any set of representatives of its cycles. That is,
    any set that contains exactly one element of `X` from every cycle of `f`. -/
lemma numCyclesOfPerm_eq_card {f : Equiv.Perm X} [Fintype (Quotient (Equiv.Perm.SameCycle.setoid f))] {s : Finset X}
  (h1 : ∀ x ∈ s, ∀ y ∈ s, f.SameCycle x y → x = y) (h2 : ∀ x : X, ∃ y ∈ s, f.SameCycle x y) : numCyclesOfPerm f = s.card := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr ⟨
    Quotient.lift (fun x ↦ ⟨(h2 x).choose, (h2 x).choose_spec.1⟩) (by
      intro a b hab
      simp
      apply h1 _ (h2 a).choose_spec.1 _ (h2 b).choose_spec.1
      exact Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm (h2 a).choose_spec.2) hab)
        (h2 b).choose_spec.2),
    fun ⟨x, hx⟩ ↦ ⟦x⟧,
    by
      intro x
      rcases Quotient.mk_surjective x with ⟨y, rfl⟩
      apply Quotient.sound
      exact Equiv.Perm.SameCycle.symm (h2 y).choose_spec.2,
    by
      intro ⟨x, hx⟩
      simp
      exact h1 _ (h2 x).choose_spec.1 x hx (Equiv.Perm.SameCycle.symm (h2 x).choose_spec.2)⟩

end CyclesOfPermutation


namespace PowersOfPermutation

/-!
## Powers of a permutation

Repeatedly applying a permutation of a finite set on some element will eventually result in that same element. If `fⁿ⁺¹ x = x`, then for
any `k ∈ ℤ`, we have `fᵏ x = fᵐ x` for some `m ∈ {0, ..., n}`.
-/

/-- Given a permutation on a finite type `f : X → X` and any `x : X` there exists `n : ℕ` such that `fⁿ⁺¹ x = x`. -/
lemma exists_perm_pow [DecidableEq X] [Fintype X] (f : Equiv.Perm X) (x : X) : ∃ n, (f ^ (n + 1)) x = x := by
  by_cases hx : x ∈ f.support
  · use (f.cycleOf x).support.card - 1
    rw [Nat.sub_add_cancel (by simp [Equiv.Perm.mem_support.1 hx]), ← (f.isCycle_cycleOf (Equiv.Perm.mem_support.1 hx)).orderOf,
      ← f.cycleOf_pow_apply_self, pow_orderOf_eq_one, Equiv.Perm.one_apply]
  · exact ⟨0, Equiv.Perm.not_mem_support.1 hx⟩

/-- Given a permutation `f` satisfying `fⁿ x = x` we can reduce `fⁿ*ᵐ⁺ʳ x` to `fʳ x`. -/
lemma perm_pow_reduce {n m r : ℕ} {f : Equiv.Perm X} {x : X} (h : (f ^ n) x = x) : (f ^ (m * n + r)) x = (f ^ r) x := by
  induction' m with _ hinduction
  · simp
  · rw [add_mul, one_mul, add_assoc, add_comm n, ← add_assoc, pow_add]
    simp [h, hinduction]

/-- Given a permutation `f` satisfying `fⁿ⁺¹ x = x` for some `n : ℕ`, then for any `k : ℤ`, `fᵏ x = fᵐ x` for some `m ∈ {0, ..., n}`. -/
lemma forall_exists_lt_perm_pow_eq_perm_pow {n : ℕ} {f : Equiv.Perm X} {x : X} (h : (f ^ (n + 1)) x = x) :
  ∀ k : ℤ, ∃ m < n + 1, (f ^ k) x = (f ^ m) x := by
  rintro (k | k)
  · use k % (n + 1), Nat.mod_lt k (Nat.zero_lt_succ n)
    nth_rewrite 1 [← Nat.div_add_mod' k (n + 1)]
    exact perm_pow_reduce h
  · simp
    rw [← Nat.div_add_mod' (k + 1) (n + 1)]
    by_cases hcases : (k + 1) % (n + 1) = 0
    · use 0, Nat.zero_lt_succ n
      rw [hcases]
      exact perm_pow_reduce ((Equiv.symm_apply_eq (f ^ (n + 1))).2 h.symm)
    · use (n + 1) - (k + 1) % (n + 1)
      constructor
      · simp
        exact Nat.zero_lt_of_ne_zero hcases
      · show (f.symm ^ ((k + 1) / (n + 1) * (n + 1) + (k + 1) % (n + 1))) x = (f ^ (n + 1 - (k + 1) % (n + 1))) x
        rw [perm_pow_reduce (Equiv.Perm.inv_eq_iff_eq.2 h.symm)]
        show (f ^ ((k + 1) % (n + 1)))⁻¹ x = (f ^ (n + 1 - (k + 1) % (n + 1))) x
        apply Equiv.Perm.inv_eq_iff_eq.2
        show x = ((f ^ ((k + 1) % (n + 1))) * ((f ^ (n + 1 - (k + 1) % (n + 1))))) x
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_succ_le (Nat.mod_lt (k + 1) (Nat.zero_lt_succ n)))]
        exact h.symm

end PowersOfPermutation


namespace ContractExpand

/-!
## Contraction or expansion of a domain of a permutation

We can contract a permutation `f` on `Fin (n + 1)` by removing `n` from the domain and remapping `f⁻¹ n ↦ f n`. We get a permutation on
`Fin n`. We can expand a permutation `f` on `Fin n` by adding `n` to the domain and defining `f n = n`. We get a permutation on
`Fin (n + 1)`.
-/

variable {n : ℕ}

/-- If `n < m + 1` and `n ≠ m` then `n < m`. -/
lemma lt_of_lt_succ_of_neq {m : ℕ} (h1 : m < n + 1) (h2 : m ≠ n) : m < n := by
  by_contra hcontra
  exact h2 (Nat.eq_of_lt_succ_of_not_lt h1 hcontra)

/-- For any permutation `f` of `Fin (n + 1)`, if `f i = n` for some `i < n`, then `f (f i) < n`. -/
lemma perm_perm_val_lt_of_perm_val_eq {f : Equiv.Perm (Fin (n + 1))} {i : Fin n} (h : (f i).1 = n) : (f (f i)).1 < n := by
  by_contra hcontra
  apply Nat.eq_of_lt_succ_of_not_lt (f (f i)).2 at hcontra
  simp [← hcontra] at h
  apply Fin.eq_of_val_eq at h
  simp at h
  simp [← h] at hcontra
  linarith [i.2]

/-- A function that takes a permutation `f` of `Fin (n + 1)` and returns a permutation of `Fin n` that behaves exactly the same as `f` on
    all inputs except on `f⁻¹ n`, where it returns `f n`, and `n`, which is no longer a valid input. -/
def permContract (f : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin n) := by
  refine ⟨
    fun i ↦
      if h : (f i).1 = n
      then ⟨(f (f i)).1, perm_perm_val_lt_of_perm_val_eq h⟩
      else ⟨(f i).1, lt_of_lt_succ_of_neq (f i).2 h⟩,
    fun i ↦
      if h : (f⁻¹ i).1 = n
      then ⟨(f⁻¹ (f⁻¹ i)).1, @perm_perm_val_lt_of_perm_val_eq n f⁻¹ i h⟩
      else ⟨(f⁻¹ i).1, (by apply lt_of_lt_succ_of_neq (f⁻¹ i).2 h)⟩,
    ?_,
    ?_⟩
  repeat
    intro i
    simp
    split_ifs with h1 h2 h3
    · simp
    · simp [h1] at h2
    · simp at h3
      linarith [h3, i.2]
    · simp

/-- A function that takes a permutation `f` of `Fin n` and returns a permutation of `Fin (n + 1)` that behaves exactly the same as `f` on
    all inputs except on `n`, where it returns `n`. -/
def permExpand (f : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) := by
  refine ⟨
    fun i ↦
      if h : i.1 = n
      then n
      else f ⟨i.1, lt_of_lt_succ_of_neq i.2 h⟩,
    fun i ↦
      if h : i.1 = n
      then n
      else f⁻¹ ⟨i.1, lt_of_lt_succ_of_neq i.2 h⟩,
    ?_,
    ?_⟩
  repeat
    intro x
    simp
    split_ifs with h1 h2 h3
    · exact Fin.eq_of_val_eq h1.symm
    · simp at h2
    · simp at h3
      linarith [(f ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩).2, (f⁻¹ ⟨x.1, lt_of_lt_succ_of_neq x.2 h1⟩).2]
    · simp

end ContractExpand
