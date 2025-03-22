import PolyaEnumerationTheorem.Concrete

/-!
## Sum of Stirling numbers of the first kind

Using *Pólya's enumeration theorem*, we prove a formula for the sum of the Stirling numbers of the first kind multiplied by powers of a
natural number.

For additional information, refer to <https://en.wikipedia.org/wiki/Stirling_numbers_of_the_first_kind>.
-/

namespace StirlingFirstKindSum

open CyclesOfGroupElements PermutationGroup

/-- The Stirling number of the first kind `stirlingFirstKind n i` represents the number of permutations of `Fin n` with exactly `i` cycles. -/
abbrev stirlingFirstKind (n i : ℕ) : ℕ :=
  numGroupOfNumCycles (Fin n) (Equiv.Perm (Fin n)) i

/-- Formula for the sum of Stirling numbers of the first kind multiplied by powers of a positive natural number.
    The sum of `(stirlingFirstKind n i) * (m + 1)ⁱ` over `i ∈ {0, ..., n}` is equal to `((n + m).choose m) * n!`. -/
lemma sum_stirlingFirstKind_mul_pow_eq_choose_mul_factorial {n m : ℕ} :
  ∑ i : Fin (n + 1), (stirlingFirstKind n i.1) * (m + 1) ^ i.1 = ((n + m).choose m) * (n.factorial) := by
  suffices ∑ i : Fin (Fintype.card (Fin n) + 1), (stirlingFirstKind n i.1) * (Fintype.card (Fin (m + 1))) ^ i.1 =
    ((n + m).choose m) * n.factorial by
    rw [← this, Fintype.card_fin, Fintype.card_fin]
  rw [← Theorem.numDistinctColorings_mul_card_group_eq_sum_numGroupOfNumCycles_mul_card_pow, -- Pólya's enumeration theorem
    ← numDistinctColoringsOfPerm, numDistinctColoringsOfPerm_eq_numWeakCompositions, numWeakCompositions]
  simp [Fintype.card_perm]

/-- The sum of `(stirlingFirstKind (n + 1) i) * 0ⁱ` over `i ∈ {0, ..., n + 1}` equals `0`. -/
lemma sum_stirlingFirstKind_of_succ_mul_zero_pow_eq_zero {n : ℕ} :
  ∑ i : Fin (n + 1 + 1), (stirlingFirstKind (n + 1) i.1) * 0 ^ i.1 = 0 := by
  simp
  intro x
  cases x.1
  · left
    simp
  · right
    simp

/-- The sum of `(stirlingFirstKind 0 i) * 0ⁱ` over `i ∈ {0}` equals `1`. -/
lemma sum_stirlingFirstKind_of_zero_mul_zero_pow_eq_one :
  ∑ i : Fin 1, (stirlingFirstKind 0 i.1) * 0 ^ i.1 = 1 := by
  rfl

end StirlingFirstKindSum
