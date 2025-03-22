import PolyaEnumerationTheorem.Basic
import Mathlib.Data.FinEnum

/-!
# Reduction to `Fin`

If we have a bijection `X → Fin n`, then the number of distinct colorings of `X` with colors in `Y` under the group action of `G` on `X`
is equal to the number of distinct colorings of `Fin n` with colors in `Y` under the induced group action of `G` on `Fin n`. This allows
us to use `Fin n` instead of more complex types when working with numbers of distinct colorings.
-/

universe u v w

namespace ReductionToFin

open DistinctColorings

variable (X : Type u) (Y : Type v) (G : Type w) [enum : FinEnum X]

/-- Given a bijection `enum.equiv : X → Fin enum.card` and a group action of `G` on `X`, construct a group action of `G` on `Fin enum.card`
    with `g • i ↦ enum.equiv (g • (enum.equiv⁻¹ i))`. -/
instance MulActionFin [Monoid G] [MulAction G X] : MulAction G (Fin (enum.card)) where
  smul := fun g i ↦ enum.equiv.1 (g • (enum.equiv.2 i))
  one_smul := by
    intro b
    show enum.equiv.1 ((1 : G) • (enum.equiv.2 b)) = b
    rw [one_smul]
    simp
  mul_smul := by
    intro x y b
    simp [HSMul.hSMul]
    show (@HMul.hMul G G G (@instHMul G MulOneClass.toMul) x y) • (enum.equiv.2 b) = x • (y • (enum.equiv.2 b))
    rw [mul_smul]

variable [Group G] [MulAction G X]

/-- A bijection between the distinct colorings of `X` with colors in `Y` under the group action of `G` on `X` and the distinct colorings of
    `Fin enum.card` with colors in `Y` under the induced group action of `G` on `Fin enum.card`. -/
def equiv_of_quotient_of_quotient_Fin :
  (Quotient (MulAction.orbitRel G (X → Y))) ≃ (Quotient (MulAction.orbitRel G (Fin enum.card → Y))) := by
  refine ⟨
    Quotient.map (fun f => f ∘ enum.equiv.2) (by
      rintro _ _ ⟨g, rfl⟩
      use g
      ext
      simp [HSMul.hSMul]
      congr
      symm
      apply (Equiv.apply_eq_iff_eq_symm_apply enum.equiv).1
      rfl),
    Quotient.map (fun f => f ∘ enum.equiv.1) (by
      rintro _ _ ⟨g, rfl⟩
      use g
      ext
      simp [HSMul.hSMul]
      congr
      apply (Equiv.apply_eq_iff_eq_symm_apply enum.equiv).2
      simp [SMul.smul]
      rfl),
    ?_,
    ?_⟩
  repeat
    intro x
    rcases Quotient.mk_surjective x with ⟨y, rfl⟩
    simp
    apply Quotient.eq''.1
    congr
    ext
    simp

/-- An instance of `Fintype` for the distinct colorings of `Fin enum.card` with colors in `Y` under the induced group action of `G` on
    `Fin enum.card`. Required by `numDistinctColorings_eq_numDistinctColorings_of_Fin`. -/
instance [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] : Fintype (Quotient (MulAction.orbitRel G (Fin enum.card → Y))) :=
  Fintype.ofEquiv (Quotient (MulAction.orbitRel G (X → Y))) (equiv_of_quotient_of_quotient_Fin X Y G)

/-- The number of distinct colorings of `X` with colors in `Y` under the group action of `G` on `X` is equal to the number of distinct
    colorings of `Fin enum.card` with colors in `Y` under the induced group action of `G` on `Fin enum.card`. -/
lemma numDistinctColorings_eq_numDistinctColorings_of_Fin [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] :
  numDistinctColorings X Y G = numDistinctColorings (Fin (enum.card)) Y G :=
  Fintype.card_congr (equiv_of_quotient_of_quotient_Fin X Y G)

end ReductionToFin
