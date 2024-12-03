import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Pólya's enumeration theorem

We interpret functions `X → Y` as colorings of `X` with colors in `Y`. The element `x : X` is colored with color `(f x) : Y` in the
coloring `f : X → Y`.

We interpret `g : G` as a transformation that permutes the elements of `X` into an equivalent configuration. If we color the
elements of `X` with `f : X → Y` and then permute `X` with `g : G`, we obtain an equivalent configuration which now has the coloring
`x ↦ (f (g⁻¹ • x))`. Note that `g⁻¹` appears in the definition of the new coloring because the color of the element `x` in the new
permuted configuration must match the color of its preimage `g⁻¹ • x` in the original configuration. Thus for any `g : G`, we consider
the colorings `f` and `x ↦ (f (g⁻¹ • x))` to be equivalent.

Given a group action of `G` on `X`, we define an instance of group action of `G` on `X → Y`, which transforms colorings into equivalent
colorings. This group action induces an equivalence relation defined by `f₁ ∼ f₂ ↔ ∃ g, f₁ = g • f₂`. Two colorings are equivalent when
one can be transformed into the other with some element of `G`. The quotient of `X → Y` by this relation contains the orbits (equivalence
classes) of equivalent colorings. The number of distinct colorings is the cardinality of this set.

We define a notion of cycles for elements of group `G` acting on `X`. Every `g : G` induces a permutation of `X` through its action.
The cycles of `g : G` are defined as the equivalence classes of `X` quotiented by the equivalence relation of being in the same cycle:
`x₁ ∼ x₂ ↔ ∃ k : ℤ, (permutation of g)ᵏ x₁ = x₂`.

We prove *Pólya's enumeration theorem*.
-/

universe u v w

namespace DistinctColorings

/-  `X` is a type of objects
    `Y` is a type of colors
    `G` is a group acting on `X`. Group action is denoted by `_ • _ : G → X → X`. -/
variable (X : Type u) (Y : Type v) (G : Type w) [Group G] [MulAction G X]

/-- Group action of `G` on `X → Y` with `g • f ↦ (x ↦ f (g⁻¹ • x))`. -/
instance MulActionColorings : MulAction G (X → Y) where
  smul := fun g f x ↦ f (g⁻¹ • x)
  one_smul := by
    intro f
    ext x
    simp [HSMul.hSMul]
    show f ((1 : G) • x) = f x
    rw [one_smul G x]
  mul_smul := by
    intro g g' f
    ext x
    simp [HSMul.hSMul]
    show f ((g'⁻¹ * g⁻¹) • x) = f (g'⁻¹ • (g⁻¹ • x))
    rw [mul_smul g'⁻¹ g⁻¹ x]

/-- Proof that the relation defined by `f₁ ∼ f₂ ↔ ∃ g, f₁ = g • f₂` is decidable. This instance enables inference of
    `Fintype (Quotient (MulAction.orbitRel G (X → Y)))` and guarantees that the number of distinct colorings can be computed when `X`, `Y`
    and `G` are finite and `X` and `Y` have decidable equalities. -/
instance [Fintype X] [DecidableEq Y] [Fintype G] :
  DecidableRel (@HasEquiv.Equiv (X → Y) (@instHasEquivOfSetoid (X → Y) (MulAction.orbitRel G (X → Y)))) :=
  fun f₁ f₂ =>
    if h : ∃ g, g • f₂ = f₁ then -- Can be decided because G, X are finite and Y has decidable equality.
      isTrue h
    else
      isFalse h
-- variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype G]
-- #check (inferInstance : Fintype (Quotient (MulAction.orbitRel G (X → Y))))   -- Can infer `Fintype`.

/-- Number of distinct colorings is the cardinality of the quotient of `X → Y` by the equivalence relation `f₁ ∼ f₂ ↔ ∃ g, f₁ = g • f₂`. -/
abbrev numDistinctColorings [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] : ℕ :=
  Fintype.card (Quotient (MulAction.orbitRel G (X → Y)))

end DistinctColorings


namespace CyclesOfGroupElements

variable (X : Type u) {G : Type v} [Group G] [MulAction G X] (g : G)

/-- Takes `X` and `g : G` and returns the permutation `x ↦ g • x`. This function is a group homomorphism. -/
abbrev toPerm : Equiv.Perm X :=
  @MulAction.toPerm _ X _ _ g

/-- The cycles of `g : G` are defined as the quotient of `X` by the equivalence relation of being in the same cycle of `g`:
    `x₁ ∼ x₂ ↔ ∃ k : ℤ, (permutation of g)ᵏ x₁ = x₂`. Cycles are unordered, and cycles of length 1 are also considered proper cycles.
    This definition of cycles differs from the standard definition of cycles in Mathlib, because cycles of length 1 are recognized as
    proper cycles. -/
abbrev CyclesOfGroup : Type u :=
  Quotient (Equiv.Perm.SameCycle.setoid (toPerm X g))
/- To see the difference add `import Mathlib.GroupTheory.Perm.Cycle.Concrete` to imports and check examples: -/
-- #eval (Equiv.Perm.cycleFactorsFinset c[0, 1] : Finset (Equiv.Perm (Fin 3))) -- c[2] is not included in factorization
-- example : Equiv.Perm.IsCycle c[2] = False := by simp

/-- Instance of `DecidableRel` for relation of being in the same cycle. Enables deciding for arbitrary elements of `X` and arbitrary
    permutation of `X` if the elements are in the same cycle of the permutation. This instance enables inference of `Fintype` and
    `DecidableEq` for `CyclesOfGroup` when `X` is finite and has decidable equality. -/
instance [Fintype X] [DecidableEq X] :
  DecidableRel (@HasEquiv.Equiv X (@instHasEquivOfSetoid X (Equiv.Perm.SameCycle.setoid (MulAction.toPerm g)))) :=
  Equiv.Perm.instDecidableRelSameCycleOfFintypeOfDecidableEq (MulAction.toPerm g)
-- variable [Fintype X] [DecidableEq X]
-- #check (inferInstance : Fintype (CyclesOfGroup X g))      -- Can infer `Fintype`.
-- #check (inferInstance : DecidableEq (CyclesOfGroup X g))  -- Can infer `DecidableEq`.

/-- Returns the number of cycles in the permutation of `g`. Cycles with only a single element are also counted
    (e.g. `c[0, 1] : Equiv.Perm (Fin 3)` has two cycles). -/
abbrev numCyclesOfGroup [Fintype (CyclesOfGroup X g)] : ℕ :=
  Fintype.card (CyclesOfGroup X g)
/- You can add `import Mathlib.GroupTheory.Perm.Cycle.Concrete` to imports and observe the example: -/
-- #eval numCyclesOfGroup (Fin 3) (c[0, 1] : Equiv.Perm (Fin 3)) -- Group of permutations of `{0, 1, 2}` act on `{0, 1, 2}`. Has two cycles.

end CyclesOfGroupElements


namespace Theorem

open DistinctColorings
open CyclesOfGroupElements

variable {X : Type u} {Y : Type v} {G : Type w} [Group G] [MulAction G X]

/-!
The proof of *Pólya's enumeration theorem* uses the set of fixed points of `g`, denoted by `MulAction.fixedBy (X → Y) g`.
This set consists of all colorings `f : X → Y` that are invariant under the action of `g`, i.e., those satisfying `g • f = f`.
-/

/-- For any `g : G` we have:
    a coloring `f` is in fixed points of `g` if and only if `f` maps all elements in the same cycle of `g` to the same color.
    Only left to right implication of this lemma is used in the proof of *Pólya's enumeration theorem*. -/
lemma f_mem_fixedBy_iff_forall_eq_to_eq (g : G) (f : X → Y) :
  f ∈ (MulAction.fixedBy (X → Y) g) ↔ ∀ a b, (⟦a⟧ : Quotient (Equiv.Perm.SameCycle.setoid (MulAction.toPerm g))) = ⟦b⟧ → f a = f b :=
  calc
    f ∈ MulAction.fixedBy (X → Y) g ↔ ∀ x, (g • f) x = f x := funext_iff
    _ ↔ ∀ x, f (g⁻¹ • x) = f x := by simp [HSMul.hSMul]
    _ ↔ ∀ (k : ℤ) x, f (((MulAction.toPerm g) ^ k) x) = f x := by
      constructor
      · intro h k x
        induction' k with n n
        · induction' n with n hn
          · rfl
          · specialize h ((MulAction.toPerm g ^ (n + 1 : ℤ)) x)
            nth_rewrite 1 [add_comm, zpow_add] at h
            simp at h ⊢
            rw [← h]
            exact hn
        · induction' n with n hn
          · exact h x
          · specialize h ((MulAction.toPerm g⁻¹ ^ (n + 1)) x)
            simp
            rw [pow_add]
            show f (g⁻¹ • (MulAction.toPerm g⁻¹ ^ (n + 1)) x) = f x
            rw [h]
            exact hn
      · intro h
        exact h (-1)
    _ ↔ ∀ a b, ⟦a⟧ = ⟦b⟧ → f a = f b := by
      constructor
      · intro h a b hab
        simp at hab
        rcases hab with ⟨k, hk⟩
        rw [← h k a, hk]
      · intro h k x
        apply h
        simp [Equiv.Perm.SameCycle.setoid]
        exact Equiv.Perm.SameCycle.refl (MulAction.toPerm g) x

/-- A function that maps a coloring from fixed points of `g` to a coloring of cycles. Colorings that are fixed by `g` map all elements
    of a cycle of `g` to the same color by lemma `f_mem_fixedBy_iff_forall_eq_to_eq`. We can transform each such coloring to a coloring
    of cycles of `g` by coloring each cycle with the color of its elements. -/
def cycle_coloring_of_fixedBy_coloring (g : G) (f : MulAction.fixedBy (X → Y) g) : (CyclesOfGroup X g) → Y :=
  Quotient.lift f (by
    intro a b hab
    exact (f_mem_fixedBy_iff_forall_eq_to_eq g f.1).1 f.2 a b (Quotient.sound hab))

/-- A function that maps a coloring of cycles to a coloring in fixed points of `g`. We color each element with the color of its cycle.
    The resulting function is in fixed points of `g` because `g⁻¹ • x` and `x` are in the same cycle of `g`. -/
def fixedBy_coloring_of_cycle_coloring (g : G) (f : (CyclesOfGroup X g) → Y) : MulAction.fixedBy (X → Y) g :=
  ⟨fun x ↦ f ⟦x⟧,
  by
    ext x
    simp [HSMul.hSMul]
    apply congrArg
    apply Quotient.sound
    simp [instHasEquivOfSetoid, Equiv.Perm.SameCycle.setoid]
    use 1
    show g • g⁻¹ • x = x
    simp⟩

/-- Functions `cycle_coloring_of_fixedBy_coloring` and `fixedBy_coloring_of_cycle_coloring` are inverses and form a bijection. -/
def equiv_of_fixedBy_coloring_of_cycle_coloring (g : G) : Equiv (CyclesOfGroup X g → Y) (MulAction.fixedBy (X → Y) g) :=
  ⟨fixedBy_coloring_of_cycle_coloring g, cycle_coloring_of_fixedBy_coloring g,
  by
    intro f
    ext x
    rcases Quotient.mk_surjective x with ⟨y, hy⟩
    rw [← hy]
    rfl,
  by
    intro f
    rfl⟩

/-- For any `g : G` we have:
    the number of colors raised to the power of the number of cycles of `g` is equal to the number of colorings that are fixed by `g`.
    To use this lemma it suffices to have: [Group G] [MulAction G X] [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]. -/
lemma forall_card_pow_numCyclesOfGroup_eq_card_fixedBy [Fintype Y] [∀ g : G, Fintype (MulAction.fixedBy (X → Y) g)]
  [∀ g : G, Fintype (CyclesOfGroup X g)] [∀ g : G, DecidableEq (CyclesOfGroup X g)] :
  ∀ g : G, Fintype.card Y ^ (numCyclesOfGroup X g) = Fintype.card (MulAction.fixedBy (X → Y) g) := by
  intro g
  unfold numCyclesOfGroup
  rw [← @Fintype.card_fun]
  apply Fintype.card_congr
  exact equiv_of_fixedBy_coloring_of_cycle_coloring g

/-- *Pólya's enumeration theorem*
    Gives a formula for the number of distinct colorings of X with colors in Y under the group action of G on X.
    To use this theorem it suffices to have: [Group G] [MulAction G X] [Fintype X] [Fintype Y] [Fintype G] [DecidableEq X] [DecidableEq Y]. -/
theorem numDistinctColorings_eq_sum_card_pow_numCyclesOfGroup_div_mul_card_group
  [Fintype Y] [Fintype G] [∀ g : G, Fintype (CyclesOfGroup X g)] [Fintype (Quotient (MulAction.orbitRel G (X → Y)))] [∀ g : G, Fintype (MulAction.fixedBy (X → Y) g)] [∀ g : G, Fintype (CyclesOfGroup X g)] [∀ g : G, DecidableEq (CyclesOfGroup X g)] :
  numDistinctColorings X Y G = (∑ g : G, (Fintype.card Y) ^ (numCyclesOfGroup X g)) / (Fintype.card G) := by
  apply Nat.eq_div_of_mul_eq_left
  · exact Fintype.card_ne_zero
  · rw [numDistinctColorings, Fintype.sum_congr _ _ forall_card_pow_numCyclesOfGroup_eq_card_fixedBy]
    symm
    exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (X → Y) -- Burnside's lemma

end Theorem
