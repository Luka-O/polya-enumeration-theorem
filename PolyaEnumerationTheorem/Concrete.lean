import PolyaEnumerationTheorem.Computation
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Numbers of distinct colorings for some concrete examples
-/

open DistinctColorings ComputationNumberOfDistinctColorings

universe u v w

namespace TrivialGroup

/-!
## Trivial group
-/

/-- When using the trivial group, every coloring is equivalent only to itself. The number of distinct colorings is equal to the number of
    functions. `⊥ : Subgroup (X ≃ X)` denotes the trivial subgroup of `X ≃ X`. -/
lemma numDistinctColoringsOfTrivialGroup (X : Type u) (Y : Type v) [Fintype X] [Fintype Y] [DecidableEq X]
  [Fintype (Quotient (MulAction.orbitRel (⊥ : Subgroup (X ≃ X)) (X → Y)))] :
  numDistinctColorings X Y (⊥ : Subgroup (X ≃ X)) = (Fintype.card Y) ^ (Fintype.card X) := by
  rw [← Fintype.card_fun]
  exact Fintype.card_congr ⟨
    Quotient.lift id (by
      intro _ _ h
      rcases h with ⟨g, rfl⟩
      rw [Subsingleton.eq_one g]
      rfl),
    fun a ↦ ⟦a⟧,
    by
      intro f
      rcases Quotient.mk_surjective f with ⟨g, rfl⟩
      apply Quotient.sound
      exact @Setoid.refl _ (MulAction.orbitRel _ _) g,
    by
      intro
      rfl⟩

end TrivialGroup


namespace Necklaces

/-!
## Necklaces

We interpret the elements of `Fin n` as `n` beads of a necklace, where `x` is connected to `x + 1` and `x - 1`, computed modulo `n`.
Necklaces can be rotated, but not reflected. We use the additive group `Fin n` with multiplicative notation, because our definitions
require a group with multiplicative notation. Elements of `Multiplicative (Fin n)` are rotations of the necklace, where `i : Fin n`
rotates the necklace by `2πi/n`. We define that there is a single coloring of a necklace with `0` beads. This is defined separately
because `Multiplicative (Fin 0)` is not a group.
-/

/-- Number of distinct colorings of a necklace with `n` beads and `m` colors. -/
def numDistinctColoringsOfNecklace : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => numDistinctColorings (Fin (n + 1)) (Fin m) (Multiplicative (Fin (n + 1)))
-- #eval ((Multiplicative.ofAdd (3 : (Fin 5))) * (Multiplicative.ofAdd (2 : (Fin 5)))) -- Equivalent to `3 + 2` in `ℤ₅`.
-- #check (inferInstance : Group (Multiplicative (Fin 0))) -- Not a group.

/-- Computes the number of distinct colorings of a necklace with `n` beads and `m` colors. -/
abbrev computeNumDistinctColoringsOfNecklace : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => computeNumDistinctColorings (Fin (n + 1)) (Fin m) (Multiplicative (Fin (n + 1)))

/-- `computeNumDistinctColoringsOfNecklace` computes the number of distinct colorings of a necklace with `n` beads and `m` colors. -/
lemma computeNumDistinctColoringsOfNecklace_eq_numDistinctColoringsOfNecklace (n m : ℕ) :
  computeNumDistinctColoringsOfNecklace n m = numDistinctColoringsOfNecklace n m := by
  unfold computeNumDistinctColoringsOfNecklace
  congr
  simp

end Necklaces


namespace Bracelets

open DihedralGroup

/-!
## Bracelets

We interpret the elements of `ZMod n` as `n` beads of a bracelet, where `x` is connected to `x + 1` and `x - 1`, computed modulo `n`.
Bracelets can be rotated and reflected. We use the `DihedralGroup n`, which contains elements `r i` that rotate the bracelet by `2πi/n`
and `sr i` that rotate the bracelet by `2πi/n` and then reflect it. We define that there is a single coloring of a bracelet with `0` beads.
This is defined separately because `ZMod 0` is `ℤ` by definition.
-/

/-- Action of the dihedral group on `ZMod n`. Elements of `ZMod n` are interpreted as beads of a bracelet. The dihedral group contains
    elements `r i` that rotate the bracelet by `2πi/n`, and elements `sr i` that rotate the bracelet by `2πi/n` and then reflect it. -/
instance MulActionBracelet (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := fun d x ↦ match d with
                    | r i  => x + i
                    | sr i => n - 1 - (x + i)
  one_smul := by
    intro
    simp [instHSMul, one_def]
  mul_smul := by
    unfold instHSMul
    rintro (_ | _) (_ | _) _
    repeat
      simp
      ring

/-- Finite enumeration of `ZMod (n + 1)`. `ZMod 0` is `ℤ` by definition and cannot be finitely enumerated. -/
instance (n : ℕ) : FinEnum (ZMod (n + 1)) where
  card := n + 1
  equiv := (1 : Equiv.Perm (ZMod (n + 1)))

/-- Number of distinct colorings of a bracelet with `n` beads and `m` colors. -/
def numDistinctColoringsOfBracelet : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => numDistinctColorings (ZMod (n + 1)) (Fin m) (DihedralGroup (n + 1))

/-- Computes the number of distinct colorings of a bracelet with `n` beads and `m` colors. -/
abbrev computeNumDistinctColoringsOfBracelet : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, m => computeNumDistinctColorings (ZMod (n + 1)) (Fin m) (DihedralGroup (n + 1))

/-- `computeNumDistinctColoringsOfBracelet` computes the number of distinct colorings of a bracelet with `n` beads and `m` colors. -/
lemma computeNumDistinctColoringsOfBracelet_eq_numDistinctColoringsOfBracelet (n m : ℕ) :
  computeNumDistinctColoringsOfBracelet n m = numDistinctColoringsOfBracelet n m := by
  unfold computeNumDistinctColoringsOfBracelet
  congr
  simp

end Bracelets


namespace Cube

/-!
## Cube

We interpret the elements of `Fin 6` as `6` faces of the cube, where:
- `0` is the face at the front,
- `1` is the face at the right,
- `2` is the face at the back,
- `3` is the face at the left,
- `4` is the face at the top,
- `5` is the face at the bottom.

There are `24` rotational symmetries of the cube.
-/

/-- The rotation of the cube by `π/2` around the axis through the centers of the top and bottom faces. The front face moves to the
    position of the right face. -/
def r := (c[0, 1, 2, 3] : Equiv.Perm (Fin 6))

/-- The rotation of the cube by `π/2` around the axis through the centers of the front and back faces. The right face moves to the
    position of the top face. -/
def s := (c[1, 4, 3, 5] : Equiv.Perm (Fin 6))

/-- The finite set of rotational symmetries of the cube. First, we rotate the cube using `s` at most three times to set the position of
    `1`. Then, we move `0` to the position of any other face by rotating the cube appropriately. To move `0` to one of the faces in
    `{0, 1, 2, 3}`, we use `r` the appropriate number of times. To move `0` to `4` or `5`, we first use `r` once to move `0` to `1`, then
    use `s` once or three times. Since we can move `0` to any position and `1` to any position adjacent to the new position of `0`
    (by using `s` the appropriate number of times in the beginning), we have `6 * 4 = 24` different rotational symmetries. Since we can
    infer the new positions of all faces based only on the new positions of `0` and `1`, we have obtained all rotational symmetries of the
    cube. -/
def rotationalSymmetriesOfCube : Finset (Equiv.Perm (Fin 6)) :=
  Finset.univ.image (fun (⟨i, j⟩ : Fin 4 × Fin 4) ↦ r ^ i.1 * s ^ j.1)
  ∪
  Finset.univ.image (fun (⟨i, j⟩ : Fin 2 × Fin 4) ↦ s ^ (2 * i.1 + 1) * r * s ^ j.1)

/-- The order of `s` is `4`. -/
lemma s_pow_four : s ^ 4 = 1 := by decide

/-- The inverse of `r` is `r³`. -/
lemma r_inv : r⁻¹ = r ^ 3 := by decide

/-- The inverse of `s` is `s³`. -/
lemma s_inv : s⁻¹ = s ^ 3 := by decide

/-- If `g` has order `n`, then we can reduce its powers modulo `n`. When its power corresponds to a sum of elements from `Fin n`, it can
    be rewritten as the sum of their values. -/
lemma pow_add_val_eq_of_pow_eq_one {n : ℕ} {G : Type u} [Monoid G] {g : G} (hg : g ^ n = 1) (i j : Fin n) :
  g ^ (i + j).1 = g ^ (i.1 + j.1) := by
  by_cases hcases : i.1 + j.1 < n
  · congr
    rw [Fin.val_add, Nat.mod_eq, if_neg]
    simp [hcases]
  · rw [(Nat.sub_eq_iff_eq_add (Nat.le_of_not_lt hcases)).1 rfl, pow_add, hg, mul_one]
    congr
    rw [Fin.val_add, Nat.mod_eq, if_pos ⟨Fin.pos i, Nat.le_of_not_lt hcases⟩, Nat.mod_eq, if_neg]
    simp
    intro
    exact Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hcases) (Nat.add_lt_add i.2 j.2)

/-- Multiplying `r` by an element of `rotationalSymmetriesOfCube` results in an element that is in `rotationalSymmetriesOfCube`. -/
lemma r_mul_mem_rotationalSymmetriesOfCube (x : Equiv.Perm (Fin 6)) (hx : x ∈ rotationalSymmetriesOfCube) :
  r * x ∈ rotationalSymmetriesOfCube := by
  simp [rotationalSymmetriesOfCube] at hx ⊢
  rcases hx with (⟨xi, xj, rfl⟩ | ⟨⟨xi, _⟩, xj, rfl⟩)
  · left
    use xi + 1, xj
    simp [@pow_add_val_eq_of_pow_eq_one 4 _ _ r (by decide)]
    group
  · right
    interval_cases xi
    · use 0, 1 + xj
      simp [pow_add_val_eq_of_pow_eq_one s_pow_four, pow_add, ← mul_assoc]
      decide
    · use 1, 3 + xj
      simp [pow_add_val_eq_of_pow_eq_one s_pow_four, pow_add, ← mul_assoc]
      decide

/-- Multiplying `s` by an element of `rotationalSymmetriesOfCube` results in an element that is in `rotationalSymmetriesOfCube`. -/
lemma s_mul_mem_rotationalSymmetriesOfCube (x : Equiv.Perm (Fin 6)) (hx : x ∈ rotationalSymmetriesOfCube) :
  s * x ∈ rotationalSymmetriesOfCube := by
  simp [rotationalSymmetriesOfCube] at hx ⊢
  rcases hx with (⟨⟨xi, _⟩, xj, rfl⟩ | ⟨⟨xi, _⟩, xj, rfl⟩)
  · interval_cases xi
    · left
      use 0, 1 + xj
      simp [pow_add_val_eq_of_pow_eq_one s_pow_four, pow_add]
    · right
      use 0, xj
      simp [mul_assoc]
    · left
      use 2, 3 + xj
      simp [pow_add_val_eq_of_pow_eq_one s_pow_four, pow_add, ← mul_assoc]
      decide
    · right
      use 1, 2 + xj
      simp [pow_add_val_eq_of_pow_eq_one s_pow_four, pow_add, ← mul_assoc]
      decide
  · interval_cases xi
    · left
      use 3, 2 + xj
      simp [pow_add_val_eq_of_pow_eq_one s_pow_four, pow_add, ← mul_assoc]
      decide
    · left
      use 1, xj
      simp [← mul_assoc]
      decide

/-- Multiplying `sⁿ * rᵐ * sᵏ` by an element of `rotationalSymmetriesOfCube` results in an element that is in `rotationalSymmetriesOfCube`. -/
lemma s_pow_r_pow_s_pow_mul_mem_rotationalSymmetriesOfCube (n m k : ℕ) (x : Equiv.Perm (Fin 6)) (hx : x ∈ rotationalSymmetriesOfCube) :
  s ^ n * r ^ m * s ^ k * x ∈ rotationalSymmetriesOfCube := by
  induction' k with _ hk generalizing x
  · induction' m with _ hm generalizing x
    · induction' n with _ hn generalizing x
      · exact hx
      · simp [pow_add, mul_assoc] at hn ⊢
        apply hn
        exact s_mul_mem_rotationalSymmetriesOfCube x hx
    · simp [pow_add, mul_assoc] at hm ⊢
      apply hm
      exact r_mul_mem_rotationalSymmetriesOfCube x hx
  · simp [pow_add, mul_assoc] at hk ⊢
    apply hk
    exact s_mul_mem_rotationalSymmetriesOfCube x hx

/-- The finite set of rotational symmetries of the cube is a subgroup of the group of permutations of the cube's faces. -/
instance RotationalSymmetriesOfCubeSubgroup : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := rotationalSymmetriesOfCube
  mul_mem' := by
    intro _ b ha hb
    simp [rotationalSymmetriesOfCube] at ha
    rcases ha with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩)
    · exact s_pow_r_pow_s_pow_mul_mem_rotationalSymmetriesOfCube 0 _ _ b hb
    · exact s_pow_r_pow_s_pow_mul_mem_rotationalSymmetriesOfCube _ 1 _ b hb
  one_mem' := by
    left
  inv_mem' := by
    intro _ ha
    simp [rotationalSymmetriesOfCube] at ha
    rcases ha with (⟨ai, aj, rfl⟩ | ⟨ai, aj, rfl⟩)
    · simp [← inv_pow, r_inv, s_inv, ← pow_mul]
      exact s_pow_r_pow_s_pow_mul_mem_rotationalSymmetriesOfCube _ _ 0 1 (by left)
    · simp [← inv_pow, r_inv, s_inv, ← pow_mul]
      rw [← mul_assoc, ← mul_one (s ^ (3 * aj.1) * r ^ 3 * s ^ (3 * (2 * ai.1 + 1)))]
      exact s_pow_r_pow_s_pow_mul_mem_rotationalSymmetriesOfCube _ 3 _ 1 (by left)

/-- The predicate defined by `a ∈ RotationalSymmetriesOfCubeSubgroup` is decidable. This instance enables inference of
    `Fintype RotationalSymmetriesOfCubeSubgroup` and guarantees that the number of distinct colorings can be computed. -/
instance : DecidablePred (Membership.mem RotationalSymmetriesOfCubeSubgroup) :=
  fun p ↦
    if h : p ∈ rotationalSymmetriesOfCube
    then isTrue h
    else isFalse h
-- #check (inferInstance : Fintype (RotationalSymmetriesOfCubeSubgroup)) -- Can infer `Fintype`.

/-- Number of distinct colorings of the faces of a cube with `n` colors. -/
abbrev numDistinctColoringsOfCube (n : ℕ) : ℕ :=
  numDistinctColorings (Fin 6) (Fin n) RotationalSymmetriesOfCubeSubgroup

/-- Computes the number of distinct colorings of the faces of a cube with `n` colors. -/
abbrev computeNumDistinctColoringsOfCube (n : ℕ) : ℕ :=
  computeNumDistinctColorings (Fin 6) (Fin n) RotationalSymmetriesOfCubeSubgroup

/-- `computeNumDistinctColoringsOfCube` computes the number of distinct colorings of the faces of a cube with `n` colors. -/
lemma computeNumDistinctColoringsOfCube_eq_numDistinctColoringsOfCube (n : ℕ) :
  computeNumDistinctColoringsOfCube n = numDistinctColoringsOfCube n :=
  computeNumDistinctColorings_eq_numDistinctColorings _ _ _

end Cube


namespace PermutationGroup

open ContractExpand

/-!
## Permutation group

We interpret the elements of `Fin n` as `n` unordered, indistinguishable objects. We use the group `Equiv.Perm (Fin n)`, which contains
all permutations of `Fin n`. Its elements permute our objects. Since we can permute the objects in any way and still obtain an equivalent
configuration, two colorings are equivalent if and only if they assign the same number of objects to each color. Consequently, the number
of distinct colorings of `n` unordered, indistinguishable objects with `m` colors is equal to the number of ways to separate `n` objects
into `m` ordered sets (the number of weak compositions of `n` into `m` parts), which is equal to `(n + m - 1).choose (m - 1)` when
`m > 0`. There is exactly one coloring of `0` objects with `0` colors, and no valid colorings of more than `0` objects with `0` colors.
-/

/-- The number of distinct colorings of `n` unordered, indistinguishable objects with `m` colors. -/
abbrev numDistinctColoringsOfPerm (n m : ℕ) : ℕ :=
  numDistinctColorings (Fin n) (Fin m) (Equiv.Perm (Fin n))

/-- The number of weak compositions of `n` into `m` parts. This represents the number of ways to separate `n` objects into `m` ordered
    sets. -/
def numWeakCompositions : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | n, m + 1 => (n + m).choose m

variable {n m : ℕ}

/-- A function that takes a function `f : Fin n → Fin (m + 1)` and a proof that `f` maps no element to `m` and returns a function of type
    `Fin n → Fin m` that behaves exactly the same as `f` on all inputs. -/
def contractCodomain {f : Fin n → Fin (m + 1)} (h : ∀ i, (f i).1 ≠ m) : Fin n → Fin m :=
  fun i ↦ ⟨(f i).1, lt_of_lt_succ_of_neq (f i).2 (h i)⟩

/-- A function that takes a function `f : Fin n → Fin m` and returns a function of type `Fin n → Fin (m + 1)` that behaves exactly the
    same as `f` on all inputs. -/
def expandCodomain (f : (Fin n → Fin m)) : Fin n → Fin (m + 1) :=
  fun i ↦ ⟨(f i).1, Nat.lt_add_right 1 (f i).2⟩

/-- A function that takes a function `f : Fin (n + 1) → Fin m` and returns a function of type `Fin n → Fin m` that behaves exactly the
    same as `f` on all inputs except for `n`, which is no longer a valid input. -/
def contractDomain (f : (Fin (n + 1) → Fin m)) : Fin n → Fin m :=
  fun i ↦ f ⟨i.1, by linarith [i.2]⟩

/-- A function that takes a function `f : Fin n → Fin (m + 1)` and returns a function of type `Fin (n + 1) → Fin (m + 1)` that behaves
    exactly the same as `f` on all inputs except at `n`, where it returns `m`. -/
def expandDomain (f : (Fin n → Fin (m + 1))) : Fin (n + 1) → Fin (m + 1) :=
  fun i ↦
    if h : i.1 = n
    then ⟨m, lt_add_one m⟩
    else f ⟨i.1, lt_of_lt_succ_of_neq i.2 h⟩

/-- A recurrence formula for the number of distinct colorings of a set of `n + 1` unordered, indistinguishable objects with `m + 1` colors.
    It equals the sum of the number of distinct colorings of a set of `n + 1` unordered, indistinguishable objects with `m` colors and the
    number of distinct colorings of a set of `n` unordered, indistinguishable objects with `m + 1` colors. -/
lemma numDistinctColoringsOfPerm_succ_succ : numDistinctColoringsOfPerm (n + 1) (m + 1) =
  numDistinctColoringsOfPerm (n + 1) m + numDistinctColoringsOfPerm n (m + 1) := by
  simp [numDistinctColorings, ← Fintype.card_sum]
  apply Fintype.card_congr
  symm
  apply Equiv.ofBijective (
    fun s ↦
      match s with
      | Sum.inl q => (Quotient.map expandCodomain (by
          rintro _ _ ⟨g, rfl⟩
          use g
          ext
          simp [expandCodomain, instHSMul])) q
      | Sum.inr q => (Quotient.map expandDomain (by
          rintro _ _ ⟨g, rfl⟩
          use permExpand g
          ext i
          simp [instHSMul]
          by_cases hcases : i.1 = n
          · simp [expandDomain, dif_pos hcases]
            rw [dif_pos]
            show ((permExpand g)⁻¹ i).1 = n
            simp [hcases, permExpand, Equiv.Perm.instInv]
          · simp [expandDomain, dif_neg hcases]
            rw [dif_neg]
            · simp [permExpand, DivInvOneMonoid.toInvOneClass, DivisionMonoid.toDivInvOneMonoid, Group.toDivisionMonoid,
                Equiv.Perm.permGroup, Equiv.Perm.instInv, hcases]
            · show ¬((permExpand g)⁻¹ i).1 = n
              simp [permExpand, Equiv.Perm.instInv, hcases]
              exact Nat.ne_of_lt ((Equiv.symm g) ⟨i.1, _⟩).2)) q)
  constructor
  · rintro (f₁ | f₁) (f₂ | f₂) hf₁f₂
    repeat'
      rcases Quotient.mk_surjective f₁ with ⟨f₁, rfl⟩
      rcases Quotient.mk_surjective f₂ with ⟨f₂, rfl⟩
      simp at hf₁f₂
      rcases hf₁f₂ with ⟨g, hg⟩
      apply congrFun at hg
    · simp
      use g
      ext i
      simp [expandCodomain, instHSMul] at hg
      exact hg i
    · specialize hg (g n)
      simp [expandDomain, expandCodomain, HSMul.hSMul] at hg
      rw [dif_pos (by simp [SMul.smul, MulAction.toSMul, Equiv.Perm.applyMulAction])] at hg
      simp at hg
      linarith [(f₁ (g (Fin.last n))).2]
    · specialize hg n
      simp [expandDomain, expandCodomain, HSMul.hSMul, SMul.smul] at hg
      linarith [(f₂ (g⁻¹ (Fin.last n))).2]
    · simp
      use permContract g
      ext i
      simp [instHSMul, DivInvOneMonoid.toInvOneClass, DivisionMonoid.toDivInvOneMonoid, Group.toDivisionMonoid, Equiv.Perm.permGroup,
        Equiv.Perm.instInv, permContract, expandDomain] at hg ⊢
      by_cases hcases : ((Equiv.symm g) i.castSucc).1 = (n : Fin (n + 1)).1
      · simp [Fin.eq_of_val_eq hcases]
        simp at hcases
        have hg' := hg n
        simp [hcases] at hg'
        specialize hg i
        simp [Nat.ne_of_lt i.2] at hg
        rw [← hg, dif_pos hcases]
        congr
        apply hg'
        simp [← hcases]
        by_contra hcontra
        apply Fin.eq_of_val_eq at hcontra
        simp at hcontra
        linarith [i.2, Fin.mk.inj_iff.1 hcontra]
      · simp at hcases
        simp [hcases]
        by_cases hcases' : i.1 = n
        · linarith [i.2]
        · specialize hg i
          simp [hcases, hcases'] at hg
          rw [← hg]
  · intro f
    rcases Quotient.mk_surjective f with ⟨f, rfl⟩
    by_cases hcases : ∀ i, (f i).1 ≠ m
    · use Sum.inl ⟦contractCodomain hcases⟧
      rfl
    · simp at hcases
      rcases hcases with ⟨j, hj⟩
      use Sum.inr ⟦contractDomain ((Equiv.swap j n) • f)⟧
      simp
      use Equiv.swap j n
      ext i
      simp [expandDomain, contractDomain]
      by_cases hcases : i.1 = (n : Fin (n + 1)).1
      · simp [instHSMul, Fin.eq_of_val_eq hcases, hj]
      · simp at hcases
        simp [if_neg hcases, instHSMul]

/-- The number of distinct colorings of `n` unordered, indistinguishable objects with `m` colors is equal to the number of weak
    compositions of `n` into `m` parts. -/
lemma numDistinctColoringsOfPerm_eq_numWeakCompositions : numDistinctColoringsOfPerm n m = numWeakCompositions n m := by
  unfold numWeakCompositions
  induction' hnm : n + m with i hinduction generalizing n m
  · simp [Nat.eq_zero_of_add_eq_zero_left hnm, Nat.eq_zero_of_add_eq_zero_right hnm]
  · cases' n with n <;> cases' m with m <;> simp
    rw [numDistinctColoringsOfPerm_succ_succ, hinduction (by linarith), hinduction (by linarith)]
    cases' m with m <;> simp
    rw [← add_assoc (n + 1), Nat.choose_succ_succ', add_comm m, ← add_assoc]

end PermutationGroup
