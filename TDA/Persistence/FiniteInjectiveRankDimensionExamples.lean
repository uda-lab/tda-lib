import TDA.Persistence.FiniteInjectiveRankDimension
import TDA.Persistence.PrincipalDownsetRankDimensionExamples

/-!
# Examples for finite injective Hom dimension bounds

These consumers check the maximum on a chain, Boolean square and singleton,
then use the public presentation, injective-module and minimal-resolution laws.
The coefficient field remains unrestricted.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteInjectiveRankDimension.Examples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteInjectivePresentation
open TDA.Persistence.FiniteInjectiveRankDimension
open TDA.Persistence.PrincipalDownsetInjective
open TDA.Persistence.PrincipalDownsetRankResolution
open TDA.Persistence.PrincipalDownsetRankDimension.Examples
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open scoped ZeroObject

variable {k : Type u} [Field k]

private instance squareBoolSmallCategory : SmallCategory (Bool × Bool) :=
  Preorder.smallCategory (Bool × Bool)

private instance zeroFiberSubsingleton {P : Type} [PartialOrder P] (p : P) :
    Subsingleton ((0 : PModule ℚ P).obj p) :=
  ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)

private instance zeroFiberFiniteDimensional {P : Type} [PartialOrder P] (p : P) :
    FiniteDimensional ℚ ((0 : PModule ℚ P).obj p) := by
  infer_instance

/-- The middle point in a three-point chain has one minimal complement point. -/
theorem chain_middle_minimalComplement :
    minimalComplement (1 : Fin 3) = {2} := by
  ext a
  fin_cases a <;> simp only [minimalComplement, Set.mem_ofPred_eq, Minimal] <;> decide

/-- The middle chain downset has one minimal complement generator. -/
theorem chain_middle_complementCard : complementCard (1 : Fin 3) = 1 := by
  unfold complementCard
  simpa using Fintype.card_of_subtype
    (p := fun a => a ∈ minimalComplement (1 : Fin 3)) ({2} : Finset (Fin 3)) (by
      intro a
      rw [chain_middle_minimalComplement]
      simp)

/-- The maximum complement cardinal on a three-point chain is one. -/
theorem chain_maxComplementCard : maxComplementCard (S := Fin 3) = 1 := by
  unfold maxComplementCard
  refine le_antisymm ?_ ?_
  · apply Finset.sup_le
    intro p hp
    fin_cases p
    · simpa [chain_complementCard]
    · simpa [chain_middle_complementCard]
    · have hc : complementCard (2 : Fin 3) = 0 :=
        (complementCard_eq_zero_iff (p := (2 : Fin 3))).2 rfl
      simp [hc]
  · have h : complementCard (0 : Fin 3) ≤
        Finset.univ.sup (fun p : Fin 3 => complementCard p) :=
      Finset.le_sup (Finset.mem_univ (0 : Fin 3))
    simpa [chain_complementCard] using h

/-- The complement above `(false, true)` has one minimal generator. -/
theorem square_false_true_minimalComplement :
    minimalComplement (false, true) = {(true, false)} := by
  ext ⟨a, b⟩
  cases a <;> cases b <;>
    simp only [minimalComplement, Set.mem_ofPred_eq, Minimal] <;> decide

/-- The complement above `(true, false)` has one minimal generator. -/
theorem square_true_false_minimalComplement :
    minimalComplement (true, false) = {(false, true)} := by
  ext ⟨a, b⟩
  cases a <;> cases b <;>
    simp only [minimalComplement, Set.mem_ofPred_eq, Minimal] <;> decide

/-- One axis point of the Boolean square has one minimal complement generator. -/
theorem square_false_true_complementCard : complementCard (false, true) = 1 := by
  unfold complementCard
  simpa using Fintype.card_of_subtype
    (p := fun a => a ∈ minimalComplement (false, true)) ({(true, false)} : Finset (Bool × Bool)) (by
      intro a
      rw [square_false_true_minimalComplement]
      simp)

/-- The other axis point of the Boolean square has one minimal complement generator. -/
theorem square_true_false_complementCard : complementCard (true, false) = 1 := by
  unfold complementCard
  simpa using Fintype.card_of_subtype
    (p := fun a => a ∈ minimalComplement (true, false)) ({(false, true)} : Finset (Bool × Bool)) (by
      intro a
      rw [square_true_false_minimalComplement]
      simp)

/-- The maximum complement cardinal on the Boolean square is two. -/
theorem square_maxComplementCard : maxComplementCard (S := Bool × Bool) = 2 := by
  unfold maxComplementCard
  refine le_antisymm ?_ ?_
  · apply Finset.sup_le
    intro p hp
    rcases p with ⟨a, b⟩
    cases a <;> cases b
    · simpa [square_complementCard]
    · simpa [square_false_true_complementCard]
    · simpa [square_true_false_complementCard]
    · have hc : complementCard (true, true) = 0 :=
        (complementCard_eq_zero_iff (p := (true, true))).2 rfl
      simp [hc]
  · have h : complementCard (false, false) ≤
        Finset.univ.sup (fun p : Bool × Bool => complementCard p) :=
      Finset.le_sup (Finset.mem_univ (false, false))
    simpa [square_complementCard] using h

/-- The unique singleton point has an empty complement, so the maximum is zero. -/
theorem singleton_maxComplementCard : maxComplementCard (S := Fin 1) = 0 := by
  unfold maxComplementCard
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro p hp
  have hpTop : p = (⊤ : Fin 1) := Subsingleton.elim _ _
  subst p
  simp [complementCard_eq_zero_iff]

/-- A two-dimensional constant fiber contributes two separate coordinates at
each of the four Boolean-square grades. -/
abbrev squareDoubleModule : PModule ℚ (Bool × Bool) :=
  (Functor.const (Bool × Bool)).obj (ModuleCat.of ℚ (ℚ × ℚ))

private instance squareDoubleModule_finiteDimensional (p : Bool × Bool) :
    FiniteDimensional ℚ (squareDoubleModule.obj p) := by
  change FiniteDimensional ℚ (ℚ × ℚ)
  infer_instance

/-- Repeated coordinate occurrences remain separate in the actual presentation. -/
theorem squareDoubleModule_coordinateCount :
    Fintype.card (FiniteInjectivePresentation.Index squareDoubleModule) = 8 := by
  simp [FiniteInjectivePresentation.Index, squareDoubleModule, Module.finrank_prod]

/-- The presentation target for the two-dimensional square module is an actual
ordinary injective object. -/
theorem squareDoubleModule_target_injective :
    Injective (FiniteInjectivePresentation.module squareDoubleModule) := inferInstance

/-- The actual Hom module of that finite injective-presentation target has
projective dimension at most one. -/
theorem squareDoubleModule_target_dimension :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := ℚ) (S := Bool × Bool)).obj
        (FiniteInjectivePresentation.module squareDoubleModule)) 1 := by
  have hmax := square_maxComplementCard
  apply presentation_hasProjectiveDimensionLE
  intro p
  have hp := complementCard_le_maxComplementCard (S := Bool × Bool) p
  rw [hmax] at hp
  omega

/-- A principal injective on the three-point chain obeys the degree-zero bound. -/
theorem chain_principal_injective_dimension :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := Fin 3)).obj
        (PrincipalDownsetInjective.module (0 : Fin 3))) 0 := by
  simpa [chain_maxComplementCard] using
    (hasProjectiveDimensionLE_of_max (k := k) (S := Fin 3)
      (PrincipalDownsetInjective.module (0 : Fin 3)))

/-- A principal injective on the Boolean square obeys the degree-one bound. -/
theorem square_principal_injective_dimension :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := Bool × Bool)).obj
        (PrincipalDownsetInjective.module (false, false))) 1 := by
  simpa [square_maxComplementCard] using
    (hasProjectiveDimensionLE_of_max (k := k) (S := Bool × Bool)
      (PrincipalDownsetInjective.module (false, false)))

/-- The zero module has an empty coordinate index, including over the chain. -/
theorem zero_module_coordinateCount :
    Fintype.card (FiniteInjectivePresentation.Index (0 : PModule ℚ (Fin 3))) = 0 := by
  simp [FiniteInjectivePresentation.Index, Module.finrank_zero_of_subsingleton]

/-- The zero module satisfies the chain's degree-zero Hom bound. -/
theorem zero_module_dimension :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := ℚ) (S := Fin 3)).obj
        (0 : PModule ℚ (Fin 3))) 0 := by
  simpa [chain_maxComplementCard] using
    (hasProjectiveDimensionLE_of_max (k := ℚ) (S := Fin 3)
      (0 : PModule ℚ (Fin 3)))

/-- The singleton principal injective has Hom dimension zero by the maximum
theorem's natural-subtraction convention. -/
theorem singleton_principal_injective_dimension :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := Fin 1)).obj
        (PrincipalDownsetInjective.module (0 : Fin 1))) 0 := by
  simpa [singleton_maxComplementCard] using
    (hasProjectiveDimensionLE_of_max (k := k) (S := Fin 1)
      (PrincipalDownsetInjective.module (0 : Fin 1)))

/-- The singleton bound applies over an arbitrary field, including an infinite
one such as `ℚ`. -/
theorem singleton_infinite_field_dimension :
    HasProjectiveDimensionLE
      ((FiniteRankProjectiveHomExact.homFunctor (k := ℚ) (S := Fin 1)).obj
        (PrincipalDownsetInjective.module (0 : Fin 1))) 0 :=
  singleton_principal_injective_dimension (k := ℚ)

/-- Every supplied certified minimal resolution of the singleton injective has
zero terms in all positive degrees. -/
theorem singleton_resolution_positive_degree_vanishing
    (R : MinimalFiniteRankProjectiveResolution
      (k := ℚ) (M := PrincipalDownsetInjective.module (0 : Fin 1)))
    (j : ℕ) (hj : 0 < j) : IsZero (R.termAt j) := by
  apply termAt_isZero_of_max (k := ℚ) (S := Fin 1)
  simpa [singleton_maxComplementCard] using hj

end TDA.Persistence.FiniteInjectiveRankDimension.Examples
