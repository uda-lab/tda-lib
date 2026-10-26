import TDA.Persistence.PrincipalDownsetRankDimension

/-!
# Principal-downset resolution and dimension examples

A chain downset needs one complement generator, while the bottom downset in the
Boolean square needs two. The top and singleton cases use the identity row.
The coefficient field remains arbitrary, including infinite fields.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.PrincipalDownsetRankDimension.Examples

open CategoryTheory CategoryTheory.Limits
open PrincipalDownsetRankResolution

variable {k : Type u} [Field k]

/-- The initial downset in a three-point chain has complement generator `1`. -/
theorem chain_minimalComplement : minimalComplement (0 : Fin 3) = {1} := by
  ext a
  fin_cases a <;> simp only [minimalComplement, Set.mem_ofPred_eq, Minimal] <;> decide

/-- The chain downset has one minimal complement generator. -/
theorem chain_complementCard : complementCard (0 : Fin 3) = 1 := by
  unfold complementCard
  simpa using Fintype.card_of_subtype (p := fun a => a ∈ minimalComplement (0 : Fin 3)) ({1} : Finset (Fin 3)) (by
    intro a
    rw [chain_minimalComplement]
    simp)

/-- The chain downset has an actual one-term resolution and degree-zero Hom bound. -/
theorem chain_resolution_and_dimension :
    (resolution (k := k) (0 : Fin 3)).length = 1 ∧
      HasProjectiveDimensionLE
        ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := Fin 3)).obj
          (PrincipalDownsetInjective.module 0)) 0 := by
  constructor
  · simp [resolution_length, chain_complementCard]
  · simpa [chain_complementCard] using hasProjectiveDimensionLE (k := k) (0 : Fin 3)

/-- The bottom downset in the Boolean square has its two coordinate atoms as generators. -/
theorem square_minimalComplement :
    minimalComplement (false, false) = {(true, false), (false, true)} := by
  ext ⟨a, b⟩
  cases a <;> cases b <;> simp only [minimalComplement, Set.mem_ofPred_eq, Minimal] <;> decide

/-- The two distinct coordinate atoms are both counted. -/
theorem square_complementCard : complementCard (false, false) = 2 := by
  unfold complementCard
  simpa using Fintype.card_of_subtype (p := fun a => a ∈ minimalComplement (false, false))
    ({(true, false), (false, true)} : Finset (Bool × Bool)) (by
      intro a
      rw [square_minimalComplement]
      simp)

/-- The Boolean-square downset has two actual quotient terms and Hom dimension at most one. -/
theorem square_resolution_and_dimension :
    (resolution (k := k) (false, false)).length = 2 ∧
      HasProjectiveDimensionLE
        ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := Bool × Bool)).obj
          (PrincipalDownsetInjective.module (false, false))) 1 := by
  constructor
  · simp [resolution_length, square_complementCard]
  · simpa [square_complementCard] using hasProjectiveDimensionLE (k := k) (false, false)

/-- The chain module is nonzero at its supported initial grade. -/
theorem chain_supported_fiber_nonzero :
    ∃ x : (PrincipalDownsetInjective.module (k := k) (0 : Fin 3)).obj 0, x ≠ 0 := by
  refine ⟨SupportInterval.one (Set.Iic (0 : Fin 3)) (by simp), ?_⟩
  intro h
  have he := congrArg Subtype.val h
  exact one_ne_zero he

/-- Empty complement at top produces one identity term and a degree-zero bound. -/
theorem top_resolution_and_dimension :
    complementCard (⊤ : Bool × Bool) = 0 ∧
      (resolution (k := k) (⊤ : Bool × Bool)).length = 1 ∧
      HasProjectiveDimensionLE
        ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := Bool × Bool)).obj
          (PrincipalDownsetInjective.module ⊤)) 0 := by
  have hc : complementCard (⊤ : Bool × Bool) = 0 := (complementCard_eq_zero_iff _).mpr rfl
  refine ⟨hc, by simp [resolution_length, hc], ?_⟩
  simpa [hc] using hasProjectiveDimensionLE (k := k) (⊤ : Bool × Bool)

/-- On the singleton lattice the unique principal-downset module uses the top identity resolution. -/
theorem singleton_resolution_and_dimension :
    (resolution (k := k) (0 : Fin 1)).length = 1 ∧
      HasProjectiveDimensionLE
        ((FiniteRankProjectiveHomExact.homFunctor (k := k) (S := Fin 1)).obj
          (PrincipalDownsetInjective.module 0)) 0 := by
  have hc : complementCard (0 : Fin 1) = 0 :=
    (complementCard_eq_zero_iff _).mpr (Subsingleton.elim _ _)
  constructor
  · simp [resolution_length, hc]
  · simpa [hc] using hasProjectiveDimensionLE (k := k) (0 : Fin 1)

/-- Any supplied certified minimal chain resolution has zero term in positive degree. -/
theorem chain_positive_degree_vanishing
    (R : MinimalFiniteRankProjectiveResolution
      (k := k) (M := PrincipalDownsetInjective.module (0 : Fin 3))) :
    IsZero (R.termAt 1) :=
  termAt_isZero _ R 1 (by simp [chain_complementCard])

/-- The bound controls every minimal square resolution, including padding past degree one. -/
theorem square_high_degree_vanishing
    (R : MinimalFiniteRankProjectiveResolution
      (k := k) (M := PrincipalDownsetInjective.module (false, false))) :
    IsZero (R.termAt 2) :=
  termAt_isZero _ R 2 (by simp [square_complementCard])

end TDA.Persistence.PrincipalDownsetRankDimension.Examples
