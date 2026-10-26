import TDA.Persistence.GeneratedUpsetQuotientFiniteResolution
import TDA.Persistence.GeneratedUpsetQuotientResolutionExamples

/-!
# Examples using the finite hook-quotient bundle

These examples exercise the public finite-resolution interface on a nonzero one-generator
quotient, repeated occurrences with a positive-degree term, and the zero and bottom-valued
boundary cases.
-/

set_option autoImplicit false

namespace TDA.Persistence.GeneratedUpsetQuotientFiniteResolution.Examples

open CategoryTheory CategoryTheory.Limits
open GeneratedUpsetQuotientFiniteResolution

/-- A one-generator family has one quotient term, which is nonzero below its birth. -/
theorem one_generator_bundle_term_nonzero :
    ∃ x : ((resolution (k := ℚ) (fun _ : Fin 1 => (1 : ℕ))).term
      ⟨0, by simp [resolution_length]⟩).obj 0,
      x ≠ 0 := by
  change ∃ x :
    (TDA.Persistence.GeneratedUpsetQuotientResolution.term (k := ℚ)
      (fun _ : Fin 1 => (1 : ℕ)) 0).obj 0, x ≠ 0
  exact TDA.Persistence.GeneratedUpsetQuotientResolution.Examples.one_generator_quotient_nonzero

/-- Two equal births remain separate occurrences in the degree-zero term. -/
theorem repeated_bundle_occurrences_distinct :
    ∃ x y : ((resolution (k := ℚ) (fun _ : Fin 2 => (1 : ℕ))).term
      ⟨0, by simp [resolution_length]⟩).obj 0,
      x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y := by
  change ∃ x y :
    (TDA.Persistence.GeneratedUpsetQuotientResolution.term (k := ℚ)
      (fun _ : Fin 2 => (1 : ℕ)) 0).obj 0, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y
  exact TDA.Persistence.GeneratedUpsetQuotientResolution.Examples.repeated_occurrence_classes_distinct

/-- Two distinct births have a nonzero term in positive degree. -/
theorem two_generator_bundle_positive_degree_nonzero :
    ∃ x : ((resolution (k := ℚ) (fun i : Fin 2 => i.val + 1)).term
      ⟨1, by simp [resolution_length]⟩).obj 0,
      x ≠ 0 := by
  change ∃ x :
    (TDA.Persistence.GeneratedUpsetQuotientResolution.term (k := ℚ)
      (fun i : Fin 2 => i.val + 1) 1).obj 0, x ≠ 0
  exact TDA.Persistence.GeneratedUpsetQuotientResolution.Examples.two_generator_positive_quotient_nonzero

/-- The quotient map in the first positive row followed by its preceding inclusion is the
actual differential on the two-generator bundle. -/
theorem two_generator_bundle_row_composition :
    (resolution (k := ℚ) (fun i : Fin 2 => i.val + 1)).quotient
        ⟨1, by simp [resolution_length]⟩ ≫
      (resolution (k := ℚ) (fun i : Fin 2 => i.val + 1)).inclusion
        ⟨0, by simp [resolution_length]⟩ =
        TDA.Persistence.GeneratedUpsetQuotientResolution.differential
          (fun i : Fin 2 => i.val + 1) 0 := by
  exact TDA.Persistence.GeneratedUpsetQuotientFiniteResolution.resolution_differential
    (k := ℚ) _ 0 (by decide)

/-- Bottom-valued births give zero terms in the bundled resolution. -/
theorem bottom_family_bundle_terms_zero (i : Fin 1) :
    IsZero ((resolution (k := ℚ) (fun _ : Fin 1 => (0 : ℕ))).term i) := by
  change IsZero (TDA.Persistence.GeneratedUpsetQuotientResolution.term (k := ℚ)
    (TDA.Persistence.GeneratedUpsetQuotientResolution.bottomFamily (P := ℕ) 1) i.val)
  exact TDA.Persistence.GeneratedUpsetQuotientResolution.term_bottomFamily_isZero
    (k := ℚ) 1 i.val

/-- The empty occurrence family gives a zero target and a zero-length bundle. -/
theorem empty_bundle_zero_target :
    IsZero (TDA.Persistence.GeneratedUpsetQuotientResolution.target
      (k := ℚ) (fun i : Fin 0 => (Fin.elim0 i : ℕ))) ∧
      (resolution (k := ℚ) (fun i : Fin 0 => (Fin.elim0 i : ℕ))).length = 0 := by
  constructor
  · exact TDA.Persistence.GeneratedUpsetQuotientFiniteResolution.terminalKernel_isZero (k := ℚ)
      (fun i : Fin 0 => (Fin.elim0 i : ℕ))
  · rfl

/-- The complement bundle keeps the same number of terms as the actual quotient bundle. -/
theorem repeated_complement_bundle_length :
    (complementResolution (k := ℚ) (fun _ : Fin 2 => (1 : ℕ)) (by decide)).length = 2 := rfl

end TDA.Persistence.GeneratedUpsetQuotientFiniteResolution.Examples
