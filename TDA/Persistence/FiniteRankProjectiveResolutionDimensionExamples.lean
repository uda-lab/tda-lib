import TDA.Persistence.FiniteRankProjectiveResolutionDimension
import TDA.Persistence.FinitePresentationKanExamples
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Consumers of the real-coordinate minimal-resolution degree bound

These consumers apply the original finite-presentation theorem to a nonzero
one-coordinate principal upset, a genuinely presented two-coordinate module
with repeated generator births and a nonzero quotient, and the zero module.
The supplied-resolution arguments also exercise the theorem's quantifier
over every certified minimal resolution after zero padding.
-/

set_option autoImplicit false

namespace TDA.Persistence.FiniteRankProjectiveResolutionDimensionExamples

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable abbrev oneCoordinateHook : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 1 → ℝ)

private theorem oneCoordinateHook_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 1 → ℝ) oneCoordinateHook :=
  GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 1 → ℝ)
    (HookInfinity.generators (P := Fin 1 → ℝ) (0 : Fin 1 → ℝ))

/-- The one-coordinate principal upset has a nonzero fiber. -/
theorem oneCoordinateHook_nonzero :
    ∃ x : oneCoordinateHook.obj (0 : Fin 1 → ℝ), x ≠ 0 := by
  let e := HookInfinity.fiberEquivOfLe (R := ℚ) (i := (0 : Fin 1 → ℝ))
    (a := (0 : Fin 1 → ℝ)) le_rfl
  refine ⟨e.symm 1, ?_⟩
  intro hx
  have hone := congrArg e hx
  exact (one_ne_zero : (1 : ℚ) ≠ 0) (by simpa using hone)

/-- In dimension one, every supplied minimal resolution of the nonzero free
module has zero terms in every positive degree. -/
theorem oneCoordinateHook_all_positive_terms_are_zero
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := oneCoordinateHook))
    {j : ℕ} (hj : 0 < j) : IsZero (R.termAt j) := by
  exact FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
    (n := 1) (by norm_num) oneCoordinateHook oneCoordinateHook_finitelyPresented R j
    (by omega)

/-- The one-coordinate finite-presentation theorem supplies a certified
minimal resolution with the same strict positive-degree bound. -/
theorem oneCoordinateHook_exists_bounded_minimal_resolution :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := oneCoordinateHook),
      ∀ j, 0 < j → IsZero (R.termAt j) := by
  obtain ⟨R, hR⟩ :=
    FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution_with_bound
      (n := 1) (by norm_num) oneCoordinateHook oneCoordinateHook_finitelyPresented
  exact ⟨R, fun j hj => hR j (by omega)⟩

private noncomputable abbrev repeatedPresentation :
    PModule.{0,0,0} ℚ (Fin 2 → ℝ) :=
  (FinitePresentationKanExamples.presentation ℚ 2).presented

private theorem repeatedPresentation_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 2 → ℝ) repeatedPresentation :=
  (FinitePresentationKanExamples.presentation ℚ 2).finitelyPresented
    (FinitePresentationKanExamples.presentation_finite ℚ 2)

/-- The two-coordinate presentation retains its repeated birth occurrences
and has a surviving nonzero quotient fiber. -/
theorem repeatedPresentation_repeated_birth_nonzero_fiber :
    (FinitePresentationKanExamples.presentation ℚ 2).generatorGridPoint
        (FinitePresentationKanExamples.presentation_finite ℚ 2) (0 : Fin 2) =
      (FinitePresentationKanExamples.presentation ℚ 2).generatorGridPoint
        (FinitePresentationKanExamples.presentation_finite ℚ 2) (1 : Fin 2) ∧
      ∃ x : repeatedPresentation.obj (0 : Fin 2 → ℝ), x ≠ 0 := by
  exact ⟨(FinitePresentationKanExamples.repeated_births ℚ 2).1,
    ⟨FinitePresentationKanExamples.secondValue ℚ 2,
      FinitePresentationKanExamples.surviving_generator 2⟩⟩

/-- For the genuine two-coordinate presentation, every supplied certified
minimal resolution vanishes strictly above degree two. -/
theorem repeatedPresentation_all_terms_above_two_are_zero
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := repeatedPresentation))
    {j : ℕ} (hj : 2 < j) : IsZero (R.termAt j) := by
  exact FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
    (n := 2) (by norm_num) repeatedPresentation repeatedPresentation_finitelyPresented R j
    (by omega)

/-- The same original presentation hypothesis supplies one certified minimal
resolution with zero-padded terms vanishing strictly above degree two. -/
theorem repeatedPresentation_exists_bounded_minimal_resolution :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := ℚ) (M := repeatedPresentation),
      ∀ j, 2 < j → IsZero (R.termAt j) := by
  obtain ⟨R, hR⟩ :=
    FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution_with_bound
      (n := 2) (by norm_num) repeatedPresentation repeatedPresentation_finitelyPresented
  exact ⟨R, fun j hj => hR j (by omega)⟩

private noncomputable abbrev emptyGenerators (n : ℕ) :
    GradedFree.GradedGenerators.{0,0} (Fin n → ℝ) where
  Carrier := Empty
  grade := Empty.elim

private theorem zero_finitelyPresented (n : ℕ) :
    GradedFree.FinitelyPresented.{0,0,0} (R := ℚ) (P := Fin n → ℝ)
      (0 : PModule.{0,0,0} ℚ (Fin n → ℝ)) := by
  let W := emptyGenerators n
  have hzero : IsZero (GradedFree.module (R := ℚ) W) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply GradedFree.hom_ext_birth W
    intro g
    exact g.elim
  exact GradedFree.finitelyPresented_of_iso
    (GradedFree.free_finitelyPresented (R := ℚ) (P := Fin n → ℝ) W) hzero.isoZero

/-- The degenerate zero module also satisfies the arbitrary supplied-resolution
bound in every positive coordinate dimension. -/
theorem zeroModule_all_terms_above_bound_are_zero
    (n : ℕ) (hn : 1 ≤ n)
    (R : MinimalFiniteRankProjectiveResolution (k := ℚ)
      (M := (0 : PModule.{0,0,0} ℚ (Fin n → ℝ)))) :
    ∀ j, 2 * n - 2 < j → IsZero (R.termAt j) :=
  FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
    hn 0 (zero_finitelyPresented n) R

end TDA.Persistence.FiniteRankProjectiveResolutionDimensionExamples
