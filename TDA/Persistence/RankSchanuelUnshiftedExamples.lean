import TDA.Persistence.RankSchanuelUnshifted
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Consumers of unshifted Schanuel interleavings

These examples exercise nonzero finite-presentation inputs in dimensions one
and two, the zero-radius case, finite-family zero components with arbitrarily
large delays, empty families, and the existing zero-padding convention.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankSchanuelUnshiftedExamples

open CategoryTheory CategoryTheory.Limits CoordinateShift
open scoped ZeroObject NNReal

private instance : HasFiniteBiproducts (PModule.{0,0,0} ℚ (Fin 1 → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

noncomputable abbrev oneCoordinateHook : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 1 → ℝ)

private theorem oneCoordinateHook_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 1 → ℝ) oneCoordinateHook :=
  GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 1 → ℝ)
    (HookInfinity.generators (P := Fin 1 → ℝ) (0 : Fin 1 → ℝ))

private noncomputable def oneCoordinateHookMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := ℚ) (M := oneCoordinateHook) :=
  Classical.choice
    (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      (by norm_num) oneCoordinateHook oneCoordinateHook_finitelyPresented)

/-- The one-coordinate hook has a nonzero fiber, so the capstone consumer is
not vacuous. -/
theorem oneCoordinateHook_nonzero_fiber :
    ∃ x : oneCoordinateHook.obj (0 : Fin 1 → ℝ), x ≠ 0 := by
  let e := HookInfinity.fiberEquivOfLe (R := ℚ) (i := (0 : Fin 1 → ℝ))
    (a := (0 : Fin 1 → ℝ)) le_rfl
  refine ⟨e.symm 1, ?_⟩
  intro hx
  have hone := congrArg e hx
  simp at hone

/-- The actual dimension-one unshifted-sum construction. The coefficient is
one and the same map handles `ε = 0`. -/
noncomputable def oneCoordinateHook_self_unshifted (ε : ℝ≥0) :
    CoordinateInterleaving (RectangleStabilityGeometry.stabilityRadius 1 ε)
      (unshiftedSchanuelLeftBiproduct
        oneCoordinateHookMinimalResolution.resolution
        oneCoordinateHookMinimalResolution.resolution)
      (unshiftedSchanuelRightBiproduct
        oneCoordinateHookMinimalResolution.resolution
        oneCoordinateHookMinimalResolution.resolution) :=
  finitelyPresented_unshiftedSchanuel_interleaving
    (by norm_num) oneCoordinateHook oneCoordinateHook
    oneCoordinateHook_finitelyPresented oneCoordinateHook_finitelyPresented
    oneCoordinateHookMinimalResolution oneCoordinateHookMinimalResolution ε
    (CoordinateInterleaving.refl ε oneCoordinateHook)

example (ε : ℝ≥0) : RectangleStabilityGeometry.stabilityRadius 1 ε = ε := by
  simp [RectangleStabilityGeometry.stabilityRadius]

noncomputable example : CoordinateInterleaving
    (RectangleStabilityGeometry.stabilityRadius 1 0)
    (unshiftedSchanuelLeftBiproduct
      oneCoordinateHookMinimalResolution.resolution
      oneCoordinateHookMinimalResolution.resolution)
    (unshiftedSchanuelRightBiproduct
      oneCoordinateHookMinimalResolution.resolution
      oneCoordinateHookMinimalResolution.resolution) :=
  oneCoordinateHook_self_unshifted 0

noncomputable abbrev twoCoordinateHook : PModule.{0,0,0} ℚ (Fin 2 → ℝ) :=
  HookInfinity.module (R := ℚ) (0 : Fin 2 → ℝ)

private theorem twoCoordinateHook_finitelyPresented :
    GradedFree.FinitelyPresented (R := ℚ) (P := Fin 2 → ℝ) twoCoordinateHook :=
  GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 2 → ℝ)
    (HookInfinity.generators (P := Fin 2 → ℝ) (0 : Fin 2 → ℝ))

private noncomputable def twoCoordinateHookMinimalResolution :
    MinimalFiniteRankProjectiveResolution (k := ℚ) (M := twoCoordinateHook) :=
  Classical.choice
    (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      (by norm_num) twoCoordinateHook twoCoordinateHook_finitelyPresented)

/-- The two-coordinate hook also has a nonzero fiber. -/
theorem twoCoordinateHook_nonzero_fiber :
    ∃ x : twoCoordinateHook.obj (0 : Fin 2 → ℝ), x ≠ 0 := by
  let e := HookInfinity.fiberEquivOfLe (R := ℚ) (i := (0 : Fin 2 → ℝ))
    (a := (0 : Fin 2 → ℝ)) le_rfl
  refine ⟨e.symm 1, ?_⟩
  intro hx
  have hone := congrArg e hx
  simp at hone

/-- Dimension two uses the `(2*n-1)` coefficient three, before any later
signed-matching step. -/
noncomputable def twoCoordinateHook_self_unshifted (ε : ℝ≥0) :
    CoordinateInterleaving (RectangleStabilityGeometry.stabilityRadius 2 ε)
      (unshiftedSchanuelLeftBiproduct
        twoCoordinateHookMinimalResolution.resolution
        twoCoordinateHookMinimalResolution.resolution)
      (unshiftedSchanuelRightBiproduct
        twoCoordinateHookMinimalResolution.resolution
        twoCoordinateHookMinimalResolution.resolution) :=
  finitelyPresented_unshiftedSchanuel_interleaving
    (by norm_num) twoCoordinateHook twoCoordinateHook
    twoCoordinateHook_finitelyPresented twoCoordinateHook_finitelyPresented
    twoCoordinateHookMinimalResolution twoCoordinateHookMinimalResolution ε
    (CoordinateInterleaving.refl ε twoCoordinateHook)

example (ε : ℝ≥0) : RectangleStabilityGeometry.stabilityRadius 2 ε = 3 * ε := by
  norm_num [RectangleStabilityGeometry.stabilityRadius]

noncomputable example (ε : ℝ≥0) : CoordinateInterleaving
    (RectangleStabilityGeometry.stabilityRadius 2 ε)
    (unshiftedSchanuelLeftBiproduct
      twoCoordinateHookMinimalResolution.resolution
      twoCoordinateHookMinimalResolution.resolution)
    (unshiftedSchanuelRightBiproduct
      twoCoordinateHookMinimalResolution.resolution
      twoCoordinateHookMinimalResolution.resolution) :=
  twoCoordinateHook_self_unshifted ε

private noncomputable def emptyFamilyDelayComparison (δ : ℝ≥0) :
    CoordinateInterleavingDelayComparison δ
      (⨁ fun _i : Empty => (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)))
      (⨁ fun _i : Empty => (shift (δ + 1)).obj
        (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ))) :=
  finiteFamilyDelayComparison δ
    (fun _i : Empty => (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)))
    (fun _ => δ + 1) (by intro i; exact i.elim)

private noncomputable def inactiveZeroFamily :
    Fin 1 → PModule.{0,0,0} ℚ (Fin 1 → ℝ) := fun _ => 0

private noncomputable def inactiveZeroDelay (δ : ℝ≥0) : Fin 1 → ℝ≥0 :=
  fun _ => δ + 1

private theorem inactiveZeroDelay_condition (δ : ℝ≥0) (_i : Fin 1) :
    inactiveZeroDelay δ _i ≤ δ ∨ IsZero (inactiveZeroFamily _i) := by
  right
  exact isZero_zero _

private noncomputable def inactiveZeroDelayComparison (δ : ℝ≥0) :
    CoordinateInterleavingDelayComparison δ
      (⨁ inactiveZeroFamily)
      (⨁ fun i => (shift (inactiveZeroDelay δ i)).obj (inactiveZeroFamily i)) :=
  finiteFamilyDelayComparison δ inactiveZeroFamily (inactiveZeroDelay δ)
    (inactiveZeroDelay_condition δ)

/-- A zero summand may have delay strictly greater than the common bound; its
reverse component is still zero. -/
theorem inactiveZero_reverse_component (δ : ℝ≥0) (i : Fin 1) :
    finiteFamilyDelayReverseComponent δ inactiveZeroFamily (inactiveZeroDelay δ) i
      (inactiveZeroDelay_condition δ i) = 0 := by
  apply finiteFamilyDelayReverseComponent_eq_zero
  change ¬ δ + 1 ≤ δ
  exact not_le_of_gt (lt_add_of_pos_right δ zero_lt_one)

/-- The reverse map of the constructed finite-family comparison has the
computed zero component on every inactive summand. -/
theorem inactiveZeroComparison_ι_reverse (δ : ℝ≥0) (i : Fin 1) :
    biproduct.ι (fun j => (shift (inactiveZeroDelay δ j)).obj
        (inactiveZeroFamily j)) i ≫
        (inactiveZeroDelayComparison δ).reverse = 0 := by
  change biproduct.ι (fun j => (shift (inactiveZeroDelay δ j)).obj
      (inactiveZeroFamily j)) i ≫
      (finiteFamilyDelayComparison δ inactiveZeroFamily (inactiveZeroDelay δ)
        (inactiveZeroDelay_condition δ)).reverse = 0
  rw [finiteFamilyDelayComparison_ι_reverse]
  rw [inactiveZero_reverse_component]
  simp

/-- Appending any number of zero terms leaves each old unshifted summand
unchanged at the same degree. -/
theorem unshiftedSchanuelLeftSummand_appendZeros
    {M N : PModule.{0,0,0} ℚ (Fin 2 → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (rpad spad : ℕ) (j : Fin (max R.length S.length)) :
    unshiftedSchanuelLeftSummand (R.appendZeros rpad) (S.appendZeros spad)
        ⟨j.val, by
          have hmax : max R.length S.length ≤
              max (R.length + rpad) (S.length + spad) :=
            max_le_max (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          simpa [FiniteRankProjectiveResolution.appendZeros_length] using
            (lt_of_lt_of_le j.isLt hmax)⟩ =
      unshiftedSchanuelLeftSummand R S j := by
  simp [unshiftedSchanuelLeftSummand,
    FiniteRankProjectiveResolution.termAt_appendZeros]

end TDA.Persistence.RankSchanuelUnshiftedExamples
