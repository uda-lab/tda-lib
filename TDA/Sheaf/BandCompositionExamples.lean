import TDA.Sheaf.BandComposition
import TDA.Sheaf.IntervalFibrationExamples

/-!
# The composition isomorphism of the band functors: fixtures

These fixtures consume `TDA.Sheaf.BandComposition` over `ℚ`, with Mathlib's standard derived
category `HasDerivedCategory.standard` installed as a local instance in this file only. `kpt` is the
sheaf on the point with value `ℚ` and `constOn X` the constant sheaf with value `kpt` on `X`
(`TDA.Sheaf.IntervalFibrationExamples`).

* **Fibres of `pr₁₃`.** Over the point `vEnd = (0, 2)` of `D (1 + 1)`, at the maximal distance
  `dist 0 2 = 1 + 1`, the fibre interval of `pr₁₃ 1 1` is the point `[1, 1]`
  (`lo_pr₁₃_vEnd`, `hi_pr₁₃_vEnd`); over `vMid = (0, 0)` it is `[-1, 1]` (`lo_pr₁₃_vMid`,
  `hi_pr₁₃_vMid`). In both cases `H⁰` of the stalk of `R(pr₁₃)_*` of the constant sheaf is
  nonzero (`not_isZero_H0_stalk_pr₁₃_vEnd`, `not_isZero_H0_stalk_pr₁₃_vMid`). For `a = b = 0`
  every fibre of `pr₁₃` is a point (`lo_eq_hi_pr₁₃_zero`).
* **Base change and derived unit.** The central square of `Z 1 1` has invertible base change
  (`isIso_baseChange_one_one`); the derived units of `pr₁₃ 1 1` and `pr₁₃ 0 0` are invertible
  (`isIso_derivedUnit_pr₁₃_one_one`, `isIso_derivedUnit_pr₁₃_zero_zero`).
* **The composition isomorphism on the constant sheaf.** For `0 ≤ a`, `0 ≤ b` and every `y`,
  `H⁰` of the stalk at `y` of `T_b (T_a (constOn ℝ))` is `kpt`, through `TComp` and the stalk
  formula of `q (a + b)` (`H0_stalk_TT`), hence nonzero (`not_isZero_H0_stalk_TT`); the cases
  `a = b = 0` (`not_isZero_H0_stalk_TT_zero`) and `a = b = 1` (`H0_stalk_TT_one_one`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandCompositionExamples

open TDA.Sheaf.IntervalCohomologyExamples (kpt)
open TDA.Sheaf.BandStalksExamples (not_isZero_kpt)
open TDA.Sheaf.IntervalFibrationExamples (constOn H0_stalk_const not_isZero_H0_stalk_const)

attribute [local instance] HasDerivedCategory.standard

section fibres

/-- The point `(0, 2)` of `D (1 + 1)`, at the maximal distance `dist 0 2 = 1 + 1`. -/
def vEnd : D (1 + 1) :=
  ⟨(0, 2), by
    change dist (0 : ℝ) 2 ≤ 1 + 1
    rw [Real.dist_eq]
    norm_num⟩

/-- The point `(0, 0)` of `D (1 + 1)`. -/
def vMid : D (1 + 1) :=
  ⟨(0, 0), by
    change dist (0 : ℝ) 0 ≤ 1 + 1
    norm_num⟩

/-- Over `vEnd = (0, 2)` the fibre interval of `pr₁₃ 1 1` starts at `max (0 - 1) (2 - 1) = 1`. -/
theorem lo_pr₁₃_vEnd : (intervalFibration_pr₁₃ 1 1).lo vEnd = 1 := by
  change max ((0 : ℝ) - 1) (2 - 1) = 1
  norm_num

/-- Over `vEnd = (0, 2)` the fibre interval of `pr₁₃ 1 1` ends at `min (0 + 1) (2 + 1) = 1`. -/
theorem hi_pr₁₃_vEnd : (intervalFibration_pr₁₃ 1 1).hi vEnd = 1 := by
  change min ((0 : ℝ) + 1) (2 + 1) = 1
  norm_num

/-- Over `vMid = (0, 0)` the fibre interval of `pr₁₃ 1 1` starts at `-1`. -/
theorem lo_pr₁₃_vMid : (intervalFibration_pr₁₃ 1 1).lo vMid = -1 := by
  change max ((0 : ℝ) - 1) (0 - 1) = -1
  norm_num

/-- Over `vMid = (0, 0)` the fibre interval of `pr₁₃ 1 1` ends at `1`. -/
theorem hi_pr₁₃_vMid : (intervalFibration_pr₁₃ 1 1).hi vMid = 1 := by
  change min ((0 : ℝ) + 1) (0 + 1) = 1
  norm_num

/-- For `a = b = 0` every fibre of `pr₁₃` is a point: over `(x, z)` with `dist x z ≤ 0`,
`max x z = min x z`. -/
theorem lo_eq_hi_pr₁₃_zero (v : D (0 + 0)) :
    (intervalFibration_pr₁₃ 0 0).lo v = (intervalFibration_pr₁₃ 0 0).hi v := by
  have h : v.1.1 = v.1.2 := dist_le_zero.1 (by simpa using v.2)
  change max (v.1.1 - 0) (v.1.2 - 0) = min (v.1.1 + 0) (v.1.2 + 0)
  rw [h]
  simp

/-- At the one-point fibre over `vEnd`, `H⁰` of the stalk of `R(pr₁₃ 1 1)_*` of the constant sheaf
is nonzero. -/
theorem not_isZero_H0_stalk_pr₁₃_vEnd :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf vEnd)).obj ((pushforwardPlus ℚ (pr₁₃ 1 1)).obj (constOn (Z 1 1))))) :=
  not_isZero_H0_stalk_const (intervalFibration_pr₁₃ 1 1) vEnd (by
    rw [lo_pr₁₃_vEnd, hi_pr₁₃_vEnd])

/-- At the fibre `[-1, 1]` over `vMid`, `H⁰` of the stalk of `R(pr₁₃ 1 1)_*` of the constant sheaf
is nonzero. -/
theorem not_isZero_H0_stalk_pr₁₃_vMid :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf vMid)).obj ((pushforwardPlus ℚ (pr₁₃ 1 1)).obj (constOn (Z 1 1))))) :=
  not_isZero_H0_stalk_const (intervalFibration_pr₁₃ 1 1) vMid (by
    rw [lo_pr₁₃_vMid, hi_pr₁₃_vMid]
    norm_num)

end fibres

section composition

/-- The central square `pr₁₂ ≫ q 1 = pr₂₃ ≫ p 1` of `Z 1 1` has invertible base change. -/
theorem isIso_baseChange_one_one : IsIso (baseChange ℚ (pr₁₂_q 1 1)) := inferInstance

/-- The derived unit of `pr₁₃ 1 1 : Z 1 1 ⟶ D (1 + 1)` is invertible. -/
theorem isIso_derivedUnit_pr₁₃_one_one : IsIso (derivedUnit ℚ (pr₁₃ 1 1)) :=
  isIso_derivedUnit_pr₁₃ ℚ zero_le_one zero_le_one

/-- The derived unit of `pr₁₃ 0 0 : Z 0 0 ⟶ D (0 + 0)`, whose fibres are points, is invertible. -/
theorem isIso_derivedUnit_pr₁₃_zero_zero : IsIso (derivedUnit ℚ (pr₁₃ 0 0)) :=
  isIso_derivedUnit_pr₁₃ ℚ le_rfl le_rfl

/-- **`H⁰` of a stalk of `T_b (T_a)` of the constant sheaf.** For `0 ≤ a`, `0 ≤ b` and `y : ℝ`,
`H⁰` of the stalk at `y` of `T_b (T_a (constOn ℝ))` is `kpt`: `TComp` identifies the object with
`T_{a+b} (constOn ℝ) = R(q (a + b))_* (constOn (D (a + b)))`, whose stalk at `y` has
`H⁰([y - (a + b), y + (a + b)]; constSh kpt) ≅ kpt` (`H0_stalk_const`). -/
def H0_stalk_TT {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y : realLine) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pullbackPlus ℚ (ptOf y)).obj ((T ℚ a ⋙ T ℚ b).obj (constOn realLine))) ≅ kpt :=
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((pullbackPlus ℚ (ptOf y)).mapIso ((TComp ℚ ha hb).app (constOn realLine)) ≪≫
        (pullbackPlus ℚ (ptOf y)).mapIso ((pushforwardPlus ℚ (q (a + b))).mapIso
          ((pullbackPlusCompIso ℚ (p (a + b)) (toPt realLine)).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt)))) ≪≫
    H0_stalk_const (intervalFibration_q (a + b)) y (by
      change y - (a + b) ≤ y + (a + b)
      linarith)

/-- For `0 ≤ a`, `0 ≤ b`, `H⁰` of every stalk of `T_b (T_a (constOn ℝ))` is nonzero. -/
theorem not_isZero_H0_stalk_TT {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y : realLine) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf y)).obj ((T ℚ a ⋙ T ℚ b).obj (constOn realLine)))) :=
  fun hz => not_isZero_kpt (hz.of_iso (H0_stalk_TT ha hb y).symm)

/-- The case `a = b = 0`: `H⁰` of the stalk at `0` of `T_0 (T_0 (constOn ℝ))` is nonzero. -/
theorem not_isZero_H0_stalk_TT_zero :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf (0 : realLine))).obj ((T ℚ 0 ⋙ T ℚ 0).obj (constOn realLine)))) :=
  not_isZero_H0_stalk_TT le_rfl le_rfl 0

/-- The case `a = b = 1`: `H⁰` of the stalk at `0` of `T_1 (T_1 (constOn ℝ))` is `kpt`, as for
`T_{1+1}`. -/
def H0_stalk_TT_one_one :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pullbackPlus ℚ (ptOf (0 : realLine))).obj ((T ℚ 1 ⋙ T ℚ 1).obj (constOn realLine))) ≅
      kpt :=
  H0_stalk_TT zero_le_one zero_le_one 0

end composition

end TDA.Sheaf.BandCompositionExamples
