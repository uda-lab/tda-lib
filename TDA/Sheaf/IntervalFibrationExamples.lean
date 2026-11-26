import TDA.Sheaf.BandBaseChange
import TDA.Sheaf.BandStalksExamples

/-!
# Interval fibrations and the fibrewise base-change criterion: fixtures

These fixtures consume `TDA.Sheaf.PointDetection` and `TDA.Sheaf.IntervalFibration` over `ℚ`,
with Mathlib's standard derived category `HasDerivedCategory.standard` installed as a local
instance in this file only. `kpt` is the sheaf on the point with value `ℚ`
(`TDA.Sheaf.IntervalCohomologyExamples`).

* `H0_stalk_const`: for any interval fibration `π : X ⟶ Y` and a point `y` with nonempty fibre
  (`lo y ≤ hi y`), `H⁰` of the stalk at `y` of `Rπ_*` of the constant sheaf with value `kpt` is
  `kpt`, through the canonical stalk formula; in particular it is nonzero
  (`not_isZero_H0_stalk_const`).
* The band projection through the general theorem: the base change of the fibre square of
  `intervalFibration_q 1` at `0` is invertible (`isIso_baseChange_q`) and `H⁰` of the stalk at `0`
  of `R(q 1)_*` of the constant sheaf is nonzero (`not_isZero_H0_stalk_q`).
* The **wedge** `W = {(x, s) | 0 ≤ s ≤ x}` over the real line, with `wπ (x, s) = x`, is an interval
  fibration (`intervalFibration_wπ`) whose fibre at `y` is `[0, y]`: empty for `y < 0`, the point
  `[0, 0]` at `y = 0`. At the one-point fibre, `H⁰` of the stalk at `0` of `R(wπ)_*` of the
  constant sheaf is nonzero (`not_isZero_H0_stalk_wedge_zero`), and `H²` of the stalk of the
  derived direct image of a sheaf vanishes (`isZero_H2_stalk_wedge`).
* **Base change along a translation** (the fibrewise criterion): the square
  `shiftD ≫ q 1 = q 1 ≫ shift` with `shift y = y + 1` and `shiftD (x, y) = (x + 1, y + 1)` has
  invertible base change `R(q 1)_* ⋙ shift⁻¹ ≅ shiftD⁻¹ ⋙ R(q 1)_*` (`isIso_baseChange_shift`):
  `fibreEmb 1 z ≫ shiftD` parametrises the fibre of `q 1` at `z + 1` in the coordinate
  `p 1 - 1` (`isFibreParam_shift`), and `isIso_baseChange_of_isFibreParam` applies.
* **Derived units.** On `[0, 1]` the derived unit is invertible at `kpt` placed in degree `3`
  (`isIso_derivedUnit_Icc_single_three`, through `isIso_derivedUnit_Icc`). The band projection
  `q 1`, with fibres `[y - 1, y + 1]`, has invertible derived unit `𝟭 ⟶ (q 1)⁻¹ ⋙ R(q 1)_*`
  (`isIso_derivedUnit_q_one`), and so has `q 0`, whose fibres are points
  (`isIso_derivedUnit_q_zero`), through `IntervalFibration.isIso_derivedUnit`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.IntervalFibrationExamples

open TDA.Sheaf.IntervalCohomologyExamples (kpt)
open TDA.Sheaf.BandStalksExamples (not_isZero_kpt)

attribute [local instance] HasDerivedCategory.standard

/-- The constant sheaf on `X` with value `kpt`, in `D⁺(Sh X)`. -/
abbrev constOn (X : TopCat.{0}) : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} ℚ)) :=
  (pullbackPlus ℚ (toPt X)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt)

section general

variable {X Y : TopCat.{0}} {π : X ⟶ Y} (hπ : IntervalFibration π)

/-- **`H⁰` of a stalk of the derived direct image of a constant sheaf.** For an interval fibration
`π` and a point `y` with nonempty fibre, `H⁰` of the stalk at `y` of `Rπ_* (constOn X)` is
`H⁰([lo y, hi y]; constSh kpt) ≅ kpt`. -/
def H0_stalk_const (y : Y) (h : hπ.lo y ≤ hπ.hi y) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((pullbackPlus ℚ (ptOf y)).obj ((pushforwardPlus ℚ π).obj (constOn X))) ≅ kpt :=
  have := isIso_derivedUnit_toPt_Icc (k := ℚ) h kpt
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso ((hπ.stalkFormula ℚ y).app _) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((pushforwardPlus ℚ (toPt (TopCat.of (Set.Icc (hπ.lo y) (hπ.hi y))))).mapIso
        ((pullbackPlusCompIso ℚ (hπ.e y) (toPt X)).app _)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      (asIso ((derivedUnit ℚ (toPt (TopCat.of (Set.Icc (hπ.lo y) (hπ.hi y))))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj kpt))).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app kpt

/-- At a point with nonempty fibre, `H⁰` of the stalk of `Rπ_* (constOn X)` is nonzero. -/
theorem not_isZero_H0_stalk_const (y : Y) (h : hπ.lo y ≤ hπ.hi y) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf y)).obj ((pushforwardPlus ℚ π).obj (constOn X)))) :=
  fun hz => not_isZero_kpt (hz.of_iso (H0_stalk_const hπ y h).symm)

end general

section band

/-- The band projection through the general theorem: the base change of the fibre square of
`intervalFibration_q 1` at `0` is an isomorphism. -/
theorem isIso_baseChange_q : IsIso (baseChange ℚ ((intervalFibration_q 1).e_comp 0)) :=
  inferInstance

/-- `H⁰` of the stalk at `0` of `R(q 1)_*` of the constant sheaf is nonzero, through the stalk
formula of the interval fibration `intervalFibration_q 1`. -/
theorem not_isZero_H0_stalk_q :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf (0 : ℝ))).obj ((pushforwardPlus ℚ (q 1)).obj (constOn (D 1))))) :=
  not_isZero_H0_stalk_const (intervalFibration_q 1) 0 (by
    change (0 : ℝ) - 1 ≤ 0 + 1
    norm_num)

end band

section wedge

/-- The wedge `{(x, s) | 0 ≤ s ≤ x}` in `ℝ²`. -/
def wedge : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ z.2 ≤ z.1}

/-- The wedge is closed. -/
theorem isClosed_wedge : IsClosed wedge :=
  (isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_fst)

/-- The wedge as a topological space. -/
abbrev W : TopCat.{0} := TopCat.of wedge

/-- The projection `(x, s) ↦ x` of the wedge to the real line. -/
def wπ : W ⟶ realLine := TopCat.ofHom ⟨fun z => z.1.1, by fun_prop⟩

/-- The projection of the wedge is proper. -/
theorem isProperMap_wπ : IsProperMap wπ := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨wπ.hom.continuous, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.bddAbove
  have hc : IsCompact (wedge ∩ Prod.fst ⁻¹' K) :=
    (hK.prod (isCompact_Icc (a := (0 : ℝ)) (b := R))).of_isClosed_subset
      (isClosed_wedge.inter (hK.isClosed.preimage continuous_fst)) (by
        rintro ⟨x, s⟩ ⟨⟨h0, hs⟩, hx⟩
        exact ⟨hx, h0, hs.trans (hR hx)⟩)
  have := isClosed_wedge.isClosedEmbedding_subtypeVal.isCompact_preimage hc
  convert this using 1
  ext z
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  exact ⟨fun h => ⟨z.2, h⟩, fun h => h.2⟩

/-- The fibre of the wedge at `y`, parametrised by `[0, y]`: `s ↦ (y, s)`. -/
def wedgeEmb (y : ℝ) : TopCat.of (Set.Icc 0 y) ⟶ W :=
  TopCat.ofHom ⟨fun s => ⟨(y, s.1), s.2.1, s.2.2⟩,
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩

/-- **The wedge projection is an interval fibration**, with fibre coordinate `(x, s) ↦ s` and
fibre `[0, y]` at `y`: empty for `y < 0` and a point at `y = 0`. -/
def intervalFibration_wπ : IntervalFibration wπ where
  t := ⟨fun z => z.1.2, by fun_prop⟩
  isInducing := Topology.IsInducing.subtypeVal
  isClosedMap := isProperMap_wπ.isClosedMap
  lo _ := 0
  hi y := y
  e := wedgeEmb
  isFibreParam y :=
    { comp_eq := rfl
      t_apply := fun _ => rfl
      mem_range := fun z hz => ⟨⟨z.1.2, z.2.1, hz ▸ z.2.2⟩, Subtype.ext (Prod.ext hz.symm rfl)⟩ }

/-- At the one-point fibre `[0, 0]` over `0`, `H⁰` of the stalk of `R(wπ)_*` of the constant
sheaf is nonzero. -/
theorem not_isZero_H0_stalk_wedge_zero :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf (0 : ℝ))).obj ((pushforwardPlus ℚ wπ).obj (constOn W)))) :=
  not_isZero_H0_stalk_const intervalFibration_wπ 0 le_rfl

/-- At every point, `H²` of the stalk of `R(wπ)_*` of a sheaf placed in degree `0` vanishes. -/
theorem isZero_H2_stalk_wedge (y : ℝ) (G : W.Sheaf (ModuleCat.{0} ℚ)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((pullbackPlus ℚ (ptOf y)).obj ((pushforwardPlus ℚ wπ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) :=
  intervalFibration_wπ.isZero_H_stalk_pushforwardPlus ℚ y G le_rfl

end wedge

section shift

/-- The translation `y ↦ y + 1` of the real line. -/
def shift : realLine ⟶ realLine := TopCat.ofHom ⟨fun y => y + 1, by fun_prop⟩

/-- The translation `(x, y) ↦ (x + 1, y + 1)` of the band `D 1`. -/
def shiftD : D 1 ⟶ D 1 :=
  TopCat.ofHom ⟨fun z => ⟨(z.1.1 + 1, z.1.2 + 1), by
      change dist (z.1.1 + 1) (z.1.2 + 1) ≤ 1
      rw [Real.dist_eq, show z.1.1 + 1 - (z.1.2 + 1) = z.1.1 - z.1.2 by ring, ← Real.dist_eq]
      exact z.2⟩, by fun_prop⟩

/-- The translation square `shiftD ≫ q 1 = q 1 ≫ shift`. -/
theorem shift_square : shiftD ≫ q 1 = q 1 ≫ shift := rfl

/-- The homeomorphism `(x, y) ↦ (y, x - 1)` of `ℝ²`. -/
def swapShift : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun z := (z.2, z.1 - 1)
  invFun z := (z.2 + 1, z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The fibre coordinate `p 1 - 1` of `q 1`. -/
def shiftCoordinate : FibreCoordinate (q 1) where
  t := ⟨fun z => z.1.1 - 1, by fun_prop⟩
  isInducing := swapShift.isInducing.comp Topology.IsInducing.subtypeVal
  isClosedMap := (isProperMap_q 1).isClosedMap

/-- `fibreEmb 1 z ≫ shiftD`, `x ↦ (x + 1, z + 1)`, parametrises the fibre of `q 1` at `z + 1` in
the coordinate `p 1 - 1`. -/
theorem isFibreParam_shift (z : ℝ) :
    shiftCoordinate.IsFibreParam (shift z) ((intervalFibration_q 1).e z ≫ shiftD) where
  comp_eq := rfl
  t_apply x := add_sub_cancel_right x.1 1
  mem_range w hw := by
    have hw' : w.1.2 = z + 1 := hw
    have hd : dist w.1.1 w.1.2 ≤ 1 := w.2
    rw [Real.dist_eq, abs_le, hw'] at hd
    refine ⟨⟨w.1.1 - 1, show z - 1 ≤ w.1.1 - 1 by linarith [hd.1],
      show w.1.1 - 1 ≤ z + 1 by linarith [hd.2]⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change w.1.1 - 1 + 1 = w.1.1
      ring
    · change z + 1 = w.1.2
      exact hw'.symm

/-- **Base change along a translation.** The base-change morphism of the translation square,
`R(q 1)_* ⋙ shift⁻¹ ⟶ shiftD⁻¹ ⋙ R(q 1)_*`, is an isomorphism (the fibrewise criterion). -/
theorem isIso_baseChange_shift : IsIso (baseChange ℚ shift_square) :=
  isIso_baseChange_of_isFibreParam ℚ shift_square shiftCoordinate (intervalFibration_q 1)
    isFibreParam_shift

end shift

section derivedUnit

/-- On `[0, 1]`, the derived unit is invertible at `kpt` placed in degree `3`: it is invertible on
all of `D⁺(Sh pt)`. -/
theorem isIso_derivedUnit_Icc_single_three :
    IsIso ((derivedUnit ℚ (toPt (TopCat.of (Set.Icc (0 : ℝ) 1)))).app
      ((DerivedCategory.Plus.singleFunctor _ 3).obj kpt)) :=
  have := isIso_derivedUnit_Icc (k := ℚ) (zero_le_one' ℝ)
  inferInstance

/-- **The band projection `q 1` has invertible derived unit**: `R(q 1)_* (q 1)⁻¹ N ≅ N` for
`N ∈ D⁺(Sh ℝ)`, since its fibres `[y - 1, y + 1]` are nonempty. -/
theorem isIso_derivedUnit_q_one : IsIso (derivedUnit ℚ (q 1)) :=
  (intervalFibration_q 1).isIso_derivedUnit ℚ fun y => by
    change y - 1 ≤ y + 1
    linarith

/-- The band projection `q 0`, whose fibres `[y - 0, y + 0]` are points, has invertible derived
unit, through the interval fibration `intervalFibration_q 0`. -/
theorem isIso_derivedUnit_q_zero : IsIso (derivedUnit ℚ (q 0)) :=
  (intervalFibration_q 0).isIso_derivedUnit ℚ fun y => by
    change y - 0 ≤ y + 0
    simp

end derivedUnit

end TDA.Sheaf.IntervalFibrationExamples
