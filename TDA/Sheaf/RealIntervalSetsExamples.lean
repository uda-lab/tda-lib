import TDA.Sheaf.RealIntervalSets
import TDA.Sheaf.RealConstructibleExtExamples

/-!
# Fixtures for interval sets and stalks of interval sheaves on the real line

One breakpoint at `0` (`p₁`), strata `0 ← 1 → 2`, coefficients `ℚ`.

* Interval sets: the point interval `[1, 1]` is the singleton `{0}`
  (`intervalSet_pointSegment`); the cells `[0, 0]` and `[2, 2]` are the unbounded open
  half-lines `(-∞, 0)` and `(0, ∞)` (`intervalSet_leftCell`, `intervalSet_rightCell`); the
  segments `[0, 1]` and `[1, 2]` are the closed half-lines `(-∞, 0]` and `[0, ∞)`
  (`intervalSet_segLeft`, `intervalSet_segRight`); the whole path `[0, 2]` is `ℝ`
  (`intervalSet_wholeLine`). Without breakpoints the single vertex is `ℝ`
  (`intervalSet_p₀`).
* Stalks: the interval sheaf of `[1, 1]` has a one-dimensional stalk at `0` and a zero stalk at
  `1` (`finrank_stalk_pointSheaf`); the interval sheaf of `[0, 0]` has a one-dimensional stalk
  at `-1` and a zero stalk at `0` (`finrank_stalk_leftOpen`); the interval sheaf of `[1, 2]`
  has a one-dimensional stalk at `0` and a zero stalk at `-1`
  (`finrank_stalk_rightClosed`); the interval sheaves of the whole path and, without
  breakpoints, of the single vertex have one-dimensional stalks everywhere
  (`finrank_stalk_wholeLineSheaf`, `finrank_stalk_constSheaf₀`).
* Restrictions: for the interval sheaf of `[1, 2]`, the restriction from `ℝ` to `(0, ∞)` is an
  isomorphism (`isIso_rightClosed_right`), while the restriction to `(-∞, 0)` is not
  (`not_isIso_rightClosed_left`).
-/

namespace TDA.Sheaf.RealIntervalSetsExamples

open CategoryTheory Limits TopologicalSpace Opposite TDA.Persistence
  TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealStratification TDA.Sheaf.RealConstructible
  TDA.Sheaf.RealStratificationExamples TDA.Sheaf.RealConstructibleExamples
  TDA.Sheaf.RealConstructibleExtExamples

/-! ### Interval sets -/

/-- The left cell `[0, 0]` of `0 ← 1 → 2`. -/
def leftCell : FiniteInterval 3 := ⟨0, 1, by decide, by decide⟩

/-- The whole path `[0, 2]` of `0 ← 1 → 2`. -/
def wholeLine : FiniteInterval 3 := ⟨0, 3, by decide, le_rfl⟩

/-- **Singleton.** The point interval `[1, 1]` has interval set `{0}`. -/
theorem intervalSet_pointSegment : intervalSet p₁ pointSegment = {0} :=
  intervalSet_eq_singleton p₁_strictMono (i := 0) rfl rfl

/-- **Unbounded, left.** The left cell `[0, 0]` has interval set `(-∞, 0)`. -/
theorem intervalSet_leftCell : intervalSet p₁ leftCell = Set.Iio 0 :=
  intervalSet_eq_Iio p₁_strictMono (j := 0) rfl rfl

/-- **Unbounded, right.** The right cell `[2, 2]` has interval set `(0, ∞)`. -/
theorem intervalSet_rightCell : intervalSet p₁ rightCell = Set.Ioi 0 :=
  intervalSet_eq_Ioi p₁_strictMono (i := 0) rfl rfl

/-- The segment `[0, 1]` has interval set `(-∞, 0]`. -/
theorem intervalSet_segLeft : intervalSet p₁ segLeft = Set.Iic 0 :=
  intervalSet_eq_Iic p₁_strictMono (j := 0) rfl rfl

/-- The segment `[1, 2]` has interval set `[0, ∞)`. -/
theorem intervalSet_segRight : intervalSet p₁ segRight = Set.Ici 0 :=
  intervalSet_eq_Ici p₁_strictMono (i := 0) rfl rfl

/-- **The whole line.** The whole path `[0, 2]` has interval set `ℝ`. -/
theorem intervalSet_wholeLine : intervalSet p₁ wholeLine = Set.univ :=
  intervalSet_eq_univ p₁_strictMono rfl rfl

/-- Without breakpoints, the single vertex has interval set `ℝ`. -/
theorem intervalSet_p₀ : intervalSet p₀ ⟨0, 1, by decide, by decide⟩ = Set.univ :=
  intervalSet_eq_univ p₀_strictMono rfl rfl

/-! ### Stalks -/

/-- The interval sheaf of the left cell `[0, 0]`, with stalk `ℚ` exactly on `(-∞, 0)`. -/
noncomputable abbrev leftOpen : TopCat.Sheaf (ModuleCat.{0} ℚ) realLine :=
  intervalSheaf ℚ leftCell

/-- The interval sheaf of the whole path `[0, 2]`, with stalk `ℚ` on all of `ℝ`. -/
noncomputable abbrev wholeLineSheaf : TopCat.Sheaf (ModuleCat.{0} ℚ) realLine :=
  intervalSheaf ℚ wholeLine

/-- The interval sheaf of `[1, 1]` has a one-dimensional stalk at `0` and a zero stalk at `1`. -/
theorem finrank_stalk_pointSheaf :
    Module.finrank ℚ ((pointSheaf ℚ).presheaf.stalk (0 : ℝ)) = 1 ∧
      Module.finrank ℚ ((pointSheaf ℚ).presheaf.stalk (1 : ℝ)) = 0 := by
  rw [finrank_stalk_extension_interval, finrank_stalk_extension_interval,
    intervalSet_pointSegment]
  norm_num

/-- The interval sheaf of `[0, 0]` has a one-dimensional stalk at `-1` and a zero stalk at
`0`. -/
theorem finrank_stalk_leftOpen :
    Module.finrank ℚ ((leftOpen).presheaf.stalk (-1 : ℝ)) = 1 ∧
      Module.finrank ℚ ((leftOpen).presheaf.stalk (0 : ℝ)) = 0 := by
  rw [finrank_stalk_extension_interval, finrank_stalk_extension_interval, intervalSet_leftCell]
  norm_num

/-- The interval sheaf of `[1, 2]` has a one-dimensional stalk at `0` and a zero stalk at
`-1`. -/
theorem finrank_stalk_rightClosed :
    Module.finrank ℚ ((rightClosed ℚ).presheaf.stalk (0 : ℝ)) = 1 ∧
      Module.finrank ℚ ((rightClosed ℚ).presheaf.stalk (-1 : ℝ)) = 0 := by
  rw [finrank_stalk_extension_interval, finrank_stalk_extension_interval, intervalSet_segRight]
  norm_num

/-- The interval sheaf of the whole path has a one-dimensional stalk at every point. -/
theorem finrank_stalk_wholeLineSheaf (x : ℝ) :
    Module.finrank ℚ (wholeLineSheaf.presheaf.stalk x) = 1 := by
  rw [finrank_stalk_extension_interval, intervalSet_wholeLine]
  simp

/-- Without breakpoints, the constant sheaf has a one-dimensional stalk at every point. -/
theorem finrank_stalk_constSheaf₀ (x : ℝ) :
    Module.finrank ℚ ((constSheaf₀ ℚ).presheaf.stalk x) = 1 := by
  rw [constSheaf₀, finrank_stalk_extension_interval, intervalSet_p₀]
  simp

/-! ### Restrictions -/

/-- For the interval sheaf of `[1, 2]`, the restriction from `ℝ` to `(0, ∞)` is an isomorphism:
both strata lie in the interval. -/
theorem isIso_rightClosed_right :
    IsIso ((rightClosed ℚ).presheaf.map
      (homOfLE (star_le_star_of_arrow p₁ arrow_one_two)).op) :=
  isIso_extension_interval_map ℚ p₁_strictMono segRight arrow_one_two (by decide) (by decide)

end TDA.Sheaf.RealIntervalSetsExamples
