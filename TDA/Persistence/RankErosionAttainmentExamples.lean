import TDA.Persistence.RankErosionAttainment
import TDA.Persistence.StrictRankErosionExamples

/-!
# Erosion attainment: executed tests, an exact distance and the need for a finite presentation

* Executed tests of grid representations over the two-element field as consumers of the
  strict lower bound: a failing test at a radius shows that the erosion distance of the actual
  Kan extensions exceeds that radius.
* The interval module `[0, 1)` against zero: both distances are `1/2`, and erosion holds exactly
  at the radii from `1/2` on.
* The module of the closed box `[0, 2c]ⁿ` is not finitely presented when there is a coordinate,
  and for `c = 0` it has distance zero from the zero module without having its rank invariant.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankErosionAttainmentExamples

open CategoryTheory
open TDA.Persistence.RatGrid TDA.Persistence.F2GridRep
open TDA.Persistence.F2GridRepExamples TDA.Persistence.F2GridErosionExamples
open TDA.Persistence.StrictRankErosionExamples
open scoped TDA.Persistence NNReal ENNReal ZeroObject

section Executed

/-- The failing executed test at radius `1/4` bounds the erosion distance of the interval
module `[0, 1)` from zero strictly from below. -/
theorem interval_zero_quarter_lt_rankErosionDistance :
    ((radius (1 / 4) quarter_nonneg : ℝ≥0) : ℝ≥0∞) <
      rankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) :=
  GradedFree.finitelyPresented_lt_rankErosionDistance_of_not_rankErosion
    (interval.finitelyPresented_lan_toModule interval_valid)
    (zero.finitelyPresented_lan_toModule zero_valid) interval_zero_not_rankErosion

/-- The two executed tests of the rays born at `0` and at `1` enclose their erosion distance:
strictly above `1/2`, the failing radius, and at most `1`, the passing radius. -/
theorem rays_rankErosionDistance_bounds :
    ((radius (1 / 2) half_nonneg : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance ((ray 0).grid.lan.obj ((ray 0).toModule ray_zero_valid))
          ((ray 1).grid.lan.obj ((ray 1).toModule ray_one_valid)) ∧
      rankErosionDistance ((ray 0).grid.lan.obj ((ray 0).toModule ray_zero_valid))
          ((ray 1).grid.lan.obj ((ray 1).toModule ray_one_valid)) ≤
        ((radius 1 zero_le_one : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hfail⟩ := runErosion_eq_fail _ _ _ _ rays_half
  exact ⟨GradedFree.finitelyPresented_lt_rankErosionDistance_of_not_rankErosion
      ((ray 0).finitelyPresented_lan_toModule ray_zero_valid)
      ((ray 1).finitelyPresented_lan_toModule ray_one_valid) hfail,
    rankErosionDistance_le_of_erosion rays_rankErosion⟩

/-- Two parameters: the failing executed test at radius `0` shows that the erosion distance of
the two modules is not zero, and the passing test at radius `1` bounds it from above. -/
theorem plane_flat_rankErosionDistance_bounds :
    rankErosionDistance (plane.grid.lan.obj (plane.toModule plane_valid))
        (flat.grid.lan.obj (flat.toModule flat_valid)) ≠ 0 ∧
      rankErosionDistance (plane.grid.lan.obj (plane.toModule plane_valid))
          (flat.grid.lan.obj (flat.toModule flat_valid)) ≤
        ((radius 1 zero_le_one : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hfail⟩ := runErosion_eq_fail _ _ _ _ plane_flat_zero
  obtain ⟨_, _, _, hpass⟩ := (runErosion_eq_pass_iff _ _ _).mp plane_flat_one
  exact ⟨(bot_le.trans_lt
      (GradedFree.finitelyPresented_lt_rankErosionDistance_of_not_rankErosion
        (plane.finitelyPresented_lan_toModule plane_valid)
        (flat.finitelyPresented_lan_toModule flat_valid) hfail)).ne',
    rankErosionDistance_le_of_erosion hpass⟩

end Executed

section IntervalDistance

theorem zero_rank_half : zero.rankAt ![1 / 2] ![1 / 2] = 0 := by decide +kernel

/-- Below radius `1/2` the diagonal pair at `1/2` is a failed test: the widened structure map
of the interval module stays inside `[0, 1)` and has rank one. -/
theorem interval_zero_not_rankErosion_of_lt {ε : ℝ≥0} (h : ε < radius (1 / 2) half_nonneg) :
    ¬ RankErosion ε (interval.grid.lan.obj (interval.toModule interval_valid))
      (zero.grid.lan.obj (zero.toModule zero_valid)) := by
  intro H
  have hε : (ε : ℝ) < 1 / 2 := by
    have hlt : (ε : ℝ) < ((1 / 2 : ℚ) : ℝ) := NNReal.coe_lt_coe.mpr h
    push_cast at hlt
    exact hlt
  have hε0 : (0 : ℝ) ≤ ε := ε.coe_nonneg
  have hle := H.1 (realGrade ![1 / 2]) (realGrade ![1 / 2]) le_rfl
  rw [← zero.rankAt_eq_of_eq zero_valid rfl rfl le_rfl, zero_rank_half,
    CoordinateGrid.rankOfStructureMap_lan_congr interval.grid (interval.toModule interval_valid)
      (erosionWide_le ε le_rfl) (realGrade_le_iff.mpr interval_inside_le) ?_ ?_,
    interval_extension_rank_inside] at hle
  · exact absurd hle (by decide)
  · intro i g hg
    obtain ⟨q, hq, rfl⟩ := (RatGrid.mem_grid interval.values).mp hg
    have hq' : q = 0 ∨ q = 1 := by simpa [interval] using hq
    obtain rfl : i = 0 := Subsingleton.elim i 0
    change (q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) - ε ↔ (q : ℝ) ≤ ((0 : ℚ) : ℝ)
    rcases hq' with rfl | rfl <;> push_cast <;> constructor <;> intro <;> linarith
  · intro i g hg
    obtain ⟨q, hq, rfl⟩ := (RatGrid.mem_grid interval.values).mp hg
    have hq' : q = 0 ∨ q = 1 := by simpa [interval] using hq
    obtain rfl : i = 0 := Subsingleton.elim i 0
    change (q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) + ε ↔ (q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ)
    rcases hq' with rfl | rfl <;> push_cast <;> constructor <;> intro <;> linarith

/-- The erosion distance of the interval module `[0, 1)` from zero is `1/2`. -/
theorem interval_zero_rankErosionDistance :
    rankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) =
      ((radius (1 / 2) half_nonneg : ℝ≥0) : ℝ≥0∞) := by
  have := CoordinateGrid.lan_finiteDimensional interval.grid (interval.toModule interval_valid)
  have := CoordinateGrid.lan_finiteDimensional zero.grid (zero.toModule zero_valid)
  refine le_antisymm (rankErosionDistance_le_of_erosion interval_zero_rankErosion)
    (ENNReal.le_of_forall_nnreal_lt fun ε hε => ?_)
  exact le_rankErosionDistance_of_not_rankErosion
    (interval_zero_not_rankErosion_of_lt (ENNReal.coe_lt_coe.mp hε))

/-- The strict-pair distance of the same two modules is `1/2` as well. -/
theorem interval_zero_strictRankErosionDistance :
    strictRankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) =
      ((radius (1 / 2) half_nonneg : ℝ≥0) : ℝ≥0∞) := by
  have := CoordinateGrid.lan_finiteDimensional interval.grid (interval.toModule interval_valid)
  have := CoordinateGrid.lan_finiteDimensional zero.grid (zero.toModule zero_valid)
  rw [strictRankErosionDistance_eq_rankErosionDistance, interval_zero_rankErosionDistance]

/-- Strict-pair erosion of the same two modules fails at every radius below `1/2`. -/
theorem interval_zero_not_strictRankErosion_of_lt {ε : ℝ≥0}
    (h : ε < radius (1 / 2) half_nonneg) :
    ¬ StrictRankErosion ε (interval.grid.lan.obj (interval.toModule interval_valid))
      (zero.grid.lan.obj (zero.toModule zero_valid)) := fun H =>
  absurd (strictRankErosionDistance_le_of_erosion H)
    (by rw [interval_zero_strictRankErosionDistance]; exact not_le.mpr (ENNReal.coe_lt_coe.mpr h))

/-- Attainment for the interval module `[0, 1)` and zero: erosion holds exactly at the radii
from `1/2` on, the distance included. -/
theorem interval_zero_rankErosion_iff (ε : ℝ≥0) :
    RankErosion ε (interval.grid.lan.obj (interval.toModule interval_valid))
        (zero.grid.lan.obj (zero.toModule zero_valid)) ↔
      radius (1 / 2) half_nonneg ≤ ε := by
  rw [← GradedFree.finitelyPresented_rankErosionDistance_le_iff_rankErosion
      (interval.finitelyPresented_lan_toModule interval_valid)
      (zero.finitelyPresented_lan_toModule zero_valid),
    interval_zero_rankErosionDistance, ENNReal.coe_le_coe]

end IntervalDistance

section ClosedBox

variable {n : ℕ}

/-- With at least one coordinate, the module of the closed box `[0, 2c]ⁿ` is not finitely
presented: its erosion distance from zero is `c`, and erosion fails at radius `c`. So
attainment does not extend to modules with finite-dimensional fibers. -/
theorem closedBox_not_finitelyPresented [NeZero n] (c : ℝ≥0) :
    ¬ GradedFree.FinitelyPresented.{0,0,0} (R := ℚ) (closedBox (n := n) c) := fun h =>
  closedBox_not_rankErosion c
    ((GradedFree.finitelyPresented_rankErosionDistance_le_iff_rankErosion h
      GradedFree.finitelyPresented_zero c).mp (closedBox_rankErosionDistance c).le)

/-- With at least one coordinate, the module supported at the single grade `0` has erosion
distance zero from the zero module, and its rank invariant differs from that of zero, on the
diagonal at `0`. So distance zero does not give equal rank invariants without a finite
presentation. -/
theorem closedBox_zero_distance_zero_and_ranks_differ [NeZero n] :
    rankErosionDistance (closedBox (n := n) 0) 0 = 0 ∧
      ¬ ∀ (a b : Fin n → ℝ) (hab : a ≤ b),
        rankOfStructureMap (closedBox (n := n) 0) hab =
          rankOfStructureMap (0 : PModule.{0,0,0} ℚ (Fin n → ℝ)) hab :=
  ⟨by simpa using closedBox_rankErosionDistance (n := n) 0,
    fun h => closedBox_not_rankErosion 0 (rankErosion_zero_iff.mpr h)⟩

end ClosedBox

end TDA.Persistence.RankErosionAttainmentExamples
