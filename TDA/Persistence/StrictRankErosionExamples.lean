import TDA.Persistence.StrictRankErosion
import TDA.Persistence.SupportInterval
import TDA.Persistence.CoordinateGridRankExact
import TDA.Persistence.RankErosionGridExamples
import TDA.Persistence.F2GridErosionExamples

/-!
# Strict-pair and weak-pair rank erosion compared

* The module supported on the closed box `[0, 2c]ⁿ`, against the zero module. Strict-pair
  erosion holds at radius `c`, and weak-pair erosion fails there, on the diagonal at the centre
  of the box. With at least one coordinate, weak-pair erosion holds at every larger radius, and
  both distances equal `c`. So the two predicates differ at a fixed radius although their
  distances agree, the weak-pair infimum is not attained, and a failed weak-pair test gives no
  strict lower bound for the distance of pointwise finite-dimensional modules. The case `c = 0`
  is a module supported at one grade.
* Executed tests of grid representations over the two-element field as consumers. A passing
  test gives strict-pair erosion at its radius. A failing test at radius `1/4` excludes
  strict-pair erosion at the smaller radius `1/8` and bounds the strict-pair distance from
  below; a failure reported at a strict pair excludes strict-pair erosion at the tested radius.
  These conclusions are what the executed tests give, not sharp values: for the interval
  `[0, 1)` against zero both distances are `1/2`, and strict-pair erosion fails at every
  radius below `1/2`. These sharp statements are proved in `RankErosionAttainmentExamples`
  (`interval_zero_rankErosionDistance`, `interval_zero_strictRankErosionDistance`,
  `interval_zero_not_strictRankErosion_of_lt`).
* No coordinates: two modules with fibers of dimensions three and two satisfy strict-pair
  erosion at every radius and have strict-pair distance zero, while weak-pair erosion fails at
  every radius and the weak-pair distance is infinite.
-/

set_option autoImplicit false

namespace TDA.Persistence.StrictRankErosionExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.RatGrid TDA.Persistence.F2GridRep
open TDA.Persistence.F2GridRepExamples TDA.Persistence.F2GridErosionExamples
open scoped TDA.Persistence NNReal ENNReal ZeroObject

section ClosedBox

variable {n : ℕ}

/-- The closed box `[0, 2c]ⁿ`. -/
def box (c : ℝ≥0) : Set (Fin n → ℝ) := Set.Icc 0 fun _ => 2 * (c : ℝ)

theorem mem_box {c : ℝ≥0} {a : Fin n → ℝ} :
    a ∈ box c ↔ ∀ i, 0 ≤ a i ∧ a i ≤ 2 * (c : ℝ) :=
  ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The module with one copy of `ℚ` at each grade of the closed box and zero elsewhere. -/
noncomputable def closedBox (c : ℝ≥0) : PModule.{0,0,0} ℚ (Fin n → ℝ) :=
  SupportInterval.module (box c) Set.ordConnected_Icc

instance closedBox_finiteDimensional (c : ℝ≥0) (p : Fin n → ℝ) :
    FiniteDimensional ℚ ((closedBox c).obj p) :=
  inferInstanceAs (FiniteDimensional ℚ (SupportInterval.fiber (k := ℚ) (box c) p))

/-- The fibers of the zero module are finite-dimensional. -/
theorem zero_finiteDimensional (p : Fin n → ℝ) :
    FiniteDimensional ℚ ((0 : PModule.{0,0,0} ℚ (Fin n → ℝ)).obj p) :=
  have : Subsingleton ((0 : PModule.{0,0,0} ℚ (Fin n → ℝ)).obj p) :=
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
  inferInstance

/-- A structure map with an endpoint outside the box has rank zero. -/
theorem closedBox_rank_eq_zero (c : ℝ≥0) {a b : Fin n → ℝ} (hab : a ≤ b)
    (h : ¬ (a ∈ box c ∧ b ∈ box c)) : rankOfStructureMap (closedBox c) hab = 0 := by
  unfold rankOfStructureMap
  rw [closedBox, SupportInterval.structureMap_eq_zero_of_not_mem _ _ hab h, LinearMap.range_zero,
    finrank_bot]

/-- A structure map between two grades of the box has positive rank. -/
theorem closedBox_rank_pos (c : ℝ≥0) {a b : Fin n → ℝ} (hab : a ≤ b) (ha : a ∈ box c)
    (hb : b ∈ box c) : 0 < rankOfStructureMap (closedBox c) hab := by
  unfold rankOfStructureMap
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hbot := Submodule.finrank_eq_zero.mp h0
  rw [LinearMap.range_eq_bot] at hbot
  exact (SupportInterval.structureMap_eq_zero_iff (k := ℚ) (box c) Set.ordConnected_Icc hab).mp
    hbot ⟨ha, hb⟩

/-- The pair `(a - c, b + c)` lies in the box only for the diagonal pair at its centre. -/
theorem eq_of_wide_mem_box (c : ℝ≥0) {a b : Fin n → ℝ} (hab : a ≤ b)
    (ha : erosionLower c a ∈ box c) (hb : erosionUpper c b ∈ box c) : a = b := by
  funext i
  have h1 : 0 ≤ a i - (c : ℝ) := (mem_box.mp ha i).1
  have h2 : b i + (c : ℝ) ≤ 2 * (c : ℝ) := (mem_box.mp hb i).2
  have h3 : a i ≤ b i := hab i
  linarith

/-- Strict-pair erosion holds at radius `c`, for any number of coordinates. -/
theorem closedBox_strictRankErosion (c : ℝ≥0) :
    StrictRankErosion c (closedBox (n := n) c) 0 := by
  constructor
  · intro a b hab hne
    rw [closedBox_rank_eq_zero c _ fun h => hne (eq_of_wide_mem_box c hab h.1 h.2)]
    exact Nat.zero_le _
  · intro a b hab _
    rw [rankOfStructureMap_zero]
    exact Nat.zero_le _

/-- Weak-pair erosion fails at radius `c`: on the diagonal at the centre of the box, the
widened structure map runs from the lowest to the highest grade of the box. -/
theorem closedBox_not_rankErosion (c : ℝ≥0) :
    ¬ RankErosion c (closedBox (n := n) c) 0 := by
  intro h
  have hle := h.1 (fun _ => (c : ℝ)) (fun _ => (c : ℝ)) le_rfl
  rw [rankOfStructureMap_zero] at hle
  refine absurd hle (not_le.mpr (closedBox_rank_pos c _ (mem_box.mpr fun i => ?_)
    (mem_box.mpr fun i => ?_)))
  · have hc : (0 : ℝ) ≤ c := c.coe_nonneg
    change 0 ≤ (c : ℝ) - c ∧ (c : ℝ) - c ≤ 2 * c
    constructor <;> linarith
  · have hc : (0 : ℝ) ≤ c := c.coe_nonneg
    change 0 ≤ (c : ℝ) + c ∧ (c : ℝ) + c ≤ 2 * c
    constructor <;> linarith

/-- The two predicates differ at the radius `c`. -/
theorem closedBox_strict_and_not_weak (c : ℝ≥0) :
    StrictRankErosion c (closedBox (n := n) c) 0 ∧ ¬ RankErosion c (closedBox (n := n) c) 0 :=
  ⟨closedBox_strictRankErosion c, closedBox_not_rankErosion c⟩

/-- With at least one coordinate, weak-pair erosion holds at every radius above `c`. -/
theorem closedBox_rankErosion_of_lt [NeZero n] {c c' : ℝ≥0} (h : c < c') :
    RankErosion c' (closedBox (n := n) c) 0 :=
  have := zero_finiteDimensional (n := n)
  (closedBox_strictRankErosion c).rankErosion_of_lt h

/-- With at least one coordinate the weak-pair distance is `c`, although weak-pair erosion
fails at `c`: the infimum is not attained. -/
theorem closedBox_rankErosionDistance [NeZero n] (c : ℝ≥0) :
    rankErosionDistance (closedBox (n := n) c) 0 = c := by
  have := zero_finiteDimensional (n := n)
  refine le_antisymm ?_ (le_rankErosionDistance_of_not_rankErosion (closedBox_not_rankErosion c))
  rw [← strictRankErosionDistance_eq_rankErosionDistance]
  exact strictRankErosionDistance_le_of_erosion (closedBox_strictRankErosion c)

/-- The strict-pair distance is the same number, and it is attained. -/
theorem closedBox_strictRankErosionDistance [NeZero n] (c : ℝ≥0) :
    strictRankErosionDistance (closedBox (n := n) c) 0 = c := by
  have := zero_finiteDimensional (n := n)
  rw [strictRankErosionDistance_eq_rankErosionDistance, closedBox_rankErosionDistance]

/-- One coordinate and `c = 0`: the module supported at the single grade `0` has the ranks of
the zero module at every strict pair. Its rank invariant differs from that of the zero module
on the diagonal, which is proved in `RankErosionAttainmentExamples`
(`closedBox_zero_distance_zero_and_ranks_differ`). -/
theorem closedBox_zero_strict_pair_ranks {a b : Fin 1 → ℝ} (hab : a ≤ b) (hne : a ≠ b) :
    rankOfStructureMap (closedBox (n := 1) 0) hab =
      rankOfStructureMap (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) hab :=
  strictRankErosion_zero_iff.mp (closedBox_strictRankErosion 0) a b hab hne

end ClosedBox

section Executed

/-- A passing executed test gives strict-pair erosion at its radius. -/
theorem interval_zero_strictRankErosion :
    StrictRankErosion (radius (1 / 2) half_nonneg)
      (interval.grid.lan.obj (interval.toModule interval_valid))
      (zero.grid.lan.obj (zero.toModule zero_valid)) :=
  interval_zero_rankErosion.strict

theorem eighth_nonneg : (0 : ℚ) ≤ 1 / 8 := by norm_num

theorem radius_eighth_lt_quarter :
    radius (1 / 8) eighth_nonneg < radius (1 / 4) quarter_nonneg := by
  rw [← NNReal.coe_lt_coe, coe_radius, coe_radius]
  norm_num

/-- The failing executed test at radius `1/4` excludes strict-pair erosion at radius `1/8`,
through the implication from strict pairs to weak pairs at a larger radius. The radius `1/8`
is not sharp: strict-pair erosion of these two modules fails at every radius below `1/2`
(`RankErosionAttainmentExamples.interval_zero_not_strictRankErosion_of_lt`). -/
theorem interval_zero_not_strictRankErosion :
    ¬ StrictRankErosion (radius (1 / 8) eighth_nonneg)
      (interval.grid.lan.obj (interval.toModule interval_valid))
      (zero.grid.lan.obj (zero.toModule zero_valid)) := by
  have := CoordinateGrid.lan_finiteDimensional interval.grid (interval.toModule interval_valid)
  have := CoordinateGrid.lan_finiteDimensional zero.grid (zero.toModule zero_valid)
  exact fun h => interval_zero_not_rankErosion (h.rankErosion_of_lt radius_eighth_lt_quarter)

/-- The two executed tests enclose the strict-pair distance between `1/4` and `1/2`. The
enclosure is what these two tests give; the distance itself is `1/2`
(`RankErosionAttainmentExamples.interval_zero_strictRankErosionDistance`). -/
theorem interval_zero_strictRankErosionDistance_bounds :
    ((radius (1 / 4) quarter_nonneg : ℝ≥0) : ℝ≥0∞) ≤
        strictRankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) ∧
      strictRankErosionDistance (interval.grid.lan.obj (interval.toModule interval_valid))
          (zero.grid.lan.obj (zero.toModule zero_valid)) ≤
        ((radius (1 / 2) half_nonneg : ℝ≥0) : ℝ≥0∞) := by
  have := CoordinateGrid.lan_finiteDimensional interval.grid (interval.toModule interval_valid)
  have := CoordinateGrid.lan_finiteDimensional zero.grid (zero.toModule zero_valid)
  refine ⟨?_, strictRankErosionDistance_le_of_erosion interval_zero_strictRankErosion⟩
  rw [strictRankErosionDistance_eq_rankErosionDistance]
  exact le_rankErosionDistance_of_not_rankErosion interval_zero_not_rankErosion

/-- The failure of the two rays at radius `1/2` is reported at the strict pair `(1/2, 1)`, so
strict-pair erosion fails at the tested radius itself. -/
theorem rays_not_strictRankErosion :
    ¬ StrictRankErosion (radius (1 / 2) half_nonneg)
      ((ray 0).grid.lan.obj ((ray 0).toModule ray_zero_valid))
      ((ray 1).grid.lan.obj ((ray 1).toModule ray_one_valid)) := by
  intro h
  obtain ⟨_, _, _, hpq, _, _, _, hfirst, _, _⟩ := runErosion_eq_fail _ _ _ _ rays_half
  obtain ⟨hwide, hnarrow⟩ := hfirst rfl
  have hne : realGrade (![1 / 2] : Fin 1 → ℚ) ≠ realGrade ![1] := fun e =>
    absurd (realGrade_injective e) (by decide +kernel)
  have hle := h.1 _ _ (realGrade_le_iff.mpr hpq) hne
  rw [← hwide, ← hnarrow] at hle
  exact absurd hle (by decide)

end Executed

section NoCoordinates

theorem noCoordinatesTwo_valid : noCoordinatesTwo.Valid := by decide +kernel

/-- With no coordinates strict-pair erosion holds at every radius, also for two modules whose
fibers have different dimensions. -/
theorem noCoordinates_strictRankErosion (ε : ℝ≥0) :
    StrictRankErosion ε (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid))
      (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid)) :=
  strictRankErosion_fin_zero ε _ _

theorem noCoordinates_strictRankErosionDistance :
    strictRankErosionDistance
      (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid))
      (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid)) = 0 :=
  strictRankErosionDistance_fin_zero _ _

/-- Weak-pair erosion of the same two modules fails at every radius: the executed test fails
at radius `3`, and with no coordinates the predicate does not depend on the radius. -/
theorem noCoordinates_not_rankErosion (ε : ℝ≥0) :
    ¬ RankErosion ε (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid))
      (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hfail⟩ := runErosion_eq_fail _ _ _ _ noCoordinates_differ
  intro h
  apply hfail
  rw [CoordinateGrid.RankErosionGridExamples.rankErosion_zero_coordinates _ _ _ _ _
    Fin.elim0] at h ⊢
  exact h

/-- Hence their weak-pair distance is infinite, while their strict-pair distance is zero. -/
theorem noCoordinates_rankErosionDistance :
    rankErosionDistance
      (noCoordinates.grid.lan.obj (noCoordinates.toModule noCoordinates_valid))
      (noCoordinatesTwo.grid.lan.obj (noCoordinatesTwo.toModule noCoordinatesTwo_valid)) = ⊤ := by
  simp [rankErosionDistance, noCoordinates_not_rankErosion]

end NoCoordinates

end TDA.Persistence.StrictRankErosionExamples
