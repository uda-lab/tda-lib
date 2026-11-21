import TDA.Persistence.FiniteSimplicialErosion
import TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Rank erosion of the translated tetrahedron-boundary homology

Uniform translates of the tetrahedron-boundary grading have coordinatewise grade error the
translation gap, so their actual degree-one homology modules satisfy rank erosion at that gap.
Through the exact interleaving distance `min |t - s| (1/2)` the erosion distances are at most
the same value. Only upper bounds are claimed: the exact erosion distance of this family is
not computed here.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteSimplicialErosionExamples

open CategoryTheory TDA.Filtration TDA.Simplicial
open TDA.Persistence TDA.Persistence.RankResolutionDegreeTwoSimplicial
open scoped TDA.Persistence NNReal ENNReal

/-- The maximal grade error of two uniform translates is at most the translation gap. -/
theorem supGradeError_translatedGrading_le (s t : ℝ) :
    (translatedGrading s).supGradeError (translatedGrading t) ≤ ‖t - s‖₊ :=
  ((translatedGrading s).supGradeError_le_iff _ _).mpr (translatedGrading_grade_error s t)

/-- Two uniform translates satisfy weak-pair rank erosion at the translation gap. -/
theorem translatedHomology_rankErosion (k : Type u) [Field k] (s t : ℝ) :
    RankErosion ‖t - s‖₊ (translatedHomology k s) (translatedHomology k t) :=
  finiteSimplicialHomology_rankErosion k _ _ 1 (translatedGrading_grade_error s t)

/-- Two uniform translates satisfy extended-rank erosion at the translation gap. -/
theorem translatedHomology_eRankErosion (k : Type u) [Field k] (s t : ℝ) :
    ERankErosion ‖t - s‖₊ (translatedHomology k s) (translatedHomology k t) :=
  finiteSimplicialHomology_eRankErosion k _ _ 1 (translatedGrading_grade_error s t)

/-- The erosion distance of two uniform translates is at most the translation gap. It follows
from `rankErosionDistance_translatedHomology_le` and is kept to exercise the grade-error
route. -/
theorem rankErosionDistance_translatedHomology_le_gap (k : Type u) [Field k] (s t : ℝ) :
    rankErosionDistance (translatedHomology k s) (translatedHomology k t) ≤ ‖t - s‖₊ :=
  rankErosionDistance_finiteSimplicialHomology_le k _ _ 1 (translatedGrading_grade_error s t)

/-- The erosion distance of two uniform translates is at most their exact interleaving
distance `min |t - s| (1/2)`. -/
theorem rankErosionDistance_translatedHomology_le (k : Type u) [Field k] (s t : ℝ) :
    rankErosionDistance (translatedHomology k s) (translatedHomology k t) ≤
      ENNReal.ofReal (min |t - s| (1 / 2)) :=
  (rankErosionDistance_le_coordinateInterleavingDistance _ _).trans_eq
    (coordinateInterleavingDistance_translatedHomology k s t)

/-- The extended erosion distance of two uniform translates is at most
`min |t - s| (1/2)`. -/
theorem eRankErosionDistance_translatedHomology_le (k : Type u) [Field k] (s t : ℝ) :
    eRankErosionDistance (translatedHomology k s) (translatedHomology k t) ≤
      ENNReal.ofReal (min |t - s| (1 / 2)) :=
  (eRankErosionDistance_le_coordinateInterleavingDistance _ _).trans_eq
    (coordinateInterleavingDistance_translatedHomology k s t)

/-- A failed erosion test between two uniform translates forces the translation gap above
the tested radius. It follows from `lt_of_not_rankErosion_translatedHomology` and is kept to
exercise the grade-error route. -/
theorem lt_gap_of_not_rankErosion_translatedHomology (k : Type u) [Field k] (s t : ℝ)
    {ε : ℝ≥0} (hfail : ¬ RankErosion ε (translatedHomology k s) (translatedHomology k t)) :
    ε < ‖t - s‖₊ :=
  lt_of_not_rankErosion_finiteSimplicialHomology k _ _ 1
    (translatedGrading_grade_error s t) hfail

/-- A failed erosion test between two uniform translates forces the radius strictly below
`min |t - s| (1/2)`, through the failure certificate. -/
theorem lt_of_not_rankErosion_translatedHomology (k : Type u) [Field k] (s t : ℝ)
    {ε : ℝ≥0} (hfail : ¬ RankErosion ε (translatedHomology k s) (translatedHomology k t)) :
    (ε : ℝ≥0∞) < ENNReal.ofReal (min |t - s| (1 / 2)) := by
  obtain ⟨hlt, hle, -⟩ := finiteSimplicialHomology_rankErosion_failure_certificate k _ _ 1 hfail
  exact (hlt.trans_le hle).trans_eq (coordinateInterleavingDistance_translatedHomology k s t)

/-- Rational coefficients: translates by `0` and `1/4` erode at radius `1/4`. -/
example : RankErosion (1 / 4) (translatedHomology ℚ 0) (translatedHomology ℚ (1 / 4)) := by
  have h := translatedHomology_rankErosion ℚ 0 (1 / 4)
  have hgap : ‖(1 / 4 : ℝ) - 0‖₊ = 1 / 4 := by
    ext
    norm_num
  rwa [hgap] at h

/-- Characteristic two: the erosion distance of any two translates is at most `1/2`. -/
example (s t : ℝ) :
    rankErosionDistance (translatedHomology (ZMod 2) s) (translatedHomology (ZMod 2) t) ≤
      ENNReal.ofReal (1 / 2) :=
  (rankErosionDistance_translatedHomology_le (ZMod 2) s t).trans
    (ENNReal.ofReal_le_ofReal (min_le_right _ _))

/-- Characteristic two: no erosion test fails between two translates at radius `1/2`. -/
example (s t : ℝ) :
    RankErosion (1 / 2) (translatedHomology (ZMod 2) s) (translatedHomology (ZMod 2) t) := by
  by_contra hfail
  have h := lt_of_not_rankErosion_translatedHomology (ZMod 2) s t hfail
  have h2 : ENNReal.ofReal (min |t - s| (1 / 2)) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by simp)
  exact (h.trans_le h2).false

end TDA.Persistence.FiniteSimplicialErosionExamples
