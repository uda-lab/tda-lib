import TDA.Persistence.FiniteSimplicialErosion
import TDA.Persistence.FiniteSimplicialErosionTranslation
import TDA.Persistence.FiniteSimplicialErosionCoordinateTranslation
import TDA.Persistence.FiniteSimplicialErosionScaledTranslation
import TDA.Persistence.FiniteSimplicialErosionScaling
import TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Rank erosion of the translated tetrahedron-boundary homology

Uniform translates of the tetrahedron-boundary grading have coordinatewise grade error at
most the translation gap (with equality for the maximal error,
`supGradeError_translatedGrading`), so their actual degree-one homology modules satisfy rank
erosion at that gap. Through the exact interleaving distance `min |t - s| (1/2)` the erosion
distances are at most the same value; `FiniteSimplicialErosionTranslation` proves the matching
lower bound from failed erosion tests. The radius `1/8` between the translates by `0` and
`1/4` is a concrete failing radius for the failure certificate. Coordinate translates by
independent signed vectors satisfy erosion at the coordinate gap `coordinateTranslationGap`;
`FiniteSimplicialErosionCoordinateTranslation` gives their exact erosion distance, and the
radius `1/8` between the translates by `0` and by the vector with coordinates `1/8` and `-1/4`
is a concrete failing radius. Delays of a common positive scaling satisfy erosion at the delay
gap; `FiniteSimplicialErosionScaledTranslation` gives their exact erosion distance, and the
radius `1/8` between the delays `0` and `1/2` under the scale with coordinates `1` and `1/4` is
a concrete failing radius at which the longer arm witnesses the failure. A positive scaling has
erosion distance to the zero module exactly half its scaled lifetime
(`FiniteSimplicialErosionScaling`); under the scale with coordinates `1` and `1/4` the radius
`1/8` is a concrete failing radius, consumed by the finitely presented certificate.
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

/-- A concrete failing radius: the translates by `0` and `1/4` fail erosion at `1/8`. -/
theorem translatedHomology_not_rankErosion_eighth (k : Type u) [Field k] :
    ¬ RankErosion (1 / 8) (translatedHomology k 0) (translatedHomology k (1 / 4)) := by
  apply translatedHomology_not_rankErosion
  norm_num [abs_of_pos]

/-- The failure certificate at the concrete failing radius `1/8` between the translates by
`0` and `1/4`; here every quantity after the radius equals `1/4`
(`rankErosionDistance_translatedHomology`, `coordinateInterleavingDistance_translatedHomology`,
`supGradeError_translatedGrading`). -/
theorem translatedHomology_rankErosion_failure_certificate_eighth (k : Type u) [Field k] :
    ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance (translatedHomology k 0) (translatedHomology k (1 / 4)) ∧
      rankErosionDistance (translatedHomology k 0) (translatedHomology k (1 / 4)) ≤
        coordinateInterleavingDistance (translatedHomology k 0)
          (translatedHomology k (1 / 4)) ∧
      coordinateInterleavingDistance (translatedHomology k 0)
          (translatedHomology k (1 / 4)) ≤
        (translatedGrading 0).supGradeError (translatedGrading (1 / 4)) :=
  finiteSimplicialHomology_rankErosion_failure_certificate k _ _ 1
    (translatedHomology_not_rankErosion_eighth k)

/-- Rational coefficients: the erosion distance of the translates by `0` and `1/4` is
exactly `1/4`. -/
example : rankErosionDistance (translatedHomology ℚ 0) (translatedHomology ℚ (1 / 4)) =
    ENNReal.ofReal (1 / 4) := by
  rw [rankErosionDistance_translatedHomology]
  norm_num [abs_of_pos]

/-- Characteristic two: the extended erosion distance of translates at least `1/2` apart is
exactly `1/2`. -/
example (s t : ℝ) (h : 1 / 2 ≤ |t - s|) :
    eRankErosionDistance (translatedHomology (ZMod 2) s) (translatedHomology (ZMod 2) t) =
      ENNReal.ofReal (1 / 2) := by
  rw [eRankErosionDistance_translatedHomology, min_eq_right h]

/-- Characteristic two: by the certificate, the concrete failing radius `1/8` is strictly
below the erosion distance. -/
example : ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
    rankErosionDistance (translatedHomology (ZMod 2) 0) (translatedHomology (ZMod 2) (1 / 4)) :=
  (translatedHomology_rankErosion_failure_certificate_eighth (ZMod 2)).1

/-! ### Coordinate translates -/

/-- Two coordinate translates satisfy weak-pair rank erosion at the coordinate gap. -/
theorem coordinateTranslatedHomology_rankErosion (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    RankErosion (coordinateTranslationGap u v) (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v) :=
  finiteSimplicialHomology_rankErosion k _ _ 1 (coordinateTranslatedGrading_grade_error u v)

/-- Two coordinate translates satisfy extended-rank erosion at the coordinate gap. -/
theorem coordinateTranslatedHomology_eRankErosion (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    ERankErosion (coordinateTranslationGap u v) (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v) :=
  finiteSimplicialHomology_eRankErosion k _ _ 1 (coordinateTranslatedGrading_grade_error u v)

/-- The erosion distance of two coordinate translates is at most the coordinate gap. It
follows from `rankErosionDistance_coordinateTranslatedHomology` and is kept to exercise the
grade-error route. -/
theorem rankErosionDistance_coordinateTranslatedHomology_le_gap (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) :
    rankErosionDistance (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) ≤
      coordinateTranslationGap u v :=
  rankErosionDistance_finiteSimplicialHomology_le k _ _ 1
    (coordinateTranslatedGrading_grade_error u v)

/-- A failed erosion test between two coordinate translates forces the coordinate gap above
the tested radius. It follows from `rankErosionDistance_coordinateTranslatedHomology` and is
kept to exercise the grade-error route. -/
theorem lt_gap_of_not_rankErosion_coordinateTranslatedHomology (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) {ε : ℝ≥0}
    (hfail : ¬ RankErosion ε (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v)) :
    ε < coordinateTranslationGap u v :=
  lt_of_not_rankErosion_finiteSimplicialHomology k _ _ 1
    (coordinateTranslatedGrading_grade_error u v) hfail

/-- A concrete failing radius: the translates by `0` and by the vector with coordinates `1/8`
and `-1/4` fail erosion at `1/8`. The gap `1/4` is attained in the second coordinate with a
negative sign, so the witness is the diagonal test at the second birth of the translate by that
vector, which is earlier in the second coordinate. -/
theorem coordinateTranslatedHomology_not_rankErosion_eighth (k : Type u) [Field k] :
    ¬ RankErosion (1 / 8) (coordinateTranslatedHomology k 0)
      (coordinateTranslatedHomology k (![1 / 8, -1 / 4] : Fin 2 → ℝ)) := by
  apply coordinateTranslatedHomology_not_rankErosion
  norm_num [abs_of_pos]

/-- The failure certificate at the concrete failing radius `1/8` between the translates by `0`
and by the vector with coordinates `1/8` and `-1/4`; here every quantity after the radius
equals `1/4` (`rankErosionDistance_coordinateTranslatedHomology`,
`coordinateInterleavingDistance_coordinateTranslatedHomology`,
`supGradeError_coordinateTranslatedGrading`). -/
theorem coordinateTranslatedHomology_rankErosion_failure_certificate_eighth
    (k : Type u) [Field k] :
    ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance (coordinateTranslatedHomology k 0)
          (coordinateTranslatedHomology k (![1 / 8, -1 / 4] : Fin 2 → ℝ)) ∧
      rankErosionDistance (coordinateTranslatedHomology k 0)
          (coordinateTranslatedHomology k (![1 / 8, -1 / 4] : Fin 2 → ℝ)) ≤
        coordinateInterleavingDistance (coordinateTranslatedHomology k 0)
          (coordinateTranslatedHomology k (![1 / 8, -1 / 4] : Fin 2 → ℝ)) ∧
      coordinateInterleavingDistance (coordinateTranslatedHomology k 0)
          (coordinateTranslatedHomology k (![1 / 8, -1 / 4] : Fin 2 → ℝ)) ≤
        (coordinateTranslatedGrading 0).supGradeError
          (coordinateTranslatedGrading (![1 / 8, -1 / 4] : Fin 2 → ℝ)) :=
  finiteSimplicialHomology_rankErosion_failure_certificate k _ _ 1
    (coordinateTranslatedHomology_not_rankErosion_eighth k)

/-- The maximal grade error of the fixture pair is `1/4`. -/
example : (coordinateTranslatedGrading 0).supGradeError
    (coordinateTranslatedGrading (![1 / 8, -1 / 4] : Fin 2 → ℝ)) = 1 / 4 := by
  rw [supGradeError_coordinateTranslatedGrading]
  ext
  norm_num [abs_of_pos]

/-- Rational coefficients: the erosion distance of the translates by `0` and by the vector
with coordinates `1/8` and `-1/4` is exactly `1/4`. -/
example : rankErosionDistance (coordinateTranslatedHomology ℚ 0)
    (coordinateTranslatedHomology ℚ (![1 / 8, -1 / 4] : Fin 2 → ℝ)) =
      ENNReal.ofReal (1 / 4) := by
  rw [rankErosionDistance_coordinateTranslatedHomology]
  norm_num [abs_of_pos]

/-- Characteristic two: a translate in the second coordinate only, by `1/3`, has extended
erosion distance exactly `1/3` from the untranslated module. -/
example : eRankErosionDistance (coordinateTranslatedHomology (ZMod 2) 0)
    (coordinateTranslatedHomology (ZMod 2) (![0, 1 / 3] : Fin 2 → ℝ)) =
      ENNReal.ofReal (1 / 3) := by
  rw [eRankErosionDistance_coordinateTranslatedHomology]
  norm_num [abs_of_pos]

/-- Characteristic two: the extended erosion distance of coordinate translates with a gap of
at least `1/2` is exactly `1/2`. -/
example (u v : Fin 2 → ℝ) (h : 1 / 2 ≤ max |v 0 - u 0| |v 1 - u 1|) :
    eRankErosionDistance (coordinateTranslatedHomology (ZMod 2) u)
      (coordinateTranslatedHomology (ZMod 2) v) = ENNReal.ofReal (1 / 2) := by
  rw [eRankErosionDistance_coordinateTranslatedHomology, min_eq_right h]

/-- Characteristic two: by the certificate, the concrete failing radius `1/8` is strictly
below the erosion distance. -/
example : ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
    rankErosionDistance (coordinateTranslatedHomology (ZMod 2) 0)
      (coordinateTranslatedHomology (ZMod 2) (![1 / 8, -1 / 4] : Fin 2 → ℝ)) :=
  (coordinateTranslatedHomology_rankErosion_failure_certificate_eighth (ZMod 2)).1

/-! ### Scaled translates -/

/-- Two delays of the same positive scaling satisfy weak-pair rank erosion at the delay gap. -/
theorem scaledTranslatedHomology_rankErosion (k : Type u) [Field k] (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t u : ℝ) :
    RankErosion (Real.toNNReal |t - u|) (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) :=
  finiteSimplicialHomology_rankErosion k _ _ 1 (scaledTranslatedGrading_grade_error s hs t u)

/-- Two delays of the same positive scaling satisfy extended-rank erosion at the delay gap. -/
theorem scaledTranslatedHomology_eRankErosion (k : Type u) [Field k] (s : Fin 2 → ℝ)
    (hs : ∀ i, 0 < s i) (t u : ℝ) :
    ERankErosion (Real.toNNReal |t - u|) (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) :=
  finiteSimplicialHomology_eRankErosion k _ _ 1 (scaledTranslatedGrading_grade_error s hs t u)

/-- The erosion distance of two delays of the same positive scaling is at most the delay gap.
It follows from `rankErosionDistance_scaledTranslatedHomology` and is kept to exercise the
grade-error route. -/
theorem rankErosionDistance_scaledTranslatedHomology_le_gap (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    rankErosionDistance (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) ≤ Real.toNNReal |t - u| :=
  rankErosionDistance_finiteSimplicialHomology_le k _ _ 1
    (scaledTranslatedGrading_grade_error s hs t u)

/-- A failed erosion test between two delays of the same positive scaling forces the delay gap
above the tested radius. It follows from `rankErosionDistance_scaledTranslatedHomology` and is
kept to exercise the grade-error route. -/
theorem lt_gap_of_not_rankErosion_scaledTranslatedHomology (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) {ε : ℝ≥0}
    (hfail : ¬ RankErosion ε (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u)) :
    ε < Real.toNNReal |t - u| :=
  lt_of_not_rankErosion_finiteSimplicialHomology k _ _ 1
    (scaledTranslatedGrading_grade_error s hs t u) hfail

/-- The anisotropic fixture scale with coordinates `1` and `1/4` has scaled lifetime `1/2`,
the lifetime of its B-arm; its A-arm lives only for `1/4`. -/
example : scaledLifetime (![1, 1 / 4] : Fin 2 → ℝ) = 1 / 2 ∧
    scaledArmLifetimeA (![1, 1 / 4] : Fin 2 → ℝ) = 1 / 4 := by
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]

/-- A concrete failing radius: under the scale with coordinates `1` and `1/4`, the delays `0`
and `1/2` fail erosion at `1/8`. The witness is the diagonal test at the B-arm birth of the
`0`-delayed module plus `1/8`; the A-arm test at the same radius sees a zero widened map. -/
theorem scaledTranslatedHomology_not_rankErosion_eighth (k : Type u) [Field k] :
    ¬ RankErosion (1 / 8)
      (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) 0)
      (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) (1 / 2)) := by
  apply scaledTranslatedHomology_not_rankErosion
  norm_num [abs_of_pos, scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]

/-- At the fixture radius `1/8` the widened A-arm map of the `0`-delayed module, across
`2 · (1/8) = 1/4`, is zero, so the A-arm diagonal test would not witness the failure. -/
example (k : Type u) [Field k] :
    structureMap
      (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) 0)
      (show scaledTranslatedBirthA (![1, 1 / 4] : Fin 2 → ℝ) 0 ≤
        (fun i => scaledTranslatedBirthA (![1, 1 / 4] : Fin 2 → ℝ) 0 i + 1 / 4) from
          fun _ => le_add_of_nonneg_right (by norm_num)) = 0 := by
  by_contra h
  have h' := (scaledTranslatedHomology_armA_structureMap_ne_zero_iff k _ _ 0 (1 / 4)
    (by norm_num)).1 h
  norm_num [scaledArmLifetimeA] at h'

/-- The failure certificate at the concrete failing radius `1/8` between the delays `0` and
`1/2` under the scale with coordinates `1` and `1/4`. Here the erosion and interleaving
distances equal `1/4` (`rankErosionDistance_scaledTranslatedHomology`,
`coordinateInterleavingDistance_scaledTranslatedHomology`), while the maximal grade error is
`1/2` (`supGradeError_scaledTranslatedGrading`), so the last inequality is strict. -/
theorem scaledTranslatedHomology_rankErosion_failure_certificate_eighth
    (k : Type u) [Field k] :
    ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) 0)
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) (1 / 2)) ∧
      rankErosionDistance
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) 0)
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) (1 / 2)) ≤
        coordinateInterleavingDistance
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) 0)
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) (1 / 2)) ∧
      coordinateInterleavingDistance
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) 0)
          (scaledTranslatedHomology k (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) (1 / 2)) ≤
        (scaledTranslatedGrading (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) 0).supGradeError
          (scaledTranslatedGrading (![1, 1 / 4] : Fin 2 → ℝ)
            (fun i => by fin_cases i <;> norm_num) (1 / 2)) :=
  finiteSimplicialHomology_rankErosion_failure_certificate k _ _ 1
    (scaledTranslatedHomology_not_rankErosion_eighth k)

/-- The maximal grade error of the fixture pair is `1/2`. -/
example :
    (scaledTranslatedGrading (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) 0).supGradeError
      (scaledTranslatedGrading (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) (1 / 2)) = 1 / 2 := by
  rw [supGradeError_scaledTranslatedGrading]
  ext
  norm_num [abs_of_pos]

/-- Rational coefficients: the erosion distance of the fixture pair is exactly `1/4`, strictly
below its maximal grade error `1/2`. -/
example :
    rankErosionDistance
      (scaledTranslatedHomology ℚ (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) 0)
      (scaledTranslatedHomology ℚ (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) (1 / 2)) =
      ENNReal.ofReal (1 / 4) := by
  rw [rankErosionDistance_scaledTranslatedHomology]
  norm_num [abs_of_pos, scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]

/-- Characteristic two: under the fixture scale, delays at most `1/4` apart have extended
erosion distance exactly their gap. -/
example (t u : ℝ) (h : |t - u| ≤ 1 / 4) :
    eRankErosionDistance
      (scaledTranslatedHomology (ZMod 2) (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) t)
      (scaledTranslatedHomology (ZMod 2) (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) u) =
      ENNReal.ofReal |t - u| := by
  rw [eRankErosionDistance_scaledTranslatedHomology, min_eq_left]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]
  exact h

/-- Characteristic two: by the certificate, the concrete failing radius `1/8` is strictly
below the erosion distance. -/
example : ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
    rankErosionDistance
      (scaledTranslatedHomology (ZMod 2) (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) 0)
      (scaledTranslatedHomology (ZMod 2) (![1, 1 / 4] : Fin 2 → ℝ)
        (fun i => by fin_cases i <;> norm_num) (1 / 2)) :=
  (scaledTranslatedHomology_rankErosion_failure_certificate_eighth (ZMod 2)).1

/-! ### Scaled family against zero -/

section ScaledZero

open scoped ZeroObject

/-- A concrete failing radius against zero: under the scale with coordinates `1` and `1/4`,
the scaled module fails erosion against the zero module at `1/8`. The witness is the diagonal
test at the B-arm birth plus `1/8`; the A-arm test at the same radius sees a zero widened
map. -/
theorem scaledHomology_not_rankErosion_zero_eighth (k : Type u) [Field k] :
    ¬ RankErosion (1 / 8)
      (scaledHomology k (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := by
  apply scaledHomology_not_rankErosion_zero
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]

/-- At the fixture radius `1/8` the widened A-arm map of the scaled module, across
`2 · (1/8) = 1/4`, is zero, so the A-arm diagonal test would not witness the failure. -/
example (k : Type u) [Field k] :
    structureMap
      (scaledHomology k (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
      (show scaledBirthA (![1, 1 / 4] : Fin 2 → ℝ) ≤
        (fun i => scaledBirthA (![1, 1 / 4] : Fin 2 → ℝ) i + 1 / 4) from
          fun _ => le_add_of_nonneg_right (by norm_num)) = 0 :=
  scaledHomology_armA_structureMap_zero_of_ge k _ _ (1 / 4) (by norm_num)
    (by norm_num [scaledArmLifetimeA])

/-- The failure certificate at the concrete failing radius `1/8` against zero. The zero module
is not the homology of a grading of the same complex in the same degree, so the general
finitely presented certificate is the consumer, with no grade-error term. Both distances equal
`1/4` (`rankErosionDistance_scaledHomology_zero`,
`coordinateInterleavingDistance_scaledHomology_zero`). -/
theorem scaledHomology_rankErosion_failure_certificate_zero_eighth (k : Type u) [Field k] :
    ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance
          (scaledHomology k (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ∧
      rankErosionDistance
          (scaledHomology k (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ≤
        coordinateInterleavingDistance
          (scaledHomology k (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) :=
  GradedFree.finitelyPresented_rankErosion_failure_certificate
    (finiteSimplicialHomology_finitelyPresented k _ 1) GradedFree.finitelyPresented_zero
    (scaledHomology_not_rankErosion_zero_eighth k)

/-- Rational coefficients: the erosion distance of the fixture to zero is exactly `1/4`. -/
example :
    rankErosionDistance
      (scaledHomology ℚ (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
      (0 : PModule.{0,0,0} ℚ (Fin 2 → ℝ)) = ENNReal.ofReal (1 / 4) := by
  rw [rankErosionDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]

/-- Characteristic two: the extended erosion distance of the fixture to zero is exactly
`1/4`. -/
example :
    eRankErosionDistance
      (scaledHomology (ZMod 2) (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
      (0 : PModule.{0,0,0} (ZMod 2) (Fin 2 → ℝ)) = ENNReal.ofReal (1 / 4) := by
  rw [eRankErosionDistance_scaledHomology_zero]
  norm_num [scaledLifetime, scaledArmLifetimeA, scaledArmLifetimeB]

/-- Characteristic two: by the certificate, the concrete failing radius `1/8` is strictly
below the erosion distance to zero. -/
example : ((1 / 8 : ℝ≥0) : ℝ≥0∞) <
    rankErosionDistance
      (scaledHomology (ZMod 2) (![1, 1 / 4] : Fin 2 → ℝ) (fun i => by fin_cases i <;> norm_num))
      (0 : PModule.{0,0,0} (ZMod 2) (Fin 2 → ℝ)) :=
  (scaledHomology_rankErosion_failure_certificate_zero_eighth (ZMod 2)).1

end ScaledZero

end TDA.Persistence.FiniteSimplicialErosionExamples
