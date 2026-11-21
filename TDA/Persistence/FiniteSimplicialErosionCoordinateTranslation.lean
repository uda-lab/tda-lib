import TDA.Persistence.FiniteSimplicialErosion
import TDA.Persistence.RankResolutionDegreeTwoSimplicialCoordinateTranslation

/-!
# Exact erosion distance of coordinate translates of the simplicial witness

Translating the tetrahedron-boundary grading by independent signed coordinate vectors `u` and
`v` gives a maximal grade error equal to the coordinate gap `max |v₀ - u₀| |v₁ - u₁|`. The
actual degree-one homology modules have both erosion distances at most the exact interleaving
distance `min (max |v₀ - u₀| |v₁ - u₁|) (1/2)`.

The matching lower bound comes from actual structure maps, not from the interleaving distance.
If `ε < v i - u i` in some coordinate `i` and `2ε < 1`, the widened diagonal test at the `i`-th
birth of the `u`-translate plus the radius sees a surviving birth map of the `u`-translate
against a zero fiber of the `v`-translate, so erosion fails. Both erosion distances therefore
equal `min (max |v₀ - u₀| |v₁ - u₁|) (1/2)`, which is also the interleaving distance.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

/-- The maximal grade error of two coordinate translates is exactly the coordinate gap. -/
theorem supGradeError_coordinateTranslatedGrading (u v : Fin 2 → ℝ) :
    (coordinateTranslatedGrading u).supGradeError (coordinateTranslatedGrading v) =
      coordinateTranslationGap u v := by
  refine le_antisymm (((coordinateTranslatedGrading u).supGradeError_le_iff _ _).mpr
    (coordinateTranslatedGrading_grade_error u v)) ?_
  have hface : ({0} : Finset (Fin 4)) ∈ boundaryTetrahedron.toPre := by decide
  have h : ∀ i : Fin 2, |v i - u i| ≤
      ((coordinateTranslatedGrading u).supGradeError (coordinateTranslatedGrading v) : ℝ) := by
    intro i
    have hi := (coordinateTranslatedGrading u).abs_grade_sub_le_supGradeError
      (coordinateTranslatedGrading v) ⟨{0}, hface⟩ i
    rw [coordinateTranslatedGrading_grade, coordinateTranslatedGrading_grade,
      show ∀ x : ℝ, x + u i - (x + v i) = u i - v i from fun x => by ring,
      abs_sub_comm] at hi
    exact hi
  rw [← NNReal.coe_le_coe, coordinateTranslationGap_coe]
  exact max_le (h 0) (h 1)

/-- Below the signed gap in one coordinate and half the diagonal lifetime, erosion fails at the
diagonal pair based at that coordinate's birth of the earlier translate plus the radius: the
widened map of the earlier translate survives while the later translate has a zero fiber
there. -/
theorem coordinateTranslatedHomology_not_rankErosion_of_lt_sub (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) (i : Fin 2) (ε : ℝ≥0) (hgap : (ε : ℝ) < v i - u i)
    (hlife : 2 * (ε : ℝ) < 1) :
    ¬ RankErosion ε (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) := by
  rintro ⟨h, -⟩
  let a : Fin 2 → ℝ := fun j => coordinateTranslatedBirth i u j + (ε : ℝ)
  have hle := h a a le_rfl
  have hzero : rankOfStructureMap (coordinateTranslatedHomology k v) (le_refl a) = 0 := by
    apply rankOfStructureMap_eq_zero_of_isZero
    apply coordinateTranslatedHomology_isZero_of_coordinate_lt k v i
    simp only [a, coordinateTranslatedBirth_selected]
    linarith
  have hsurvive : ∀ {p q : Fin 2 → ℝ} (hpq : p ≤ q), p = coordinateTranslatedBirth i u →
      q = (fun j => coordinateTranslatedBirth i u j + 2 * (ε : ℝ)) →
      structureMap (coordinateTranslatedHomology k u) hpq ≠ 0 := by
    rintro p q hpq rfl rfl
    exact coordinateTranslatedHomology_birth_structureMap_ne_zero k u i (2 * (ε : ℝ))
      (by positivity) hlife
  have hpos : 1 ≤ rankOfStructureMap (coordinateTranslatedHomology k u)
      (erosionWide_le ε (le_refl a)) := by
    apply one_le_rankOfStructureMap_of_ne_zero
    apply hsurvive
    · funext j
      simp only [erosionLower, a]
      ring
    · funext j
      simp only [erosionUpper, a]
      ring
  omega

/-- Two coordinate translates fail weak-pair rank erosion at every radius strictly below
`min (max |v₀ - u₀| |v₁ - u₁|) (1/2)`. -/
theorem coordinateTranslatedHomology_not_rankErosion (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) (ε : ℝ≥0)
    (hε : (ε : ℝ) < min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) :
    ¬ RankErosion ε (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) := by
  have hlife : 2 * (ε : ℝ) < 1 := by
    have := hε.trans_le (min_le_right _ _)
    linarith
  have hgap : ∃ i : Fin 2, (ε : ℝ) < |v i - u i| := by
    rcases lt_max_iff.mp (hε.trans_le (min_le_left _ _)) with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  obtain ⟨i, hi⟩ := hgap
  rcases le_total (u i) (v i) with huv | hvu
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)] at hi
    exact coordinateTranslatedHomology_not_rankErosion_of_lt_sub k u v i ε hi hlife
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hvu)] at hi
    exact fun h =>
      coordinateTranslatedHomology_not_rankErosion_of_lt_sub k v u i ε hi hlife h.symm

/-- Two coordinate translates fail extended-rank erosion at every radius strictly below
`min (max |v₀ - u₀| |v₁ - u₁|) (1/2)`. -/
theorem coordinateTranslatedHomology_not_eRankErosion (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) (ε : ℝ≥0)
    (hε : (ε : ℝ) < min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) :
    ¬ ERankErosion ε (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) := by
  rw [eRankErosion_iff_rankErosion]
  exact coordinateTranslatedHomology_not_rankErosion k u v ε hε

/-- The weak-pair rank erosion distance of two coordinate translates is exactly
`min (max |v₀ - u₀| |v₁ - u₁|) (1/2)`. The lower bound comes from the failed tests of
`coordinateTranslatedHomology_not_rankErosion`, not from the interleaving distance. -/
theorem rankErosionDistance_coordinateTranslatedHomology (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) :
    rankErosionDistance (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) =
      ENNReal.ofReal (min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) := by
  refine le_antisymm ((rankErosionDistance_le_coordinateInterleavingDistance _ _).trans_eq
    (coordinateInterleavingDistance_coordinateTranslatedHomology k u v)) ?_
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  exact le_rankErosionDistance_of_not_rankErosion
    (coordinateTranslatedHomology_not_rankErosion k u v r (ENNReal.coe_lt_ofReal.mp hr))

/-- The extended-rank erosion distance of two coordinate translates is exactly
`min (max |v₀ - u₀| |v₁ - u₁|) (1/2)`. -/
theorem eRankErosionDistance_coordinateTranslatedHomology (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) :
    eRankErosionDistance (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) =
      ENNReal.ofReal (min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) := by
  rw [eRankErosionDistance_eq_rankErosionDistance,
    rankErosionDistance_coordinateTranslatedHomology]

/-- On coordinate translates the weak-pair rank erosion distance equals the interleaving
distance. -/
theorem rankErosionDistance_coordinateTranslatedHomology_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    rankErosionDistance (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) =
      coordinateInterleavingDistance (coordinateTranslatedHomology k u)
        (coordinateTranslatedHomology k v) := by
  rw [rankErosionDistance_coordinateTranslatedHomology,
    coordinateInterleavingDistance_coordinateTranslatedHomology]

/-- On coordinate translates the extended-rank erosion distance equals the interleaving
distance. -/
theorem eRankErosionDistance_coordinateTranslatedHomology_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    eRankErosionDistance (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) =
      coordinateInterleavingDistance (coordinateTranslatedHomology k u)
        (coordinateTranslatedHomology k v) := by
  rw [eRankErosionDistance_coordinateTranslatedHomology,
    coordinateInterleavingDistance_coordinateTranslatedHomology]

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
