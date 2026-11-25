import TDA.Persistence.FiniteSimplicialErosion
import TDA.Persistence.RankResolutionDegreeTwoSimplicialScaledTranslation

/-!
# Exact erosion distance of scaled uniform translates of the simplicial witness

Positively scaling both coordinates of the tetrahedron-boundary grading by `s` and adding a
common signed delay `t` or `u` gives a maximal grade error equal to the delay gap `|t - u|`.
The actual degree-one homology modules have both erosion distances at most the exact
interleaving distance `min |t - u| (scaledLifetime s / 2)`.

The matching lower bound comes from actual structure maps, not from the interleaving distance.
If `ε < u - t` and `2ε < scaledLifetime s`, the widened diagonal test at the birth of the
longer arm of the `t`-delayed module plus the radius sees a surviving arm map of the
`t`-delayed module against a zero fiber of the `u`-delayed module, so erosion fails. The
longer arm is needed: under an anisotropic scale the shorter arm's widened map can already be
zero. Both erosion distances therefore equal `min |t - u| (scaledLifetime s / 2)`, which is
also the interleaving distance.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

/-- The maximal grade error of two delays of the same positive scaling is exactly the delay
gap. -/
theorem supGradeError_scaledTranslatedGrading (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i)
    (t u : ℝ) :
    (scaledTranslatedGrading s hs t).supGradeError (scaledTranslatedGrading s hs u) =
      Real.toNNReal |t - u| := by
  refine le_antisymm (((scaledTranslatedGrading s hs t).supGradeError_le_iff _ _).mpr
    (scaledTranslatedGrading_grade_error s hs t u)) ?_
  have hface : ({0} : Finset (Fin 4)) ∈ boundaryTetrahedron.toPre := by decide
  have h := (scaledTranslatedGrading s hs t).abs_grade_sub_le_supGradeError
    (scaledTranslatedGrading s hs u) ⟨{0}, hface⟩ 0
  rw [scaledTranslatedGrading_grade, scaledTranslatedGrading_grade,
    show ∀ x : ℝ, x + t - (x + u) = t - u from fun x => by ring] at h
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (abs_nonneg _)]
  exact h

/-- Below the signed delay gap and half the scaled lifetime, erosion fails at the diagonal pair
based at the birth of the longer arm of the `t`-delayed module plus the radius: that arm's
widened map survives while the `u`-delayed module has a zero fiber there. -/
theorem scaledTranslatedHomology_not_rankErosion_of_lt_sub (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) (ε : ℝ≥0)
    (hgap : (ε : ℝ) < u - t) (hlife : 2 * (ε : ℝ) < scaledLifetime s) :
    ¬ RankErosion ε (scaledTranslatedHomology k s hs t) (scaledTranslatedHomology k s hs u) := by
  rintro ⟨h, -⟩
  have h2ε : 0 ≤ 2 * (ε : ℝ) := by positivity
  -- Pick the longer arm: its birth `b`, the coordinate `j` where `b j = t`, and its survival.
  obtain ⟨b, j, hbj, hsurv⟩ : ∃ (b : Fin 2 → ℝ) (j : Fin 2), b j = t ∧
      ∀ hle : b ≤ (fun i => b i + 2 * (ε : ℝ)),
        structureMap (scaledTranslatedHomology k s hs t) hle ≠ 0 := by
    rcases le_total (scaledArmLifetimeA s) (scaledArmLifetimeB s) with hAB | hBA
    · refine ⟨scaledTranslatedBirthB s t, 1, scaledTranslatedBirthB_one s t, fun _ => ?_⟩
      apply (scaledTranslatedHomology_armB_structureMap_ne_zero_iff k s hs t _ h2ε).2
      rwa [scaledLifetime, max_eq_right hAB] at hlife
    · refine ⟨scaledTranslatedBirthA s t, 0, scaledTranslatedBirthA_zero s t, fun _ => ?_⟩
      apply (scaledTranslatedHomology_armA_structureMap_ne_zero_iff k s hs t _ h2ε).2
      rwa [scaledLifetime, max_eq_left hBA] at hlife
  let a : Fin 2 → ℝ := fun i => b i + (ε : ℝ)
  have hle := h a a le_rfl
  have hzero : rankOfStructureMap (scaledTranslatedHomology k s hs u) (le_refl a) = 0 := by
    apply rankOfStructureMap_eq_zero_of_isZero
    apply scaledTranslatedHomology_isZero_of_coordinate_lt k s hs u a j
    simp only [a, hbj]
    linarith
  have hsurvive : ∀ {p q : Fin 2 → ℝ} (hpq : p ≤ q), p = b →
      q = (fun i => b i + 2 * (ε : ℝ)) →
      structureMap (scaledTranslatedHomology k s hs t) hpq ≠ 0 := by
    rintro p q hpq rfl rfl
    exact hsurv hpq
  have hpos : 1 ≤ rankOfStructureMap (scaledTranslatedHomology k s hs t)
      (erosionWide_le ε (le_refl a)) := by
    apply one_le_rankOfStructureMap_of_ne_zero
    apply hsurvive
    · funext i
      simp only [erosionLower, a]
      ring
    · funext i
      simp only [erosionUpper, a]
      ring
  omega

/-- Two delays of the same positive scaling fail weak-pair rank erosion at every radius
strictly below `min |t - u| (scaledLifetime s / 2)`. -/
theorem scaledTranslatedHomology_not_rankErosion (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) (ε : ℝ≥0)
    (hε : (ε : ℝ) < min |t - u| (scaledLifetime s / 2)) :
    ¬ RankErosion ε (scaledTranslatedHomology k s hs t) (scaledTranslatedHomology k s hs u) := by
  have hgap : (ε : ℝ) < |t - u| := hε.trans_le (min_le_left _ _)
  have hlife : 2 * (ε : ℝ) < scaledLifetime s := by
    have := hε.trans_le (min_le_right _ _)
    linarith
  rcases le_total t u with htu | hut
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htu)] at hgap
    exact scaledTranslatedHomology_not_rankErosion_of_lt_sub k s hs t u ε hgap hlife
  · rw [abs_of_nonneg (sub_nonneg.mpr hut)] at hgap
    exact fun h =>
      scaledTranslatedHomology_not_rankErosion_of_lt_sub k s hs u t ε hgap hlife h.symm

/-- Two delays of the same positive scaling fail extended-rank erosion at every radius
strictly below `min |t - u| (scaledLifetime s / 2)`. -/
theorem scaledTranslatedHomology_not_eRankErosion (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) (ε : ℝ≥0)
    (hε : (ε : ℝ) < min |t - u| (scaledLifetime s / 2)) :
    ¬ ERankErosion ε (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) := by
  rw [eRankErosion_iff_rankErosion]
  exact scaledTranslatedHomology_not_rankErosion k s hs t u ε hε

/-- The weak-pair rank erosion distance of two delays of the same positive scaling is exactly
`min |t - u| (scaledLifetime s / 2)`. The lower bound comes from the failed tests of
`scaledTranslatedHomology_not_rankErosion`, not from the interleaving distance. -/
theorem rankErosionDistance_scaledTranslatedHomology (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    rankErosionDistance (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) =
        ENNReal.ofReal (min |t - u| (scaledLifetime s / 2)) := by
  refine le_antisymm ((rankErosionDistance_le_coordinateInterleavingDistance _ _).trans_eq
    (coordinateInterleavingDistance_scaledTranslatedHomology k s hs t u)) ?_
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  exact le_rankErosionDistance_of_not_rankErosion
    (scaledTranslatedHomology_not_rankErosion k s hs t u r (ENNReal.coe_lt_ofReal.mp hr))

/-- The extended-rank erosion distance of two delays of the same positive scaling is exactly
`min |t - u| (scaledLifetime s / 2)`. -/
theorem eRankErosionDistance_scaledTranslatedHomology (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    eRankErosionDistance (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) =
        ENNReal.ofReal (min |t - u| (scaledLifetime s / 2)) := by
  rw [eRankErosionDistance_eq_rankErosionDistance,
    rankErosionDistance_scaledTranslatedHomology]

/-- On delays of the same positive scaling the weak-pair rank erosion distance equals the
interleaving distance. -/
theorem rankErosionDistance_scaledTranslatedHomology_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    rankErosionDistance (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) =
        coordinateInterleavingDistance (scaledTranslatedHomology k s hs t)
          (scaledTranslatedHomology k s hs u) := by
  rw [rankErosionDistance_scaledTranslatedHomology,
    coordinateInterleavingDistance_scaledTranslatedHomology]

/-- On delays of the same positive scaling the extended-rank erosion distance equals the
interleaving distance. -/
theorem eRankErosionDistance_scaledTranslatedHomology_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (t u : ℝ) :
    eRankErosionDistance (scaledTranslatedHomology k s hs t)
      (scaledTranslatedHomology k s hs u) =
        coordinateInterleavingDistance (scaledTranslatedHomology k s hs t)
          (scaledTranslatedHomology k s hs u) := by
  rw [eRankErosionDistance_scaledTranslatedHomology,
    coordinateInterleavingDistance_scaledTranslatedHomology]

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
