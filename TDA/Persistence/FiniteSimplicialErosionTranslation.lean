import TDA.Persistence.FiniteSimplicialErosion
import TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslation

/-!
# Exact erosion distance of uniform translates of the simplicial witness

Uniform translates of the tetrahedron-boundary grading have maximal grade error equal to the
translation gap. Their actual degree-one homology modules have both erosion distances at most
the exact interleaving distance `min |t - s| (1/2)`.

The matching lower bound comes from actual structure maps, not from the interleaving
distance. Below the threshold `min |t - s| (1/2)` the widened diagonal test at the earlier
birth plus the radius sees a surviving birth map of the earlier translate against a zero fiber
of the later one, so erosion fails. Both erosion distances therefore equal
`min |t - s| (1/2)`, which is also the interleaving distance.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

/-- The maximal grade error of two uniform translates is exactly the translation gap. -/
theorem supGradeError_translatedGrading (s t : ℝ) :
    (translatedGrading s).supGradeError (translatedGrading t) = ‖t - s‖₊ := by
  refine le_antisymm (((translatedGrading s).supGradeError_le_iff _ _).mpr
    (translatedGrading_grade_error s t)) ?_
  have hface : ({0} : Finset (Fin 4)) ∈ boundaryTetrahedron.toPre := by decide
  have h := (translatedGrading s).abs_grade_sub_le_supGradeError (translatedGrading t)
    ⟨{0}, hface⟩ 0
  rw [translatedGrading_grade, translatedGrading_grade,
    show ∀ x : ℝ, x + s - (x + t) = s - t from fun x => by ring, abs_sub_comm] at h
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact h

/-- A nonzero structure map with a finite-dimensional target has rank at least one. -/
private theorem one_le_rankOfStructureMap_of_ne_zero {k : Type u} [Field k] {n : ℕ}
    (M : PModule.{u,0,u} k (Fin n → ℝ)) {p q : Fin n → ℝ} (hpq : p ≤ q)
    [FiniteDimensional k (M.obj q)] (h : structureMap M hpq ≠ 0) :
    1 ≤ rankOfStructureMap M hpq := by
  unfold rankOfStructureMap
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  exact h (ModuleCat.hom_ext (by simpa [structureMapLinear] using h0))

/-- A structure map into a zero fiber has rank zero. -/
private theorem rankOfStructureMap_eq_zero_of_isZero {k : Type u} [Field k] {n : ℕ}
    (M : PModule.{u,0,u} k (Fin n → ℝ)) {p q : Fin n → ℝ} (hpq : p ≤ q)
    (hq : CategoryTheory.Limits.IsZero (M.obj q)) : rankOfStructureMap M hpq = 0 := by
  unfold rankOfStructureMap
  have htarget : Subsingleton (M.obj q) := ModuleCat.subsingleton_of_isZero hq
  have hrange : Subsingleton (LinearMap.range (structureMapLinear M hpq)) :=
    ⟨fun x y => Subtype.ext (htarget.elim x.val y.val)⟩
  exact @Module.finrank_zero_of_subsingleton k _ _ _ _ _ hrange

/-- Below the signed gap and half the diagonal lifetime, erosion fails at the diagonal pair
based at the earlier birth plus the radius: the widened map of the earlier translate survives
while the later translate has a zero fiber there. -/
theorem translatedHomology_not_rankErosion_of_lt_sub (k : Type u) [Field k] (s t : ℝ)
    (ε : ℝ≥0) (hgap : (ε : ℝ) < t - s) (hlife : 2 * (ε : ℝ) < 1) :
    ¬ RankErosion ε (translatedHomology k s) (translatedHomology k t) := by
  rintro ⟨h, -⟩
  let a : Fin 2 → ℝ := fun i => translatedBirth s i + (ε : ℝ)
  have hle := h a a le_rfl
  have hzero : rankOfStructureMap (translatedHomology k t) (le_refl a) = 0 := by
    apply rankOfStructureMap_eq_zero_of_isZero
    apply translatedHomology_isZero_of_first_lt
    simp only [a, translatedBirth_first]
    linarith
  have hsurvive : ∀ {p q : Fin 2 → ℝ} (hpq : p ≤ q), p = translatedBirth s →
      q = (fun i => translatedBirth s i + 2 * (ε : ℝ)) →
      structureMap (translatedHomology k s) hpq ≠ 0 := by
    rintro p q hpq rfl rfl
    exact translatedHomology_birth_structureMap_ne_zero k s (2 * (ε : ℝ)) (by positivity) hlife
  have hpos :
      1 ≤ rankOfStructureMap (translatedHomology k s) (erosionWide_le ε (le_refl a)) := by
    apply one_le_rankOfStructureMap_of_ne_zero
    apply hsurvive
    · funext i
      simp only [erosionLower, a]
      ring
    · funext i
      simp only [erosionUpper, a]
      ring
  omega

/-- Two uniform translates fail weak-pair rank erosion at every radius strictly below
`min |t - s| (1/2)`. -/
theorem translatedHomology_not_rankErosion (k : Type u) [Field k] (s t : ℝ) (ε : ℝ≥0)
    (hε : (ε : ℝ) < min |t - s| (1 / 2)) :
    ¬ RankErosion ε (translatedHomology k s) (translatedHomology k t) := by
  have hgap : (ε : ℝ) < |t - s| := hε.trans_le (min_le_left _ _)
  have hlife : 2 * (ε : ℝ) < 1 := by
    have := hε.trans_le (min_le_right _ _)
    linarith
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)] at hgap
    exact translatedHomology_not_rankErosion_of_lt_sub k s t ε hgap hlife
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)] at hgap
    exact fun h => translatedHomology_not_rankErosion_of_lt_sub k t s ε hgap hlife h.symm

/-- Two uniform translates fail extended-rank erosion at every radius strictly below
`min |t - s| (1/2)`. -/
theorem translatedHomology_not_eRankErosion (k : Type u) [Field k] (s t : ℝ) (ε : ℝ≥0)
    (hε : (ε : ℝ) < min |t - s| (1 / 2)) :
    ¬ ERankErosion ε (translatedHomology k s) (translatedHomology k t) := by
  rw [eRankErosion_iff_rankErosion]
  exact translatedHomology_not_rankErosion k s t ε hε

/-- The weak-pair rank erosion distance of two uniform translates is exactly
`min |t - s| (1/2)`. The lower bound comes from the failed tests of
`translatedHomology_not_rankErosion`, not from the interleaving distance. -/
theorem rankErosionDistance_translatedHomology (k : Type u) [Field k] (s t : ℝ) :
    rankErosionDistance (translatedHomology k s) (translatedHomology k t) =
      ENNReal.ofReal (min |t - s| (1 / 2)) := by
  refine le_antisymm ((rankErosionDistance_le_coordinateInterleavingDistance _ _).trans_eq
    (coordinateInterleavingDistance_translatedHomology k s t)) ?_
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  exact le_rankErosionDistance_of_not_rankErosion
    (translatedHomology_not_rankErosion k s t r (ENNReal.coe_lt_ofReal.mp hr))

/-- The extended-rank erosion distance of two uniform translates is exactly
`min |t - s| (1/2)`. -/
theorem eRankErosionDistance_translatedHomology (k : Type u) [Field k] (s t : ℝ) :
    eRankErosionDistance (translatedHomology k s) (translatedHomology k t) =
      ENNReal.ofReal (min |t - s| (1 / 2)) := by
  rw [eRankErosionDistance_eq_rankErosionDistance, rankErosionDistance_translatedHomology]

/-- On uniform translates the weak-pair rank erosion distance equals the interleaving
distance. -/
theorem rankErosionDistance_translatedHomology_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (s t : ℝ) :
    rankErosionDistance (translatedHomology k s) (translatedHomology k t) =
      coordinateInterleavingDistance (translatedHomology k s) (translatedHomology k t) := by
  rw [rankErosionDistance_translatedHomology, coordinateInterleavingDistance_translatedHomology]

/-- On uniform translates the extended-rank erosion distance equals the interleaving
distance. -/
theorem eRankErosionDistance_translatedHomology_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (s t : ℝ) :
    eRankErosionDistance (translatedHomology k s) (translatedHomology k t) =
      coordinateInterleavingDistance (translatedHomology k s) (translatedHomology k t) := by
  rw [eRankErosionDistance_translatedHomology, coordinateInterleavingDistance_translatedHomology]

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
