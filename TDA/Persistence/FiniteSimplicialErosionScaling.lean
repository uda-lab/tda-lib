import TDA.Persistence.FiniteSimplicialErosion
import TDA.Persistence.RankResolutionDegreeTwoSimplicialScaling

/-!
# Exact erosion distance of the scaled simplicial witness against zero

Positively scaling the two coordinates of the tetrahedron-boundary grading by `s` gives an
actual degree-one homology module whose interleaving distance to the zero module is
`scaledLifetime s / 2`. Both erosion distances to zero are at most that value.

The matching lower bound comes from actual structure maps, not from the interleaving distance.
If `2ε < scaledLifetime s`, the widened diagonal test at the birth of the longer arm plus the
radius sees a surviving arm map of the scaled module against the zero module, whose ranks all
vanish, so erosion fails. The longer arm is needed: under an anisotropic scale the shorter
arm's widened map can already be zero. Both erosion distances to zero therefore equal
`scaledLifetime s / 2`, which is also the interleaving distance.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal ZeroObject

/-- Every fiber of the zero module is finite-dimensional. -/
private theorem zeroFiber_finiteDimensional (k : Type u) [Field k] (p : Fin 2 → ℝ) :
    FiniteDimensional k ((0 : PModule.{u,0,u} k (Fin 2 → ℝ)).obj p) := by
  have : Subsingleton ((0 : PModule.{u,0,u} k (Fin 2 → ℝ)).obj p) :=
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
  infer_instance

attribute [local instance] zeroFiber_finiteDimensional

/-- Below half the scaled lifetime, erosion against the zero module fails at the diagonal pair
based at the birth of the longer arm plus the radius: that arm's widened map survives while
every rank of the zero module vanishes. -/
theorem scaledHomology_not_rankErosion_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (ε : ℝ≥0)
    (hε : (ε : ℝ) < scaledLifetime s / 2) :
    ¬ RankErosion ε (scaledHomology k s hs) (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := by
  rintro ⟨h, -⟩
  have h2ε : 0 ≤ 2 * (ε : ℝ) := by positivity
  have hlife : 2 * (ε : ℝ) < scaledLifetime s := by linarith
  -- Pick the longer arm: its birth `b` and its survival across `2ε`.
  obtain ⟨b, hsurv⟩ : ∃ b : Fin 2 → ℝ,
      ∀ hle : b ≤ (fun i => b i + 2 * (ε : ℝ)),
        structureMap (scaledHomology k s hs) hle ≠ 0 := by
    rcases le_total (scaledArmLifetimeA s) (scaledArmLifetimeB s) with hAB | hBA
    · refine ⟨scaledBirthB s, fun _ => ?_⟩
      apply (scaledHomology_armB_structureMap_ne_zero_iff k s hs _ h2ε).2
      rwa [scaledLifetime, max_eq_right hAB] at hlife
    · refine ⟨scaledBirthA s, fun _ => ?_⟩
      apply (scaledHomology_armA_structureMap_ne_zero_iff k s hs _ h2ε).2
      rwa [scaledLifetime, max_eq_left hBA] at hlife
  let a : Fin 2 → ℝ := fun i => b i + (ε : ℝ)
  have hle := h a a le_rfl
  have hzero : rankOfStructureMap (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) (le_refl a) = 0 :=
    rankOfStructureMap_eq_zero_of_isZero _ _ (Functor.zero_obj a)
  have hsurvive : ∀ {p q : Fin 2 → ℝ} (hpq : p ≤ q), p = b →
      q = (fun i => b i + 2 * (ε : ℝ)) →
      structureMap (scaledHomology k s hs) hpq ≠ 0 := by
    rintro p q hpq rfl rfl
    exact hsurv hpq
  have hpos : 1 ≤ rankOfStructureMap (scaledHomology k s hs)
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

/-- Below half the scaled lifetime, extended-rank erosion against the zero module fails. -/
theorem scaledHomology_not_eRankErosion_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) (ε : ℝ≥0)
    (hε : (ε : ℝ) < scaledLifetime s / 2) :
    ¬ ERankErosion ε (scaledHomology k s hs) (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := by
  rw [eRankErosion_iff_rankErosion]
  exact scaledHomology_not_rankErosion_zero k s hs ε hε

/-- The weak-pair rank erosion distance from the scaled module to zero is exactly
`scaledLifetime s / 2`. The lower bound comes from the failed tests of
`scaledHomology_not_rankErosion_zero`, not from the interleaving distance. -/
theorem rankErosionDistance_scaledHomology_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    rankErosionDistance (scaledHomology k s hs) (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) =
      ENNReal.ofReal (scaledLifetime s / 2) := by
  refine le_antisymm ((rankErosionDistance_le_coordinateInterleavingDistance _ _).trans_eq
    (coordinateInterleavingDistance_scaledHomology_zero k s hs)) ?_
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  exact le_rankErosionDistance_of_not_rankErosion
    (scaledHomology_not_rankErosion_zero k s hs r (ENNReal.coe_lt_ofReal.mp hr))

/-- The extended-rank erosion distance from the scaled module to zero is exactly
`scaledLifetime s / 2`. -/
theorem eRankErosionDistance_scaledHomology_zero (k : Type u) [Field k]
    (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    eRankErosionDistance (scaledHomology k s hs) (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) =
      ENNReal.ofReal (scaledLifetime s / 2) := by
  rw [eRankErosionDistance_eq_rankErosionDistance, rankErosionDistance_scaledHomology_zero]

/-- From the scaled module to zero the weak-pair rank erosion distance equals the
interleaving distance. -/
theorem rankErosionDistance_scaledHomology_zero_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    rankErosionDistance (scaledHomology k s hs) (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) =
      coordinateInterleavingDistance (scaledHomology k s hs)
        (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := by
  rw [rankErosionDistance_scaledHomology_zero, coordinateInterleavingDistance_scaledHomology_zero]

/-- From the scaled module to zero the extended-rank erosion distance equals the
interleaving distance. -/
theorem eRankErosionDistance_scaledHomology_zero_eq_coordinateInterleavingDistance
    (k : Type u) [Field k] (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) :
    eRankErosionDistance (scaledHomology k s hs) (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) =
      coordinateInterleavingDistance (scaledHomology k s hs)
        (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := by
  rw [eRankErosionDistance_scaledHomology_zero,
    coordinateInterleavingDistance_scaledHomology_zero]

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
