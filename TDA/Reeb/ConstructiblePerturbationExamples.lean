import TDA.Reeb.ConstructiblePerturbation
import TDA.Reeb.ConstructibleSpaceExamples
import TDA.Reeb.ConstructibleQuotientExamples
import TDA.Reeb.RGraphExamples
import TDA.Reeb.GeometricDistanceBoundsExamples
import TDA.Reeb.ConstructibleThickeningQuotientExamples

/-!
# Fixtures for changes of levels

The pinch presentation has a noninjective attachment map. Stretching its single
gap changes the midpoint height, preserves the endpoint identifications and has
the inverse supplied by the level homeomorphism. The thickened pinch exercises
constructibility and stability on continuous pieces, including a carrier
presented by a nonidentity level isomorphism. A single-edge graph also satisfies
the geometric stability bound. A lower-bound fixture detects the moved upper
level in the thickened pinch. Exact translation distances are exercised both on
that presentation and on a one-level interval presentation with no edges.
Acceptance fixtures also cover attained singleton and single-edge bounds, a
translated cycle, rejected reversed levels, the empty-realization boundary and
the identity change on the thickened pinch.
-/

set_option autoImplicit false

namespace TDA.Reeb.Examples.ConstructiblePerturbation

noncomputable section

open CylinderPresentation Examples.Cylinder
open TDA.Reeb.Examples.ConstructibleCylinder (S012)
open TDA.Reeb.Examples.ConstructibleRepresentation (pt0)
open TDA.Reeb.Examples.RGraphThickening (single)
open TDA.Reeb.Examples.RGraphSmoothing (singletonGraph)
open TDA.Reeb.RGraph.Examples (singleEdge cycleData)

/-- Levels `0 < 2`. -/
def S02 : CriticalValues 1 where
  value i := 2 * ((i : ℕ) : ℝ)
  strictMono _ _ h := mul_lt_mul_of_pos_left (Nat.cast_lt.mpr h) (by norm_num)

/-- Stretching moves an interior point even when the attachment is noninjective. -/
theorem pinch_midpoint_height_change :
    ¬ Function.Injective (pinch.left 0) ∧
    |pinch.height S01 (pinch.ofCylinder S01 0 (false, gapIncl S01 0 half)) -
      pinch.height S02 (pinch.levelMap S01 S02
        (pinch.ofCylinder S01 0 (false, gapIncl S01 0 half)))| = 1 / 2 := by
  refine ⟨pinch_left_not_injective, ?_⟩
  simp only [levelMap_ofCylinder, height_ofCylinder]
  norm_num [segMap, gapIncl, half, S01, S02]

/-- Both glued bottom ends still map to the same vertex after stretching. -/
theorem pinch_levelMap_glued_bottom :
    pinch.levelMap S01 S02 (pinch.ofCylinder S01 0 (false, segBot S01 0)) =
      pinch.levelMap S01 S02 (pinch.ofCylinder S01 0 (true, segBot S01 0)) :=
  congrArg (pinch.levelMap S01 S02) pinch_segBot_glued

/-- Reversing the level change fixes every point of the noninjective-attachment quotient. -/
theorem pinch_levelHomeomorph_roundTrip (q : pinch.Realization S01) :
    pinch.levelHomeomorph S02 S01 (pinch.levelHomeomorph S01 S02 q) = q := by
  simp only [levelHomeomorph_apply, levelMap_levelMap]

/-- With no level change, the induced continuous map is the identity. -/
theorem pinch_levelMap_self : pinch.levelMap S01 S01 = ContinuousMap.id _ :=
  pinch.levelMap_self S01

private theorem S01_S02_edist_le_one : edist S01.value S02.value ≤ 1 := by
  apply edist_pi_le_iff.mpr
  intro i
  fin_cases i <;> norm_num [S01, S02, edist_dist, Real.dist_eq]

/-- The single-edge graph satisfies the level-list geometric stability bound. -/
theorem singleEdge_geometric_stability_le_one :
    RGraph.geometricInterleavingDistance
        ((RGraph.toRGraph S01).obj TDA.Reeb.RGraph.Examples.singleEdge)
        ((RGraph.toRGraph S02).obj TDA.Reeb.RGraph.Examples.singleEdge) ≤ 1 :=
  (RGraph.geometricInterleavingDistance_toRGraph_le _ S01 S02).trans S01_S02_edist_le_one

/-- The new finite-data stability bound is attained on singleton graphs at arbitrary heights. -/
theorem singleton_stability_attained (a b : ℝ) :
    RGraph.geometricInterleavingDistance (singletonGraph a) (singletonGraph b) ≤
        ENNReal.ofReal |a - b| ∧
      RGraph.geometricInterleavingDistance (singletonGraph a) (singletonGraph b) =
        ENNReal.ofReal |a - b| := by
  have hlevels : edist (single a).value (single b).value = ENNReal.ofReal |a - b| := by
    change edist (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) = _
    rw [edist_pi_const, edist_dist, Real.dist_eq]
  constructor
  · simpa only [hlevels] using
      RGraph.geometricInterleavingDistance_toRGraph_le pt0 (single a) (single b)
  · exact Examples.GeometricDistanceBounds.geometricInterleavingDistance_singleton

private abbrev singleEdgePresentation := ofFiniteData singleEdge

private theorem singleEdge_sSup_height (S : CriticalValues 1) :
    sSup (Set.range (singleEdgePresentation.height S)) = S.value 1 := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · exact ⟨singleEdgePresentation.ofVertex S 1 (), singleEdgePresentation.height_ofVertex S 1 _⟩
  · rintro _ ⟨q, rfl⟩
    exact (singleEdgePresentation.height_mem_Icc S q).2

/-- Moving the single edge's top from one to two has geometric distance exactly one. -/
theorem singleEdge_geometric_distance_eq_one :
    RGraph.geometricInterleavingDistance
      ((RGraph.toRGraph S01).obj singleEdge) ((RGraph.toRGraph S02).obj singleEdge) = 1 := by
  apply le_antisymm singleEdge_geometric_stability_le_one
  rw [← RGraph.constructibleInterleavingDistance_rgraphToConstructible]
  change 1 ≤ RGraph.constructibleInterleavingDistance
    (singleEdgePresentation.realizationSpace S01) (singleEdgePresentation.realizationSpace S02)
  let : Nonempty (singleEdgePresentation.realizationSpace S01).obj.left :=
    ⟨singleEdgePresentation.ofVertex S01 1 ()⟩
  let : Nonempty (singleEdgePresentation.realizationSpace S02).obj.left :=
    ⟨singleEdgePresentation.ofVertex S02 1 ()⟩
  have h := RGraph.ofReal_abs_sSup_range_sub_le_constructibleInterleavingDistance
    (singleEdgePresentation.realizationSpace S01) (singleEdgePresentation.realizationSpace S02)
  change ENNReal.ofReal |sSup (Set.range (singleEdgePresentation.height S01)) -
    sSup (Set.range (singleEdgePresentation.height S02))| ≤ _ at h
  rw [singleEdge_sSup_height S01, singleEdge_sSup_height S02] at h
  norm_num [S01, S02] at h
  exact h

/-- The exact translation formula applies to the cycle data over three levels. -/
theorem cycle_translation_distance (c : ℝ) :
    RGraph.constructibleInterleavingDistance ((ofFiniteData cycleData).realizationSpace S012)
        ((ofFiniteData cycleData).realizationSpace (S012.translate c)) = ENNReal.ofReal |c| := by
  let : Nonempty ((ofFiniteData cycleData).Realization S012) :=
    ⟨(ofFiniteData cycleData).ofVertex S012 0 ⟨0, by decide⟩⟩
  exact RGraph.constructibleInterleavingDistance_realizationSpace_translate _ S012 c

/-- A reversed reassignment is excluded by the strict monotonicity of a level list. -/
theorem reversed_levels_not_criticalValues : ¬ ∃ S : CriticalValues 1, S.value = ![1, 0] := by
  rintro ⟨S, hS⟩
  have h := S.strictMono (show (0 : Fin 2) < 1 by decide)
  rw [hS] at h
  norm_num at h

/-- Empty realizations have distance zero after translation, so the nonempty hypothesis
of the exact translation theorem cannot be dropped. -/
theorem empty_translation_distance_zero :
    let d := RGraph.constructibleInterleavingDistance
      ((ofFiniteData (emptyData 1)).realizationSpace S01)
      ((ofFiniteData (emptyData 1)).realizationSpace (S01.translate 1))
    d = 0 ∧ d ≠ ENNReal.ofReal |(1 : ℝ)| := by
  let P := ofFiniteData (emptyData 1)
  have e : P.realizationSpace S01 ≅ P.realizationSpace (S01.translate 1) :=
    CategoryTheory.ObjectProperty.isoMk _ (CategoryTheory.Over.isoMk
      (TopCat.isoOfHomeo (P.levelHomeomorph S01 (S01.translate 1))) (by
        ext q
        exact ((emptyData_isEmpty 1 S01).false q).elim))
  have hz : RGraph.constructibleInterleavingDistance
      (P.realizationSpace S01) (P.realizationSpace (S01.translate 1)) = 0 := by
    rw [RGraph.constructibleInterleavingDistance_congr (CategoryTheory.Iso.refl _) e.symm]
    exact RGraph.constructibleInterleavingDistance_self _
  exact ⟨hz, by rw [hz]; norm_num⟩

section thickened

open CategoryTheory
open Examples.ConstructibleQuotient (pinchI pinchI_left_not_injective intervalPres)

attribute [local instance] Examples.ConstructibleQuotient.locallyPathConnectedSpace_unitInterval

/-- Continuous pieces with a noninjective attachment retain constructibility after a level change. -/
theorem pinchI_transported_height_constructible :
    ¬ Function.Injective (pinchI.left 0) ∧
      IsConstructibleSpace (Over.mk (TopCat.ofHom
        ((pinchI.height S02).comp (pinchI.levelMap S01 S02)))) :=
  ⟨pinchI_left_not_injective, pinchI.isConstructibleSpace_height_comp_levelMap S01 S02⟩

/-- The supplied presentation isomorphism can change the underlying realization's level list. -/
theorem pinchI_carrier_perturbation_constructible :
    IsConstructibleSpace (pinchI.levelPerturbation (pinchI.levelOverIso S02 S01) S02) :=
  RGraph.isConstructibleSpace_levelPerturbation pinchI (pinchI.levelOverIso S02 S01) S02

/-- The carrier bound applies through the nonidentity isomorphism from `S02` to `S01`. -/
theorem pinchI_carrier_perturbation_edist_le :
    edist (UniformFun.ofFun ⇑((pinchI.height S01).comp (pinchI.levelMap S02 S01)))
        (UniformFun.ofFun ⇑(overBaseMap
          (pinchI.levelPerturbation (pinchI.levelOverIso S02 S01) S02))) ≤ 1 := by
  refine (RGraph.edist_levelPerturbation_le pinchI (pinchI.levelOverIso S02 S01) S02).trans ?_
  apply edist_pi_le_iff.mpr
  intro i
  fin_cases i <;> norm_num [S01, S02, edist_dist, Real.dist_eq]

/-- Stability applies to the thickened pinch, with its noninjective attachment. -/
theorem pinchI_constructible_stability_le_one :
    RGraph.constructibleInterleavingDistance
      (pinchI.realizationSpace S01) (pinchI.realizationSpace S02) ≤ 1 :=
  (RGraph.constructibleInterleavingDistance_realizationSpace_le pinchI S01 S02).trans
    S01_S02_edist_le_one

/-- The carrier theorem retains its height-distance bound through a nonidentity
presentation isomorphism, and that distance is at most one in this example. -/
theorem pinchI_carrier_stability :
    let X : ConstructibleSpaceCat :=
      ⟨_, pinchI.isConstructibleSpace_height_comp_levelMap S02 S01⟩
    let Y : ConstructibleSpaceCat :=
      ⟨_, RGraph.isConstructibleSpace_levelPerturbation pinchI
        (pinchI.levelOverIso S02 S01) S02⟩
    RGraph.constructibleInterleavingDistance X Y ≤
        edist (UniformFun.ofFun ⇑(overBaseMap X.obj))
          (UniformFun.ofFun ⇑(overBaseMap Y.obj)) ∧
      RGraph.constructibleInterleavingDistance X Y ≤ 1 := by
  have h := RGraph.constructibleInterleavingDistance_levelPerturbation_le pinchI
    (pinchI.levelOverIso S02 S01) S02
  exact ⟨h, h.trans pinchI_carrier_perturbation_edist_le⟩

private theorem pinchI_sSup_height (S : CriticalValues 1) :
    sSup (Set.range (pinchI.height S)) = S.value 1 := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · exact ⟨pinchI.ofVertex S 1 ((false : Bool), (0 : unitInterval)),
      pinchI.height_ofVertex S 1 _⟩
  · rintro _ ⟨q, rfl⟩
    exact (pinchI.height_mem_Icc S q).2

/-- The general supremum obstruction detects the moved top level in a thickened pinch. -/
theorem one_le_pinchI_constructible_distance :
    1 ≤ RGraph.constructibleInterleavingDistance
      (pinchI.realizationSpace S01) (pinchI.realizationSpace S02) := by
  let : Nonempty (pinchI.realizationSpace S01).obj.left :=
    ⟨pinchI.ofVertex S01 1 ((false : Bool), (0 : unitInterval))⟩
  let : Nonempty (pinchI.realizationSpace S02).obj.left :=
    ⟨pinchI.ofVertex S02 1 ((false : Bool), (0 : unitInterval))⟩
  have h := RGraph.ofReal_abs_sSup_range_sub_le_constructibleInterleavingDistance
    (pinchI.realizationSpace S01) (pinchI.realizationSpace S02)
  change ENNReal.ofReal |sSup (Set.range (pinchI.height S01)) -
      sSup (Set.range (pinchI.height S02))| ≤ _ at h
  rw [pinchI_sSup_height S01, pinchI_sSup_height S02] at h
  norm_num [S01, S02] at h
  exact h

/-- A noninjective-attachment presentation with interval pieces attains the translation distance. -/
theorem pinchI_translation_distance (c : ℝ) :
    RGraph.constructibleInterleavingDistance (pinchI.realizationSpace S01)
      (pinchI.realizationSpace (S01.translate c)) = ENNReal.ofReal |c| := by
  let : Nonempty (pinchI.Realization S01) :=
    ⟨pinchI.ofVertex S01 1 ((false : Bool), (0 : unitInterval))⟩
  exact RGraph.constructibleInterleavingDistance_realizationSpace_translate pinchI S01 c

/-- The exact formula also holds with one level, continuous vertex pieces and no edges. -/
theorem interval_zero_gap_translation_distance (c : ℝ) :
    RGraph.constructibleInterleavingDistance
        (intervalPres.realizationSpace Examples.ConstructibleCylinder.S0)
        (intervalPres.realizationSpace (Examples.ConstructibleCylinder.S0.translate c)) =
      ENNReal.ofReal |c| := by
  let : Nonempty (intervalPres.Realization Examples.ConstructibleCylinder.S0) :=
    ⟨intervalPres.ofVertex Examples.ConstructibleCylinder.S0 0 (0 : unitInterval)⟩
  exact RGraph.constructibleInterleavingDistance_realizationSpace_translate
    intervalPres Examples.ConstructibleCylinder.S0 c

/-- The identity level change fixes the thickened pinch and has distance at most zero. -/
theorem pinchI_identity :
    pinchI.levelMap S01 S01 = ContinuousMap.id _ ∧
      RGraph.constructibleInterleavingDistance
        (pinchI.realizationSpace S01) (pinchI.realizationSpace S01) ≤ 0 := by
  refine ⟨pinchI.levelMap_self S01, ?_⟩
  simpa only [edist_self] using
    RGraph.constructibleInterleavingDistance_realizationSpace_le pinchI S01 S01

end thickened

end

end TDA.Reeb.Examples.ConstructiblePerturbation
