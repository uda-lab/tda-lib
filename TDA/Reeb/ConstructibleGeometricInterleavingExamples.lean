import TDA.Reeb.ConstructibleGeometricInterleaving
import TDA.Reeb.ConstructibleThickeningQuotientExamples
import TDA.Reeb.RGraphCosheafEquivalenceExamples
import TDA.Reeb.GeometricInterleavingExamples
import TDA.Reeb.GeometricDistanceBoundsExamples

/-!
# Fixtures for interleavings of constructible ℝ-spaces

These fixtures cover the reflection of constructible spaces to Reeb graph objects, the exact graph
distances transported back to constructible spaces, the strict threshold below the edge midpoint,
non-graph smoothing, and the supremum-distance stability bound.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.ConstructibleGeometricInterleaving

open OpenInterval CylinderPresentation FiniteReebData RGraph
open TDA.Reeb.Examples.Cylinder (homeomorphZero height_zero)
open TDA.Reeb.Examples.ConstructibleCylinder (S0)
open TDA.Reeb.Examples.ConstructibleQuotient (intervalPres interval_ofVertex_zero_ne_one)
open TDA.Reeb.Examples.ConstructibleThickeningQuotient
  (interval_isConstructibleSpace pinchSpace pointSpace)
open TDA.Reeb.Examples.ConstructibleRepresentation (pt0)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter)
open TDA.Reeb.Examples.RGraphCosheafEquivalence
  (constInterval_iso_realization collapseToPoint isIso_collapseToPoint pointGraph singleGraph)
open TDA.Reeb.Examples.GeometricInterleaving
  (midGraph coe_halfNN_ennreal geometricInterleavingDistance_edge_mid)
open TDA.Reeb.Examples.GeometricDistanceBounds
  (geometricInterleavingDistance_singleton_zero_one)
open TDA.Reeb.Examples.RGraphSmoothing (singletonGraph)
open TDA.Reeb.Examples.RGraphThickening (single coe_halfNN)

/-! ### F1: a non-graph input -/

/-- The constant-height interval as a constructible real-space. -/
abbrev intervalSpace : ConstructibleSpaceCat :=
  ⟨Over.mk (TopCat.ofHom (intervalPres.height S0)), interval_isConstructibleSpace⟩

/-- The constructible distance between the constant interval and the point is zero. -/
theorem constructibleInterleavingDistance_interval_point :
    constructibleInterleavingDistance intervalSpace pointSpace = 0 := by
  rw [constructibleInterleavingDistance_eq_interleavingDistance]
  apply interleavingDistance_eq_zero_of_iso
  change intervalComponentsOver.obj intervalSpace.obj ≅
    intervalComponentsOver.obj pointSpace.obj
  exact intervalComponentsOver.mapIso constInterval_iso_realization.symm ≪≫
    asIso (intervalComponentsOver.map collapseToPoint)

/-- The interval is zero-interleaved with the constructible space underlying its Reeb quotient. -/
theorem interval_toQuotient_nonempty :
    Nonempty (ConstructibleInterleaving 0 intervalSpace
      (rgraphToConstructible.obj (quotientRGraphFunctor.obj intervalSpace))) :=
  ⟨ConstructibleInterleaving.toQuotient intervalSpace⟩

/-- The interval and point spaces are not isomorphic as spaces over `ℝ`. -/
theorem not_nonempty_interval_iso_point : ¬ Nonempty (intervalSpace ≅ pointSpace) := by
  rintro ⟨e⟩
  have hinv : ∀ x : intervalSpace.obj.left,
      e.inv.hom.left.hom (e.hom.hom.left.hom x) = x := fun x =>
    congrArg (fun φ : intervalSpace ⟶ intervalSpace => φ.hom.left.hom x) e.hom_inv_id
  have hinj : Function.Injective e.hom.hom.left.hom := by
    intro x y hxy
    calc
      x = e.inv.hom.left.hom (e.hom.hom.left.hom x) := (hinv x).symm
      _ = e.inv.hom.left.hom (e.hom.hom.left.hom y) := congrArg _ hxy
      _ = y := hinv y
  have hpoint : Subsingleton pointGraph.obj.left := by
    have : Subsingleton ((ofFiniteData pt0).V 0) := inferInstanceAs (Subsingleton Unit)
    exact (homeomorphZero S0 (ofFiniteData pt0)).symm.injective.subsingleton
  apply interval_ofVertex_zero_ne_one
  apply hinj
  exact @Subsingleton.elim pointGraph.obj.left hpoint _ _

/-! ### F2: exact values on graph inputs -/

/-- The constructible distance between the singleton graphs at heights `0` and `1` is `1`. -/
theorem constructibleInterleavingDistance_singleton_zero_one :
    constructibleInterleavingDistance (rgraphToConstructible.obj (singletonGraph 0))
        (rgraphToConstructible.obj (singletonGraph 1)) = 1 := by
  rw [constructibleInterleavingDistance_rgraphToConstructible,
    geometricInterleavingDistance_singleton_zero_one]

/-- The constructible distance between the single edge and its midpoint is `1 / 2`. -/
theorem constructibleInterleavingDistance_single_mid :
    constructibleInterleavingDistance (rgraphToConstructible.obj singleGraph)
        (rgraphToConstructible.obj midGraph) = 1 / 2 := by
  rw [constructibleInterleavingDistance_rgraphToConstructible,
    geometricInterleavingDistance_edge_mid]

/-! ### F3: the strict threshold below the edge midpoint -/

/-- Below `1 / 2` there is no constructible interleaving of the edge and its midpoint. -/
theorem single_mid_isEmpty {ε : ℝ≥0} (hε : (ε : ℝ) < 1 / 2) :
    IsEmpty (ConstructibleInterleaving ε (rgraphToConstructible.obj singleGraph)
      (rgraphToConstructible.obj midGraph)) := by
  refine ⟨fun i => ?_⟩
  have hhalf : (1 / 2 : ℝ≥0∞) ≤ (ε : ℝ≥0∞) := by
    rw [← constructibleInterleavingDistance_single_mid]
    exact constructibleInterleavingDistance_le_of_nonempty ⟨i⟩
  have hhalfReal : (1 / 2 : ℝ) ≤ (ε : ℝ) := by
    rw [← coe_halfNN_ennreal, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe, coe_halfNN] at hhalf
    exact hhalf
  exact (not_lt_of_ge hhalfReal) hε

/-! ### F4: smoothing a non-graph input -/

/-- The pinch and its constructible quarter-smoothing are at distance at most `quarter`. -/
theorem constructibleInterleavingDistance_pinch_smoothing_le :
    constructibleInterleavingDistance pinchSpace
        ((RGraph.constructibleSmoothing quarter).obj pinchSpace) ≤ quarter :=
  constructibleInterleavingDistance_constructibleSmoothing_self_le quarter pinchSpace

/-! ### F5: stability for constant heights -/

/-- A constant height on `unitInterval` gives a constructible real-space. -/
theorem const_isConstructibleSpace (c : ℝ) :
    IsConstructibleSpace (Over.mk (TopCat.ofHom (ContinuousMap.const unitInterval c))) := by
  refine ⟨0, single c, intervalPres, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    infer_instance
  · intro i
    infer_instance
  · intro e
    infer_instance
  · intro e
    infer_instance
  · exact ⟨Over.isoMk (TopCat.isoOfHomeo (homeomorphZero (single c) intervalPres)) (by
      ext x
      change intervalPres.height (single c) (homeomorphZero (single c) intervalPres x) = c
      exact height_zero (single c) intervalPres _)⟩

/-- The constant-zero height on `unitInterval` is constructible. -/
theorem constZero_isConstructibleSpace :
    IsConstructibleSpace (Over.mk (TopCat.ofHom (ContinuousMap.const unitInterval (0 : ℝ)))) :=
  const_isConstructibleSpace 0

/-- The constant-one height on `unitInterval` is constructible. -/
theorem constOne_isConstructibleSpace :
    IsConstructibleSpace (Over.mk (TopCat.ofHom (ContinuousMap.const unitInterval (1 : ℝ)))) :=
  const_isConstructibleSpace 1

/-- The constructible distance between the constant-zero and constant-one heights is at most `1`. -/
theorem constructibleInterleavingDistance_const_zero_one_le :
    constructibleInterleavingDistance
        ⟨_, constZero_isConstructibleSpace⟩
        ⟨_, constOne_isConstructibleSpace⟩ ≤ 1 := by
  refine (constructibleInterleavingDistance_le_edist
    constZero_isConstructibleSpace constOne_isConstructibleSpace).trans ?_
  rw [← ENNReal.coe_one]
  exact edist_uniformFun_ofFun_le_coe_iff.2 (by
    intro x
    norm_num)

end Examples.ConstructibleGeometricInterleaving

end
end TDA.Reeb
