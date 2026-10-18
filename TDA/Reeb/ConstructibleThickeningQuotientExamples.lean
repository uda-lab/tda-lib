import TDA.Reeb.ConstructibleThickeningQuotient
import TDA.Reeb.ConstructibleQuotientExamples
import TDA.Reeb.QuotientThickeningAbsorptionExamples

/-!
# Fixtures for absorption on constructible ℝ-spaces

These fixtures cover a non-graph interval, a thickened pinch with a non-injective attaching map,
the one-point graph at the boundary parameters, and the failure of graphness for a thickened
identity map on all of `ℝ`.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace Examples.ConstructibleThickeningQuotient

open OpenInterval CylinderPresentation RGraph
open TDA.Reeb.Examples.Cylinder (S01 homeomorphZero pinchData)
open TDA.Reeb.Examples.ConstructibleCylinder (S0)
open TDA.Reeb.Examples.ConstructibleRepresentation (pt0)
open TDA.Reeb.Examples.ConstructibleQuotient
  (intervalPres pinchI thicken_isConstructibleSpace)
open TDA.Reeb.Examples.ConstructibleSmoothing (quarter)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (pointGraph)
open TDA.Reeb.Examples.QuotientThickeningAbsorption (fiber_subsingleton_of_iso)
open TDA.Reeb.Examples.RGraphSmoothing (fiber_subsingleton_of_cosheaf)

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

/-! ### F1: a non-graph input -/

/-- The constant-height interval is a constructible real-space. -/
theorem interval_isConstructibleSpace :
    IsConstructibleSpace (Over.mk (TopCat.ofHom (intervalPres.height S0))) :=
  ⟨0, S0, intervalPres, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance, fun _ => inferInstance, ⟨Iso.refl _⟩⟩

/-- The quotient of the quarter-thickened interval is a graph object. -/
theorem interval_isRGraph_quotient_thickening_quarter :
    IsRGraph ((ℛ).obj ((GeometricThickening.functor quarter).obj
      (Over.mk (TopCat.ofHom (intervalPres.height S0))))) :=
  isRGraph_quotient_thickening_of_isConstructibleSpace
    interval_isConstructibleSpace quarter

/-- The absorption morphism for the quarter-thickened interval is an isomorphism. -/
theorem interval_isIso_absorption_quarter :
    IsIso ((ℛ).map ((GeometricThickening.functor quarter).map
      ((ReebQuotient.projNatTrans ℝ).app
        (Over.mk (TopCat.ofHom (intervalPres.height S0)))))) := by
  rw [← absorptionOverIso_hom interval_isConstructibleSpace quarter]
  infer_instance

/-! ### F2: a thickened pinch -/

/-- The thickened pinch has a graph quotient after quarter thickening. -/
theorem pinch_isRGraph_quotient_thickening_quarter :
    IsRGraph ((ℛ).obj ((GeometricThickening.functor quarter).obj
      (Over.mk (TopCat.ofHom (pinchI.height S01))))) :=
  isRGraph_quotient_thickening_of_isConstructibleSpace
    (thicken_isConstructibleSpace S01 pinchData) quarter

/-- The thickened pinch as an object of `ConstructibleSpaceCat`. -/
abbrev pinchSpace : ConstructibleSpaceCat :=
  ⟨Over.mk (TopCat.ofHom (pinchI.height S01)),
    thicken_isConstructibleSpace S01 pinchData⟩

/-- The pinch absorption component is the absorption morphism and is invertible. -/
theorem pinch_thickeningQuotientAbsorptionIso_hom :
    (((thickeningQuotientAbsorptionIso quarter).hom.app pinchSpace).hom =
      (ℛ).map ((GeometricThickening.functor quarter).map
        ((ReebQuotient.projNatTrans ℝ).app pinchSpace.obj))) ∧
      IsIso (((thickeningQuotientAbsorptionIso quarter).hom.app pinchSpace).hom) := by
  constructor
  · exact thickeningQuotientAbsorptionIso_hom_app_hom quarter pinchSpace
  · rw [thickeningQuotientAbsorptionIso_hom_app_hom quarter pinchSpace]
    exact isIso_quotientFunctor_map_functor_map_projNatTrans_app_constructible
      pinchSpace quarter

/-! ### F3: the one-point boundary -/

/-- The point graph viewed as a constructible real-space. -/
abbrev pointSpace : ConstructibleSpaceCat :=
  ⟨pointGraph.obj, isConstructibleSpace_of_isRGraph pointGraph.property⟩

/-- The zero-thickened point has a graph quotient. -/
theorem point_isRGraph_quotient_thickening_zero :
    IsRGraph ((ℛ).obj ((GeometricThickening.functor 0).obj pointSpace.obj)) :=
  isRGraph_quotient_thickening_of_isConstructibleSpace pointSpace.property 0

/-- The unit-thickened point has a graph quotient. -/
theorem point_isRGraph_quotient_thickening_one :
    IsRGraph ((ℛ).obj ((GeometricThickening.functor 1).obj pointSpace.obj)) :=
  isRGraph_quotient_thickening_of_isConstructibleSpace pointSpace.property 1

/-- Every height fibre of the unit-thickened quotient point is a subsingleton. -/
theorem point_thickeningQuotient_one_fiber_subsingleton (t : ℝ) :
    Subsingleton (overBaseMap ((thickeningQuotient 1).obj pointSpace).obj ⁻¹' {t}) := by
  apply fiber_subsingleton_of_iso ((thickeningQuotientAbsorptionIso 1).app pointSpace) t
  have hpoint : Subsingleton pointGraph.obj.left := by
    have : Subsingleton ((ofFiniteData pt0).V 0) := inferInstanceAs (Subsingleton Unit)
    exact (homeomorphZero S0 (ofFiniteData pt0)).symm.injective.subsingleton
  have : Subsingleton pointGraph.obj.left := hpoint
  let pointQuotientIso : pointGraph ≅ quotientRGraphFunctor.obj pointSpace :=
    ObjectProperty.isoMk _ (RGraph.projNatIso.app pointGraph)
  apply fiber_subsingleton_of_iso
    (((geometricSmoothing 1).mapIso pointQuotientIso).symm) t
  apply fiber_subsingleton_of_cosheaf
  intro I
  have h : Subsingleton
      ((intervalComponents (overBaseMap pointGraph.obj)).obj (thicken 1 I)) := by
    constructor
    intro c d
    induction c using ZerothHomotopy.rec with
    | mk x =>
      induction d using ZerothHomotopy.rec with
      | mk y =>
        exact congrArg ZerothHomotopy.mk (Subtype.ext (Subsingleton.elim x.1 y.1))
  exact (geometricSmoothingValueEquiv 1 pointGraph I).subsingleton_congr.2 h

/-! ### F4: an unbounded negative control -/

/-- The quotient of the unit thickening of `id ℝ` is not a graph object. -/
theorem id_thickening_quotient_not_isRGraph :
    ¬ IsRGraph ((ℛ).obj ((GeometricThickening.functor 1).obj
      (Over.mk (TopCat.ofHom (ContinuousMap.id ℝ))))) := by
  let X : Over (TopCat.of ℝ) := Over.mk (TopCat.ofHom (ContinuousMap.id ℝ))
  change ¬ IsRGraph ((ℛ).obj ((GeometricThickening.functor 1).obj X))
  intro hA
  obtain ⟨m, T, D, ⟨e⟩⟩ := hA
  have hsurj : ∀ t : ℝ, ∃ q : ((ℛ).obj ((GeometricThickening.functor 1).obj X)).left,
      overBaseMap ((ℛ).obj ((GeometricThickening.functor 1).obj X)) q = t := by
    intro t
    refine ⟨ReebQuotient.mk _ (t, ⟨0, GeometricThickening.zero_mem_band 1⟩), ?_⟩
    change (ContinuousMap.id ℝ) t + 0 = t
    simp
  obtain ⟨q, hq⟩ := hsurj (T.value (Fin.last m) + 1)
  have hq' : (ofFiniteData D).height T (e.hom.left.hom q) =
      T.value (Fin.last m) + 1 := by
    calc
      (ofFiniteData D).height T (e.hom.left.hom q) =
          overBaseMap ((ℛ).obj ((GeometricThickening.functor 1).obj X)) q :=
        overBaseMap_comm e.hom q
      _ = T.value (Fin.last m) + 1 := hq
  have hbound := (ofFiniteData D).height_mem_Icc T (e.hom.left.hom q)
  linarith [hbound.2, hq']

end Examples.ConstructibleThickeningQuotient

end
end TDA.Reeb
