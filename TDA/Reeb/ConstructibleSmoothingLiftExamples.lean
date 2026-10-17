import TDA.Reeb.ConstructibleSmoothingLift
import TDA.Reeb.ConstructibleShiftMap
import TDA.Reeb.ConstructibleSmoothingExamples
import TDA.Reeb.GeometricInterleavingExamples

/-!
# Fixtures for the lifted smoothing structure

Acceptance fixtures for the enlargement, composition, commutation and shifted-map lifts on
constructible cosheaves.
-/

open Set CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

open OpenInterval
open TDA.Reeb.RGraph
open TDA.Reeb.Examples.ConstructibleSmoothing
  (quarter coe_quarter pinchGraph smoothedPinchObj smoothedPinchUObj
    smoothedPinch_lower_isEmpty)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph singleGraph)
open TDA.Reeb.Examples.GeometricInterleaving (parallelSingleInterleaving)
open TDA.Reeb.Examples.Cylinder (S01)
open TDA.Reeb.Examples.ConstructibleCylinder (DP pinch_J0_mem_iff)
open TDA.Reeb.Examples.ConstructibleRepresentation (FP)

namespace Examples.ConstructibleSmoothingLift

/-! ### F1: lifted composition on the parallel graph -/

/-- The lifted composition isomorphism has the expected component on the parallel graph. -/
theorem compIso_parallel_component (I : OpenInterval) :
    ((constructibleSmoothingCompIso quarter quarter).hom.app
      (cosheafFunctor.obj parallelGraph)).hom.app I =
      (cosheafFunctor.obj parallelGraph).obj.map
        ((thickenCompIso quarter quarter).hom.app I) :=
  rfl

/-- The inverse followed by the lifted composition isomorphism is the identity on the parallel
graph object. -/
theorem compIso_parallel_inv_hom :
    (constructibleSmoothingCompIso quarter quarter).inv.app
        (cosheafFunctor.obj parallelGraph) ≫
      (constructibleSmoothingCompIso quarter quarter).hom.app
        (cosheafFunctor.obj parallelGraph) =
      𝟙 _ :=
  Iso.inv_hom_id_app (constructibleSmoothingCompIso quarter quarter)
    (cosheafFunctor.obj parallelGraph)

/-! ### F2: lifted interleaving triangles -/

/-- The lifted `φ; ψ` triangle of the parallel-single interleaving. -/
theorem parallelSingleInterleaving_constructible_phi_psi :
    constructibleShiftMap parallelSingleInterleaving.φ ≫
        (constructibleSmoothing quarter).map
          (constructibleShiftMap parallelSingleInterleaving.ψ) ≫
      (constructibleSmoothingCompIso quarter quarter).hom.app
        (cosheafFunctor.obj parallelGraph) =
      (constructibleSmoothingUnit (quarter + quarter)).app
        (cosheafFunctor.obj parallelGraph) := by
  rw [← constructibleShiftMap_comp, parallelSingleInterleaving.φ_ψ,
    constructibleShiftMap_unit]

/-- The lifted `ψ; φ` triangle of the parallel-single interleaving. -/
theorem parallelSingleInterleaving_constructible_psi_phi :
    constructibleShiftMap parallelSingleInterleaving.ψ ≫
        (constructibleSmoothing quarter).map
          (constructibleShiftMap parallelSingleInterleaving.φ) ≫
      (constructibleSmoothingCompIso quarter quarter).hom.app
        (cosheafFunctor.obj singleGraph) =
      (constructibleSmoothingUnit (quarter + quarter)).app
        (cosheafFunctor.obj singleGraph) := by
  rw [← constructibleShiftMap_comp, parallelSingleInterleaving.ψ_φ,
    constructibleShiftMap_unit]

/-! ### F3: enlargement negative control -/

/-- The numerical inequality used by the non-isomorphism fixture. -/
theorem one_le_two_nn : (1 : ℝ≥0) ≤ 2 := by
  norm_num

/-- Enlarging the pinch from `1` to `2` is not an isomorphism. -/
theorem constructibleSmoothingMap_pinch_not_isIso :
    ¬ IsIso ((constructibleSmoothingMap one_le_two_nn).app
      (cosheafFunctor.obj pinchGraph)) := by
  intro h
  have hhom : IsIso (((constructibleSmoothingMap one_le_two_nn).app
      (cosheafFunctor.obj pinchGraph)).hom) :=
    (ObjectProperty.isIso_hom_iff _).2 h
  have hsource : IsEmpty (((smoothing 1).obj FP).obj (iio (-1))) :=
    smoothedPinch_lower_isEmpty
  have htarget : Nonempty (FP.obj (thicken 2 (iio (-1)))) := by
    have h : thicken 2 (iio (-1)) = S01.J 0 := by
      ext x
      rw [thicken_iio, pinch_J0_mem_iff, mem_iio]
      norm_num
    change Nonempty (FP.obj (thicken 2 (iio (-1))))
    rw [h]
    exact ⟨DP.vertexLabel S01 0 (0 : Fin 2)⟩
  have hbij : Function.Bijective
      (((constructibleSmoothingMap one_le_two_nn).app
        (cosheafFunctor.obj pinchGraph)).hom.app (iio (-1))) :=
    (CategoryTheory.isIso_iff_bijective _).1
      (NatIso.isIso_app_of_isIso
        ((constructibleSmoothingMap one_le_two_nn).app
          (cosheafFunctor.obj pinchGraph)).hom (iio (-1)))
  obtain ⟨y⟩ := htarget
  obtain ⟨x, _⟩ := hbij.2 y
  exact (hsource.false x).elim

/-- At equal parameters, the lifted enlargement is the identity on the pinch graph object. -/
theorem constructibleSmoothingMap_pinch_refl :
    (constructibleSmoothingMap (le_refl quarter)).app
        (cosheafFunctor.obj pinchGraph) =
      𝟙 ((constructibleSmoothing quarter).obj (cosheafFunctor.obj pinchGraph)) := by
  rw [constructibleSmoothingMap_refl]
  rfl

/-! ### F4: a zero law on the single graph -/

/-- The lifted left-zero composition law at the single graph. -/
theorem compIso_zero_left_singleGraph :
    (constructibleSmoothingCompIso 0 quarter).hom.app
        (cosheafFunctor.obj singleGraph) ≫
      (constructibleSmoothingMap (zero_add quarter).le).app
        (cosheafFunctor.obj singleGraph) =
      constructibleSmoothingZeroIso.hom.app
        ((constructibleSmoothing quarter).obj (cosheafFunctor.obj singleGraph)) :=
  constructibleSmoothingCompIso_zero_left quarter (cosheafFunctor.obj singleGraph)

/-- The underlying interval component of the single-graph left-zero law is the expected map. -/
theorem compIso_zero_left_singleGraph_component (I : OpenInterval) :
    ((constructibleSmoothingCompIso 0 quarter).hom.app
        (cosheafFunctor.obj singleGraph) ≫
      (constructibleSmoothingMap (zero_add quarter).le).app
        (cosheafFunctor.obj singleGraph)).hom.app I =
      (cosheafFunctor.obj singleGraph).obj.map
        (((thickenCompIso 0 quarter).hom.app I) ≫
          ((thickenMap (zero_add quarter).le).app I)) := by
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-! ### F5: value universe `1` -/

/-- The lifted composition isomorphism elaborates in value universe `1`. -/
theorem universe_one_compIso_component :
    ((constructibleSmoothingCompIso.{1} quarter quarter).hom.app
      (smoothedPinchUObj 0)).hom =
      (smoothingCompIso quarter quarter).hom.app (smoothedPinchUObj 0).obj :=
  rfl

/-- The lifted enlargement elaborates in value universe `1`. -/
theorem universe_one_map_component :
    ((constructibleSmoothingMap.{1} one_le_two_nn).app
      (smoothedPinchUObj 0)).hom =
      (smoothingMap one_le_two_nn).app (smoothedPinchUObj 0).obj :=
  rfl

/-! ### F6: commutation -/

/-- The lifted commutation isomorphism has the expected interval component. -/
theorem commIso_parallel_component (I : OpenInterval) :
    ((constructibleSmoothingCommIso quarter 1).hom.app
      (cosheafFunctor.obj parallelGraph)).hom.app I =
      (cosheafFunctor.obj parallelGraph).obj.map
        (homOfLE (thicken_comm quarter 1 I).le) :=
  smoothingCommIso_hom_app_app quarter 1 (cosheafFunctor.obj parallelGraph).obj I

end Examples.ConstructibleSmoothingLift

end

end TDA.Reeb
