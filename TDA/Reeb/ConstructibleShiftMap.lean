import TDA.Reeb.ConstructibleSmoothingLift
import TDA.Reeb.GeometricInterleavingEquivalence

/-!
# Shifted maps in constructible cosheaves

The graph-side shifted maps and the comparison with interval smoothing lift from the underlying
precosheaf category to `ConstructibleCosheafCat`.  The lifted composition law is stated directly
in the full subcategory, and the existing precosheaf law is recovered by taking underlying maps.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace RGraph

open OpenInterval

variable {ε δ : ℝ≥0} {A B D : RGraphCat}

/-! ### Shifted maps -/

/--
The constructible shifted map `C φ` followed by the comparison `β^ε`.
-/
def constructibleShiftMap (φ : A ⟶ (geometricSmoothing ε).obj B) :
    cosheafFunctor.obj A ⟶ (constructibleSmoothing ε).obj (cosheafFunctor.obj B) :=
  cosheafFunctor.map φ ≫ (geometricSmoothingComparisonIso ε).hom.app B

/--
The underlying precosheaf map of `constructibleShiftMap` is `cosheafShiftMap`.
-/
@[simp] theorem constructibleShiftMap_hom
    (φ : A ⟶ (geometricSmoothing ε).obj B) :
    (constructibleShiftMap φ).hom = cosheafShiftMap φ :=
  rfl

/--
The constructible shifted map of the geometric smoothing unit is the constructible smoothing
unit.
-/
theorem constructibleShiftMap_unit (ε : ℝ≥0) (A : RGraphCat) :
    constructibleShiftMap ((geometricSmoothingUnit ε).app A) =
      (constructibleSmoothingUnit ε).app (cosheafFunctor.obj A) := by
  apply ObjectProperty.hom_ext
  exact cosheafShiftMap_unit ε A

/--
The composition comparison square in constructible cosheaves.
-/
@[reassoc] theorem cosheafFunctor_map_geometricSmoothingCompIso_hom_app_comp
    (ε δ : ℝ≥0) (A : RGraphCat) :
    cosheafFunctor.map ((geometricSmoothingCompIso ε δ).hom.app A) ≫
        (geometricSmoothingComparisonIso (ε + δ)).hom.app A =
      (geometricSmoothingComparisonIso ε).hom.app ((geometricSmoothing δ).obj A) ≫
        (constructibleSmoothing ε).map ((geometricSmoothingComparisonIso δ).hom.app A) ≫
        (constructibleSmoothingCompIso ε δ).hom.app (cosheafFunctor.obj A) := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, constructibleSmoothing_map_hom,
    constructibleSmoothingCompIso_hom_app_hom]
  exact cosheafFunctor_map_geometricSmoothingCompIso_hom_app ε δ A

/--
The composition comparison square as a natural-transformation equation in constructible
cosheaves.
-/
theorem geometricSmoothingComparisonIso_compIso (ε δ : ℝ≥0) :
    Functor.whiskerRight (geometricSmoothingCompIso ε δ).hom cosheafFunctor ≫
        (geometricSmoothingComparisonIso (ε + δ)).hom =
      Functor.whiskerLeft (geometricSmoothing δ) (geometricSmoothingComparisonIso ε).hom ≫
        Functor.whiskerRight (geometricSmoothingComparisonIso δ).hom (constructibleSmoothing ε) ≫
        Functor.whiskerLeft cosheafFunctor (constructibleSmoothingCompIso ε δ).hom := by
  ext A : 2
  exact cosheafFunctor_map_geometricSmoothingCompIso_hom_app_comp ε δ A

/--
The three-object composition law for constructible shifted maps.
-/
theorem constructibleShiftMap_comp (φ : A ⟶ (geometricSmoothing ε).obj B)
    (ψ : B ⟶ (geometricSmoothing δ).obj D) :
    constructibleShiftMap (φ ≫ (geometricSmoothing ε).map ψ ≫
        (geometricSmoothingCompIso ε δ).hom.app D) =
      constructibleShiftMap φ ≫ (constructibleSmoothing ε).map (constructibleShiftMap ψ) ≫
        (constructibleSmoothingCompIso ε δ).hom.app (cosheafFunctor.obj D) := by
  unfold constructibleShiftMap
  have hnat :
      cosheafFunctor.map ((geometricSmoothing ε).map ψ) ≫
          (geometricSmoothingComparisonIso ε).hom.app ((geometricSmoothing δ).obj D) =
        (geometricSmoothingComparisonIso ε).hom.app B ≫
          (constructibleSmoothing ε).map (cosheafFunctor.map ψ) :=
    (geometricSmoothingComparisonIso ε).hom.naturality ψ
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [cosheafFunctor_map_geometricSmoothingCompIso_hom_app_comp, reassoc_of% hnat]

/--
The underlying precosheaf three-object composition law recovered from the constructible law.
-/
theorem cosheafShiftMap_comp_of_constructible (φ : A ⟶ (geometricSmoothing ε).obj B)
    (ψ : B ⟶ (geometricSmoothing δ).obj D) :
    cosheafShiftMap (φ ≫ (geometricSmoothing ε).map ψ ≫
        (geometricSmoothingCompIso ε δ).hom.app D) =
      cosheafShiftMap φ ≫ (smoothing ε).map (cosheafShiftMap ψ) ≫
        (smoothingCompIso ε δ).hom.app (cosheafFunctor.obj D).obj := by
  exact congrArg (fun f => f.hom) (constructibleShiftMap_comp φ ψ)

end RGraph

end

end TDA.Reeb
