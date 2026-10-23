import TDA.Reeb.ConstructibleSmoothing

/-!
# Lifted smoothing structure on constructible cosheaves

The enlargement maps, composition isomorphisms and commutation isomorphisms of interval
precosheaf smoothing restrict to the full subcategory of constructible cosheaves.  This file
packages those maps and their coherence laws in `ConstructibleCosheafCat`.
-/

open Set CategoryTheory
open scoped NNReal

universe u

namespace TDA.Reeb

noncomputable section

open OpenInterval

/--
The enlargement `S_ε ⟶ S_δ` on constructible cosheaves induced by `ε ≤ δ`.
-/
def constructibleSmoothingMap {ε δ : ℝ≥0} (h : ε ≤ δ) :
    constructibleSmoothing.{u} ε ⟶ constructibleSmoothing δ where
  app G := ObjectProperty.homMk ((smoothingMap h).app G.obj)
  naturality _ _ f := by
    ext : 1
    exact (smoothingMap h).naturality f.hom

/--
The underlying precosheaf map of `constructibleSmoothingMap` at a constructible cosheaf.
-/
@[simp] theorem constructibleSmoothingMap_app_hom {ε δ : ℝ≥0} (h : ε ≤ δ)
    (G : ConstructibleCosheafCat.{u}) :
    ((constructibleSmoothingMap h).app G).hom = (smoothingMap h).app G.obj :=
  rfl

/--
The interval component of the underlying map of `constructibleSmoothingMap`.
-/
theorem constructibleSmoothingMap_app_hom_app {ε δ : ℝ≥0} (h : ε ≤ δ)
    (G : ConstructibleCosheafCat.{u}) (I : OpenInterval) :
    ((constructibleSmoothingMap h).app G).hom.app I = G.obj.map ((thickenMap h).app I) :=
  rfl

/--
The enlargement map at equal smoothing parameters is the identity.
-/
theorem constructibleSmoothingMap_refl (ε : ℝ≥0) :
    constructibleSmoothingMap (le_refl ε) = 𝟙 (constructibleSmoothing.{u} ε) := by
  ext G : 2
  apply ObjectProperty.hom_ext
  exact congrArg (fun t => t.app G.obj) (smoothingMap_refl ε)

/--
Enlargements of constructible smoothings compose along inequalities of parameters.
-/
theorem constructibleSmoothingMap_comp {ε δ γ : ℝ≥0} (h : ε ≤ δ) (h' : δ ≤ γ) :
    constructibleSmoothingMap.{u} h ≫ constructibleSmoothingMap h' =
      constructibleSmoothingMap (h.trans h') := by
  ext G : 2
  apply ObjectProperty.hom_ext
  exact congrArg (fun t => t.app G.obj) (smoothingMap_comp h h')

/--
The lifted smoothing unit is compatible with the lifted enlargement map.
-/
theorem constructibleSmoothingUnit_comp_constructibleSmoothingMap {ε δ : ℝ≥0}
    (h : ε ≤ δ) :
    constructibleSmoothingUnit.{u} ε ≫ constructibleSmoothingMap h =
      constructibleSmoothingUnit δ := by
  ext G : 2
  apply ObjectProperty.hom_ext
  exact congrArg (fun t => t.app G.obj) (smoothingUnit_comp_smoothingMap h)

/--
The lifted composition isomorphism `S_ε S_δ ≅ S_(ε+δ)` on constructible cosheaves.
-/
def constructibleSmoothingCompIso (ε δ : ℝ≥0) :
    constructibleSmoothing.{u} δ ⋙ constructibleSmoothing ε ≅
      constructibleSmoothing (ε + δ) :=
  NatIso.ofComponents
    (fun G => ObjectProperty.isoMk _ ((smoothingCompIso ε δ).app G.obj))
    (fun f => by
      ext : 1
      exact (smoothingCompIso ε δ).hom.naturality f.hom)

/--
The underlying hom of the lifted smoothing composition isomorphism.
-/
@[simp] theorem constructibleSmoothingCompIso_hom_app_hom (ε δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    ((constructibleSmoothingCompIso ε δ).hom.app G).hom =
      (smoothingCompIso ε δ).hom.app G.obj :=
  rfl

/--
The underlying inverse hom of the lifted smoothing composition isomorphism.
-/
@[simp] theorem constructibleSmoothingCompIso_inv_app_hom (ε δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    ((constructibleSmoothingCompIso ε δ).inv.app G).hom =
      (smoothingCompIso ε δ).inv.app G.obj :=
  rfl

/--
The first unit coherence for the lifted smoothing composition isomorphism.
-/
theorem constructibleSmoothingUnit_comp_constructibleSmoothingUnit (ε δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    (constructibleSmoothingUnit δ).app G ≫
        (constructibleSmoothingUnit ε).app ((constructibleSmoothing δ).obj G) ≫
      (constructibleSmoothingCompIso ε δ).hom.app G =
      (constructibleSmoothingUnit (ε + δ)).app G := by
  apply ObjectProperty.hom_ext
  exact smoothingUnit_comp_smoothingUnit ε δ G.obj

/--
The second unit coherence for the lifted smoothing composition isomorphism.
-/
theorem constructibleSmoothingUnit_comp_map_constructibleSmoothingUnit (ε δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    (constructibleSmoothingUnit ε).app G ≫
        (constructibleSmoothing ε).map ((constructibleSmoothingUnit δ).app G) ≫
      (constructibleSmoothingCompIso ε δ).hom.app G =
      (constructibleSmoothingUnit (ε + δ)).app G := by
  apply ObjectProperty.hom_ext
  exact smoothingUnit_comp_map_smoothingUnit ε δ G.obj

/--
The associativity coherence for the lifted smoothing composition isomorphisms.
-/
theorem constructibleSmoothingCompIso_assoc (ε δ γ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    (constructibleSmoothing ε).map ((constructibleSmoothingCompIso δ γ).hom.app G) ≫
        (constructibleSmoothingCompIso ε (δ + γ)).hom.app G ≫
        (constructibleSmoothingMap (add_assoc ε δ γ).ge).app G =
      (constructibleSmoothingCompIso ε δ).hom.app ((constructibleSmoothing γ).obj G) ≫
        (constructibleSmoothingCompIso (ε + δ) γ).hom.app G := by
  apply ObjectProperty.hom_ext
  exact smoothingCompIso_assoc ε δ γ G.obj

/--
The left zero coherence for the lifted smoothing composition isomorphism.
-/
theorem constructibleSmoothingCompIso_zero_left (δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    (constructibleSmoothingCompIso 0 δ).hom.app G ≫
        (constructibleSmoothingMap (zero_add δ).le).app G =
      constructibleSmoothingZeroIso.hom.app ((constructibleSmoothing δ).obj G) := by
  apply ObjectProperty.hom_ext
  exact smoothingCompIso_zero_left δ G.obj

/--
The right zero coherence for the lifted smoothing composition isomorphism.
-/
theorem constructibleSmoothingCompIso_zero_right (δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    (constructibleSmoothingCompIso δ 0).hom.app G ≫
        (constructibleSmoothingMap (add_zero δ).le).app G =
      (constructibleSmoothing δ).map (constructibleSmoothingZeroIso.hom.app G) := by
  apply ObjectProperty.hom_ext
  exact smoothingCompIso_zero_right δ G.obj

/--
The commutation isomorphism between two lifted smoothing functors.
-/
def constructibleSmoothingCommIso (ε δ : ℝ≥0) :
    constructibleSmoothing.{u} ε ⋙ constructibleSmoothing δ ≅
      constructibleSmoothing δ ⋙ constructibleSmoothing ε :=
  NatIso.ofComponents
    (fun G => ObjectProperty.isoMk _ ((smoothingCommIso ε δ).app G.obj))
    (fun f => by
      ext : 1
      exact (smoothingCommIso ε δ).hom.naturality f.hom)

/--
The underlying hom of the lifted smoothing commutation isomorphism.
-/
@[simp] theorem constructibleSmoothingCommIso_hom_app_hom (ε δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    ((constructibleSmoothingCommIso ε δ).hom.app G).hom =
      (smoothingCommIso ε δ).hom.app G.obj :=
  rfl

/--
The underlying inverse hom of the lifted smoothing commutation isomorphism.
-/
@[simp] theorem constructibleSmoothingCommIso_inv_app_hom (ε δ : ℝ≥0)
    (G : ConstructibleCosheafCat.{u}) :
    ((constructibleSmoothingCommIso ε δ).inv.app G).hom =
      (smoothingCommIso ε δ).inv.app G.obj :=
  rfl

end

end TDA.Reeb
