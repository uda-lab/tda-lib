import TDA.Reeb.ConstructibleThickeningQuotient
import TDA.Reeb.GeometricEnlargement
import TDA.Reeb.Stability

/-!
# Interleavings of constructible ℝ-spaces

This module develops the constructible-space side of geometric interleavings.  It first packages
the Reeb quotient as a reflection from constructible ℝ-spaces to graph objects, and then transports
geometric smoothing, its unit, and its additive coherence to constructible ℝ-spaces.  The later
parts of the file define interleavings by maps out of the spaces themselves, identify them with the
transpose formulation on graph objects, and record the resulting distance identities and stability
bounds.  These are library statements; only the statement shape of DMP15-v1 Definition 4.36 is
attributed to that source.  See `docs/math/reeb-geometric-interleaving-equivalence.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace RGraph

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ
local notation "Rq" => quotientRGraphFunctor

/-! ### (A) The reflection -/

/-- Graph objects are constructible ℝ-spaces, with the fully faithful inclusion. -/
def rgraphToConstructible : RGraphCat ⥤ ConstructibleSpaceCat :=
  ObjectProperty.ιOfLE (fun _ hA => isConstructibleSpace_of_isRGraph hA)

/-- The quotient functor maps the projection of a constructible space to the next projection. -/
theorem quotientFunctor_map_projNatTrans_app (X : ConstructibleSpaceCat) :
    (ℛ).map ((ReebQuotient.projNatTrans ℝ).app X.obj) =
      (ReebQuotient.projNatTrans ℝ).app ((ℛ).obj X.obj) := by
  exact Over.OverMorphism.ext (by
    ext q
    induction q using ReebQuotient.ind with
    | h x => rfl)

/-- The Reeb quotient is left adjoint to the inclusion of graph objects. -/
def quotientRGraphAdjunction : quotientRGraphFunctor ⊣ rgraphToConstructible :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app := fun X => ObjectProperty.homMk ((ReebQuotient.projNatTrans ℝ).app X.obj)
          naturality := by
            intro X Y f
            ext1
            exact (ReebQuotient.projNatTrans ℝ).naturality f.hom }
      counit :=
        { app := fun A => ObjectProperty.homMk (projNatIso.app A).inv
          naturality := by
            intro A B f
            ext1
            change (ℛ).map f.hom ≫ (projNatIso.app B).inv =
              (projNatIso.app A).inv ≫ f.hom
            rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
            change (ReebQuotient.projNatTrans ℝ).app A.obj ≫ (ℛ).map f.hom =
              f.hom ≫ (ReebQuotient.projNatTrans ℝ).app B.obj
            exact ((ReebQuotient.projNatTrans ℝ).naturality f.hom).symm }
      left_triangle := by
        refine NatTrans.ext (funext fun X => ObjectProperty.hom_ext _ ?_)
        change (ℛ).map ((ReebQuotient.projNatTrans ℝ).app X.obj) ≫
          (projNatIso.app (quotientRGraphFunctor.obj X)).inv = 𝟙 _
        rw [quotientFunctor_map_projNatTrans_app]
        exact (projNatIso.app (quotientRGraphFunctor.obj X)).hom_inv_id
      right_triangle := by
        refine NatTrans.ext (funext fun A => ObjectProperty.hom_ext _ ?_)
        change (projNatIso.app A).hom ≫ (projNatIso.app A).inv = 𝟙 _
        exact (projNatIso.app A).hom_inv_id }

/-- The unit of the reflection is the canonical Reeb projection. -/
theorem quotientRGraphAdjunction_unit_app_hom (X : ConstructibleSpaceCat) :
    (quotientRGraphAdjunction.unit.app X).hom =
      (ReebQuotient.projNatTrans ℝ).app X.obj :=
  rfl

/-- The counit of the reflection is the inverse of the graph projection isomorphism. -/
theorem quotientRGraphAdjunction_counit_app_hom (A : RGraphCat) :
    (quotientRGraphAdjunction.counit.app A).hom = (projNatIso.app A).inv :=
  rfl

/-! ### (B) Smoothing on constructible ℝ-spaces -/

/-- `ℛ T_ε` as an endofunctor of constructible ℝ-spaces. -/
def constructibleSmoothing (ε : ℝ≥0) : ConstructibleSpaceCat ⥤ ConstructibleSpaceCat :=
  thickeningQuotient ε ⋙ rgraphToConstructible

/-- The inclusion followed by constructible thickening and quotient is graph smoothing. -/
theorem rgraphToConstructible_comp_thickeningQuotient (ε : ℝ≥0) :
    rgraphToConstructible ⋙ thickeningQuotient ε = geometricSmoothing ε :=
  rfl

/-- The unit `X ⟶ ℛ T_ε X`, given by `x ↦ [(x, 0)]`. -/
def constructibleSmoothingUnit (ε : ℝ≥0) :
    𝟭 ConstructibleSpaceCat ⟶ constructibleSmoothing ε where
  app X := ObjectProperty.homMk ((GeometricThickening.zeroSectionNatTrans ε).app X.obj ≫
    (ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor ε).obj X.obj))
  naturality _ _ φ := by
    ext1
    exact (GeometricThickening.zeroSectionNatTrans ε ≫
      Functor.whiskerLeft (GeometricThickening.functor ε) (ReebQuotient.projNatTrans ℝ)).naturality
      φ.hom

/-- The underlying hom of the constructible smoothing unit. -/
theorem constructibleSmoothingUnit_app_hom (ε : ℝ≥0) (X : ConstructibleSpaceCat) :
    ((constructibleSmoothingUnit ε).app X).hom =
      (GeometricThickening.zeroSectionNatTrans ε).app X.obj ≫
        (ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor ε).obj X.obj) :=
  rfl

/-- On points, the constructible smoothing unit is `x ↦ [(x, 0)]`. -/
theorem constructibleSmoothingUnit_app_hom_left_apply (ε : ℝ≥0) (X : ConstructibleSpaceCat)
    (x : X.obj.left) :
    ((constructibleSmoothingUnit ε).app X).hom.left.hom x =
      ReebQuotient.mk _ (GeometricThickening.zeroSection X.obj.left ε x) :=
  rfl

/-- The additive coherence isomorphism for constructible smoothing, with components obtained by
applying the inclusion to `thickeningQuotientCompIso`; this uses the inclusion identity
`rgraphToConstructible_comp_thickeningQuotient`, which is definitional (`rfl`). -/
def constructibleSmoothingCompIso (ε δ : ℝ≥0) :
    constructibleSmoothing δ ⋙ constructibleSmoothing ε ≅ constructibleSmoothing (ε + δ) :=
  NatIso.ofComponents
    (fun X => rgraphToConstructible.mapIso ((thickeningQuotientCompIso ε δ).app X))
    (fun f => (Functor.isoWhiskerRight (thickeningQuotientCompIso ε δ)
      rgraphToConstructible).hom.naturality f)

/-- The hom component of constructible smoothing coherence is the graph coherence map. -/
theorem constructibleSmoothingCompIso_hom_app (ε δ : ℝ≥0) (X : ConstructibleSpaceCat) :
    (constructibleSmoothingCompIso ε δ).hom.app X =
      rgraphToConstructible.map ((thickeningQuotientCompIso ε δ).hom.app X) := by
  rfl

/-! ### Compatibility with the reflection -/

/-- The absorption component is constructible thickening of the adjunction unit. -/
theorem thickeningQuotientAbsorptionIso_hom_app_eq (ε : ℝ≥0) (X : ConstructibleSpaceCat) :
    (thickeningQuotientAbsorptionIso ε).hom.app X =
      (thickeningQuotient ε).map (quotientRGraphAdjunction.unit.app X) := by
  ext1
  rw [thickeningQuotientAbsorptionIso_hom_app_hom]
  rfl

/-- The constructible smoothing unit is the transpose of the graph smoothing unit. -/
theorem homEquiv_symm_constructibleSmoothingUnit (ε : ℝ≥0) (X : ConstructibleSpaceCat) :
    (quotientRGraphAdjunction.homEquiv _ _).symm ((constructibleSmoothingUnit ε).app X) ≫
        (thickeningQuotientAbsorptionIso ε).hom.app X =
      (geometricSmoothingUnit ε).app (quotientRGraphFunctor.obj X) := by
  let u : X ⟶ rgraphToConstructible.obj ((thickeningQuotient ε).obj X) :=
    (constructibleSmoothingUnit ε).app X
  have h : u ≫ rgraphToConstructible.map ((thickeningQuotientAbsorptionIso ε).hom.app X) =
      quotientRGraphAdjunction.unit.app X ≫
        rgraphToConstructible.map ((geometricSmoothingUnit ε).app (quotientRGraphFunctor.obj X)) := by
    ext1
    exact Over.OverMorphism.ext (by
      ext x
      rfl)
  calc
    (quotientRGraphAdjunction.homEquiv _ _).symm u ≫
        (thickeningQuotientAbsorptionIso ε).hom.app X =
      (quotientRGraphAdjunction.homEquiv _ _).symm
        (u ≫ rgraphToConstructible.map ((thickeningQuotientAbsorptionIso ε).hom.app X)) :=
      (Adjunction.homEquiv_naturality_right_symm quotientRGraphAdjunction u
        ((thickeningQuotientAbsorptionIso ε).hom.app X)).symm
    _ = (quotientRGraphAdjunction.homEquiv _ _).symm
          (quotientRGraphAdjunction.homEquiv _ _
            ((geometricSmoothingUnit ε).app (quotientRGraphFunctor.obj X))) := by
        rw [h, Adjunction.homEquiv_unit]
        rfl
    _ = _ := Equiv.symm_apply_apply _ _

/-! ### (C) Constructible interleavings -/

/-- A constructible `ε`-interleaving, with maps out of the spaces themselves. -/
structure ConstructibleInterleaving (ε : ℝ≥0) (X Y : ConstructibleSpaceCat) where
  /-- The map from `X` to the smoothing of `Y`. -/
  φ : X ⟶ (constructibleSmoothing ε).obj Y
  /-- The map from `Y` to the smoothing of `X`. -/
  ψ : Y ⟶ (constructibleSmoothing ε).obj X
  /-- The shifted composite at `X` is the smoothing unit. -/
  φ_ψ : φ ≫ (constructibleSmoothing ε).map ψ ≫
      (constructibleSmoothingCompIso ε ε).hom.app X =
    (constructibleSmoothingUnit (ε + ε)).app X
  /-- The shifted composite at `Y` is the smoothing unit. -/
  ψ_φ : ψ ≫ (constructibleSmoothing ε).map φ ≫
      (constructibleSmoothingCompIso ε ε).hom.app Y =
    (constructibleSmoothingUnit (ε + ε)).app Y

namespace ConstructibleInterleaving

variable {ε : ℝ≥0} {X Y : ConstructibleSpaceCat}

/-- Two constructible interleavings are equal when their two maps are equal. -/
@[ext] theorem ext {i j : ConstructibleInterleaving ε X Y} (hφ : i.φ = j.φ)
    (hψ : i.ψ = j.ψ) : i = j := by
  cases i
  cases j
  cases hφ
  cases hψ
  rfl

/-- Symmetry: swap the two maps and the two coherence equations. -/
def symm (i : ConstructibleInterleaving ε X Y) : ConstructibleInterleaving ε Y X where
  φ := i.ψ
  ψ := i.φ
  φ_ψ := i.ψ_φ
  ψ_φ := i.φ_ψ

/-- The transpose calculation identifying constructible and graph coherence. -/
theorem coherence_iff (φ : X ⟶ (constructibleSmoothing ε).obj Y)
    (ψ : Y ⟶ (constructibleSmoothing ε).obj X) :
    (φ ≫ (constructibleSmoothing ε).map ψ ≫
        (constructibleSmoothingCompIso ε ε).hom.app X =
      (constructibleSmoothingUnit (ε + ε)).app X) ↔
      ((quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ ≫
        (thickeningQuotientAbsorptionIso ε).hom.app Y) ≫
        (geometricSmoothing ε).map
          ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ ≫
            (thickeningQuotientAbsorptionIso ε).hom.app X) ≫
        (geometricSmoothingCompIso ε ε).hom.app (quotientRGraphFunctor.obj X) =
      (geometricSmoothingUnit (ε + ε)).app (quotientRGraphFunctor.obj X) := by
  let φ₀ : X ⟶ rgraphToConstructible.obj ((thickeningQuotient ε).obj Y) := φ
  let ψ₀ : Y ⟶ rgraphToConstructible.obj ((thickeningQuotient ε).obj X) := ψ
  change
    (φ₀ ≫ rgraphToConstructible.map ((thickeningQuotient ε).map ψ₀) ≫
        rgraphToConstructible.map ((thickeningQuotientCompIso ε ε).hom.app X) =
      (constructibleSmoothingUnit (ε + ε)).app X) ↔
      ((quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ₀ ≫
        (thickeningQuotientAbsorptionIso ε).hom.app Y) ≫
        (geometricSmoothing ε).map
          ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀ ≫
            (thickeningQuotientAbsorptionIso ε).hom.app X) ≫
        (geometricSmoothingCompIso ε ε).hom.app (quotientRGraphFunctor.obj X) =
      (geometricSmoothingUnit (ε + ε)).app (quotientRGraphFunctor.obj X)
  let aε := thickeningQuotientAbsorptionIso ε
  let a2ε := thickeningQuotientAbsorptionIso (ε + ε)
  let μ := geometricSmoothingCompIso ε ε
  let c := thickeningQuotientCompIso ε ε
  have hmap {A B : RGraphCat} (g : A ⟶ B) :
      (thickeningQuotient ε).map (rgraphToConstructible.map g) =
        (geometricSmoothing ε).map g := by
    change (rgraphToConstructible ⋙ thickeningQuotient ε).map g =
      (geometricSmoothing ε).map g
    rfl
  have hc : c.hom.app X =
      (geometricSmoothing ε).map (aε.hom.app X) ≫
        μ.hom.app (quotientRGraphFunctor.obj X) ≫ a2ε.inv.app X := by
    simp [c, aε, a2ε, μ, thickeningQuotientCompIso, Functor.associator]
  have hψ : ψ₀ = quotientRGraphAdjunction.unit.app Y ≫
      rgraphToConstructible.map
        ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀) := by
    change ψ₀ =
      (quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X))
        ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀)
    exact ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).apply_symm_apply ψ₀).symm.trans
      (Adjunction.homEquiv_unit quotientRGraphAdjunction _ _ _)
  have hcomp :
      (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient (ε + ε)).obj X)).symm
          (φ₀ ≫ rgraphToConstructible.map ((thickeningQuotient ε).map ψ₀) ≫
            rgraphToConstructible.map (c.hom.app X)) =
        (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ₀ ≫
          (thickeningQuotient ε).map ψ₀ ≫ c.hom.app X := by
    calc
      _ = (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient (ε + ε)).obj X)).symm
          (φ₀ ≫ rgraphToConstructible.map
            ((thickeningQuotient ε).map ψ₀ ≫ c.hom.app X)) := by
        exact congrArg
          (fun k => (quotientRGraphAdjunction.homEquiv
            X ((thickeningQuotient (ε + ε)).obj X)).symm (φ₀ ≫ k))
          (rgraphToConstructible.map_comp ((thickeningQuotient ε).map ψ₀)
            (c.hom.app X)).symm
      _ = (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ₀ ≫
          (thickeningQuotient ε).map ψ₀ ≫ c.hom.app X :=
        Adjunction.homEquiv_naturality_right_symm quotientRGraphAdjunction φ₀
          ((thickeningQuotient ε).map ψ₀ ≫ c.hom.app X)
  have hcomp' :
      (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient (ε + ε)).obj X)).symm
          (φ₀ ≫ rgraphToConstructible.map ((thickeningQuotient ε).map ψ₀) ≫
            rgraphToConstructible.map (c.hom.app X)) =
        ((quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ₀ ≫
          aε.hom.app Y) ≫
          (geometricSmoothing ε).map
            ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀ ≫
              aε.hom.app X) ≫
          μ.hom.app (quotientRGraphFunctor.obj X) ≫ a2ε.inv.app X := by
    calc
      _ = (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ₀ ≫
          (thickeningQuotient ε).map ψ₀ ≫ c.hom.app X := hcomp
      _ = (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ₀ ≫
          aε.hom.app Y ≫
          (geometricSmoothing ε).map
            ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀) ≫
          c.hom.app X := by
        have hT : (thickeningQuotient ε).map ψ₀ = aε.hom.app Y ≫
            (geometricSmoothing ε).map
              ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀) := by
          calc
            (thickeningQuotient ε).map ψ₀ = (thickeningQuotient ε).map
                (quotientRGraphAdjunction.unit.app Y ≫ rgraphToConstructible.map
                  ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀)) :=
              congrArg _ hψ
            _ = (thickeningQuotient ε).map (quotientRGraphAdjunction.unit.app Y) ≫
                (thickeningQuotient ε).map (rgraphToConstructible.map
                  ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀)) :=
              Functor.map_comp _ _ _
            _ = _ := by
              rw [← thickeningQuotientAbsorptionIso_hom_app_eq]
              rfl
        rw [hT]
        exact congrArg (fun k => _ ≫ k) (Category.assoc _ _ _)
      _ = ((quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm φ₀ ≫
            aε.hom.app Y) ≫
          (geometricSmoothing ε).map
            ((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm ψ₀ ≫
              aε.hom.app X) ≫
          μ.hom.app (quotientRGraphFunctor.obj X) ≫ a2ε.inv.app X := by
        rw [hc]
        simp only [Functor.map_comp, Category.assoc]
  have hunit :
      (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient (ε + ε)).obj X)).symm
          ((constructibleSmoothingUnit (ε + ε)).app X) =
        (geometricSmoothingUnit (ε + ε)).app (quotientRGraphFunctor.obj X) ≫
          a2ε.inv.app X := by
    calc
      _ = ((quotientRGraphAdjunction.homEquiv X ((thickeningQuotient (ε + ε)).obj X)).symm
            ((constructibleSmoothingUnit (ε + ε)).app X) ≫ a2ε.hom.app X) ≫
          a2ε.inv.app X := by simp [a2ε]
      _ = (geometricSmoothingUnit (ε + ε)).app (quotientRGraphFunctor.obj X) ≫
          a2ε.inv.app X := by
        exact congrArg (fun k => k ≫ a2ε.inv.app X)
          (homEquiv_symm_constructibleSmoothingUnit (ε + ε) X)
  constructor
  · intro h
    exact (cancel_mono (a2ε.inv.app X)).1
      (hcomp'.symm.trans
        ((congrArg (fun k =>
          (quotientRGraphAdjunction.homEquiv
            X ((thickeningQuotient (ε + ε)).obj X)).symm k) h).trans hunit))
  · intro h
    apply (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient (ε + ε)).obj X)).symm.injective
    exact hcomp'.trans
      ((congrArg (fun k => k ≫ a2ε.inv.app X) h).trans hunit.symm)

/-- The equivalence between constructible and graph geometric interleavings. -/
def equivGeometric (ε : ℝ≥0) (X Y : ConstructibleSpaceCat) :
    ConstructibleInterleaving ε X Y ≃
      GeometricInterleaving ε (quotientRGraphFunctor.obj X) (quotientRGraphFunctor.obj Y) where
  toFun i :=
    { φ := (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm i.φ ≫
          (thickeningQuotientAbsorptionIso ε).hom.app Y
      ψ := (quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm i.ψ ≫
          (thickeningQuotientAbsorptionIso ε).hom.app X
      φ_ψ := (coherence_iff i.φ i.ψ).1 i.φ_ψ
      ψ_φ := (coherence_iff (X := Y) (Y := X) i.ψ i.φ).1 i.ψ_φ }
  invFun j :=
    { φ := quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)
          (j.φ ≫ (thickeningQuotientAbsorptionIso ε).inv.app Y)
      ψ := quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)
          (j.ψ ≫ (thickeningQuotientAbsorptionIso ε).inv.app X)
      φ_ψ := by
        apply (coherence_iff _ _).2
        simp only [Equiv.symm_apply_apply, Category.assoc, Iso.inv_hom_id_app]
        erw [Category.id_comp, Category.comp_id]
        exact j.φ_ψ
      ψ_φ := by
        apply (coherence_iff (X := Y) (Y := X) _ _).2
        simp only [Equiv.symm_apply_apply, Category.assoc, Iso.inv_hom_id_app]
        erw [Category.id_comp, Category.comp_id]
        exact j.ψ_φ }
  left_inv i := by
    apply ConstructibleInterleaving.ext
    · change (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y))
          (((quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm i.φ ≫
            (thickeningQuotientAbsorptionIso ε).hom.app Y) ≫
            (thickeningQuotientAbsorptionIso ε).inv.app Y) = i.φ
      simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      exact Equiv.apply_symm_apply _ _
    · change (quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X))
          (((quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm i.ψ ≫
            (thickeningQuotientAbsorptionIso ε).hom.app X) ≫
            (thickeningQuotientAbsorptionIso ε).inv.app X) = i.ψ
      simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      exact Equiv.apply_symm_apply _ _
  right_inv j := by
    apply GeometricInterleaving.ext
    · simp [Category.assoc]
    · simp [Category.assoc]

/-- The first map of the transpose equivalence. -/
theorem equivGeometric_φ (i : ConstructibleInterleaving ε X Y) :
    (equivGeometric ε X Y i).φ =
      (quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)).symm i.φ ≫
        (thickeningQuotientAbsorptionIso ε).hom.app Y :=
  rfl

/-- The second map of the transpose equivalence. -/
theorem equivGeometric_ψ (i : ConstructibleInterleaving ε X Y) :
    (equivGeometric ε X Y i).ψ =
      (quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)).symm i.ψ ≫
        (thickeningQuotientAbsorptionIso ε).hom.app X :=
  rfl

/-- The first map obtained by transposing a graph interleaving back. -/
theorem equivGeometric_symm_φ
    (j : GeometricInterleaving ε (quotientRGraphFunctor.obj X)
      (quotientRGraphFunctor.obj Y)) :
    ((equivGeometric ε X Y).symm j).φ =
      quotientRGraphAdjunction.homEquiv X ((thickeningQuotient ε).obj Y)
        (j.φ ≫ (thickeningQuotientAbsorptionIso ε).inv.app Y) :=
  rfl

/-- The second map obtained by transposing a graph interleaving back. -/
theorem equivGeometric_symm_ψ
    (j : GeometricInterleaving ε (quotientRGraphFunctor.obj X)
      (quotientRGraphFunctor.obj Y)) :
    ((equivGeometric ε X Y).symm j).ψ =
      quotientRGraphAdjunction.homEquiv Y ((thickeningQuotient ε).obj X)
        (j.ψ ≫ (thickeningQuotientAbsorptionIso ε).inv.app X) :=
  rfl

/-- `X` and its Reeb graph are `0`-interleaved. -/
def toQuotient (X : ConstructibleSpaceCat) :
    ConstructibleInterleaving 0 X
      (rgraphToConstructible.obj (quotientRGraphFunctor.obj X)) := by
  let e : quotientRGraphFunctor.obj X ≅
      quotientRGraphFunctor.obj (rgraphToConstructible.obj (quotientRGraphFunctor.obj X)) :=
    (ObjectProperty.isoMk _ (projNatIso.app (quotientRGraphFunctor.obj X)).symm).symm
  exact (equivGeometric 0 X
    (rgraphToConstructible.obj (quotientRGraphFunctor.obj X))).symm
    (GeometricInterleaving.ofIso e)

end ConstructibleInterleaving

/-! ### (D) The constructible interleaving distance -/

/-- The distance is the infimum of constructible interleaving parameters. -/
noncomputable def constructibleInterleavingDistance (X Y : ConstructibleSpaceCat) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (ConstructibleInterleaving ε X Y)), (ε : ℝ≥0∞)

variable {X Y : ConstructibleSpaceCat}

/-- A constructible interleaving witnesses an upper bound for the distance. -/
theorem constructibleInterleavingDistance_le_of_nonempty {ε : ℝ≥0}
    (h : Nonempty (ConstructibleInterleaving ε X Y)) :
    constructibleInterleavingDistance X Y ≤ ε :=
  iInf₂_le ε h

/-- The constructible distance equals the geometric distance of the Reeb graphs. -/
theorem constructibleInterleavingDistance_eq_geometricInterleavingDistance
    (X Y : ConstructibleSpaceCat) :
    constructibleInterleavingDistance X Y =
      geometricInterleavingDistance (quotientRGraphFunctor.obj X)
        (quotientRGraphFunctor.obj Y) := by
  unfold constructibleInterleavingDistance geometricInterleavingDistance
  refine iInf_congr fun ε => ?_
  exact iInf_congr_Prop (ConstructibleInterleaving.equivGeometric ε X Y).nonempty_congr
    (fun _ => rfl)

/-- The constructible distance is the interleaving distance of the spaces' interval components. -/
theorem constructibleInterleavingDistance_eq_interleavingDistance
    (X Y : ConstructibleSpaceCat) :
    constructibleInterleavingDistance X Y =
      interleavingDistance (intervalComponents (overBaseMap X.obj))
        (intervalComponents (overBaseMap Y.obj)) := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance,
    geometricInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_congr
    (show (cosheafFunctor.obj (quotientRGraphFunctor.obj X)).obj ≅
        intervalComponents (overBaseMap X.obj) from
      (constructibleComponentComparisonIso.app X).symm)
    (show (cosheafFunctor.obj (quotientRGraphFunctor.obj Y)).obj ≅
        intervalComponents (overBaseMap Y.obj) from
      (constructibleComponentComparisonIso.app Y).symm)

/-- The constructible distance from a space to itself is zero. -/
theorem constructibleInterleavingDistance_self (X : ConstructibleSpaceCat) :
    constructibleInterleavingDistance X X = 0 := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance]
  exact geometricInterleavingDistance_self _

/-- The constructible distance is symmetric. -/
theorem constructibleInterleavingDistance_comm (X Y : ConstructibleSpaceCat) :
    constructibleInterleavingDistance X Y = constructibleInterleavingDistance Y X := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance,
    constructibleInterleavingDistance_eq_geometricInterleavingDistance]
  exact geometricInterleavingDistance_comm _ _

/-- The constructible distance satisfies the triangle inequality. -/
theorem constructibleInterleavingDistance_triangle
    (X Y Z : ConstructibleSpaceCat) :
    constructibleInterleavingDistance X Z ≤
      constructibleInterleavingDistance X Y + constructibleInterleavingDistance Y Z := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance,
    constructibleInterleavingDistance_eq_geometricInterleavingDistance,
    constructibleInterleavingDistance_eq_geometricInterleavingDistance]
  exact geometricInterleavingDistance_triangle _ _ _

/-- Zero constructible distance is equivalent to witnesses at every positive parameter. -/
theorem constructibleInterleavingDistance_eq_zero_iff :
    constructibleInterleavingDistance X Y = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε → Nonempty (ConstructibleInterleaving ε X Y) := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance,
    geometricInterleavingDistance_eq_zero_iff]
  exact forall₂_congr fun ε hε =>
    (ConstructibleInterleaving.equivGeometric ε X Y).nonempty_congr.symm

/-- The constructible distance is invariant under isomorphisms in both arguments. -/
theorem constructibleInterleavingDistance_congr {X X' Y Y' : ConstructibleSpaceCat}
    (e : X ≅ X') (e' : Y ≅ Y') :
    constructibleInterleavingDistance X Y = constructibleInterleavingDistance X' Y' := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance,
    constructibleInterleavingDistance_eq_geometricInterleavingDistance]
  exact geometricInterleavingDistance_congr (quotientRGraphFunctor.mapIso e)
    (quotientRGraphFunctor.mapIso e')

/-- A constructible space has zero distance from its Reeb graph viewed as a space. -/
theorem constructibleInterleavingDistance_quotient (X : ConstructibleSpaceCat) :
    constructibleInterleavingDistance X
      (rgraphToConstructible.obj (quotientRGraphFunctor.obj X)) = 0 := by
  apply nonpos_iff_eq_zero.1
  exact constructibleInterleavingDistance_le_of_nonempty
    ⟨ConstructibleInterleaving.toQuotient X⟩

private def quotientCounitIso (A : RGraphCat) :
    quotientRGraphFunctor.obj (rgraphToConstructible.obj A) ≅ A :=
  ObjectProperty.isoMk _ (projNatIso.app A).symm

/-- On graph objects, the constructible distance is the geometric graph distance. -/
theorem constructibleInterleavingDistance_rgraphToConstructible (A B : RGraphCat) :
    constructibleInterleavingDistance (rgraphToConstructible.obj A)
        (rgraphToConstructible.obj B) = geometricInterleavingDistance A B := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance]
  exact geometricInterleavingDistance_congr
    (quotientCounitIso A) (quotientCounitIso B)

private def constructibleSmoothingQuotientIso (ε : ℝ≥0) (X : ConstructibleSpaceCat) :
    quotientRGraphFunctor.obj ((constructibleSmoothing ε).obj X) ≅
      (geometricSmoothing ε).obj (quotientRGraphFunctor.obj X) :=
  quotientCounitIso ((thickeningQuotient ε).obj X) ≪≫
    (thickeningQuotientAbsorptionIso ε).app X

/-- A space and its constructible smoothing are at most `ε` apart. -/
theorem constructibleInterleavingDistance_constructibleSmoothing_self_le
    (ε : ℝ≥0) (X : ConstructibleSpaceCat) :
    constructibleInterleavingDistance X ((constructibleSmoothing ε).obj X) ≤ ε := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance]
  calc
    geometricInterleavingDistance (quotientRGraphFunctor.obj X)
        (quotientRGraphFunctor.obj ((constructibleSmoothing ε).obj X)) =
      geometricInterleavingDistance (quotientRGraphFunctor.obj X)
        ((geometricSmoothing ε).obj (quotientRGraphFunctor.obj X)) :=
      geometricInterleavingDistance_congr (Iso.refl _)
        (constructibleSmoothingQuotientIso ε X)
    _ ≤ ε := geometricInterleavingDistance_geometricSmoothing_self_le ε _

/-- Smoothing both constructible spaces is nonexpansive for the distance. -/
theorem constructibleInterleavingDistance_constructibleSmoothing_le
    (ε : ℝ≥0) (X Y : ConstructibleSpaceCat) :
    constructibleInterleavingDistance ((constructibleSmoothing ε).obj X)
        ((constructibleSmoothing ε).obj Y) ≤ constructibleInterleavingDistance X Y := by
  rw [constructibleInterleavingDistance_eq_geometricInterleavingDistance,
    constructibleInterleavingDistance_eq_geometricInterleavingDistance]
  calc
    geometricInterleavingDistance (quotientRGraphFunctor.obj ((constructibleSmoothing ε).obj X))
        (quotientRGraphFunctor.obj ((constructibleSmoothing ε).obj Y)) =
      geometricInterleavingDistance ((geometricSmoothing ε).obj (quotientRGraphFunctor.obj X))
        ((geometricSmoothing ε).obj (quotientRGraphFunctor.obj Y)) :=
      geometricInterleavingDistance_congr (constructibleSmoothingQuotientIso ε X)
        (constructibleSmoothingQuotientIso ε Y)
    _ ≤ geometricInterleavingDistance (quotientRGraphFunctor.obj X)
        (quotientRGraphFunctor.obj Y) := geometricInterleavingDistance_geometricSmoothing_le ε _ _

/-- Sup-norm stability for constructible spaces on a common carrier. -/
theorem constructibleInterleavingDistance_le_edist {Z : Type} [TopologicalSpace Z]
    {f g : C(Z, ℝ)}
    (hf : IsConstructibleSpace (Over.mk (TopCat.ofHom f)))
    (hg : IsConstructibleSpace (Over.mk (TopCat.ofHom g))) :
    constructibleInterleavingDistance ⟨_, hf⟩ ⟨_, hg⟩ ≤
      edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) := by
  rw [constructibleInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_intervalComponents_le_edist f g

end RGraph

end

end TDA.Reeb
