import TDA.Sheaf.BaseChangePasting
import TDA.Sheaf.DerivedStalks
import TDA.Sheaf.PointSheaf

/-!
# Detection at points and the fibrewise criterion for base change

Let `k` be a ring and `X : TopCat.{0}`. For a point `x : X` write `ptOf x : pt ⟶ X` for its
inclusion.

* `rightDerivedFunctorPlusCompHomologyIso F i`: for an exact functor `F` between abelian
  categories (enough injectives on the source), the natural isomorphism
  `RF ⋙ Hⁱ ≅ Hⁱ ⋙ F` of functors on `D⁺`. On `Q K` it is the comparison `F K ≅ RF(K)` followed by
  `Hⁱ(F K) ≅ F(Hⁱ K)`; the localization property of `Q` extends it to all of `D⁺`.
* `isIso_iff_forall_isIso_pullbackPlus_pt`: **detection at points.** A morphism `φ` of
  `D⁺(Sh X)` is an isomorphism if and only if its derived inverse image `(ptOf x)⁻¹ φ` to the
  point is an isomorphism for every `x : X`. The inverse image along `ptOf x` is exact, so
  `Hⁱ((ptOf x)⁻¹ φ)` is `(ptOf x)⁻¹ Hⁱ(φ)`, whose stalk is the stalk of `Hⁱ(φ)` at `x`
  (`stalkPullbackSheafNatIso`); `isIso_iff_isIso_stalk_homology` concludes.
* `isIso_baseChange_congr`: base-change morphisms of two squares with the same vertical maps and
  equal horizontal maps are invertible together.
* `isIso_baseChange_of_fibres`: **the fibrewise criterion.** For a commutative square
  `w : g' ≫ f = f' ≫ g`, suppose that at every point `z : Y'` a square
  `e z ≫ f' = toPt (F z) ≫ ptOf z` (a fibre of `f'` at `z`) has invertible base change, and so
  has its pasting `(e z ≫ g') ≫ f = toPt (F z) ≫ ptOf z ≫ g` with `w`. Then the base change of
  `w` is invertible. By pasting (`baseChange_comp_app`), `(ptOf z)⁻¹` of the base change of `w`
  is invertible at every `z`, and detection at points concludes.
-/

noncomputable section
open CategoryTheory Limits

namespace TDA.Sheaf

section exact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

variable (C) in
/-- On `Q K`, the homology functor of `D⁺` is the homology of the complex `K`. -/
private def plusHomologyQIso (i : ℤ) :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C i ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.QCompιIso C) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C i)

/-- A functor preserving homology commutes with the homology of complexes. -/
private def mapHomologicalComplexHomologyIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [F.PreservesHomology] (i : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso F)
    (fun φ => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map φ) F)

variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- **The derived functor of an exact functor commutes with homology.** For an exact functor
`F` and every degree `i`, the natural isomorphism `RF ⋙ Hⁱ ≅ Hⁱ ⋙ F` of functors
`D⁺(C) ⥤ D`. -/
def rightDerivedFunctorPlusCompHomologyIso (i : ℤ) :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D i ≅
      DerivedCategory.Plus.homologyFunctor C i ⋙ F :=
  Localization.liftNatIso DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C)
    (DerivedCategory.Plus.Q ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D i)
    (DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.homologyFunctor C i ⋙ F) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso F.rightDerivedFunctorPlusUnit).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (plusHomologyQIso D i) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapCochainComplexPlusCompι _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (mapHomologicalComplexHomologyIso F i) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (plusHomologyQIso C i).symm F ≪≫
      Functor.associator _ _ _)

end exact

variable {k : Type} [Ring k]

/-- **Detection of isomorphisms at points.** A morphism `φ` of `D⁺(Sh X)`, for sheaves of
`k`-modules on `X`, is an isomorphism if and only if, for every point `x : X`, its derived inverse
image `(ptOf x)⁻¹ φ` along the inclusion of the point is an isomorphism of `D⁺(Sh pt)`. -/
theorem isIso_iff_forall_isIso_pullbackPlus_pt {X : TopCat.{0}}
    [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
    {K L : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))} (φ : K ⟶ L) :
    IsIso φ ↔ ∀ x : X, IsIso ((pullbackPlus k (ptOf x)).map φ) := by
  refine ⟨fun _ x => inferInstance, fun h => ?_⟩
  rw [isIso_iff_isIso_stalk_homology]
  intro i x
  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map
      ((pullbackPlus k (ptOf x)).map φ)) := inferInstance
  have h₂ : IsIso ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptOf x)).map
      ((DerivedCategory.Plus.homologyFunctor _ i).map φ)) :=
    (NatIso.isIso_map_iff (rightDerivedFunctorPlusCompHomologyIso
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptOf x)) i) φ).1 h₁
  exact (NatIso.isIso_map_iff (stalkPullbackSheafNatIso k (ptOf x) PUnit.unit)
    ((DerivedCategory.Plus.homologyFunctor _ i).map φ)).2
    (Functor.map_isIso (TopCat.Sheaf.forget (ModuleCat.{0} k) pt ⋙
      TopCat.Presheaf.stalkFunctor _ PUnit.unit) ((TopCat.Sheaf.pullback (ModuleCat.{0} k)
        (ptOf x)).map ((DerivedCategory.Plus.homologyFunctor _ i).map φ)))

section fibrewise

variable (k)
variable {X Y X' Y' : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Base change along equal maps.** For two commutative squares with the same vertical maps
`f`, `f'` and equal horizontal maps, one base-change morphism is invertible if and only if the
other is. -/
theorem isIso_baseChange_congr {g₁ g₂ : Y' ⟶ Y} {h₁ h₂ : X' ⟶ X} (w₁ : h₁ ≫ f = f' ≫ g₁)
    (w₂ : h₂ ≫ f = f' ≫ g₂) (hg : g₁ = g₂) (hh : h₁ = h₂) :
    IsIso (baseChange k w₁) ↔ IsIso (baseChange k w₂) := by
  subst hg hh
  rfl

variable [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]

/-- **The fibrewise criterion for base change.** Let `w : g' ≫ f = f' ≫ g` be a commutative
square. Suppose that for every point `z : Y'` a square `e z ≫ f' = toPt (F z) ≫ ptOf z` over the
point `z` has invertible base change, and that the pasted square
`(e z ≫ g') ≫ f = toPt (F z) ≫ ptOf z ≫ g` has invertible base change. Then the base-change
morphism `Rf_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ Rf'_*` of `w` is an isomorphism. -/
theorem isIso_baseChange_of_fibres (w : g' ≫ f = f' ≫ g) (F : Y' → TopCat.{0})
    [∀ z, HasDerivedCategory ((F z).Sheaf (ModuleCat.{0} k))] (e : ∀ z, F z ⟶ X')
    (we : ∀ z, e z ≫ f' = toPt (F z) ≫ ptOf z) (h₁ : ∀ z, IsIso (baseChange k (we z)))
    (h₂ : ∀ z (wz : (e z ≫ g') ≫ f = toPt (F z) ≫ ptOf z ≫ g), IsIso (baseChange k wz)) :
    IsIso (baseChange k w) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [isIso_iff_forall_isIso_pullbackPlus_pt]
  intro z
  have wz : (e z ≫ g') ≫ f = toPt (F z) ≫ ptOf z ≫ g := by
    rw [Category.assoc, w, ← Category.assoc, we z, Category.assoc]
  have := h₁ z
  have h3 : IsIso ((baseChange k wz).app M) := (NatTrans.isIso_iff_isIso_app _).1 (h₂ z wz) M
  rw [baseChange_comp_app k w (we z) wz M, isIso_comp_left_iff, ← Category.assoc,
    isIso_comp_right_iff, isIso_comp_right_iff] at h3
  exact h3

end fibrewise

end TDA.Sheaf
