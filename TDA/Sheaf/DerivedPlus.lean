import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedComposition
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Sheaves.Abelian

/-!
# Derived inverse and direct images of sheaves of modules on `D⁺`

Let `k` be a ring and write `Sh(X) := X.Sheaf (ModuleCat k)` for a topological space
`X : TopCat`. Sheaves of `k`-modules form a Grothendieck abelian category with enough
injectives. For each space a derived category structure is taken as an instance argument
`[HasDerivedCategory (X.Sheaf (ModuleCat k))]`; no global instance is installed. All functors
below act on the bounded below derived categories `DerivedCategory.Plus (Sh X)`.

* `pullbackPlus k f : D⁺(Sh Y) ⥤ D⁺(Sh X)` is Mathlib's `rightDerivedFunctorPlus` of the
  sheaf inverse image `f⁻¹ = TopCat.Sheaf.pullback (ModuleCat k) f`. This functor is exact
  (`pullback_preservesFiniteLimits`, `pullback_additive`), so its derived-functor
  comparisons are invertible (`isIso_rightDerivedFunctorPlusUnit_of_exact` on complexes,
  `isIso_rightDerivedFunctorPlusUnith_of_exact` on the homotopy category): `pullbackPlus`
  applies `f⁻¹` termwise.
* `pushforwardPlus k f : D⁺(Sh X) ⥤ D⁺(Sh Y)` is the right derived functor `Rf_*` of the
  direct image.
* `pushforwardPlusComp k f g : R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*` is Mathlib's comparison for
  composed right derived functors; it is invertible (`isIso_pushforwardPlusComp`) because
  `f_*` preserves injective objects. `pushforwardPlusCompIso` is the isomorphism.
* `pullbackPlusCompIso k f g : g⁻¹ ⋙ f⁻¹ ≅ (f ≫ g)⁻¹` on `D⁺`, induced by the underived
  `pullbackCompIso` (uniqueness of left adjoints).
* `derivedUnit k f : 𝟭 ⟶ f⁻¹ ⋙ Rf_*` is the derived unit: on `Q K` it is the sheaf
  adjunction unit applied termwise, followed by the derived-functor comparisons
  (`derivedUnit_app_Q`).

Coherence results:

* `isIso_derivedUnit`: the derived unit is invertible along a homeomorphism (an isomorphism
  in `TopCat`), because then `f_*` is an equivalence of sheaf categories
  (`pushforwardEquivalence`).
* `derivedUnit_comp_app`: the derived unit of `f ≫ g` agrees with the unit of `g`, then that
  of `f`, followed by `pullbackPlusCompIso` and `pushforwardPlusComp`.
* `pushforwardPlusComp_assoc_app`, `pullbackPlusCompHom_assoc_app` and
  `pullbackPlusCompIso_hom_assoc_app`: associativity of the composition comparisons;
  `pullbackCompIso_assoc` is the underived statement.

Correspondences. For maps `p : X ⟶ Z` and `q : X ⟶ W`, the functor
`pullbackPlus k p ⋙ pushforwardPlus k q` transforms along the correspondence `(p, q)`. A map
`j : X' ⟶ X` restricts it to `(j ≫ p, j ≫ q)`: `corrRestr k j p q` is the derived unit of `j`
followed by the composition isomorphisms. It is the identity for `j = 𝟙` (`corrRestr_id`),
composes along `i ≫ j` (`corrRestr_comp`) and is invertible when `j` is
(`isIso_corrRestr`), or more generally when the derived unit of `j` is
(`isIso_corrRestr_of_isIso_derivedUnit`).

Only `D⁺` is treated: at the pinned Mathlib, right derived functors exist on the bounded
below derived category.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

universe u

namespace TDA.Sheaf


variable (k : Type u) [Ring k]

section instances
variable {X Y : TopCat.{u}} (f : X ⟶ Y)

-- Instance search for exactness of the opaque sheaf pullback needs a larger local bound.
set_option synthInstance.maxHeartbeats 400000 in
/-- The sheaf inverse image is left exact. Instance search does not see through
`TopCat.Sheaf.pullback`, so the flat-pullback instance for `Opens.map f` is named. -/
instance pullback_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{u} k) f) :=
  Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f) (ModuleCat.{u} k) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The sheaf direct image is additive. -/
instance pushforward_additive : (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The sheaf inverse image is additive (left adjoint of an additive functor). -/
instance pullback_additive : (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).Additive :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction _ f).left_adjoint_additive


end instances

section exact
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [HasDerivedCategory C] [EnoughInjectives C] in
private lemma inverts_quasiIso_of_exact :
    (CochainComplex.Plus.quasiIso C).IsInvertedBy
      (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) := by
  intro K L g hg
  have hg' : CochainComplex.Plus.quasiIso D (F.mapCochainComplexPlus.map g) := by
    rw [CochainComplex.Plus.quasiIso_iff] at hg ⊢
    have : QuasiIso ((CochainComplex.Plus.ι C).map g) := hg
    exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  exact Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso D) _ hg'

/-- For an exact functor, the comparison `F.mapCochainComplexPlus ⋙ Q ⟶ Q ⋙ RF` of its
right derived functor on `D⁺` is invertible: `RF` applies `F` termwise. -/
instance isIso_rightDerivedFunctorPlusUnit_of_exact :
    IsIso F.rightDerivedFunctorPlusUnit :=
  Functor.isIso_of_isRightDerivedFunctor_of_inverts (W := CochainComplex.Plus.quasiIso C)
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit (inverts_quasiIso_of_exact F)

omit [HasDerivedCategory C] [EnoughInjectives C] in
private lemma inverts_quasiIso_of_exact_homotopy :
    (HomotopyCategory.Plus.quasiIso C).IsInvertedBy
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) := by
  rw [← HomotopyCategory.Plus.quasiIso_map_quotient_eq_quasiIso]
  rintro _ _ _ ⟨K, L, g, hg, ⟨e⟩⟩
  refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).mapArrow.mapIso e)).1 ?_
  have hg' : CochainComplex.Plus.quasiIso D (F.mapCochainComplexPlus.map g) := by
    rw [CochainComplex.Plus.quasiIso_iff] at hg ⊢
    have : QuasiIso ((CochainComplex.Plus.ι C).map g) := hg
    exact HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have h := Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso D) _ hg'
  have h' : IsIso ((HomotopyCategory.Plus.quotient D ⋙ DerivedCategory.Plus.Qh).map
      (F.mapCochainComplexPlus.map g)) :=
    (NatIso.isIso_map_iff (DerivedCategory.Plus.quotientCompQhIso D) _).2 h
  exact h'

/-- For an exact functor, the comparison `F.mapHomotopyCategoryPlus ⋙ Qh ⟶ Qh ⋙ RF` on
bounded below homotopy categories is invertible. -/
instance isIso_rightDerivedFunctorPlusUnith_of_exact :
    IsIso F.rightDerivedFunctorPlusUnith :=
  Functor.isIso_of_isRightDerivedFunctor_of_inverts (W := HomotopyCategory.Plus.quasiIso C)
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
    (inverts_quasiIso_of_exact_homotopy F)

end exact

/-- An isomorphism `F ⋙ G ≅ H` of additive functors induces
`F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅ H.mapCochainComplexPlus`, termwise. -/
def mapCochainComplexPlusCompIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] :
    F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅ H.mapCochainComplexPlus where
  hom := (NatTrans.mapCochainComplexPlus e.hom : (F ⋙ G).mapCochainComplexPlus ⟶ _)
  inv := (NatTrans.mapCochainComplexPlus e.inv : _ ⟶ (F ⋙ G).mapCochainComplexPlus)
  hom_inv_id := by
    rw [← NatTrans.mapCochainComplexPlus_comp]; simp; rfl
  inv_hom_id := by
    rw [← NatTrans.mapCochainComplexPlus_comp]; simp

/-- In degree `n`, `mapCochainComplexPlusCompIso e` is `e` at the `n`-th term. -/
@[simp]
lemma mapCochainComplexPlusCompIso_hom_app_hom_f {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Preadditive C] [Preadditive D] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (K : CochainComplex.Plus C) (n : ℤ) :
    ((mapCochainComplexPlusCompIso e).hom.app K).hom.f n = e.hom.app (K.obj.X n) := rfl

/-- In degree `n`, `(mapCochainComplexPlusCompIso e).inv` is `e.inv` at the `n`-th term. -/
@[simp]
lemma mapCochainComplexPlusCompIso_inv_app_hom_f {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Preadditive C] [Preadditive D] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (K : CochainComplex.Plus C) (n : ℤ) :
    ((mapCochainComplexPlusCompIso e).inv.app K).hom.f n = e.inv.app (K.obj.X n) := rfl

/-- A natural isomorphism induces an isomorphism on bounded below cochain complexes. -/
instance isIso_mapCochainComplexPlus {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive]
    (τ : F₁ ⟶ F₂) [IsIso τ] : IsIso (NatTrans.mapCochainComplexPlus τ) :=
  ⟨NatTrans.mapCochainComplexPlus (inv τ), by
    rw [← NatTrans.mapCochainComplexPlus_comp]; simp, by
    rw [← NatTrans.mapCochainComplexPlus_comp]; simp⟩





section ops
variable {X Y Z W : TopCat.{u}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (W.Sheaf (ModuleCat.{u} k))]

/-- The derived inverse image `f⁻¹ : D⁺(Sh Y) ⥤ D⁺(Sh X)`, the right derived functor of the
exact sheaf inverse image. -/
abbrev pullbackPlus (f : X ⟶ Y) :
    DerivedCategory.Plus (Y.Sheaf (ModuleCat.{u} k)) ⥤ DerivedCategory.Plus (X.Sheaf (ModuleCat.{u} k)) :=
  (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).rightDerivedFunctorPlus

/-- The derived direct image `Rf_* : D⁺(Sh X) ⥤ D⁺(Sh Y)`. -/
abbrev pushforwardPlus (f : X ⟶ Y) :
    DerivedCategory.Plus (X.Sheaf (ModuleCat.{u} k)) ⥤ DerivedCategory.Plus (Y.Sheaf (ModuleCat.{u} k)) :=
  (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlus


/-- Underived `f_* ⋙ g_* ≅ (f ≫ g)_*`; it holds definitionally. -/
def pushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pushforward (ModuleCat.{u} k) f ⋙ TopCat.Sheaf.pushforward _ g ≅
      TopCat.Sheaf.pushforward _ (f ≫ g) :=
  Iso.refl _

/-- The comparison `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*` of composed derived direct images. -/
def pushforwardPlusComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardPlus k (f ≫ g) ⟶ pushforwardPlus k f ⋙ pushforwardPlus k g :=
  Functor.natTransOfIsRightDerivedFunctorComp
    (mapCochainComplexPlusCompIso (pushforwardCompIso k f g))
    DerivedCategory.Plus.Q DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso _)
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit

/-- The derived-functor comparison is invertible on a bounded below complex of injective
objects. -/
lemma isIso_rightDerivedFunctorPlusUnit_app_of_injective {C D : Type*} [Category* C]
    [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive] (K : CochainComplex.Plus C)
    [∀ n, Injective (K.obj.X n)] : IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  simp only [F.rightDerivedFunctorPlusUnit_app]
  infer_instance

/-- The comparison `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*` is invertible: `f_*` preserves injective
objects, and every object of `D⁺` has a bounded below injective model. -/
instance isIso_pushforwardPlusComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (pushforwardPlusComp k f g) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Yd
  obtain ⟨n, hn⟩ := Yd.property
  have : Yd.IsGE n := (Yd.isGE_ι_obj_iff n).1 hn
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Yd n
  rw [← NatTrans.isIso_app_iff_of_iso (pushforwardPlusComp k f g) e]
  have h₁ : ∀ m : ℤ, Injective
      (((InjectiveObject.ι (X.Sheaf (ModuleCat.{u} k))).mapCochainComplexPlus.obj L).obj.X m) :=
    fun m => (L.obj.X m).property
  have h₂ : ∀ m : ℤ, Injective
      (((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).mapCochainComplexPlus.obj
        ((InjectiveObject.ι (X.Sheaf (ModuleCat.{u} k))).mapCochainComplexPlus.obj L)).obj.X m) :=
    fun m => Injective.injective_of_adjoint (TopCat.Sheaf.pullbackPushforwardAdjunction _ f)
      (L.obj.X m).obj
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g))
    ((InjectiveObject.ι (X.Sheaf (ModuleCat.{u} k))).mapCochainComplexPlus.obj L)
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f)
    ((InjectiveObject.ι (X.Sheaf (ModuleCat.{u} k))).mapCochainComplexPlus.obj L)
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) g)
    ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).mapCochainComplexPlus.obj
        ((InjectiveObject.ι (X.Sheaf (ModuleCat.{u} k))).mapCochainComplexPlus.obj L))
  exact Functor.isIso_natTransOfIsRightDerivedFunctorComp_app _ _ _ _ _ _ _ _ _

/-- Underived `g⁻¹ ⋙ f⁻¹ ≅ (f ≫ g)⁻¹`, by uniqueness of left adjoints. -/
def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback (ModuleCat.{u} k) g ⋙ TopCat.Sheaf.pullback _ f ≅
      TopCat.Sheaf.pullback _ (f ≫ g) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction _ g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ f)).leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ (f ≫ g))

/-- The comparison `(f ≫ g)⁻¹ ⟶ g⁻¹ ⋙ f⁻¹` on `D⁺`, induced by `pullbackCompIso`. -/
def pullbackPlusCompHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackPlus k (f ≫ g) ⟶ pullbackPlus k g ⋙ pullbackPlus k f :=
  Functor.natTransOfIsRightDerivedFunctorComp
    (mapCochainComplexPlusCompIso (pullbackCompIso k f g))
    DerivedCategory.Plus.Q DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso _)
    (TopCat.Sheaf.pullback (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pullback (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit

/-- `pullbackPlusCompHom` is invertible, since all inverse images involved are exact. -/
instance isIso_pullbackPlusCompHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (pullbackPlusCompHom k f g) := by
  have := Localization.essSurj (DerivedCategory.Plus.Q (C := Z.Sheaf (ModuleCat.{u} k)))
    (CochainComplex.Plus.quasiIso _)
  rw [NatTrans.isIso_iff_isIso_app]
  intro Yd
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Plus.Q.objObjPreimageIso Yd)]
  exact Functor.isIso_natTransOfIsRightDerivedFunctorComp_app _ _ _ _ _ _ _ _ _

/-- The composition isomorphism `g⁻¹ ⋙ f⁻¹ ≅ (f ≫ g)⁻¹` on `D⁺`. -/
def pullbackPlusCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackPlus k g ⋙ pullbackPlus k f ≅ pullbackPlus k (f ≫ g) :=
  (asIso (pullbackPlusCompHom k f g)).symm

/-- The sheaf adjunction unit `𝟭 ⟶ f_* f⁻¹`, applied termwise to bounded below complexes. -/
def unitCochain (f : X ⟶ Y) :
    𝟭 (CochainComplex.Plus (Y.Sheaf (ModuleCat.{u} k))) ⟶
      (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).mapCochainComplexPlus ⋙
        (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).mapCochainComplexPlus :=
  NatTrans.mapCochainComplexPlus (TopCat.Sheaf.pullbackPushforwardAdjunction _ f).unit

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))] in
/-- In degree `n`, `unitCochain` is the adjunction unit at the `n`-th term. -/
@[simp]
lemma unitCochain_app_hom_f (f : X ⟶ Y) (K : CochainComplex.Plus (Y.Sheaf (ModuleCat.{u} k)))
    (n : ℤ) : ((unitCochain k f).app K).hom.f n =
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ f).unit.app (K.obj.X n) := rfl

/-- The identity of `D⁺` is the right derived functor of the localization functor `Q`. -/
instance isRightDerivedFunctor_id (Y : TopCat.{u}) [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))] :
    (𝟭 (DerivedCategory.Plus (Y.Sheaf (ModuleCat.{u} k)))).IsRightDerivedFunctor
      (Functor.rightUnitor (DerivedCategory.Plus.Q (C := Y.Sheaf (ModuleCat.{u} k)))).inv
      (CochainComplex.Plus.quasiIso _) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ _

private def derivedUnitAux (f : X ⟶ Y) :
    DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ (pullbackPlus k f ⋙ pushforwardPlus k f) :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (unitCochain k f) _ ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).mapCochainComplexPlus
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit
    (pushforwardPlus k f) ≫
  (Functor.associator _ _ _).hom

/-- The derived unit `𝟭 ⟶ f⁻¹ ⋙ Rf_*` on `D⁺(Sh Y)`, by the universal property of `𝟭` as the
right derived functor of `Q`; its value on `Q K` is `derivedUnit_app_Q`. -/
def derivedUnit (f : X ⟶ Y) : 𝟭 _ ⟶ pullbackPlus k f ⋙ pushforwardPlus k f :=
  (𝟭 _).rightDerivedDesc (Functor.rightUnitor DerivedCategory.Plus.Q).inv
    (CochainComplex.Plus.quasiIso _) _ (derivedUnitAux k f)

/-- On `Q K`, the derived unit is the termwise sheaf adjunction unit followed by the
derived-functor comparisons of `f_*` and `f⁻¹`. -/
lemma derivedUnit_app_Q (f : X ⟶ Y) (K : CochainComplex.Plus (Y.Sheaf (ModuleCat.{u} k))) :
    (derivedUnit k f).app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((unitCochain k f).app K) ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit.app _ ≫
        (pushforwardPlus k f).map
          ((TopCat.Sheaf.pullback (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit.app K) := by
  have := (𝟭 _).rightDerived_fac_app (Functor.rightUnitor DerivedCategory.Plus.Q).inv
    (CochainComplex.Plus.quasiIso _) _ (derivedUnitAux k f) K
  unfold derivedUnit
  simpa [derivedUnitAux] using this

/-- Characterization of `pushforwardPlusComp` on `Q K`. -/
@[reassoc (attr := simp)]
lemma pushforwardPlusComp_fac_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{u} k))) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit.app K ≫
        (pushforwardPlusComp k f g).app (DerivedCategory.Plus.Q.obj K) =
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit.app
          ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).mapCochainComplexPlus.obj K) ≫
        (pushforwardPlus k g).map
          ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit.app K) := by
  have := Functor.comp_natTransOfIsRightDerivedFunctorComp_app
    (mapCochainComplexPlusCompIso (pushforwardCompIso k f g))
    DerivedCategory.Plus.Q DerivedCategory.Plus.Q DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso _)
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit K
  have h : (mapCochainComplexPlusCompIso (pushforwardCompIso k f g)).inv.app K = 𝟙 _ := rfl
  have h' : DerivedCategory.Plus.Q.map
      ((mapCochainComplexPlusCompIso (pushforwardCompIso k f g)).inv.app K) = 𝟙 _ := by
    rw [h]; exact DerivedCategory.Plus.Q.map_id _
  refine this.trans ?_
  rw [h']
  exact Category.id_comp _

private lemma pushforwardPlusComp_fac_app_assoc' (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{u} k)))
    {T : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{u} k))}
    (φ : (pushforwardPlus k g).obj ((pushforwardPlus k f).obj (DerivedCategory.Plus.Q.obj K)) ⟶ T) :
    (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit.app K ≫
        (pushforwardPlusComp k f g).app (DerivedCategory.Plus.Q.obj K) ≫ φ =
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit.app
          ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).mapCochainComplexPlus.obj K) ≫
        (pushforwardPlus k g).map
          ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit.app K) ≫ φ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ φ) (pushforwardPlusComp_fac_app k f g K)).trans (Category.assoc _ _ _))

/-- Characterization of `pullbackPlusCompHom` on `Q K`. -/
@[reassoc (attr := simp)]
lemma pullbackPlusCompHom_fac_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex.Plus (Z.Sheaf (ModuleCat.{u} k))) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit.app K ≫
        (pullbackPlusCompHom k f g).app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((mapCochainComplexPlusCompIso (pullbackCompIso k f g)).inv.app K) ≫
      (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit.app
          ((TopCat.Sheaf.pullback (ModuleCat.{u} k) g).mapCochainComplexPlus.obj K) ≫
        (pullbackPlus k f).map
          ((TopCat.Sheaf.pullback (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit.app K) :=
  Functor.comp_natTransOfIsRightDerivedFunctorComp_app _ _ _ _ _ _ _ _ K

/-- Characterization of `pullbackPlusCompIso` on `Q K`. -/
@[reassoc]
lemma pullbackPlusCompIso_hom_fac_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex.Plus (Z.Sheaf (ModuleCat.{u} k))) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit.app
          ((TopCat.Sheaf.pullback (ModuleCat.{u} k) g).mapCochainComplexPlus.obj K) ≫
        (pullbackPlus k f).map
          ((TopCat.Sheaf.pullback (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit.app K) ≫
        (pullbackPlusCompIso k f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((mapCochainComplexPlusCompIso (pullbackCompIso k f g)).hom.app K) ≫
      (TopCat.Sheaf.pullback (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit.app K := by
  rw [← cancel_mono ((pullbackPlusCompHom k f g).app _)]
  simp only [Category.assoc, pullbackPlusCompHom_fac_app]
  simp [pullbackPlusCompIso]

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))] in
/-- The unit of `f ≫ g` is the unit of `g`, then that of `f`, then `pullbackCompIso`. -/
@[reassoc (attr := simp)]
lemma unit_pullbackCompIso_hom_app (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Sheaf (ModuleCat.{u} k)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ g).unit.app F ≫
      (TopCat.Sheaf.pushforward _ g).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.pullback _ g).obj F)) ≫
      (TopCat.Sheaf.pushforward _ (f ≫ g)).map ((pullbackCompIso k f g).hom.app F) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ (f ≫ g)).unit.app F := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} k) g).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ f))
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ (f ≫ g)) F
  simp only [Adjunction.comp_unit_app, Category.assoc] at this
  exact this

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))] in
private lemma unit_pullbackCompIso_hom_app' (f : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Sheaf (ModuleCat.{u} k)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ g).unit.app F ≫
      (TopCat.Sheaf.pushforward _ g).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.pullback _ g).obj F)) ≫
      (TopCat.Sheaf.pushforward _ g).map ((TopCat.Sheaf.pushforward _ f).map
        ((pullbackCompIso k f g).hom.app F)) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ (f ≫ g)).unit.app F :=
  unit_pullbackCompIso_hom_app k f g F

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))] [HasDerivedCategory (W.Sheaf (ModuleCat.{u} k))] in
/-- Associativity of the underived composition isomorphisms of inverse images. -/
lemma pullbackCompIso_assoc (i : X ⟶ Y) (j : Y ⟶ Z) (p : Z ⟶ W) (F : W.Sheaf (ModuleCat.{u} k)) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} k) i).map ((pullbackCompIso k j p).hom.app F) ≫
        (pullbackCompIso k i (j ≫ p)).hom.app F =
      (pullbackCompIso k i j).hom.app ((TopCat.Sheaf.pullback (ModuleCat.{u} k) p).obj F) ≫
        (pullbackCompIso k (i ≫ j) p).hom.app F := by
  let A := ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} k) p).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction _ j)).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ i)
  apply (A.homEquiv _ _).injective
  simp only [A, Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Functor.comp_obj, CategoryTheory.Functor.map_comp, Category.assoc]
  have e₁ := unit_pullbackCompIso_hom_app' k j p F
  have e₂ : (TopCat.Sheaf.pullbackPushforwardAdjunction _ (j ≫ p)).unit.app F ≫
      (TopCat.Sheaf.pushforward _ p).map ((TopCat.Sheaf.pushforward _ j).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction _ i).unit.app
          ((TopCat.Sheaf.pullback _ (j ≫ p)).obj F))) ≫
      (TopCat.Sheaf.pushforward _ p).map ((TopCat.Sheaf.pushforward _ j).map
        ((TopCat.Sheaf.pushforward _ i).map ((pullbackCompIso k i (j ≫ p)).hom.app F))) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} k) (i ≫ j ≫ p)).unit.app F :=
    unit_pullbackCompIso_hom_app k i (j ≫ p) F
  have e₃ := unit_pullbackCompIso_hom_app' k i j ((TopCat.Sheaf.pullback (ModuleCat.{u} k) p).obj F)
  have e₄ : (TopCat.Sheaf.pullbackPushforwardAdjunction _ p).unit.app F ≫
      (TopCat.Sheaf.pushforward _ p).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction _ (i ≫ j)).unit.app
          ((TopCat.Sheaf.pullback _ p).obj F)) ≫
      (TopCat.Sheaf.pushforward _ p).map ((TopCat.Sheaf.pushforward _ j).map
        ((TopCat.Sheaf.pushforward _ i).map ((pullbackCompIso k (i ≫ j) p).hom.app F))) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} k) (i ≫ j ≫ p)).unit.app F :=
    unit_pullbackCompIso_hom_app k (i ≫ j) p F
  have n₁ := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} k) i).unit.naturality
    ((pullbackCompIso k j p).hom.app F)
  simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n₁
  have n₁' := congrArg (fun x => (TopCat.Sheaf.pushforward (ModuleCat.{u} k) p).map
    ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) j).map x)) n₁
  have e₃' := congrArg (fun x => (TopCat.Sheaf.pushforward (ModuleCat.{u} k) p).map x) e₃
  simp only [CategoryTheory.Functor.map_comp] at n₁' e₃'
  rw [← reassoc_of% n₁', reassoc_of% e₁]
  refine e₂.trans ?_
  rw [reassoc_of% e₃']
  exact e₄.symm

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))] in
private lemma unitCochain_comp_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex.Plus (Z.Sheaf (ModuleCat.{u} k))) :
    (unitCochain k g).app K ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) g).mapCochainComplexPlus.map
        ((unitCochain k f).app ((TopCat.Sheaf.pullback (ModuleCat.{u} k) g).mapCochainComplexPlus.obj K)) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g)).mapCochainComplexPlus.map
        ((mapCochainComplexPlusCompIso (pullbackCompIso k f g)).hom.app K) =
    (unitCochain k (f ≫ g)).app K := by
  ext n : 2
  simp only [ObjectProperty.FullSubcategory.comp_hom, HomologicalComplex.comp_f,
    unitCochain_app_hom_f]
  exact unit_pullbackCompIso_hom_app k f g (K.obj.X n)

-- Pasting of derived units and composition isomorphisms elaborates slowly; the larger bound is
-- local to this declaration.
set_option maxHeartbeats 1000000 in
/-- Coherence of the derived unit with composition: the unit of `f ≫ g`, followed by
`pushforwardPlusComp`, is the unit of `g`, then `Rg_*` of the unit of `f`, then
`pullbackPlusCompIso`. -/
lemma derivedUnit_comp_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (Yd : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{u} k))) :
    (derivedUnit k (f ≫ g)).app Yd ≫
        (pushforwardPlusComp k f g).app ((pullbackPlus k (f ≫ g)).obj Yd) =
      (derivedUnit k g).app Yd ≫
        (pushforwardPlus k g).map ((derivedUnit k f).app ((pullbackPlus k g).obj Yd)) ≫
        (pushforwardPlus k g).map ((pushforwardPlus k f).map
          ((pullbackPlusCompIso k f g).hom.app Yd)) := by
  let τ₁ : 𝟭 _ ⟶ pullbackPlus k (f ≫ g) ⋙ pushforwardPlus k f ⋙ pushforwardPlus k g :=
    derivedUnit k (f ≫ g) ≫ Functor.whiskerLeft _ (pushforwardPlusComp k f g)
  let τ₂ : 𝟭 _ ⟶ pullbackPlus k (f ≫ g) ⋙ pushforwardPlus k f ⋙ pushforwardPlus k g :=
    derivedUnit k g ≫ Functor.whiskerLeft (pullbackPlus k g)
      (Functor.whiskerRight (derivedUnit k f) (pushforwardPlus k g)) ≫
      Functor.whiskerRight (pullbackPlusCompIso k f g).hom
        (pushforwardPlus k f ⋙ pushforwardPlus k g)
  have key : τ₁ = τ₂ := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _)
    intro K
    simp only [τ₁, τ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.id_obj, Functor.comp_obj]
    rw [derivedUnit_app_Q, derivedUnit_app_Q]
    simp only [Category.assoc]
    have nat₁ := (derivedUnit k f).naturality
      ((TopCat.Sheaf.pullback (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit.app K)
    simp only [Functor.id_map, Functor.comp_map] at nat₁
    simp only [← CategoryTheory.Functor.map_comp, reassoc_of% nat₁]
    rw [derivedUnit_app_Q]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, pullbackPlusCompIso_hom_fac_app]
    rw [← unitCochain_comp_app k f g K]
    erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    have nat₂ := (TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit.naturality
      ((mapCochainComplexPlusCompIso (pullbackCompIso k f g)).hom.app K)
    have nat₃ := (pushforwardPlusComp k f g).naturality
      (DerivedCategory.Plus.Q.map ((mapCochainComplexPlusCompIso (pullbackCompIso k f g)).hom.app K) ≫
        (TopCat.Sheaf.pullback (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit.app K)
    have nat₄ := (TopCat.Sheaf.pushforward (ModuleCat.{u} k) g).rightDerivedFunctorPlusUnit.naturality
      ((unitCochain k f).app ((TopCat.Sheaf.pullback (ModuleCat.{u} k) g).mapCochainComplexPlus.obj K))
    simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Category.assoc] at nat₂ nat₃ nat₄ ⊢
    erw [reassoc_of% nat₂]
    erw [nat₃]
    erw [pushforwardPlusComp_fac_app_assoc]
    erw [Category.assoc]
    erw [reassoc_of% nat₄]
  exact congr_app key Yd

-- Pasting of derived units and composition isomorphisms elaborates slowly; the larger bound is
-- local to this declaration.
set_option maxHeartbeats 1000000 in
/-- Associativity of the composition comparisons of derived direct images. -/
lemma pushforwardPlusComp_assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : DerivedCategory.Plus (X.Sheaf (ModuleCat.{u} k))) :
    (pushforwardPlusComp k (f ≫ g) h).app M ≫
        (pushforwardPlus k h).map ((pushforwardPlusComp k f g).app M) =
      (pushforwardPlusComp k f (g ≫ h)).app M ≫
        (pushforwardPlusComp k g h).app ((pushforwardPlus k f).obj M) := by
  let γ₁ : pushforwardPlus k ((f ≫ g) ≫ h) ⟶
      pushforwardPlus k f ⋙ pushforwardPlus k g ⋙ pushforwardPlus k h :=
    pushforwardPlusComp k (f ≫ g) h ≫
      Functor.whiskerRight (pushforwardPlusComp k f g) (pushforwardPlus k h)
  let γ₂ : pushforwardPlus k ((f ≫ g) ≫ h) ⟶
      pushforwardPlus k f ⋙ pushforwardPlus k g ⋙ pushforwardPlus k h :=
    pushforwardPlusComp k f (g ≫ h) ≫
      Functor.whiskerLeft (pushforwardPlus k f) (pushforwardPlusComp k g h)
  have key : γ₁ = γ₂ := by
    apply Functor.rightDerived_ext (pushforwardPlus k ((f ≫ g) ≫ h))
      (TopCat.Sheaf.pushforward (ModuleCat.{u} k) ((f ≫ g) ≫ h)).rightDerivedFunctorPlusUnit
      (CochainComplex.Plus.quasiIso _)
    refine NatTrans.ext (funext fun K => ?_)
    simp only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    conv_lhs =>
      erw [pushforwardPlusComp_fac_app_assoc' k (f ≫ g) h K]
      erw [← CategoryTheory.Functor.map_comp (pushforwardPlus k h)
        ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) (f ≫ g)).rightDerivedFunctorPlusUnit.app K)]
      erw [pushforwardPlusComp_fac_app k f g K]
      erw [CategoryTheory.Functor.map_comp (pushforwardPlus k h)]
    conv_rhs =>
      erw [pushforwardPlusComp_fac_app_assoc' k f (g ≫ h) K]
      erw [(pushforwardPlusComp k g h).naturality
        ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).rightDerivedFunctorPlusUnit.app K)]
      erw [pushforwardPlusComp_fac_app_assoc' k g h
        ((TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).mapCochainComplexPlus.obj K)]
    rfl
  exact congr_app key M

omit [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))] [HasDerivedCategory (W.Sheaf (ModuleCat.{u} k))] in
private lemma pullbackCompIso_inv_assoc (i : X ⟶ Y) (j : Y ⟶ Z) (p : Z ⟶ W)
    (F : W.Sheaf (ModuleCat.{u} k)) :
    (pullbackCompIso k i (j ≫ p)).inv.app F ≫
        (TopCat.Sheaf.pullback (ModuleCat.{u} k) i).map ((pullbackCompIso k j p).inv.app F) =
      (pullbackCompIso k (i ≫ j) p).inv.app F ≫
        (pullbackCompIso k i j).inv.app ((TopCat.Sheaf.pullback (ModuleCat.{u} k) p).obj F) := by
  have h := pullbackCompIso_assoc k i j p F
  rw [← cancel_epi ((TopCat.Sheaf.pullback (ModuleCat.{u} k) i).map
    ((pullbackCompIso k j p).hom.app F) ≫ (pullbackCompIso k i (j ≫ p)).hom.app F)]
  conv_rhs => rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rfl

omit [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))] [HasDerivedCategory (W.Sheaf (ModuleCat.{u} k))] in
private lemma mapCochainComplexPlus_pullbackCompIso_inv_assoc (i : X ⟶ Y) (j : Y ⟶ Z) (p : Z ⟶ W)
    (K : CochainComplex.Plus (W.Sheaf (ModuleCat.{u} k))) :
    DerivedCategory.Plus.Q.map ((mapCochainComplexPlusCompIso (pullbackCompIso k i (j ≫ p))).inv.app K) ≫
      DerivedCategory.Plus.Q.map ((TopCat.Sheaf.pullback (ModuleCat.{u} k) i).mapCochainComplexPlus.map
        ((mapCochainComplexPlusCompIso (pullbackCompIso k j p)).inv.app K)) =
    DerivedCategory.Plus.Q.map ((mapCochainComplexPlusCompIso (pullbackCompIso k (i ≫ j) p)).inv.app K) ≫
      DerivedCategory.Plus.Q.map ((mapCochainComplexPlusCompIso (pullbackCompIso k i j)).inv.app
        ((TopCat.Sheaf.pullback (ModuleCat.{u} k) p).mapCochainComplexPlus.obj K)) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  ext n : 2
  exact pullbackCompIso_inv_assoc k i j p (K.obj.X n)

-- Pasting of derived units and composition isomorphisms elaborates slowly; the larger bound is
-- local to this declaration.
set_option maxHeartbeats 1000000 in
/-- Associativity of the composition comparisons of derived inverse images. -/
lemma pullbackPlusCompHom_assoc_app (i : X ⟶ Y) (j : Y ⟶ Z) (p : Z ⟶ W)
    (M : DerivedCategory.Plus (W.Sheaf (ModuleCat.{u} k))) :
    (pullbackPlusCompHom k i (j ≫ p)).app M ≫
        (pullbackPlus k i).map ((pullbackPlusCompHom k j p).app M) =
      (pullbackPlusCompHom k (i ≫ j) p).app M ≫
        (pullbackPlusCompHom k i j).app ((pullbackPlus k p).obj M) := by
  let γ₁ : pullbackPlus k (i ≫ j ≫ p) ⟶
      pullbackPlus k p ⋙ pullbackPlus k j ⋙ pullbackPlus k i :=
    pullbackPlusCompHom k i (j ≫ p) ≫
      Functor.whiskerRight (pullbackPlusCompHom k j p) (pullbackPlus k i)
  let γ₂ : pullbackPlus k (i ≫ j ≫ p) ⟶
      pullbackPlus k p ⋙ pullbackPlus k j ⋙ pullbackPlus k i :=
    pullbackPlusCompHom k (i ≫ j) p ≫
      Functor.whiskerLeft (pullbackPlus k p) (pullbackPlusCompHom k i j)
  have key : γ₁ = γ₂ := by
    apply Functor.rightDerived_ext (pullbackPlus k (i ≫ j ≫ p))
      (TopCat.Sheaf.pullback (ModuleCat.{u} k) (i ≫ j ≫ p)).rightDerivedFunctorPlusUnit
      (CochainComplex.Plus.quasiIso _)
    refine NatTrans.ext (funext fun K => ?_)
    simp only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have nat₁ := (TopCat.Sheaf.pullback (ModuleCat.{u} k) i).rightDerivedFunctorPlusUnit.naturality
      ((mapCochainComplexPlusCompIso (pullbackCompIso k j p)).inv.app K)
    have nat₂ := (pullbackPlusCompHom k i j).naturality
      ((TopCat.Sheaf.pullback (ModuleCat.{u} k) p).rightDerivedFunctorPlusUnit.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at nat₁ nat₂
    conv_lhs =>
      rw [pullbackPlusCompHom_fac_app_assoc k i (j ≫ p) K]
      rw [← CategoryTheory.Functor.map_comp (pullbackPlus k i)]
      rw [pullbackPlusCompHom_fac_app k j p K]
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rw [← reassoc_of% nat₁]
    conv_rhs =>
      erw [pullbackPlusCompHom_fac_app_assoc k (i ≫ j) p K]
      rw [nat₂]
      rw [pullbackPlusCompHom_fac_app_assoc k i j]
    rw [reassoc_of% mapCochainComplexPlus_pullbackCompIso_inv_assoc k i j p K]
  exact congr_app key M

/-- The inverse of `pullbackPlusCompIso` is `pullbackPlusCompHom`. -/
lemma pullbackPlusCompIso_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackPlusCompIso k f g).inv = pullbackPlusCompHom k f g := rfl

/-- Associativity of `pullbackPlusCompIso`. -/
lemma pullbackPlusCompIso_hom_assoc_app (i : X ⟶ Y) (j : Y ⟶ Z) (p : Z ⟶ W)
    (M : DerivedCategory.Plus (W.Sheaf (ModuleCat.{u} k))) :
    (pullbackPlus k i).map ((pullbackPlusCompIso k j p).hom.app M) ≫
        (pullbackPlusCompIso k i (j ≫ p)).hom.app M =
      (pullbackPlusCompIso k i j).hom.app ((pullbackPlus k p).obj M) ≫
        (pullbackPlusCompIso k (i ≫ j) p).hom.app M := by
  rw [← cancel_mono ((pullbackPlusCompIso k i (j ≫ p)).inv.app M ≫
    (pullbackPlus k i).map ((pullbackPlusCompIso k j p).inv.app M))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [pullbackPlusCompIso_inv, pullbackPlusCompIso_inv, pullbackPlusCompHom_assoc_app,
    ← pullbackPlusCompIso_inv, ← pullbackPlusCompIso_inv]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  rfl

/-- The derived composition comparison for direct images, as an isomorphism. -/
def pushforwardPlusCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardPlus k (f ≫ g) ≅ pushforwardPlus k f ⋙ pushforwardPlus k g :=
  asIso (pushforwardPlusComp k f g)

/-- The underlying morphism of `pushforwardPlusCompIso`. -/
@[simp]
lemma pushforwardPlusCompIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforwardPlusCompIso k f g).hom = pushforwardPlusComp k f g := rfl

/-- `derivedUnit_comp_app` solved for the unit of `f ≫ g`. -/
lemma derivedUnit_comp_app' (f : X ⟶ Y) (g : Y ⟶ Z)
    (Yd : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{u} k))) :
    (derivedUnit k (f ≫ g)).app Yd =
      (derivedUnit k g).app Yd ≫
        (pushforwardPlus k g).map ((derivedUnit k f).app ((pullbackPlus k g).obj Yd)) ≫
        (pushforwardPlus k g).map ((pushforwardPlus k f).map
          ((pullbackPlusCompIso k f g).hom.app Yd)) ≫
        (pushforwardPlusCompIso k f g).inv.app ((pullbackPlus k (f ≫ g)).obj Yd) := by
  rw [← cancel_mono ((pushforwardPlusComp k f g).app _), derivedUnit_comp_app]
  simp [← pushforwardPlusCompIso_hom]

/-- Associativity of the inverse composition isomorphisms of derived direct images. -/
lemma pushforwardPlusCompIso_inv_assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : DerivedCategory.Plus (X.Sheaf (ModuleCat.{u} k))) :
    (pushforwardPlus k h).map ((pushforwardPlusCompIso k f g).inv.app M) ≫
        (pushforwardPlusCompIso k (f ≫ g) h).inv.app M =
      (pushforwardPlusCompIso k g h).inv.app ((pushforwardPlus k f).obj M) ≫
        (pushforwardPlusCompIso k f (g ≫ h)).inv.app M := by
  rw [← cancel_epi ((pushforwardPlusComp k (f ≫ g) h).app M ≫
    (pushforwardPlus k h).map ((pushforwardPlusComp k f g).app M))]
  conv_rhs => rw [pushforwardPlusComp_assoc_app]
  simp only [← pushforwardPlusCompIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact Iso.hom_inv_id_app _ _

end ops

section corr
variable {X'' X' X Z W : TopCat.{u}}
  [HasDerivedCategory (X''.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (W.Sheaf (ModuleCat.{u} k))]

/-- Restriction of the transform `p⁻¹ ⋙ Rq_*` along `j : X' ⟶ X`: the derived unit of `j`,
then `Rq_* Rj_* ≅ R(j ≫ q)_*` and `j⁻¹ p⁻¹ ≅ (j ≫ p)⁻¹`. -/
def corrRestr (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W) :
    pullbackPlus k p ⋙ pushforwardPlus k q ⟶
      pullbackPlus k (j ≫ p) ⋙ pushforwardPlus k (j ≫ q) :=
  Functor.whiskerLeft (pullbackPlus k p)
      ((Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (derivedUnit k j) (pushforwardPlus k q) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (pullbackPlus k j) (pushforwardPlusCompIso k j q).inv) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullbackPlusCompIso k j p).hom (pushforwardPlus k (j ≫ q))

/-- The components of `corrRestr`. -/
lemma corrRestr_app (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W)
    (M : DerivedCategory.Plus (Z.Sheaf (ModuleCat.{u} k))) :
    (corrRestr k j p q).app M =
      (pushforwardPlus k q).map ((derivedUnit k j).app ((pullbackPlus k p).obj M)) ≫
        (pushforwardPlusCompIso k j q).inv.app ((pullbackPlus k j).obj ((pullbackPlus k p).obj M)) ≫
        (pushforwardPlus k (j ≫ q)).map ((pullbackPlusCompIso k j p).hom.app M) := by
  simp [corrRestr]

-- Pasting of derived units and composition isomorphisms elaborates slowly; the larger bound is
-- local to this declaration.
set_option maxHeartbeats 1000000 in
/-- `corrRestr` composes along `i ≫ j`. -/
lemma corrRestr_comp (i : X'' ⟶ X') (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W) :
    corrRestr k j p q ≫ corrRestr k i (j ≫ p) (j ≫ q) = corrRestr k (i ≫ j) p q := by
  refine NatTrans.ext (funext fun M => ?_)
  simp only [NatTrans.comp_app, corrRestr_app]
  -- abbreviations of the objects involved
  set pM := (pullbackPlus k p).obj M with hpM
  have n₁ := (pushforwardPlusCompIso k j q).inv.naturality
    ((pushforwardPlus k i).map ((pullbackPlusCompIso k i j).hom.app pM))
  have n₂ := (pushforwardPlusCompIso k j q).inv.naturality
    ((derivedUnit k i).app ((pullbackPlus k j).obj pM))
  have n₃ := (pushforwardPlusCompIso k i (j ≫ q)).inv.naturality
    ((pullbackPlusCompIso k i j).hom.app pM)
  have n₄ := (derivedUnit k i).naturality ((pullbackPlusCompIso k j p).hom.app M)
  have n₅ := (pushforwardPlusCompIso k i (j ≫ q)).inv.naturality
    ((pullbackPlus k i).map ((pullbackPlusCompIso k j p).hom.app M))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at n₁ n₂ n₃ n₄ n₅
  conv_rhs =>
    rw [derivedUnit_comp_app' k i j pM]
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp]
    rw [Category.assoc (obj := DerivedCategory.Plus (W.Sheaf (ModuleCat.{u} k))),
      Category.assoc (obj := DerivedCategory.Plus (W.Sheaf (ModuleCat.{u} k))),
      Category.assoc (obj := DerivedCategory.Plus (W.Sheaf (ModuleCat.{u} k)))]
    rw [reassoc_of% (pushforwardPlusCompIso_inv_assoc_app k i j q
      ((pullbackPlus k (i ≫ j)).obj pM))]
    rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% n₃]
    erw [← CategoryTheory.Functor.map_comp (pushforwardPlus k (i ≫ j ≫ q))
      ((pullbackPlusCompIso k i j).hom.app pM) ((pullbackPlusCompIso k (i ≫ j) p).hom.app M)]
    rw [← pullbackPlusCompIso_hom_assoc_app k i j p M, CategoryTheory.Functor.map_comp]
  conv_lhs =>
    rw [Category.assoc (obj := DerivedCategory.Plus (W.Sheaf (ModuleCat.{u} k))),
      Category.assoc (obj := DerivedCategory.Plus (W.Sheaf (ModuleCat.{u} k)))]
    rw [← CategoryTheory.Functor.map_comp_assoc (pushforwardPlus k (j ≫ q)), n₄,
      CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% n₅]

end corr

section homeo
variable {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f]

/-- Along a homeomorphism `f`, the sheaf direct image is an equivalence with inverse
`(inv f)_*`. -/
def pushforwardEquivalence : X.Sheaf (ModuleCat.{u} k) ≌ Y.Sheaf (ModuleCat.{u} k) :=
  CategoryTheory.Equivalence.mk (TopCat.Sheaf.pushforward _ f) (TopCat.Sheaf.pushforward _ (inv f))
    (eqToIso (by
      change 𝟭 _ = TopCat.Sheaf.pushforward _ (f ≫ inv f)
      rw [IsIso.hom_inv_id]; rfl))
    (eqToIso (by
      change TopCat.Sheaf.pushforward _ (inv f ≫ f) = 𝟭 _
      rw [IsIso.inv_hom_id]; rfl))

/-- Along a homeomorphism, the sheaf direct image is an equivalence. -/
instance pushforward_isEquivalence : (TopCat.Sheaf.pushforward (ModuleCat.{u} k) f).IsEquivalence :=
  (pushforwardEquivalence k f).isEquivalence_functor

variable [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{u} k))]

/-- Along a homeomorphism the derived unit `𝟭 ⟶ f⁻¹ ⋙ Rf_*` is invertible. -/
instance isIso_derivedUnit : IsIso (derivedUnit k f) := by
  have := Localization.essSurj (DerivedCategory.Plus.Q (C := Y.Sheaf (ModuleCat.{u} k)))
    (CochainComplex.Plus.quasiIso _)
  rw [NatTrans.isIso_iff_isIso_app]
  intro Yd
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Plus.Q.objObjPreimageIso Yd)]
  rw [derivedUnit_app_Q]
  have : IsIso (unitCochain k f) := by
    unfold unitCochain
    infer_instance
  infer_instance

end homeo

section corrId
variable {X' X Z W : TopCat.{u}}
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (X.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (Z.Sheaf (ModuleCat.{u} k))]
  [HasDerivedCategory (W.Sheaf (ModuleCat.{u} k))]

/-- `corrRestr` along an isomorphism is invertible. -/
instance isIso_corrRestr (j : X' ⟶ X) [IsIso j] (p : X ⟶ Z) (q : X ⟶ W) :
    IsIso (corrRestr k j p q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [corrRestr_app]
  infer_instance

/-- `corrRestr` along a map whose derived unit is invertible is invertible: its components are
`Rq_*` of the derived unit of `j` followed by composition isomorphisms. -/
theorem isIso_corrRestr_of_isIso_derivedUnit (j : X' ⟶ X) [IsIso (derivedUnit k j)] (p : X ⟶ Z)
    (q : X ⟶ W) : IsIso (corrRestr k j p q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [corrRestr_app]
  infer_instance

/-- `corrRestr` along the identity is the identity. -/
lemma corrRestr_id (p : X ⟶ Z) (q : X ⟶ W) : corrRestr k (𝟙 X) p q = 𝟙 _ := by
  have h : corrRestr k (𝟙 X) p q ≫ corrRestr k (𝟙 X) p q = corrRestr k (𝟙 X) p q :=
    corrRestr_comp k (𝟙 X) (𝟙 X) p q
  exact (cancel_epi (corrRestr k (𝟙 X) p q)).1 (h.trans (Category.comp_id _).symm)

end corrId

end TDA.Sheaf
