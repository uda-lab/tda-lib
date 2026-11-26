import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import TDA.Sheaf.DerivedPlus

/-!
# The derived base-change morphism

Let `k` be a ring and write `Sh(X) := X.Sheaf (ModuleCat k)`. For a continuous map `f : X ⟶ Y`,
`TDA.Sheaf.DerivedPlus` provides the derived inverse image `pullbackPlus k f`, the derived
direct image `pushforwardPlus k f` and the derived unit `derivedUnit k f`. This file completes
them to an adjunction and constructs the base-change morphism of a commutative square as a mate.

* `isRightDerivedFunctor_rightDerivedFunctorPlus_comp`: for an additive functor `F` out of an
  abelian category with enough injectives, `RF ⋙ H` is the right derived functor of
  `F ⋙ Q ⋙ H` for every functor `H` on `D⁺` (the derived functor `RF` is absolute). This is the
  input that Mathlib's `Adjunction.derived'` needs.
* `pullbackPushforwardAdjunctionPlus k f`: the sheaf adjunction `f⁻¹ ⊣ f_*` applied termwise to
  bounded below cochain complexes.
* `derivedCounit k f : Rf_* ⋙ f⁻¹ ⟶ 𝟭` and `derivedAdjunction k f : f⁻¹ ⊣ Rf_*` on `D⁺`, whose
  unit is B1's `derivedUnit k f` (`derivedAdjunction_unit`). On `Q K`, after the derived-functor
  comparisons, the counit is the termwise sheaf counit (`derivedCounit_fac_app`). Along a
  homeomorphism the counit is invertible (`isIso_derivedCounit`).
* For a commutative square `w : g' ≫ f = f' ≫ g` of continuous maps

  ```
        g'
    X' ---> X
    |       |
  f'|       | f
    v       v
    Y' ---> Y
        g
  ```

  `pullbackPlusSquare k w : g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ g'⁻¹` is the isomorphism of inverse images
  (through `pullbackPlusCompIso` and `w`), and the **base-change morphism**

  `baseChange k w : Rf_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ Rf'_*`,

  that is `g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ g'⁻¹`, is its mate (`mateEquiv`) for the derived adjunctions of
  `f` and `f'`. Its components are the unit of `f'`, `pullbackPlusSquare` and the counit of `f`
  (`baseChange_app`); it is characterised by `derivedUnit_baseChange`, is natural
  (`baseChange_naturality`) and is invertible when `f` and `f'` are homeomorphisms
  (`isIso_baseChange_of_isIso`), in particular for the identity square.

Derived categories are instance arguments `[HasDerivedCategory (X.Sheaf (ModuleCat k))]`, one for
each space a statement mentions, as in `TDA.Sheaf.DerivedPlus`.
-/

noncomputable section
open CategoryTheory Limits

namespace TDA.Sheaf

section absolute

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]
  (H : DerivedCategory.Plus D ⥤ E)

/-- **Absolute derived functors.** For an additive functor `F` out of an abelian category with
enough injectives and any functor `H` on `D⁺`, the composite `RF ⋙ H` is the right derived functor
of `F ⋙ Q ⋙ H`, with the comparison of `RF` whiskered by `H`. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp :
    (F.rightDerivedFunctorPlus ⋙ H).IsRightDerivedFunctor
      (Functor.whiskerRight F.rightDerivedFunctorPlusUnit H ≫ (Functor.associator _ _ _).hom)
      (CochainComplex.Plus.quasiIso C) := by
  have h : (CochainComplex.Plus.localizerMorphism C).Derives
      (F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ H) := by
    intro K L φ hφ
    have := CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus F φ hφ
    exact Functor.map_isIso H
      (((CochainComplex.Plus.localizerMorphism C).functor ⋙ F.mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q).map φ)
  refine h.isRightDerivedFunctor_of_isIso _ (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  have : ∀ n : ℤ, Injective (((CochainComplex.Plus.localizerMorphism C).functor.obj K).obj.X n) :=
    fun n => (K.obj.X n).property
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective F
    ((CochainComplex.Plus.localizerMorphism C).functor.obj K)
  exact Functor.map_isIso H _

end absolute

variable (k : Type) [Ring k]

section adjunction

variable {X Y : TopCat.{0}}

/-- The sheaf adjunction `f⁻¹ ⊣ f_*`, applied termwise to bounded below cochain complexes. -/
def pullbackPushforwardAdjunctionPlus (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapCochainComplexPlus ⊣
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapCochainComplexPlus :=
  Adjunction.mkOfUnitCounit
    { unit := unitCochain k f
      counit := NatTrans.mapCochainComplexPlus
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).counit
      left_triangle := by
        ext K n : 4
        exact (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).left_triangle_components
          (K.obj.X n)
      right_triangle := by
        ext K n : 4
        exact (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).right_triangle_components
          (K.obj.X n) }

/-- The unit of `pullbackPushforwardAdjunctionPlus` is `unitCochain`. -/
@[simp]
lemma pullbackPushforwardAdjunctionPlus_unit (f : X ⟶ Y) :
    (pullbackPushforwardAdjunctionPlus k f).unit = unitCochain k f := rfl

/-- In degree `n`, the counit of `pullbackPushforwardAdjunctionPlus` is the sheaf counit. -/
@[simp]
lemma pullbackPushforwardAdjunctionPlus_counit_app_hom_f (f : X ⟶ Y)
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k))) (n : ℤ) :
    ((pullbackPushforwardAdjunctionPlus k f).counit.app K).hom.f n =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).counit.app (K.obj.X n) :=
  rfl

variable [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]

/-- The derived inverse image is also the *left* derived functor of the termwise inverse image:
its derived-functor comparison is invertible (`f⁻¹` is exact). -/
instance isLeftDerivedFunctor_pullbackPlus (f : X ⟶ Y) :
    (pullbackPlus k f).IsLeftDerivedFunctor
      (inv (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit)
      (CochainComplex.Plus.quasiIso _) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (asIso (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit).symm

/-- The derived counit `Rf_* ⋙ f⁻¹ ⟶ 𝟭` on `D⁺(Sh X)`, by the universal property of the absolute
derived functor `Rf_* ⋙ f⁻¹` (`Adjunction.derivedε`); its value on `Q K` is
`derivedCounit_fac_app`. -/
def derivedCounit (f : X ⟶ Y) : pushforwardPlus k f ⋙ pullbackPlus k f ⟶ 𝟭 _ :=
  (pullbackPushforwardAdjunctionPlus k f).derivedε (CochainComplex.Plus.quasiIso _)
    (inv (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit)
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit

/-- On `Q K`, after `f⁻¹` of the derived-functor comparison of `f_*`, the derived counit is the
inverse comparison of `f⁻¹` followed by the termwise sheaf counit. -/
@[reassoc]
lemma derivedCounit_fac_app (f : X ⟶ Y) (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k f).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit.app K) ≫
      (derivedCounit k f).app (DerivedCategory.Plus.Q.obj K) =
    inv ((TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.Q.map ((pullbackPushforwardAdjunctionPlus k f).counit.app K) := by
  have := (pullbackPushforwardAdjunctionPlus k f).derivedε_fac_app
    (CochainComplex.Plus.quasiIso _)
    (inv (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit)
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit K
  rw [NatIso.isIso_inv_app] at this
  exact this

/-- **The derived adjunction** `f⁻¹ ⊣ Rf_*` on `D⁺`: its unit is `derivedUnit k f` and its counit
is `derivedCounit k f`. -/
def derivedAdjunction (f : X ⟶ Y) : pullbackPlus k f ⊣ pushforwardPlus k f :=
  (pullbackPushforwardAdjunctionPlus k f).derived' (CochainComplex.Plus.quasiIso _)
    (CochainComplex.Plus.quasiIso _)
    (inv (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit)
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit
    (derivedUnit k f) (derivedCounit k f)
    (fun K => by
      rw [derivedUnit_app_Q]
      simp)
    (fun K => by
      rw [NatIso.isIso_inv_app]
      exact derivedCounit_fac_app k f K)

/-- The unit of the derived adjunction is the derived unit of `TDA.Sheaf.DerivedPlus`. -/
@[simp]
lemma derivedAdjunction_unit (f : X ⟶ Y) : (derivedAdjunction k f).unit = derivedUnit k f := rfl

/-- The counit of the derived adjunction is `derivedCounit`. -/
@[simp]
lemma derivedAdjunction_counit (f : X ⟶ Y) :
    (derivedAdjunction k f).counit = derivedCounit k f := rfl

/-- Along a homeomorphism the derived counit `Rf_* ⋙ f⁻¹ ⟶ 𝟭` is invertible. -/
instance isIso_derivedCounit (f : X ⟶ Y) [IsIso f] : IsIso (derivedCounit k f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  obtain ⟨n, hn⟩ := M.property
  have : M.IsGE n := (M.isGE_ι_obj_iff n).1 hn
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso M n
  rw [← NatTrans.isIso_app_iff_of_iso (derivedCounit k f) e]
  have hL : ∀ m : ℤ, Injective
      (((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L).obj.X m) :=
    fun m => (L.obj.X m).property
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f)
    ((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L)
  have : IsIso (pullbackPushforwardAdjunctionPlus k f).counit := by
    change IsIso (NatTrans.mapCochainComplexPlus
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f).counit)
    infer_instance
  have h := derivedCounit_fac_app k f
    ((InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L)
  rw [← isIso_comp_left_iff ((pullbackPlus k f).map
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit.app _)), h]
  infer_instance

end adjunction

section square

variable {X Y X' Y' : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (X'.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y'.Sheaf (ModuleCat.{0} k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- For a commutative square `w : g' ≫ f = f' ≫ g`, the isomorphism of derived inverse images
`g⁻¹ ⋙ f'⁻¹ ≅ (f' ≫ g)⁻¹ = (g' ≫ f)⁻¹ ≅ f⁻¹ ⋙ g'⁻¹`, the 2-square (`TwoSquare`) whose mate
is `baseChange`. Its type is spelled out as a natural transformation rather than as a
`TwoSquare`: with the `TwoSquare` spelling, kernel checks of the mate lemmas below time out. -/
def pullbackPlusSquare (w : g' ≫ f = f' ≫ g) :
    pullbackPlus k g ⋙ pullbackPlus k f' ⟶ pullbackPlus k f ⋙ pullbackPlus k g' :=
  (pullbackPlusCompIso k f' g).hom ≫ eqToHom (by rw [w]) ≫ (pullbackPlusCompIso k g' f).inv

/-- `pullbackPlusSquare` is invertible. -/
instance isIso_pullbackPlusSquare (w : g' ≫ f = f' ≫ g) :
    IsIso (pullbackPlusSquare k w) := by
  unfold pullbackPlusSquare
  infer_instance

/-- **The derived base-change morphism** `g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ g'⁻¹` of a commutative square
`w : g' ≫ f = f' ≫ g`, written `Rf_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ Rf'_*`: the mate of `pullbackPlusSquare k w`
for the derived adjunctions `f⁻¹ ⊣ Rf_*` and `f'⁻¹ ⊣ Rf'_*`. -/
def baseChange (w : g' ≫ f = f' ≫ g) :
    pushforwardPlus k f ⋙ pullbackPlus k g ⟶ pullbackPlus k g' ⋙ pushforwardPlus k f' :=
  mateEquiv (derivedAdjunction k f) (derivedAdjunction k f') (pullbackPlusSquare k w)

/-- `baseChange` as a mate. Proofs rewrite with this equation: a kernel check of the same
identity by unfolding, under `NatTrans.app`, is slow. -/
lemma baseChange_eq (w : g' ≫ f = f' ≫ g) :
    baseChange k w =
      mateEquiv (derivedAdjunction k f) (derivedAdjunction k f') (pullbackPlusSquare k w) :=
  rfl

/-- `unit_mateEquiv` for the derived adjunctions and an arbitrary 2-cell. -/
private lemma unit_mateEquiv_derived
    (α : pullbackPlus k g ⋙ pullbackPlus k f' ⟶ pullbackPlus k f ⋙ pullbackPlus k g')
    (N : DerivedCategory.Plus (Y.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k g).map ((derivedAdjunction k f).unit.app N) ≫
        (mateEquiv (derivedAdjunction k f) (derivedAdjunction k f') α).app
          ((pullbackPlus k f).obj N) =
      (derivedAdjunction k f').unit.app ((pullbackPlus k g).obj N) ≫
        (pushforwardPlus k f').map (α.app N) :=
  unit_mateEquiv (derivedAdjunction k f) (derivedAdjunction k f') α N

/-- The components of the mate of an arbitrary 2-cell for the derived adjunctions. -/
private lemma mateEquiv_derived_app
    (α : pullbackPlus k g ⋙ pullbackPlus k f' ⟶ pullbackPlus k f ⋙ pullbackPlus k g')
    (M : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))) :
    (mateEquiv (derivedAdjunction k f) (derivedAdjunction k f') α).app M =
      (derivedAdjunction k f').unit.app ((pullbackPlus k g).obj ((pushforwardPlus k f).obj M)) ≫
        (pushforwardPlus k f').map (α.app ((pushforwardPlus k f).obj M)) ≫
        (pushforwardPlus k f').map
          ((pullbackPlus k g').map ((derivedAdjunction k f).counit.app M)) := by
  simp [mateEquiv_apply, -derivedAdjunction_unit, -derivedAdjunction_counit]

/-- The components of `baseChange`: the derived unit of `f'`, then `pullbackPlusSquare`, then the
derived counit of `f`. -/
lemma baseChange_app (w : g' ≫ f = f' ≫ g) (M : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))) :
    (baseChange k w).app M =
      (derivedUnit k f').app ((pullbackPlus k g).obj ((pushforwardPlus k f).obj M)) ≫
        (pushforwardPlus k f').map ((pullbackPlusSquare k w).app ((pushforwardPlus k f).obj M)) ≫
        (pushforwardPlus k f').map ((pullbackPlus k g').map ((derivedCounit k f).app M)) := by
  rw [baseChange_eq, ← derivedAdjunction_unit, ← derivedAdjunction_counit]
  exact mateEquiv_derived_app k _ M

/-- **Characterisation of `baseChange`.** `g⁻¹` of the derived unit of `f`, followed by
`baseChange` at `f⁻¹ N`, is the derived unit of `f'` at `g⁻¹ N` followed by `Rf'_*` of
`pullbackPlusSquare`. By adjunction this determines `baseChange`. -/
@[reassoc]
lemma derivedUnit_baseChange (w : g' ≫ f = f' ≫ g)
    (N : DerivedCategory.Plus (Y.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k g).map ((derivedUnit k f).app N) ≫
        (baseChange k w).app ((pullbackPlus k f).obj N) =
      (derivedUnit k f').app ((pullbackPlus k g).obj N) ≫
        (pushforwardPlus k f').map ((pullbackPlusSquare k w).app N) := by
  rw [baseChange_eq, ← derivedAdjunction_unit, ← derivedAdjunction_unit]
  exact unit_mateEquiv_derived k _ N

/-- **Naturality of `baseChange`.** For `φ : M ⟶ N` in `D⁺(Sh X)`,
`g⁻¹ Rf_* φ ≫ baseChange N = baseChange M ≫ Rf'_* g'⁻¹ φ`. -/
@[reassoc]
lemma baseChange_naturality (w : g' ≫ f = f' ≫ g)
    {M N : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))} (φ : M ⟶ N) :
    (pullbackPlus k g).map ((pushforwardPlus k f).map φ) ≫ (baseChange k w).app N =
      (baseChange k w).app M ≫ (pushforwardPlus k f').map ((pullbackPlus k g').map φ) :=
  (baseChange k w).naturality φ

/-- **Base change along homeomorphic direct images.** If `f` and `f'` are homeomorphisms, the
base-change morphism of any commutative square `w : g' ≫ f = f' ≫ g` is an isomorphism. -/
theorem isIso_baseChange_of_isIso (w : g' ≫ f = f' ≫ g) [IsIso f] [IsIso f'] :
    IsIso (baseChange k w) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [baseChange_app]
  infer_instance

end square

end TDA.Sheaf
