import TDA.Sheaf.DerivedPlus
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Reading off the homology of a right derived functor on `D⁺`

Let `C` and `D` be abelian categories, `C` with enough injectives, and `F : C ⥤ D` an additive
functor with right derived functor `RF = F.rightDerivedFunctorPlus` on the bounded below derived
categories.

* `homologyRightDerivedIsoOfInjective F K i`: for a bounded below complex `K` of injective
  objects, `Hⁱ(RF(K)) ≅ Hⁱ(F K)`. The derived-functor comparison `F K ⟶ RF(K)` is invertible on
  such complexes (`isIso_rightDerivedFunctorPlusUnit_app_of_injective`).
* `homologyRightDerivedIsoOfQuasiIso F j i`: the same through a quasi-isomorphism `j : K₀ ⟶ K`
  to a bounded below complex of injective objects, `Hⁱ(RF(K₀)) ≅ Hⁱ(F K)`. Such a `j` exists for
  every bounded below `K₀` (Mathlib's `CochainComplex.Plus.exists_quasiIso_injective`).
* `isIso_Q_map_comp_rightDerivedFunctorPlusUnit`: through such a `j : A ⟶ B`, a morphism
  `u : X ⟶ F A` followed by the comparison `F A ⟶ RF(A)` is invertible in `D⁺` when
  `u ≫ F j` is a quasi-isomorphism.
* `singlePlus n X` is `X` placed in degree `n`, as a bounded below complex, and
  `singleFunctorIsoQ n X` identifies its image in `D⁺` with
  `DerivedCategory.Plus.singleFunctor C n` at `X`.
* `rightDerivedFunctorPlusSingleIso F n A`: an exact functor `F` has right derived functor on
  `D⁺` sending `A` in degree `n` to `F A` in degree `n`.

Naturality in the object:

* `singlePlusFunctor C n : C ⥤ CochainComplex.Plus C` places an object in degree `n`
  (its value at `X` is `singlePlus n X`); `singleFunctorIsoCompQPlus C n` identifies
  `DerivedCategory.Plus.singleFunctor C n` with `singlePlusFunctor C n ⋙ Q`, and
  `singlePlusFunctorCompIso F n` commutes `singlePlusFunctor` with `F` applied termwise.
* `singleRightDerivedFunctorPlusComparison F n : F ⋙ singleFunctor D n ⟶ singleFunctor C n ⋙ RF`
  is the derived-functor comparison at single complexes
  (`singleRightDerivedFunctorPlusComparison_app`). For an exact `F` it is invertible, and
  `singleRightDerivedFunctorPlusIso F n` is the resulting natural isomorphism.
* **Degree `0` of a left exact functor.** `homologyZeroRightDerivedSingleIso F`:
  `H⁰(RF(X[0])) ≅ F X`, naturally in `X`, for a left exact additive `F`. Its inverse is
  `toHomologyZeroRightDerivedSingle F`, `H⁰` of the comparison after
  `F X ≅ H⁰((F X)[0])` (`singleFunctorCompHomologyFunctorIsoPlus`). It is invertible because on
  an injective resolution `X[0] ⟶ I` the comparison at `I` is, and `F` keeps the
  quasi-isomorphism in degree `0` (`quasiIsoAt_zero_map_of_preservesFiniteLimits`,
  `isIso_homologyFunctor_map_rightDerivedFunctorPlusUnit_app`).
-/

noncomputable section
open CategoryTheory Limits

namespace TDA.Sheaf

section readOff

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **Read-off of right derived homology.** On a bounded below complex `K` of injective objects,
`Hⁱ(RF(K))` is the `i`-th homology of `F` applied termwise to `K`. -/
def homologyRightDerivedIsoOfInjective (F : C ⥤ D) [F.Additive] (K : CochainComplex.Plus C)
    [∀ n, Injective (K.obj.X n)] (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D i).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≅
      (F.mapCochainComplexPlus.obj K).obj.homology i :=
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective F K
  (DerivedCategory.Plus.homologyFunctor D i).mapIso
      (asIso (F.rightDerivedFunctorPlusUnit.app K)).symm ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso
      ((DerivedCategory.Plus.QCompιIso D).app (F.mapCochainComplexPlus.obj K)) ≪≫
    (DerivedCategory.homologyFunctorFactors D i).app (F.mapCochainComplexPlus.obj K).obj

/-- Read-off of right derived homology through a quasi-isomorphism `j : K₀ ⟶ K` to a bounded
below complex of injective objects: `Hⁱ(RF(K₀)) ≅ Hⁱ(F K)`. -/
def homologyRightDerivedIsoOfQuasiIso (F : C ⥤ D) [F.Additive] {K₀ K : CochainComplex.Plus C}
    (j : K₀ ⟶ K) (hj : CochainComplex.Plus.quasiIso C j) [∀ n, Injective (K.obj.X n)] (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D i).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K₀)) ≅
      (F.mapCochainComplexPlus.obj K).obj.homology i :=
  have : IsIso (DerivedCategory.Plus.Q.map j) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso C) j hj
  (DerivedCategory.Plus.homologyFunctor D i).mapIso
      (F.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map j))) ≪≫
    homologyRightDerivedIsoOfInjective F K i

/-- Let `j : A ⟶ B` be a quasi-isomorphism to a bounded below complex of injective objects. A
morphism `u : X ⟶ F A` followed by the derived-functor comparison of `F` at `A` is invertible
in `D⁺` when `u ≫ F j` is a quasi-isomorphism. -/
theorem isIso_Q_map_comp_rightDerivedFunctorPlusUnit (F : C ⥤ D) [F.Additive]
    {X : CochainComplex.Plus D} {A B : CochainComplex.Plus C}
    (u : X ⟶ F.mapCochainComplexPlus.obj A) (j : A ⟶ B)
    (hj : CochainComplex.Plus.quasiIso C j) [∀ n, Injective (B.obj.X n)]
    (hψ : CochainComplex.Plus.quasiIso D (u ≫ F.mapCochainComplexPlus.map j)) :
    IsIso (DerivedCategory.Plus.Q.map u ≫ F.rightDerivedFunctorPlusUnit.app A) := by
  have : IsIso (DerivedCategory.Plus.Q.map j) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso _) j hj
  have : IsIso (DerivedCategory.Plus.Q.map (u ≫ F.mapCochainComplexPlus.map j)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso _) _ hψ
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective F B
  have nat : DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map j) ≫
      F.rightDerivedFunctorPlusUnit.app B =
      F.rightDerivedFunctorPlusUnit.app A ≫
        F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map j) :=
    F.rightDerivedFunctorPlusUnit.naturality j
  have eq : DerivedCategory.Plus.Q.map u ≫ F.rightDerivedFunctorPlusUnit.app A =
      (DerivedCategory.Plus.Q.map (u ≫ F.mapCochainComplexPlus.map j) ≫
        F.rightDerivedFunctorPlusUnit.app B) ≫
          inv (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map j)) := by
    rw [IsIso.eq_comp_inv, Functor.map_comp, Category.assoc, Category.assoc, nat]
  rw [eq]
  infer_instance

end readOff

section single

variable {C : Type*} [Category* C] [Abelian C]

/-- The object `X` placed in degree `n`, as a bounded below cochain complex. -/
abbrev singlePlus (n : ℤ) (X : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C n).obj X, n, inferInstance⟩

variable [HasDerivedCategory C]

/-- The object `X` placed in degree `n` of `D⁺` is the localization of `singlePlus n X`. -/
def singleFunctorIsoQ (n : ℤ) (X : C) :
    (DerivedCategory.Plus.singleFunctor C n).obj X ≅ DerivedCategory.Plus.Q.obj (singlePlus n X) :=
  DerivedCategory.Plus.ι.preimageIso ((DerivedCategory.Plus.singleFunctorιIso C n).app X ≪≫
    (DerivedCategory.singleFunctorIsoCompQ C n).app X ≪≫
    ((DerivedCategory.Plus.QCompιIso C).app (singlePlus n X)).symm)

end single

section exact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The right derived functor of an exact functor `F` on `D⁺` sends `A` placed in degree `n` to
`F A` placed in degree `n`. -/
def rightDerivedFunctorPlusSingleIso (n : ℤ) (A : C) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj A) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (F.obj A) :=
  F.rightDerivedFunctorPlus.mapIso (singleFunctorIsoQ n A) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app (singlePlus n A))).symm ≪≫
    DerivedCategory.Plus.Q.mapIso ((CochainComplex.Plus.fullyFaithfulι D).preimageIso
      (Y := singlePlus n (F.obj A))
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app A)) ≪≫
    (singleFunctorIsoQ n (F.obj A)).symm

end exact

section singleFunctors

variable (C : Type*) [Category* C] [Abelian C]

/-- The functor placing an object in degree `n`, as a bounded below cochain complex. Its value at
`X` is `singlePlus n X`. -/
abbrev singlePlusFunctor (n : ℤ) : C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (CochainComplex.singleFunctor C n) fun _ => ⟨n, inferInstance⟩

variable [HasDerivedCategory C]

/-- The single functor of `D⁺` is the localization of `singlePlusFunctor`, naturally. -/
def singleFunctorIsoCompQPlus (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ≅ singlePlusFunctor C n ⋙ DerivedCategory.Plus.Q :=
  ((Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := C))).whiskeringRight
      C).preimageIso
    (DerivedCategory.Plus.singleFunctorιIso C n ≪≫ DerivedCategory.singleFunctorIsoCompQ C n ≪≫
      Functor.isoWhiskerLeft (singlePlusFunctor C n) (DerivedCategory.Plus.QCompιIso C).symm ≪≫
      (Functor.associator _ _ _).symm)


variable {C} {D : Type*} [Category* D] [Abelian D]

/-- Placing an object in degree `n` commutes with an additive functor applied termwise. -/
def singlePlusFunctorCompIso (F : C ⥤ D) [F.Additive] (n : ℤ) :
    singlePlusFunctor C n ⋙ F.mapCochainComplexPlus ≅ F ⋙ singlePlusFunctor D n :=
  ((CochainComplex.Plus.fullyFaithfulι D).whiskeringRight C).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ F.mapCochainComplexPlusCompι ≪≫
      (Functor.associator _ _ _).symm ≪≫ F.mapCochainComplexSingleFunctor n ≪≫
      (Functor.associator F (singlePlusFunctor D n) (CochainComplex.Plus.ι D)).symm)

end singleFunctors

section comparison

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- The comparison `F(X)[n] ⟶ RF(X[n])` on `D⁺`, natural in `X`: the derived-functor comparison
`F.rightDerivedFunctorPlusUnit` at the single complexes. -/
def singleRightDerivedFunctorPlusComparison (F : C ⥤ D) [F.Additive] (n : ℤ) :
    F ⋙ DerivedCategory.Plus.singleFunctor D n ⟶
      DerivedCategory.Plus.singleFunctor C n ⋙ F.rightDerivedFunctorPlus :=
  (Functor.isoWhiskerLeft F (singleFunctorIsoCompQPlus D n) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (singlePlusFunctorCompIso F n).symm _ ≪≫
      Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (singlePlusFunctor C n) F.rightDerivedFunctorPlusUnit ≫
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (singleFunctorIsoCompQPlus C n).symm _).hom

theorem singleRightDerivedFunctorPlusComparison_app (F : C ⥤ D) [F.Additive] (n : ℤ) (X : C) :
    (singleRightDerivedFunctorPlusComparison F n).app X =
      (singleFunctorIsoCompQPlus D n).hom.app (F.obj X) ≫
        DerivedCategory.Plus.Q.map ((singlePlusFunctorCompIso F n).inv.app X) ≫
        F.rightDerivedFunctorPlusUnit.app (singlePlus n X) ≫
        F.rightDerivedFunctorPlus.map ((singleFunctorIsoCompQPlus C n).inv.app X) := by
  simp [singleRightDerivedFunctorPlusComparison]
  rfl

/-- For an exact `F`, the comparison `F(X)[n] ⟶ RF(X[n])` is invertible. -/
instance isIso_singleRightDerivedFunctorPlusComparison (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    IsIso (singleRightDerivedFunctorPlusComparison F n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [singleRightDerivedFunctorPlusComparison_app]
  infer_instance

/-- For an exact `F`, `F(X)[n] ≅ RF(X[n])` on `D⁺`, naturally in `X`: the natural form of
`rightDerivedFunctorPlusSingleIso`, with hom `singleRightDerivedFunctorPlusComparison F n`. -/
def singleRightDerivedFunctorPlusIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (n : ℤ) :
    F ⋙ DerivedCategory.Plus.singleFunctor D n ≅
      DerivedCategory.Plus.singleFunctor C n ⋙ F.rightDerivedFunctorPlus :=
  asIso (singleRightDerivedFunctorPlusComparison F n)

end comparison



section leftExact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- A left exact additive functor keeps a quasi-isomorphism in degree `0` between cochain
complexes concentrated in degrees `≥ 0` a quasi-isomorphism in degree `0`. -/
theorem quasiIsoAt_zero_map_of_preservesFiniteLimits (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex C ℤ} (φ : K ⟶ L) [K.IsStrictlyGE 0]
    [L.IsStrictlyGE 0] [QuasiIsoAt φ 0] :
    QuasiIsoAt ((F.mapHomologicalComplex _).map φ) 0 := by
  have : F.PreservesLeftHomologyOf (K.sc 0) := Functor.preservesLeftHomology_of_zero_f F _
    ((K.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _)
  have : F.PreservesLeftHomologyOf (L.sc 0) := Functor.preservesLeftHomology_of_zero_f F _
    ((L.isZero_of_isStrictlyGE 0 _ (by simp)).eq_of_src _ _)
  have hφ : QuasiIsoAt φ 0 := inferInstance
  rw [quasiIsoAt_iff] at hφ ⊢
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F
    ((HomologicalComplex.shortComplexFunctor C _ 0).map φ)

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- `H⁰` of the derived-functor comparison at an object placed in degree `0` is invertible for a
left exact `F`. -/
theorem isIso_homologyFunctor_map_rightDerivedFunctorPlusUnit_app (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (X : C) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app (singlePlus 0 X))) := by
  let R := injectiveResolution X
  let I : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  let j : singlePlus 0 X ⟶ I := ObjectProperty.homMk R.ι'
  have hj : IsIso (DerivedCategory.Plus.Q.map j) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso C) j
      ((CochainComplex.Plus.quasiIso_iff _ j).2 (inferInstanceAs (QuasiIso R.ι')))
  have hI : IsIso (F.rightDerivedFunctorPlusUnit.app I) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_injective F I
  have hFj : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map j))) := by
    have : QuasiIsoAt ((F.mapHomologicalComplex _).map R.ι') 0 :=
      quasiIsoAt_zero_map_of_preservesFiniteLimits F R.ι'
    change IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor D 0).map
      ((F.mapHomologicalComplex _).map R.ι'))
    rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D 0)]
    exact (quasiIsoAt_iff_isIso_homologyMap _ 0).1 this
  have nat := F.rightDerivedFunctorPlusUnit.naturality j
  have : F.rightDerivedFunctorPlusUnit.app (singlePlus 0 X) =
      (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map j) ≫
        F.rightDerivedFunctorPlusUnit.app I) ≫
        inv (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map j)) := by
    rw [IsIso.eq_comp_inv]
    exact nat.symm
  rw [this, Functor.map_comp, Functor.map_comp]
  infer_instance


/-- `H⁰(X[0]) ≅ X` on `D⁺`, the bounded below form of
`DerivedCategory.singleFunctorCompHomologyFunctorIso`. -/
def singleFunctorCompHomologyFunctorIsoPlus (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) :
    DerivedCategory.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.homologyFunctor C n ≅ 𝟭 C :=
  DerivedCategory.singleFunctorCompHomologyFunctorIso C n

/-- The comparison `F X ⟶ H⁰(RF(X[0]))`, natural in `X`: `H⁰` of
`singleRightDerivedFunctorPlusComparison F 0`, after `F X ≅ H⁰((F X)[0])`. -/
def toHomologyZeroRightDerivedSingle (F : C ⥤ D) [F.Additive] :
    F ⟶ DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D 0 where
  app X := (singleFunctorCompHomologyFunctorIsoPlus D 0).inv.app (F.obj X) ≫
    (DerivedCategory.Plus.homologyFunctor D 0).map
      ((singleRightDerivedFunctorPlusComparison F 0).app X)
  naturality X Y f := by
    have h₁ := (singleFunctorCompHomologyFunctorIsoPlus D 0).inv.naturality (F.map f)
    have h₂ := (singleRightDerivedFunctorPlusComparison F 0).naturality f
    dsimp at h₁ h₂ ⊢
    rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, Category.assoc]

/-- The components of `toHomologyZeroRightDerivedSingle`. -/
theorem toHomologyZeroRightDerivedSingle_app (F : C ⥤ D) [F.Additive] (X : C) :
    (toHomologyZeroRightDerivedSingle F).app X =
      (singleFunctorCompHomologyFunctorIsoPlus D 0).inv.app (F.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          ((singleRightDerivedFunctorPlusComparison F 0).app X) :=
  rfl

/-- For a left exact `F`, the comparison `F X ⟶ H⁰(RF(X[0]))` is invertible. -/
instance isIso_toHomologyZeroRightDerivedSingle (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] : IsIso (toHomologyZeroRightDerivedSingle F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have := isIso_homologyFunctor_map_rightDerivedFunctorPlusUnit_app F X
  rw [toHomologyZeroRightDerivedSingle_app, singleRightDerivedFunctorPlusComparison_app]
  simp only [Functor.map_comp]
  infer_instance

/-- **`H⁰` of a right derived functor.** For a left exact additive `F`, `H⁰(RF(X[0])) ≅ F X`,
naturally in `X`. The inverse is `toHomologyZeroRightDerivedSingle F`. -/
def homologyZeroRightDerivedSingleIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor D 0 ≅ F :=
  (asIso (toHomologyZeroRightDerivedSingle F)).symm

/-- The inverse of `homologyZeroRightDerivedSingleIso` is `toHomologyZeroRightDerivedSingle`. -/
@[simp]
theorem homologyZeroRightDerivedSingleIso_inv (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] :
    (homologyZeroRightDerivedSingleIso F).inv = toHomologyZeroRightDerivedSingle F :=
  rfl

end leftExact

end TDA.Sheaf
