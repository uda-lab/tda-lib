import TDA.Sheaf.DerivedPlus

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

end TDA.Sheaf
