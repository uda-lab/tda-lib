import TDA.Sheaf.BandIntervalDegreeZero

/-!
# Degree-zero band convolution maps

The radius map induces `H0Restr`. On an order-connected open, `H0TSectionsIso_hom_restr`
identifies it with restriction of sections along the inclusion of thickened opens. For
interval sheaves, intersection of the degree-zero output intervals detects nonvanishing.
For the augmentation `H0Aug`, the second interval is the input interval.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory TopologicalSpace Opposite TDA.Persistence

namespace TDA.Sheaf.BandConvolution

private abbrev Sh (k : Type) [Ring k] (X : TopCat.{0}) := X.Sheaf (ModuleCat.{0} k)

-- Apply degree-zero homology to a comparison of single-complex maps.
private theorem singleHomology_naturality {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {A B : C} {X Y : Plus C}
    (f : A ⟶ B) (g : X ⟶ Y)
    (c : (Plus.singleFunctor C 0).obj A ⟶ X)
    (d : (Plus.singleFunctor C 0).obj B ⟶ Y)
    (h : c ≫ g = (Plus.singleFunctor C 0).map f ≫ d) :
    ((singleFunctorCompHomologyFunctorIsoPlus C 0).inv.app A ≫
        (Plus.homologyFunctor C 0).map c) ≫ (Plus.homologyFunctor C 0).map g =
      f ≫ (singleFunctorCompHomologyFunctorIsoPlus C 0).inv.app B ≫
        (Plus.homologyFunctor C 0).map d := by
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  have hn := (singleFunctorCompHomologyFunctorIsoPlus C 0).inv.naturality f
  exact ((reassoc_of% hn) _).symm

private theorem iso_hom_square {C : Type*} [Category* C] {A B A' B' : C}
    (e : A ≅ A') (d : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : e.inv ≫ f = g ≫ d.inv) : f ≫ d.hom = e.hom ≫ g := by
  apply e.inv_comp_eq.mp
  rw [← Category.assoc, h, Category.assoc, d.inv_hom_id, Category.comp_id]

private theorem comparison_restr_paste {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {R : A ⥤ C} {S : B ⥤ C} {Rj : B ⥤ A} {Pj : A ⥤ B}
    (e : S ≅ Rj ⋙ R) (η : 𝟭 A ⟶ Pj ⋙ Rj)
    {a a' a₀ : A} {b b' t : B} {x x' x'' : C}
    (f : a ⟶ a') (g : b ⟶ Pj.obj a) (u : a ⟶ a₀) (v : a₀ ⟶ Rj.obj b)
    (c : b ⟶ b') (d : b' ⟶ t) (z : Pj.obj a' ⟶ t)
    (χ : x ⟶ R.obj a) (χ₀ : x' ⟶ R.obj a₀) (ζ : x' ⟶ S.obj b) (ζ' : x'' ⟶ S.obj b')
    (i : x ⟶ x') (l : x' ⟶ x'')
    (hχ : χ ≫ R.map u = i ≫ χ₀) (he : χ₀ ≫ R.map v = ζ ≫ e.hom.app b)
    (hη : η.app a = u ≫ v ≫ Rj.map g) (hz : g ≫ Pj.map f ≫ z = c ≫ d)
    (hζ : ζ ≫ S.map c = l ≫ ζ') :
    (χ ≫ R.map f) ≫
      R.map (η.app a') ≫ e.inv.app (Pj.obj a') ≫ S.map z =
        (i ≫ l) ≫ ζ' ≫ S.map d := by
  have hn : f ≫ η.app a' = η.app a ≫ Rj.map (Pj.map f) := η.naturality f
  have hn' : R.map (Rj.map (g ≫ Pj.map f)) ≫ e.inv.app (Pj.obj a') =
      e.inv.app b ≫ S.map (g ≫ Pj.map f) := e.inv.naturality _
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hn, hη]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hχ, reassoc_of% he]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, reassoc_of% hn',
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Category.assoc, hz, Functor.map_comp,
    reassoc_of% hζ]

section Comparison

variable (k : Type) [Ring k] {X X' Z W : TopCat.{0}}
  [HasDerivedCategory (Sh k X)] [HasDerivedCategory (Sh k X')]
  [HasDerivedCategory (Sh k Z)] [HasDerivedCategory (Sh k W)]

local notation "P" => TopCat.Sheaf.pullback (ModuleCat k)
local notation "Qf" => TopCat.Sheaf.pushforward (ModuleCat k)
local notation "η" => Functor.rightDerivedFunctorPlusUnit

private def corrSheaf (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W) :
    P p ⋙ Qf q ⟶ P (j ≫ p) ⋙ Qf (j ≫ q) :=
  Functor.whiskerLeft _ (Functor.whiskerRight
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) j).unit (Qf q)) ≫
      Functor.whiskerRight (pullbackCompIso k j p).hom (Qf (j ≫ q))

private def corrComparison (p : X ⟶ Z) (q : X ⟶ W)
    (K : CochainComplex.Plus (Sh k Z)) :
    Plus.Q.obj (((P p ⋙ Qf q).mapCochainComplexPlus).obj K) ⟶
      (pushforwardPlus k q).obj ((pullbackPlus k p).obj (Plus.Q.obj K)) :=
  (η (Qf q)).app ((P p).mapCochainComplexPlus.obj K) ≫
    (pushforwardPlus k q).map ((η (P p)).app K)

private theorem corrComparison_restr (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W)
    (K : CochainComplex.Plus (Sh k Z)) :
    corrComparison k p q K ≫ (corrRestr k j p q).app (Plus.Q.obj K) =
      Plus.Q.map ((NatTrans.mapCochainComplexPlus (corrSheaf k j p q)).app K) ≫
        corrComparison k (j ≫ p) (j ≫ q) K := by
  let A := (P p).mapCochainComplexPlus.obj K
  let B := (P j).mapCochainComplexPlus.obj A
  let f := (η (P p)).app K
  let g := (η (P j)).app A
  let u := (unitCochain k j).app A
  let c := ((mapCochainComplexPlusCompIso (pullbackCompIso k j p)).hom.app K)
  let R := pushforwardPlus k q
  let S := pushforwardPlus k (j ≫ q)
  let C := pushforwardPlusCompIso k j q
  let Pj := pullbackPlus k j
  have hη := (η (Qf q)).naturality u
  change Plus.Q.map ((Qf q).mapCochainComplexPlus.map u) ≫ (η (Qf q)).app _ =
    (η (Qf q)).app A ≫ R.map (Plus.Q.map u) at hη
  have hC : (η (Qf q)).app ((Qf j).mapCochainComplexPlus.obj B) ≫
      R.map ((η (Qf j)).app B) =
        (η (Qf (j ≫ q))).app B ≫ C.hom.app (Plus.Q.obj B) :=
    (pushforwardPlusComp_fac_app k j q B).symm
  have hp : g ≫ Pj.map f ≫ (pullbackPlusCompIso k j p).hom.app (Plus.Q.obj K) =
      Plus.Q.map c ≫ (η (P (j ≫ p))).app K :=
    pullbackPlusCompIso_hom_fac_app k j p K
  have hq := (η (Qf (j ≫ q))).naturality c
  change Plus.Q.map ((Qf (j ≫ q)).mapCochainComplexPlus.map c) ≫ (η (Qf (j ≫ q))).app _ =
    (η (Qf (j ≫ q))).app B ≫ S.map (Plus.Q.map c) at hq
  have ht : (NatTrans.mapCochainComplexPlus (corrSheaf k j p q)).app K =
      (Qf q).mapCochainComplexPlus.map u ≫ (Qf (j ≫ q)).mapCochainComplexPlus.map c := by
    ext n : 2
    rfl
  rw [corrRestr_app]
  have hpaste := comparison_restr_paste C (derivedUnit k j) f g (Plus.Q.map u)
    ((η (Qf j)).app B) (Plus.Q.map c) ((η (P (j ≫ p))).app K)
    ((pullbackPlusCompIso k j p).hom.app (Plus.Q.obj K))
    ((η (Qf q)).app A) ((η (Qf q)).app ((Qf j).mapCochainComplexPlus.obj B))
    ((η (Qf (j ≫ q))).app B) ((η (Qf (j ≫ q))).app _)
    (Plus.Q.map ((Qf q).mapCochainComplexPlus.map u))
    (Plus.Q.map ((Qf (j ≫ q)).mapCochainComplexPlus.map c))
    hη.symm hC (derivedUnit_app_Q k j A) hp hq.symm
  refine hpaste.trans ?_
  exact congrArg (· ≫ corrComparison k (j ≫ p) (j ≫ q) K)
    ((Functor.map_comp Plus.Q _ _).symm.trans (congrArg Plus.Q.map ht.symm))

private theorem singleCompInv_map {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] (A : C) :
    (CochainComplex.Plus.ι D).map ((singlePlusFunctorCompIso F 0).inv.app A) =
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app A := by
  simp [singlePlusFunctorCompIso, Functor.mapCochainComplexSingleFunctor]
  rfl

private theorem singleComp_inv {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (A : C) :
    (singlePlusFunctorCompIso (F ⋙ G) 0).inv.app A =
      (singlePlusFunctorCompIso G 0).inv.app (F.obj A) ≫
        G.mapCochainComplexPlus.map ((singlePlusFunctorCompIso F 0).inv.app A) := by
  apply (CochainComplex.Plus.ι E).map_injective
  simp only [Functor.map_comp, singleCompInv_map]
  have he : (CochainComplex.Plus.ι E).map
      (G.mapCochainComplexPlus.map ((singlePlusFunctorCompIso F 0).inv.app A)) =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((CochainComplex.Plus.ι D).map ((singlePlusFunctorCompIso F 0).inv.app A)) := rfl
  rw [he, singleCompInv_map]
  exact HomologicalComplex.singleMapHomologicalComplex_comp_inv_app F G (ComplexShape.up ℤ) 0 A

private theorem singleTermwise_app {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) (A : C) :
    (singlePlusFunctorCompIso F 0).inv.app A ≫
      (NatTrans.mapCochainComplexPlus τ).app (singlePlus 0 A) =
        (singlePlusFunctor D 0).map (τ.app A) ≫ (singlePlusFunctorCompIso G 0).inv.app A := by
  apply (CochainComplex.Plus.ι D).map_injective
  simp only [Functor.map_comp, singleCompInv_map]
  change (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app A ≫
      (τ.mapHomologicalComplex _).app _ = _
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj, Iso.inv_hom_id_app_assoc]
  rfl

private def corrSingleComparison (p : X ⟶ Z) (q : X ⟶ W) (F : Sh k Z) :
    (Plus.singleFunctor _ 0).obj ((P p ⋙ Qf q).obj F) ⟶
      (pushforwardPlus k q).obj ((pullbackPlus k p).obj ((Plus.singleFunctor _ 0).obj F)) :=
  (singleRightDerivedFunctorPlusComparison (Qf q) 0).app ((P p).obj F) ≫
    (pushforwardPlus k q).map ((singleRightDerivedFunctorPlusComparison (P p) 0).app F)

private theorem singleComparison_comp_fac {C D E : Type*}
    [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D] (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] (A : C) :
    (singleRightDerivedFunctorPlusComparison G 0).app (F.obj A) ≫
        G.rightDerivedFunctorPlus.map ((singleRightDerivedFunctorPlusComparison F 0).app A) =
      (singleFunctorIsoCompQPlus E 0).hom.app ((F ⋙ G).obj A) ≫
        Plus.Q.map ((singlePlusFunctorCompIso (F ⋙ G) 0).inv.app A) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj (singlePlus 0 A)) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app (singlePlus 0 A)) ≫
        (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).map
          ((singleFunctorIsoCompQPlus C 0).inv.app A) := by
  rw [singleRightDerivedFunctorPlusComparison_app, singleRightDerivedFunctorPlusComparison_app,
    singleComp_inv]
  let e := (singleFunctorIsoCompQPlus D 0).app (F.obj A)
  let d := (singlePlusFunctorCompIso F 0).inv.app A
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj, Functor.comp_map]
  change _ ≫ _ ≫ _ ≫ G.rightDerivedFunctorPlus.map e.inv ≫
    G.rightDerivedFunctorPlus.map e.hom ≫ _ = _
  rw [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hn : Plus.Q.map (G.mapCochainComplexPlus.map d) ≫
      G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj (singlePlus 0 A)) =
    G.rightDerivedFunctorPlusUnit.app (singlePlus 0 (F.obj A)) ≫
      G.rightDerivedFunctorPlus.map (Plus.Q.map d) :=
    G.rightDerivedFunctorPlusUnit.naturality d
  rw [reassoc_of% hn]

private theorem corrSingleComparison_fac (p : X ⟶ Z) (q : X ⟶ W) (F : Sh k Z) :
    corrSingleComparison k p q F =
      (singleFunctorIsoCompQPlus (Sh k W) 0).hom.app ((P p ⋙ Qf q).obj F) ≫
        Plus.Q.map ((singlePlusFunctorCompIso (P p ⋙ Qf q) 0).inv.app F) ≫
        corrComparison k p q (singlePlus 0 F) ≫
        ((pullbackPlus k p) ⋙ (pushforwardPlus k q)).map
          ((singleFunctorIsoCompQPlus (Sh k Z) 0).inv.app F) := by
  rw [corrSingleComparison, corrComparison, Category.assoc]
  exact singleComparison_comp_fac (P p) (Qf q) F

private theorem singleComparison_naturality {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] {R S : Plus C ⥤ Plus D}
    (τ : F ⟶ G) (ρ : R ⟶ S) (A : C)
    (α : Plus.Q.obj (F.mapCochainComplexPlus.obj (singlePlus 0 A)) ⟶
      R.obj (Plus.Q.obj (singlePlus 0 A)))
    (β : Plus.Q.obj (G.mapCochainComplexPlus.obj (singlePlus 0 A)) ⟶
      S.obj (Plus.Q.obj (singlePlus 0 A)))
    (h : α ≫ ρ.app (Plus.Q.obj (singlePlus 0 A)) =
      Plus.Q.map ((τ.mapCochainComplexPlus).app (singlePlus 0 A)) ≫ β) :
    ((singleFunctorIsoCompQPlus D 0).hom.app (F.obj A) ≫
      Plus.Q.map ((singlePlusFunctorCompIso F 0).inv.app A) ≫ α ≫
      R.map ((singleFunctorIsoCompQPlus C 0).inv.app A)) ≫
        ρ.app ((Plus.singleFunctor C 0).obj A) =
      (Plus.singleFunctor D 0).map (τ.app A) ≫
        (singleFunctorIsoCompQPlus D 0).hom.app (G.obj A) ≫
        Plus.Q.map ((singlePlusFunctorCompIso G 0).inv.app A) ≫ β ≫
        S.map ((singleFunctorIsoCompQPlus C 0).inv.app A) := by
  simp only [Category.assoc]
  rw [ρ.naturality, reassoc_of% h, ← Functor.map_comp_assoc, singleTermwise_app,
    Functor.map_comp, Category.assoc]
  have hn := (singleFunctorIsoCompQPlus D 0).hom.naturality (τ.app A)
  exact ((reassoc_of% hn) _).symm

private theorem corrSingleComparison_restr (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W)
    (F : Sh k Z) :
    corrSingleComparison k p q F ≫ (corrRestr k j p q).app ((Plus.singleFunctor _ 0).obj F) =
      (Plus.singleFunctor _ 0).map ((corrSheaf k j p q).app F) ≫
        corrSingleComparison k (j ≫ p) (j ≫ q) F := by
  rw [corrSingleComparison_fac, corrSingleComparison_fac]
  exact singleComparison_naturality (corrSheaf k j p q) (corrRestr k j p q) F _ _
    (corrComparison_restr k j p q (singlePlus 0 F))

private def derivedIdentityComparison (C : Type*) [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] : (𝟭 C).rightDerivedFunctorPlus ⟶ 𝟭 (Plus C) :=
  (𝟭 C).rightDerivedFunctorPlus.rightDerivedDesc (𝟭 C).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso C) _ (Functor.rightUnitor Plus.Q).inv

private theorem derivedIdentityComparison_fac {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] (K : CochainComplex.Plus C) :
    (𝟭 C).rightDerivedFunctorPlusUnit.app K ≫
      (derivedIdentityComparison C).app (Plus.Q.obj K) = 𝟙 (Plus.Q.obj K) :=
  Functor.rightDerived_fac_app _ _ (CochainComplex.Plus.quasiIso C) _ _ K

private theorem derivedIdentityComparison_single {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] (A : C) :
    ((singleRightDerivedFunctorPlusComparison (𝟭 C) 0).app A) ≫
      (derivedIdentityComparison C).app ((Plus.singleFunctor C 0).obj A) = 𝟙 _ := by
  have hi : (singlePlusFunctorCompIso (𝟭 C) 0).inv.app A = 𝟙 _ := by
    apply (CochainComplex.Plus.ι C).map_injective
    rw [singleCompInv_map, CategoryTheory.Functor.map_id]
    exact HomologicalComplex.singleMapHomologicalComplex_id_inv_app (ComplexShape.up ℤ) 0 A
  let e := (singleFunctorIsoCompQPlus C 0).app A
  let ρ := derivedIdentityComparison C
  let K := singlePlus 0 A
  have hm : Plus.Q.map ((singlePlusFunctorCompIso (𝟭 C) 0).inv.app A) =
      𝟙 (Plus.Q.obj K) := (congrArg Plus.Q.map hi).trans ((Plus.Q (C := C)).map_id K)
  rw [singleRightDerivedFunctorPlusComparison_app, hm]
  change (e.hom ≫ 𝟙 (Plus.Q.obj K) ≫ (η (𝟭 C)).app K ≫
    (𝟭 C).rightDerivedFunctorPlus.map e.inv) ≫ ρ.app _ = 𝟙 _
  have hn : (𝟭 C).rightDerivedFunctorPlus.map e.inv ≫ ρ.app _ =
      ρ.app (Plus.Q.obj K) ≫ e.inv := ρ.naturality e.inv
  calc
    _ = e.hom ≫ (η (𝟭 C)).app K ≫ ρ.app (Plus.Q.obj K) ≫ e.inv := by
      simp only [Category.assoc, hn]
      exact congrArg (e.hom ≫ ·) (Category.id_comp _)
    _ = _ := by
      rw [reassoc_of% (derivedIdentityComparison_fac K)]
      exact (congrArg (e.hom ≫ ·) (Category.id_comp e.inv)).trans e.hom_inv_id

omit [HasDerivedCategory (Sh k X')] in
private def corrDerivedComparison (p : X ⟶ Z) (q : X ⟶ W) :
    (P p ⋙ Qf q).rightDerivedFunctorPlus ⟶ pullbackPlus k p ⋙ pushforwardPlus k q :=
  Functor.natTransOfIsRightDerivedFunctorComp
    (mapCochainComplexPlusCompIso (Iso.refl (P p ⋙ Qf q)))
    Plus.Q Plus.Q Plus.Q (CochainComplex.Plus.quasiIso _)
    (η (P p)) (η (Qf q)) (η (P p ⋙ Qf q))

omit [HasDerivedCategory (Sh k X')] in
private theorem corrDerivedComparison_fac (p : X ⟶ Z) (q : X ⟶ W)
    (K : CochainComplex.Plus (Sh k Z)) :
    (η (P p ⋙ Qf q)).app K ≫ (corrDerivedComparison k p q).app (Plus.Q.obj K) =
      corrComparison k p q K := by
  have hf := Functor.comp_natTransOfIsRightDerivedFunctorComp_app
    (mapCochainComplexPlusCompIso (Iso.refl (P p ⋙ Qf q)))
    Plus.Q Plus.Q Plus.Q (CochainComplex.Plus.quasiIso _)
    (η (P p)) (η (Qf q)) (η (P p ⋙ Qf q)) K
  have he : (mapCochainComplexPlusCompIso (Iso.refl (P p ⋙ Qf q))).inv.app K = 𝟙 _ := rfl
  have hm : Plus.Q.map ((mapCochainComplexPlusCompIso (Iso.refl (P p ⋙ Qf q))).inv.app K) =
      𝟙 _ := by
    rw [he]
    exact (Plus.Q (C := Sh k W)).map_id _
  rw [hm, Category.id_comp] at hf
  exact hf

omit [HasDerivedCategory (Sh k X')] in
private theorem corrDerivedComparison_single (p : X ⟶ Z) (q : X ⟶ W) (F : Sh k Z) :
    (singleRightDerivedFunctorPlusComparison (P p ⋙ Qf q) 0).app F ≫
      (corrDerivedComparison k p q).app ((Plus.singleFunctor _ 0).obj F) =
        corrSingleComparison k p q F := by
  rw [singleRightDerivedFunctorPlusComparison_app, corrSingleComparison_fac]
  simp only [Category.assoc, NatTrans.naturality,
    reassoc_of% (corrDerivedComparison_fac k p q (singlePlus 0 F))]

omit [HasDerivedCategory (Sh k X')] [HasDerivedCategory (Sh k W)] in
private theorem derivedUnit_rightDerived (f : X ⟶ Z) :
    derivedIdentityComparison (Sh k Z) ≫ derivedUnit k f =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) f).unit).rightDerivedFunctorPlus ≫
        corrDerivedComparison k f f := by
  let u := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) f).unit
  apply Functor.rightDerived_ext _ ((𝟭 (Sh k Z)).rightDerivedFunctorPlusUnit)
    (CochainComplex.Plus.quasiIso _) _ _ _
  apply NatTrans.ext
  funext K
  change _ ≫ (derivedIdentityComparison _).app _ ≫ (derivedUnit k f).app _ =
    _ ≫ u.rightDerivedFunctorPlus.app _ ≫ (corrDerivedComparison k f f).app _
  calc
    _ = (derivedUnit k f).app (Plus.Q.obj K) := by
      rw [← Category.assoc, derivedIdentityComparison_fac]
      exact Category.id_comp _
    _ = _ := by
      rw [← Category.assoc, u.rightDerivedFunctorPlus_fac_app, Category.assoc,
        corrDerivedComparison_fac, derivedUnit_app_Q]
      rfl

private theorem homologyZero_comparison_comp
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (A : C) {Y : Plus D}
    (f : G.rightDerivedFunctorPlus.obj ((Plus.singleFunctor C 0).obj A) ⟶ Y)
    (g : (Plus.singleFunctor D 0).obj (G.obj A) ⟶ Y)
    (h : (singleRightDerivedFunctorPlusComparison G 0).app A ≫ f = g) :
    (homologyZeroRightDerivedSingleIso G).inv.app A ≫ (Plus.homologyFunctor D 0).map f =
      (singleFunctorCompHomologyFunctorIsoPlus D 0).inv.app (G.obj A) ≫
        (Plus.homologyFunctor D 0).map g := by
  rw [homologyZeroRightDerivedSingleIso_inv, toHomologyZeroRightDerivedSingle_app,
    Category.assoc, ← Functor.map_comp, h]

omit [HasDerivedCategory (Sh k X)] [HasDerivedCategory (Sh k X')]
  [HasDerivedCategory (Sh k Z)] [HasDerivedCategory (Sh k W)] in
private theorem corrSheaf_unitRes (j : X' ⟶ X) (p : X ⟶ Z) (q : X ⟶ W)
    (F : Sh k Z) (U : Opens W) (V : Opens Z)
    (h : (Opens.map q).obj U ≤ (Opens.map p).obj V)
    (h' : (Opens.map (j ≫ q)).obj U ≤ (Opens.map (j ≫ p)).obj V) :
    pullbackUnitRes k p F h ≫ ((corrSheaf k j p q).app F).hom.app (op U) =
      pullbackUnitRes k (j ≫ p) F h' := by
  let G := (P p).obj F
  let u := ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) j).unit.app G).hom
  let c := ((pullbackCompIso k j p).hom.app F).hom
  let W₀ := (Opens.map q).obj U
  let V₀ := (Opens.map p).obj V
  let f := (homOfLE h).op
  let f' := ((Opens.map j).map (homOfLE h)).op
  let t := ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) p).unit.app F).hom
  change (t.app (op V) ≫ G.presheaf.map f) ≫
    u.app (op W₀) ≫ c.app (op ((Opens.map j).obj W₀)) = _
  have hu : G.presheaf.map f ≫ u.app (op W₀) =
      u.app (op V₀) ≫ ((P j).obj G).presheaf.map f' := u.naturality f
  have hc := c.naturality f'
  have he := congrArg (fun g : F ⟶ (Qf (j ≫ p)).obj ((P (j ≫ p)).obj F) =>
    g.hom.app (op V)) (unit_pullbackCompIso_hom_app k j p F)
  change t.app (op V) ≫ u.app (op V₀) ≫ c.app (op ((Opens.map j).obj V₀)) = _ at he
  calc
    _ = t.app (op V) ≫ u.app (op V₀) ≫ c.app (op ((Opens.map j).obj V₀)) ≫
        ((P (j ≫ p)).obj F).presheaf.map f' := by
      erw [Category.assoc, reassoc_of% hu, Category.assoc, hc]
      rfl
    _ = _ := (reassoc_of% he) _

/-- The degree-zero comparison for additive left exact functors is natural in the functor.
For `τ : F ⟶ G`, the map `H⁰(Rτ(X[0]))` corresponds to `τ.app X`. -/
@[reassoc]
theorem _root_.TDA.Sheaf.homologyZeroRightDerivedSingleIso_inv_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (τ : F ⟶ G) (A : C) :
    (homologyZeroRightDerivedSingleIso F).inv.app A ≫
        (Plus.homologyFunctor D 0).map
          (τ.rightDerivedFunctorPlus.app ((Plus.singleFunctor C 0).obj A)) =
      τ.app A ≫ (homologyZeroRightDerivedSingleIso G).inv.app A := by
  have h :
      (singleRightDerivedFunctorPlusComparison F 0).app A ≫
          τ.rightDerivedFunctorPlus.app ((Plus.singleFunctor C 0).obj A) =
        (Plus.singleFunctor D 0).map (τ.app A) ≫
          (singleRightDerivedFunctorPlusComparison G 0).app A := by
    rw [singleRightDerivedFunctorPlusComparison_app, singleRightDerivedFunctorPlusComparison_app]
    exact singleComparison_naturality τ τ.rightDerivedFunctorPlus A _ _
      (τ.rightDerivedFunctorPlus_fac_app (singlePlus 0 A))
  simp only [homologyZeroRightDerivedSingleIso_inv, toHomologyZeroRightDerivedSingle_app]
  exact singleHomology_naturality _ _ _ _ h


omit [HasDerivedCategory (Sh k X')] [HasDerivedCategory (Sh k W)] in
private theorem derivedUnit_homology (q : X ⟶ Z) (F : Sh k Z) :
    (singleFunctorCompHomologyFunctorIsoPlus (Sh k Z) 0).inv.app F ≫
      (Plus.homologyFunctor _ 0).map ((derivedUnit k q).app ((Plus.singleFunctor _ 0).obj F)) =
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) q).unit.app F ≫
      ((singleFunctorCompHomologyFunctorIsoPlus (Sh k Z) 0).inv.app ((P q ⋙ Qf q).obj F) ≫
        (Plus.homologyFunctor _ 0).map (corrSingleComparison k q q F)) := by
  let S := Plus.singleFunctor (Sh k Z) 0
  let H := Plus.homologyFunctor (Sh k Z) 0
  let c := corrDerivedComparison k q q
  let e := derivedIdentityComparison (Sh k Z)
  let u := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) q).unit
  let v := (derivedUnit k q).app (S.obj F)
  let z := (singleFunctorCompHomologyFunctorIsoPlus (Sh k Z) 0).inv
  let α := (homologyZeroRightDerivedSingleIso (𝟭 (Sh k Z))).inv.app F
  let β := (homologyZeroRightDerivedSingleIso (P q ⋙ Qf q)).inv.app F
  have he : α ≫ H.map (e.app (S.obj F)) = z.app F := by
    have h := homologyZero_comparison_comp (𝟭 (Sh k Z)) F (e.app (S.obj F)) (𝟙 _)
      (derivedIdentityComparison_single F)
    rw [CategoryTheory.Functor.map_id] at h
    exact h.trans (Category.comp_id _)
  have hc : β ≫ H.map (c.app (S.obj F)) =
      z.app ((P q ⋙ Qf q).obj F) ≫ H.map (corrSingleComparison k q q F) :=
    homologyZero_comparison_comp (P q ⋙ Qf q) F (c.app (S.obj F))
      (corrSingleComparison k q q F) (corrDerivedComparison_single k q q F)
  have hu : e.app (S.obj F) ≫ v =
      u.rightDerivedFunctorPlus.app (S.obj F) ≫ c.app (S.obj F) :=
    congrArg (fun t => t.app (S.obj F)) (derivedUnit_rightDerived k q)
  change z.app F ≫ H.map v = u.app F ≫ _
  calc
    _ = (α ≫ H.map (e.app (S.obj F))) ≫ H.map v := congrArg (· ≫ H.map v) he.symm
    _ = α ≫ H.map (u.rightDerivedFunctorPlus.app (S.obj F) ≫ c.app (S.obj F)) := by
      rw [Category.assoc, ← H.map_comp, hu]
    _ = (α ≫ H.map (u.rightDerivedFunctorPlus.app (S.obj F))) ≫ H.map (c.app (S.obj F)) := by
      rw [H.map_comp, Category.assoc]
    _ = u.app F ≫ (β ≫ H.map (c.app (S.obj F))) := by
      rw [homologyZeroRightDerivedSingleIso_inv_naturality u F, Category.assoc]
    _ = _ := congrArg (u.app F ≫ ·) hc

omit [HasDerivedCategory (Sh k X)] [HasDerivedCategory (Sh k X')]
  [HasDerivedCategory (Sh k Z)] [HasDerivedCategory (Sh k W)] in
private def transportedUnit {p q : X ⟶ Z} (h : q = p) : 𝟭 _ ⟶ P p ⋙ Qf q :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) q).unit ≫
    Functor.whiskerRight (eqToHom (congrArg P h)) (Qf q)

omit [HasDerivedCategory (Sh k X')] [HasDerivedCategory (Sh k W)] in
private def transportedDerivedUnit {p q : X ⟶ Z} (h : q = p) :
    𝟭 _ ⟶ pullbackPlus k p ⋙ pushforwardPlus k q :=
  derivedUnit k q ≫
    Functor.whiskerRight (eqToHom (congrArg (pullbackPlus k) h)) (pushforwardPlus k q)

omit [HasDerivedCategory (Sh k X')] [HasDerivedCategory (Sh k W)] in
private theorem transportedDerivedUnit_homology {p q : X ⟶ Z} (h : q = p) (F : Sh k Z) :
    (singleFunctorCompHomologyFunctorIsoPlus (Sh k Z) 0).inv.app F ≫
      (Plus.homologyFunctor _ 0).map
        ((transportedDerivedUnit k h).app ((Plus.singleFunctor _ 0).obj F)) =
    (transportedUnit k h).app F ≫
      ((singleFunctorCompHomologyFunctorIsoPlus (Sh k Z) 0).inv.app ((P p ⋙ Qf q).obj F) ≫
        (Plus.homologyFunctor _ 0).map (corrSingleComparison k p q F)) := by
  subst p
  have hρ : transportedDerivedUnit k (rfl : q = q) = derivedUnit k q := by
    rw [transportedDerivedUnit, eqToHom_refl, Functor.whiskerRight_id']
    exact Category.comp_id _
  have hu : transportedUnit k (rfl : q = q) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) q).unit := by
    rw [transportedUnit, eqToHom_refl, Functor.whiskerRight_id']
    exact Category.comp_id _
  rw [hρ, hu]
  exact derivedUnit_homology k q F

end Comparison

section Maps

variable (k : Type) [Ring k] [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

local notation "H₀" => Plus.homologyFunctor (realLine.Sheaf (ModuleCat k)) 0
local notation "S₀" => Plus.singleFunctor (realLine.Sheaf (ModuleCat k)) 0
local notation "P" => TopCat.Sheaf.pullback (ModuleCat k)
local notation "Qf" => TopCat.Sheaf.pushforward (ModuleCat k)

/-- The map on degree-zero convolution induced by a radius comparison. -/
def H0Restr {δ ε : ℝ} (h : δ ≤ ε) (F : realLine.Sheaf (ModuleCat k)) :
    (H₀).obj ((T k ε).obj ((S₀).obj F)) ⟶ (H₀).obj ((T k δ).obj ((S₀).obj F)) :=
  (H₀).map ((restr k h).app ((S₀).obj F))

/-- The degree-zero augmentation to a sheaf, using the single-complex identification. -/
def H0Aug {ε : ℝ} (h : 0 ≤ ε) (F : realLine.Sheaf (ModuleCat k)) :
    (H₀).obj ((T k ε).obj ((S₀).obj F)) ⟶ F :=
  (H₀).map ((aug k h).app ((S₀).obj F)) ≫
    (singleFunctorCompHomologyFunctorIsoPlus _ 0).hom.app F

private theorem H0Aug_ne_zero_iff {ε : ℝ} (h : 0 ≤ ε) (F : Sh k realLine) :
    H0Aug k h F ≠ 0 ↔ H0Restr k h F ≠ 0 := by
  let e := ((H₀).mapIso ((T0Iso k).app ((S₀).obj F))) ≪≫
    (singleFunctorCompHomologyFunctorIsoPlus _ 0).app F
  have he : H0Aug k h F = H0Restr k h F ≫ e.hom := by
    unfold H0Aug H0Restr
    rw [aug, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rfl
  rw [he]
  exact not_congr (comp_eq_zero_iff_of_mono e.hom)

private theorem H0TIso_inv_app_eq (ε : ℝ) (F : Sh k realLine) :
    (H0TIso k ε).inv.app F =
      (singleFunctorCompHomologyFunctorIsoPlus (Sh k realLine) 0).inv.app
        ((thickening k ε).obj F) ≫ (H₀).map (corrSingleComparison k (p ε) (q ε) F) := by
  rw [H0TIso_inv_app, toHomologyZeroRightDerivedSingle_app, corrSingleComparison,
    Functor.map_comp, Category.assoc]
  rfl

private theorem H0Restr_comparison {δ ε : ℝ} (h : δ ≤ ε) (F : Sh k realLine) :
    (H0TIso k ε).inv.app F ≫ H0Restr k h F =
      (corrSheaf k (incl h) (p ε) (q ε)).app F ≫ (H0TIso k δ).inv.app F := by
  let a : (thickening k ε).obj F ⟶ (thickening k δ).obj F :=
    (corrSheaf k (incl h) (p ε) (q ε)).app F
  let r : (T k ε).obj ((S₀).obj F) ⟶ (T k δ).obj ((S₀).obj F) :=
    (restr k h).app ((S₀).obj F)
  have hs : corrSingleComparison k (p ε) (q ε) F ≫ r =
      (S₀).map a ≫ corrSingleComparison k (p δ) (q δ) F :=
    corrSingleComparison_restr k (incl h) (p ε) (q ε) F
  have hn := singleHomology_naturality a r (corrSingleComparison k (p ε) (q ε) F)
    (corrSingleComparison k (p δ) (q δ) F) hs
  change _ ≫ (H₀).map r = a ≫ _
  rw [H0TIso_inv_app_eq, H0TIso_inv_app_eq]
  exact hn

private theorem H0TSectionsIso_inv_restr {δ ε : ℝ} (h : δ ≤ ε) (F : Sh k realLine)
    (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    (H0TSectionsIso k ε F U hU).inv ≫ (H0Restr k h F).hom.app (op U) =
      F.presheaf.map (homOfLE (bandOpen_mono h U)).op ≫ (H0TSectionsIso k δ F U hU).inv := by
  let ev : realLine.Sheaf (ModuleCat k) ⥤ ModuleCat k :=
    sheafToPresheaf (Opens.grothendieckTopology realLine) (ModuleCat k) ⋙
      (evaluation _ _).obj (op U)
  let a : (thickening k ε).obj F ⟶ (thickening k δ).obj F :=
    (corrSheaf k (incl h) (p ε) (q ε)).app F
  have hn : ev.map ((H0TIso k ε).inv.app F) ≫ ev.map (H0Restr k h F) =
      ev.map a ≫ ev.map ((H0TIso k δ).inv.app F) :=
    (ev.map_comp _ _).symm.trans
      ((congrArg ev.map (H0Restr_comparison k h F)).trans (ev.map_comp a _))
  change (thickeningSectionsIso k ε F U hU).inv ≫ (ev.map ((H0TIso k ε).inv.app F) ≫
      ev.map (H0Restr k h F)) =
    F.presheaf.map (homOfLE (bandOpen_mono h U)).op ≫ (thickeningSectionsIso k δ F U hU).inv ≫
      ev.map ((H0TIso k δ).inv.app F)
  rw [hn, ← Category.assoc, thickeningSectionsIso_inv, thickeningSectionsIso_inv]
  have hlarge : (Opens.map (q δ)).obj U ≤ (Opens.map (p δ)).obj (bandOpen ε U) :=
    (tube_le_bandOpen δ U).trans ((Opens.map (p δ)).monotone (bandOpen_mono h U))
  have hh := corrSheaf_unitRes k (incl h) (p ε) (q ε) F U (bandOpen ε U)
    (tube_le_bandOpen ε U) hlarge
  change pullbackUnitRes k (p ε) F (tube_le_bandOpen ε U) ≫
    ev.map a = _ at hh
  have ht := pullbackUnitRes_map k (p δ) F hlarge (tube_le_bandOpen δ U)
    le_rfl (bandOpen_mono h U)
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id] at ht
  exact (congrArg (· ≫ ev.map ((H0TIso k δ).inv.app F)) (hh.trans ht)).trans
    (Category.assoc _ _ _)

/-- Under the section isomorphisms, the radius map restricts from the larger thickened open
to the smaller one. -/
@[reassoc]
theorem H0TSectionsIso_hom_restr {δ ε : ℝ} (_hδ : 0 ≤ δ) (h : δ ≤ ε)
    (F : realLine.Sheaf (ModuleCat k)) (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    (H0Restr k h F).hom.app (op U) ≫ (H0TSectionsIso k δ F U hU).hom =
      (H0TSectionsIso k ε F U hU).hom ≫ F.presheaf.map (homOfLE (bandOpen_mono h U)).op := by
  exact iso_hom_square (H0TSectionsIso k ε F U hU) (H0TSectionsIso k δ F U hU)
    ((H0Restr k h F).hom.app (op U)) (F.presheaf.map (homOfLE (bandOpen_mono h U)).op)
    (H0TSectionsIso_inv_restr k h F U hU)

private def thickeningZeroUnit (F : Sh k realLine) : F ⟶ (thickening k 0).obj F :=
  (transportedUnit k p_zero_eq_q_zero.symm).app F

private theorem H0TIso_inv_app_of_eq {ε : ℝ} (h : q ε = p ε) (F : Sh k realLine) :
    (singleFunctorCompHomologyFunctorIsoPlus (Sh k realLine) 0).inv.app F ≫
      (H₀).map ((transportedDerivedUnit k h).app ((S₀).obj F)) =
        (transportedUnit k h).app F ≫ (H0TIso k ε).inv.app F := by
  rw [H0TIso_inv_app_eq]
  exact transportedDerivedUnit_homology k h F

private theorem H0TIso_inv_app_zero (F : Sh k realLine) :
    (singleFunctorCompHomologyFunctorIsoPlus (Sh k realLine) 0).inv.app F ≫
      (H₀).map ((T0Iso k).inv.app ((S₀).obj F)) =
        thickeningZeroUnit k F ≫ (H0TIso k 0).inv.app F := by
  have he : (T0Iso k).inv = transportedDerivedUnit k p_zero_eq_q_zero.symm := T0Iso_inv k
  rw [he]
  exact H0TIso_inv_app_of_eq k p_zero_eq_q_zero.symm F

private theorem H0TSectionsIso_inv_aug_zero (F : Sh k realLine) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) :
    (H0TSectionsIso k 0 F U hU).inv ≫ (H0Aug k (le_refl (0 : ℝ)) F).hom.app (op U) =
      F.presheaf.map (homOfLE (le_bandOpen (le_refl (0 : ℝ)) U)).op := by
  let ev : realLine.Sheaf (ModuleCat k) ⥤ ModuleCat k :=
    sheafToPresheaf (Opens.grothendieckTopology realLine) (ModuleCat k) ⋙
      (evaluation _ _).obj (op U)
  have hW : (Opens.map (q 0)).obj U ≤ (Opens.map (p 0)).obj U := by
    rw [p_zero_eq_q_zero]
  have hunit : pullbackUnitRes k (p 0) F hW = ev.map (thickeningZeroUnit k F) := by
    have h' : ∀ (p₀ : D 0 ⟶ realLine) (he : q 0 = p₀)
      (hW' : (Opens.map (q 0)).obj U ≤ (Opens.map p₀).obj U),
        pullbackUnitRes k p₀ F hW' =
          ev.map ((transportedUnit k he).app F) := by
      intro p₀ he hW'
      subst p₀
      have hu : transportedUnit k (rfl : q 0 = q 0) =
          (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) (q 0)).unit := by
        rw [transportedUnit, eqToHom_refl, Functor.whiskerRight_id']
        exact Category.comp_id _
      rw [hu]
      let G := (P (q 0)).obj F
      let V := (Opens.map (q 0)).obj U
      let u := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) (q 0)).unit.app F
      change u.hom.app (op U) ≫ G.presheaf.map ((homOfLE hW' : V ⟶ V).op) =
        u.hom.app (op U)
      have hid : (homOfLE hW' : V ⟶ V).op = 𝟙 (op V) := Subsingleton.elim _ _
      have hmap := (congrArg G.presheaf.map hid).trans (G.presheaf.map_id (op V))
      exact (congrArg (u.hom.app (op U) ≫ ·) hmap).trans (Category.comp_id _)
    exact h' (p 0) p_zero_eq_q_zero.symm hW
  have hres := pullbackUnitRes_map k (p 0) F (tube_le_bandOpen 0 U) hW le_rfl
    (le_bandOpen (le_refl (0 : ℝ)) U)
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id] at hres
  have hr : pullbackUnitRes k (p 0) F (tube_le_bandOpen 0 U) =
      F.presheaf.map (homOfLE (le_bandOpen (le_refl (0 : ℝ)) U)).op ≫
        ev.map (thickeningZeroUnit k F) := hres.trans (congrArg (_ ≫ ·) hunit)
  have he : thickeningZeroUnit k F ≫ (H0TIso k 0).inv.app F ≫
      H0Aug k (le_refl (0 : ℝ)) F = 𝟙 F := by
    let E := (H₀).mapIso ((T0Iso k).app ((S₀).obj F)) ≪≫
      (singleFunctorCompHomologyFunctorIsoPlus _ 0).app F
    have hinv : thickeningZeroUnit k F ≫ (H0TIso k 0).inv.app F = E.inv :=
      (H0TIso_inv_app_zero k F).symm
    have hhom : H0Aug k (le_refl (0 : ℝ)) F = E.hom := by
      rw [H0Aug, aug_zero]
      rfl
    calc
      _ = E.inv ≫ E.hom := by rw [← Category.assoc, hinv, hhom]
      _ = _ := E.inv_hom_id
  change (thickeningSectionsIso k 0 F U hU).inv ≫
    ev.map ((H0TIso k 0).inv.app F) ≫ ev.map (H0Aug k (le_refl (0 : ℝ)) F) = _
  rw [thickeningSectionsIso_inv]
  calc
    _ = (F.presheaf.map (homOfLE (le_bandOpen (le_refl (0 : ℝ)) U)).op ≫
        ev.map (thickeningZeroUnit k F)) ≫
        ev.map ((H0TIso k 0).inv.app F) ≫ ev.map (H0Aug k le_rfl F) :=
      congrArg (· ≫ _) hr
    _ = _ := by
      simp only [Category.assoc, ← ev.map_comp, he, ev.map_id]
      exact Category.comp_id _

/-- Under the section isomorphism, augmentation restricts from the thickened open to the open. -/
@[reassoc]
theorem H0TSectionsIso_hom_aug {ε : ℝ} (hε : 0 ≤ ε)
    (F : realLine.Sheaf (ModuleCat k)) (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    (H0Aug k hε F).hom.app (op U) =
      (H0TSectionsIso k ε F U hU).hom ≫ F.presheaf.map (homOfLE (le_bandOpen hε U)).op := by
  have haug : H0Restr k hε F ≫ H0Aug k (le_refl (0 : ℝ)) F = H0Aug k hε F := by
    let e := (singleFunctorCompHomologyFunctorIsoPlus (Sh k realLine) 0).hom.app F
    let t := (T0Iso k).hom.app ((S₀).obj F)
    let r := (restr k hε).app ((S₀).obj F)
    calc
      _ = (H₀).map r ≫ (H₀).map t ≫ e := by rw [H0Aug, aug_zero]; rfl
      _ = (H₀).map (r ≫ t) ≫ e := (Functor.map_comp_assoc _ _ _ _).symm
      _ = H0Aug k hε F := rfl
  let ev : realLine.Sheaf (ModuleCat k) ⥤ ModuleCat k :=
    sheafToPresheaf (Opens.grothendieckTopology realLine) (ModuleCat k) ⋙
      (evaluation _ _).obj (op U)
  have he : (H0Restr k hε F).hom.app (op U) ≫
      (H0Aug k (le_refl (0 : ℝ)) F).hom.app (op U) = (H0Aug k hε F).hom.app (op U) :=
    ((ev.map_comp _ _).symm.trans (congrArg ev.map haug))
  let E := H0TSectionsIso k ε F U hU
  apply (cancel_epi E.inv).mp
  rw [Iso.inv_hom_id_assoc, ← he, ← Category.assoc]
  rw [H0TSectionsIso_inv_restr k hε F U hU, Category.assoc,
    H0TSectionsIso_inv_aug_zero k F U hU]
  rw [← F.presheaf.map_comp]
  congr 1

end Maps

section IntervalCriteria

open AlternatingDiagram RealConstructible RealStratification

variable {k : Type} [Field k] {m : ℕ} {p : Fin m → ℝ}

local notation "ISh[" k "," hp "," J "]" => Functor.obj (extension k hp) (interval _ J)

private theorem ne_zero_iff_of_interval_sections
    {n : ℕ} {q : Fin n → ℝ} (hp : StrictMono p) (hq : StrictMono q)
    (J : FiniteInterval (2 * m + 1)) (K : FiniteInterval (2 * n + 1))
    {F G : Sh k realLine} (eF : F ≅ ISh[k,hp,J]) (eG : G ≅ ISh[k,hq,K]) (f : F ⟶ G)
    (hf : ∀ (U : Opens realLine), (U : Set ℝ).OrdConnected →
      MeetsClosed (intervalSet p J) U → MeetsClosed (intervalSet q K) U →
      IsIso (f.hom.app (op U))) :
    f ≠ 0 ↔ (intervalSet p J ∩ intervalSet q K).Nonempty := by
  let stalk (y : ℝ) := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) y
  constructor
  · intro hf
    by_contra h
    apply hf
    have hz (y : ℝ) : (stalk y).map f = 0 := by
      by_cases hy : y ∈ intervalSet p J
      · have hg := isZero_stalk_extension_interval k hq (J := K) (fun hy' => h ⟨y, hy, hy'⟩)
        exact (hg.of_iso ((stalk y).mapIso eG)).eq_of_tgt _ _
      · exact ((isZero_stalk_extension_interval k hp (J := J) hy).of_iso
          ((stalk y).mapIso eF)).eq_of_src _ _
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change f.hom.app (op U.unop) s = 0
    apply TopCat.Presheaf.section_ext G U.unop
    intro y hy
    have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop y hy f.hom s
    change (stalk y).map f (F.presheaf.germ U.unop y hy s) = _ at hgerm
    rw [← hgerm, hz]
    change (0 : F.presheaf.stalk y →ₗ[k] G.presheaf.stalk y) _ = G.presheaf.germ U.unop y hy 0
    rw [LinearMap.zero_apply, map_zero]
  · rintro ⟨y, hyJ, hyK⟩ hzero
    let W := coborder (intervalSet p J) ∩ coborder (intervalSet q K)
    have hW : IsOpen W := (isLocallyClosed_intervalSet hp J).isOpen_coborder.inter
      (isLocallyClosed_intervalSet hq K).isOpen_coborder
    have hyW : y ∈ W := ⟨subset_coborder hyJ, subset_coborder hyK⟩
    obtain ⟨a, b, hy, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hW.mem_nhds hyW)
    let U : Opens realLine := ⟨Set.Ioo a b, isOpen_Ioo⟩
    have hU : (U : Set ℝ).OrdConnected := Set.ordConnected_Ioo
    have hcJ : closure (intervalSet p J) ∩ U ⊆ intervalSet p J := by
      intro z hz
      exact mem_coborder_iff_imp.1 (hsub hz.2).1 hz.1
    have hcK : closure (intervalSet q K) ∩ U ⊆ intervalSet q K := by
      intro z hz
      exact mem_coborder_iff_imp.1 (hsub hz.2).2 hz.1
    have hi := hf U hU ⟨hcJ, ⟨y, hy, hyJ⟩⟩ ⟨hcK, ⟨y, hy, hyK⟩⟩
    let ev := sheafToPresheaf (Opens.grothendieckTopology realLine) (ModuleCat k) ⋙
      (evaluation _ _).obj (op U)
    change IsIso (ev.map f) at hi
    rw [hzero] at hi
    have he0 : ev.map (0 : F ⟶ G) = 0 := ev.map_zero F G
    have hi0 : IsIso (0 : ev.obj F ⟶ ev.obj G) := he0 ▸ hi
    have hs : IsZero (G.presheaf.obj (op U)) :=
      ((isIsoZero_iff_source_target_isZero _ _).1 hi0).2
    have he := (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).mapIso eG
    have hz := hs.of_iso he.symm
    have := isIso_germ_extension_interval k hq K hU hcK hy hyK
    have hz' := hz.of_iso (asIso ((ISh[k,hq,K]).presheaf.germ U y hy)).symm
    obtain ⟨ey⟩ := nonempty_stalk_extension_interval_iso k hq hyK
    exact zero_ne_one ((ModuleCat.isZero_iff_subsingleton.1 (hz'.of_iso ey.symm)).elim
      (0 : k) (1 : k))

private theorem meetsClosed_thickening {ε : ℝ} (hε : 0 ≤ ε)
    (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected) :
    MeetsClosed (outSet0 ε (intervalSet p J)) U ↔
      MeetsClosed (intervalSet p J) (bandOpen ε U) :=
  meetsClosed_outSet0_iff hε (ordConnected_intervalSet hp J)
    (isLocallyClosed_intervalSet hp J) hU

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

/-- The degree-zero radius map of an interval sheaf is nonzero exactly when its
degree-zero output intervals intersect. -/
theorem H0Restr_interval_ne_zero_iff {δ ε : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ ε)
    (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    H0Restr k h (ISh[k,hp,J]) ≠ 0 ↔
      (outSet0 ε (intervalSet p J) ∩ outSet0 δ (intervalSet p J)).Nonempty := by
  have hε := hδ.trans h
  rcases (outSet0 ε (intervalSet p J)).eq_empty_or_nonempty with he | he
  · have hz := isZero_H0T_interval (k := k) hp J hε he
    simp [he, hz.eq_of_src (H0Restr k h (ISh[k,hp,J])) 0]
  rcases (outSet0 δ (intervalSet p J)).eq_empty_or_nonempty with hd | hd
  · have hz := isZero_H0T_interval (k := k) hp J hδ hd
    simp [hd, hz.eq_of_tgt (H0Restr k h (ISh[k,hp,J])) 0]
  obtain ⟨A, hA, ⟨eA⟩⟩ := exists_intervalSheaf_H0T (k := k) hp J hε he
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_intervalSheaf_H0T (k := k) hp J hδ hd
  rw [← hA, ← hB]
  refine ne_zero_iff_of_interval_sections (strictMono_sortedBreakpoints (bandBreakpoints p ε))
    (strictMono_sortedBreakpoints (bandBreakpoints p δ)) A B eA eB (H0Restr k h (ISh[k,hp,J])) ?_
  intro U hU ha hb
  rw [hA] at ha
  rw [hB] at hb
  have ha' := (meetsClosed_thickening hε hp J hU).1 ha
  have hb' := (meetsClosed_thickening hδ hp J hU).1 hb
  obtain ⟨x, hx, hxI⟩ := hb'.2
  have hr := isIso_map_extension_interval k hp J (bandOpen_mono h U)
    (ordConnected_bandOpen δ hU) (ordConnected_bandOpen ε hU) hb'.1 ha'.1 hx hxI
  have hcomp : IsIso ((H0Restr k h (ISh[k,hp,J])).hom.app (op U) ≫
      (H0TSectionsIso k δ (ISh[k,hp,J]) U hU).hom) := by
    rw [H0TSectionsIso_hom_restr k hδ h]
    exact IsIso.comp_isIso' (Iso.isIso_hom _) hr
  exact IsIso.of_isIso_comp_right _ (H0TSectionsIso k δ (ISh[k,hp,J]) U hU).hom

/-- The degree-zero augmentation of an interval sheaf is nonzero exactly when the
degree-zero output intersects the input interval. -/
theorem H0Aug_interval_ne_zero_iff {ε : ℝ} (hε : 0 ≤ ε)
    (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    H0Aug k hε (ISh[k,hp,J]) ≠ 0 ↔
      (outSet0 ε (intervalSet p J) ∩ intervalSet p J).Nonempty := by
  rw [H0Aug_ne_zero_iff, H0Restr_interval_ne_zero_iff le_rfl hε hp J, outSet0_zero]

end IntervalCriteria

end TDA.Sheaf.BandConvolution
