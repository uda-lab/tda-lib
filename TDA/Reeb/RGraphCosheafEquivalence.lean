import TDA.Reeb.RGraphRefinement
import TDA.Reeb.ConstructibleRepresentation

/-!
# Finite ℝ-graphs and constructible cosheaves

The interval path-component functor, restricted to graph objects, is an equivalence onto the
category of constructible interval cosheaves (de Silva, Munch and Patel, *Categorified Reeb
Graphs*, Theorem 3.22).

## Categories

* Source: `RGraph.RGraphCat`, the full subcategory of the real slice `Over (TopCat.of ℝ)` on
  objects isomorphic to a realization `toOver T D` of finite data. Its morphisms are all continuous
  height-preserving maps. It lives in universe `0`.
* Target: `ConstructibleCosheafCat.{u}`, the full subcategory of interval precosheaves
  `OpenInterval ⥤ Type u` on `IsConstructibleCosheaf`: the interval cosheaf condition
  `IsIntervalCosheaf.{0}` for covers indexed in universe `0`, and the **existence** of a finite
  critical witness `S` with `S.IsConstructibleAt F`. The witness is not part of the object, and a
  larger witness is allowed. The value at `⊥` is empty by the cosheaf condition; the zero cosheaf
  is an object, with a one-level witness and empty data.

The target property and category are defined at every value universe `u`. The functor, its inverse
and the equivalence are at value universe `0`, matching `RGraphCat`; the equivalence is not stated
at other value universes.

## The functor

`intervalComponentsOver` is `ReebQuotient.componentFunctorOver ℝ` followed by precomposition with
`toOpensFunctor`: an object `A` goes to `intervalComponents (overBaseMap A)` and a slice morphism
`f` to `componentNatTrans f.left.hom` on intervals (both by `rfl`). `RGraph.cosheafFunctor` is its
lift from `RGraphCat`, the source's `𝒞''`. It lands in `ConstructibleCosheafCat` because a
presentation `A ≅ toOver T D` carries the cosheaf of `A` to `D.toCosheaf T`, which is a
constructible interval cosheaf at `T`, and both conditions are invariant under natural isomorphism.

## Proof

1. **Finite level.** For finite data `D`, `D'` over explicit levels `S` and a finite map `φ`,
   `realizeNatTrans S φ` is the component transformation of the realized map. On labels it acts
   by `φ`: `λV (φ.v i v)` and `λE (φ.e e y)` (`realizeNatTrans_vertexLabel`,
   `realizeNatTrans_edgeLabel`). Hence its extracted finite map is
   `fromExtractHom ≫ φ ≫ toExtractHom` (`natTransEquivDiagramHom_realizeNatTrans`). The
   classification `natTransEquivDiagramHom` and the round trip `extract_toCosheaf_iso` then make
   `φ ↦ realizeNatTrans S φ` a bijection (`realizeNatTransEquiv`); realization followed by interval
   components is fully faithful over a common `S` (`realizationCosheafFullyFaithful`).
2. **Full faithfulness.** Graph objects `A`, `B` have presentations over one common list `T`
   (`exists_common_presentation`). The actual component map of a slice morphism `g` is the realized
   transformation of its classified finite map `homEquivOfIso iA iB g`, conjugated by the images of
   the presentations (`intervalComponentsOver_map_eq`). So `cosheafFunctor.map` is a composite of
   bijections (`cosheafHomEquiv_apply`) and is bijective on all continuous height-preserving maps
   between graph objects (`cosheafFunctor_map_bijective`). The comparison formulas
   `cosheafFunctor_map_conj` and `natTransEquivDiagramHom_cosheafFunctor_map` state the morphism
   comparison for consumers.
3. **Essential surjectivity.** For `F` with a witness `S`, the graph object of the extracted data
   `(toRGraph S).obj (S.extract F _)` goes to `(S.extract F _).toCosheaf S` by definition, and the
   reconstruction `realizeExtractIso` identifies that cosheaf with `F` (`cosheafFunctorObjIso`).
4. **Packaging.** `ofCosheafFunctor` sends `G` to the graph object extracted at a witness chosen by
   `Classical.choose`, and a transformation to the unique graph map whose image is the
   transformation conjugated by the reconstructions (`cosheafFunctor_map_ofCosheafFunctor_map`).
   `cosheafEquivalence` is `Equivalence.mk cosheafFunctor ofCosheafFunctor ofCosheafUnitIso
   ofCosheafCounitIso`: its counit is the reconstruction `ofCosheafCounitIso`, and its unit is the
   adjointification of `ofCosheafUnitIso`, not `ofCosheafUnitIso` itself. Graph objects extracted at
   two witnesses are isomorphic by a map whose image is the composite of the two reconstructions
   (`ofCosheafIso`, `cosheafFunctor_map_ofCosheafIso`), so the inverse at any witness is the
   extracted graph object up to that isomorphism (`ofCosheafFunctorObjIso`). Any equivalence whose
   functor is isomorphic to `cosheafFunctor` has an inverse naturally isomorphic to
   `ofCosheafFunctor` (`inverseIsoOfFunctorIso`). No definitional equality of presentations,
   witnesses or inverse choices is claimed.

No compactness, Hausdorff or local path-connectedness hypothesis appears: graph realizations have
discrete pieces. Not claimed: an equivalence on all ℝ-spaces, on all constructible ℝ-spaces or on
Reeb-ordering objects. The fixture `negative_boundary` of
`TDA.Reeb.RGraphCosheafEquivalenceExamples` shows why the source category is restricted.
-/

open Set Topology CategoryTheory

universe u

namespace TDA.Reeb

noncomputable section

open OpenInterval

/-! ### Constructible cosheaves as a full subcategory -/

/-- A constructible interval cosheaf (DMP Definition 3.9 with the nonempty-source correction):
the cosheaf condition for covers indexed in universe `0` and some finite critical witness. The
witness is a property, not data. -/
structure IsConstructibleCosheaf (F : OpenInterval ⥤ Type u) : Prop where
  /-- The interval cosheaf condition. -/
  isIntervalCosheaf : IsIntervalCosheaf.{0} F
  /-- Existence of a finite critical witness. -/
  exists_isConstructibleAt : ∃ (n : ℕ) (S : CriticalValues n), S.IsConstructibleAt F

/-- Constructible interval cosheaves: the full subcategory of interval precosheaves on
`IsConstructibleCosheaf`. Morphisms are all natural transformations. -/
abbrev ConstructibleCosheafCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory (IsConstructibleCosheaf.{u})

namespace IsConstructibleCosheaf

variable {F G : OpenInterval ⥤ Type u}

/-- A witness and the cosheaf condition give an object. -/
theorem of_isConstructibleAt {n : ℕ} {S : CriticalValues n} (hF : S.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) : IsConstructibleCosheaf F :=
  ⟨hFc, n, S, hF⟩

/-- Invariance under natural isomorphism. -/
theorem of_iso (e : F ≅ G) (hF : IsConstructibleCosheaf F) : IsConstructibleCosheaf G := by
  obtain ⟨hc, n, S, hS⟩ := hF
  exact ⟨IsIntervalCosheaf.of_iso e hc, n, S, CriticalValues.IsConstructibleAt.of_iso e hS⟩

instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleCosheaf.{u}) where
  of_iso e h := of_iso e h

end IsConstructibleCosheaf

/-! ### Interval components on the real slice -/

/-- Interval components on the real slice: `ReebQuotient.componentFunctorOver ℝ` followed by
precomposition with `toOpensFunctor`. -/
def intervalComponentsOver : Over (TopCat.of ℝ) ⥤ (OpenInterval ⥤ Type) :=
  ReebQuotient.componentFunctorOver ℝ ⋙ (Functor.whiskeringLeft _ _ _).obj toOpensFunctor

/-- On objects: the actual `intervalComponents` of the structure map. -/
theorem intervalComponentsOver_obj (A : Over (TopCat.of ℝ)) :
    intervalComponentsOver.obj A = intervalComponents (overBaseMap A) := rfl

/-- On morphisms: `componentNatTrans` of the underlying map, precomposed with `toOpensFunctor`. -/
theorem intervalComponentsOver_map {A B : Over (TopCat.of ℝ)} (f : A ⟶ B) :
    intervalComponentsOver.map f =
      Functor.whiskerLeft toOpensFunctor (componentNatTrans f.left.hom (overBaseMap_comm f)) :=
  rfl

/-- Pointwise: a component class goes to the class of the image point. -/
theorem intervalComponentsOver_map_app_mk {A B : Over (TopCat.of ℝ)} (f : A ⟶ B)
    (I : OpenInterval) (x : {x : A.left // overBaseMap A x ∈ toOpens I}) :
    (intervalComponentsOver.map f).app I (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (⟨f.left.hom x.1, by rw [overBaseMap_comm]; exact x.2⟩ :
        {y : B.left // overBaseMap B y ∈ toOpens I}) :=
  rfl

/-- On a realization of finite data it is the cosheaf `D.toCosheaf S` of the data. -/
theorem intervalComponentsOver_obj_toOver {n : ℕ} (S : CriticalValues n)
    (D : FiniteReebData.{0} n) : intervalComponentsOver.obj (RGraph.toOver S D) = D.toCosheaf S :=
  rfl

/-! ### Finite level: realized maps on labels -/

namespace FiniteReebData

open CylinderPresentation

variable {n : ℕ} (S : CriticalValues n) {D D' : FiniteReebData.{u} n}

/-- The transformation of component cosheaves induced by a finite map: `componentNatTrans` of
the realized map, precomposed with `toOpensFunctor`. -/
def realizeNatTrans (φ : D.Hom D') : D.toCosheaf S ⟶ D'.toCosheaf S :=
  Functor.whiskerLeft toOpensFunctor (componentNatTrans (realizeHom S φ) (height_realizeHom S φ))

/-- On a vertex label the realized transformation acts by the vertex component. -/
theorem realizeNatTrans_vertexLabel (φ : D.Hom D') (i : Fin (n + 1)) (v : D.V i) :
    (realizeNatTrans S φ).app (S.J i) (D.vertexLabel S i v) = D'.vertexLabel S i (φ.v i v) :=
  rfl

/-- On an edge label the realized transformation acts by the edge component. -/
theorem realizeNatTrans_edgeLabel (φ : D.Hom D') (e : Fin n) (y : D.E e) :
    (realizeNatTrans S φ).app (S.K e) (D.edgeLabel S e y) = D'.edgeLabel S e (φ.e e y) := by
  rw [D.edgeLabel_apply S e (S.gapMidpoint e), D'.edgeLabel_apply S e (S.gapMidpoint e)]
  rfl

/-- The extracted finite map of a realized transformation is `φ` conjugated by the labels. -/
theorem natTransEquivDiagramHom_realizeNatTrans (φ : D.Hom D') :
    S.natTransEquivDiagramHom (D.toCosheaf_isConstructibleAt S) (D.toCosheaf_isIntervalCosheaf S)
        (D'.toCosheaf_isConstructibleAt S) (D'.toCosheaf_isIntervalCosheaf S)
        (realizeNatTrans S φ) =
      (D.fromExtractHom S).comp (φ.comp (D'.toExtractHom S)) := by
  apply Hom.ext
  · funext i x
    obtain ⟨v, rfl⟩ := (D.vertexLabel S i).surjective x
    show (realizeNatTrans S φ).app (S.J i) (D.vertexLabel S i v) =
      D'.vertexLabel S i (φ.v i ((D.fromExtractHom S).v i (D.vertexLabel S i v)))
    rw [realizeNatTrans_vertexLabel, fromExtractHom_v_apply, Equiv.symm_apply_apply]
  · funext e x
    obtain ⟨y, rfl⟩ := (D.edgeLabel S e).surjective x
    show (realizeNatTrans S φ).app (S.K e) (D.edgeLabel S e y) =
      D'.edgeLabel S e (φ.e e ((D.fromExtractHom S).e e (D.edgeLabel S e y)))
    rw [realizeNatTrans_edgeLabel, fromExtractHom_e_apply, Equiv.symm_apply_apply]

variable (D D') in
/-- **Finite full faithfulness**: realized transformations are exactly the transformations of
the component cosheaves of finite data over a common `S`. -/
def realizeNatTransEquiv : D.Hom D' ≃ (D.toCosheaf S ⟶ D'.toCosheaf S) where
  toFun := realizeNatTrans S
  invFun α := (D.toExtractHom S).comp
    ((S.natTransEquivDiagramHom (D.toCosheaf_isConstructibleAt S)
      (D.toCosheaf_isIntervalCosheaf S) (D'.toCosheaf_isConstructibleAt S)
      (D'.toCosheaf_isIntervalCosheaf S) α).comp (D'.fromExtractHom S))
  left_inv φ := by
    show (D.toExtractHom S).comp ((S.natTransEquivDiagramHom _ _ _ _
      (realizeNatTrans S φ)).comp (D'.fromExtractHom S)) = φ
    rw [natTransEquivDiagramHom_realizeNatTrans]
    show ((D.toExtractHom S).comp (D.fromExtractHom S)).comp
      (φ.comp ((D'.toExtractHom S).comp (D'.fromExtractHom S))) = φ
    rw [(D.extract_toCosheaf_iso S).1, (D'.extract_toCosheaf_iso S).1]
    rfl
  right_inv α := by
    apply (S.natTransEquivDiagramHom (D.toCosheaf_isConstructibleAt S)
      (D.toCosheaf_isIntervalCosheaf S) (D'.toCosheaf_isConstructibleAt S)
      (D'.toCosheaf_isIntervalCosheaf S)).injective
    rw [natTransEquivDiagramHom_realizeNatTrans]
    show ((D.fromExtractHom S).comp (D.toExtractHom S)).comp
      ((S.natTransEquivDiagramHom _ _ _ _ α).comp
        ((D'.fromExtractHom S).comp (D'.toExtractHom S))) = _
    rw [(D.extract_toCosheaf_iso S).2, (D'.extract_toCosheaf_iso S).2]
    rfl

theorem realizeNatTransEquiv_apply (φ : D.Hom D') :
    realizeNatTransEquiv S D D' φ = realizeNatTrans S φ := rfl

end FiniteReebData

namespace RGraph

open FiniteReebData

/-- Realization followed by interval components acts by `realizeNatTrans`. -/
theorem realizationFunctor_comp_intervalComponentsOver_map {n : ℕ} (S : CriticalValues n)
    {D D' : FiniteReebData.{0} n} (φ : D ⟶ D') :
    (realizationFunctor S ⋙ intervalComponentsOver).map φ = realizeNatTrans S φ :=
  rfl

/-- Realization followed by interval components is fully faithful over a common `S`. -/
def realizationCosheafFullyFaithful {n : ℕ} (S : CriticalValues n) :
    (realizationFunctor S ⋙ intervalComponentsOver).FullyFaithful where
  preimage {D D'} α := (realizeNatTransEquiv S D D').symm α
  map_preimage {D D'} α := (realizeNatTransEquiv S D D').apply_symm_apply α
  preimage_map {D D'} φ := (realizeNatTransEquiv S D D').symm_apply_apply φ

/-! ### The functor on graph objects -/

/-- The interval components of a graph object form a constructible cosheaf. -/
theorem isConstructibleCosheaf_intervalComponentsOver (A : RGraphCat) :
    IsConstructibleCosheaf (intervalComponentsOver.obj A.obj) := by
  obtain ⟨m, T, D, ⟨i⟩⟩ := A.property
  exact IsConstructibleCosheaf.of_iso (intervalComponentsOver.mapIso i).symm
    (IsConstructibleCosheaf.of_isConstructibleAt (F := intervalComponentsOver.obj (toOver T D))
      (D.toCosheaf_isConstructibleAt T) (D.toCosheaf_isIntervalCosheaf T))

/-- **The component functor on graph objects** (DMP `𝒞''`, Theorem 3.22). -/
def cosheafFunctor : RGraphCat ⥤ ConstructibleCosheafCat.{0} :=
  ObjectProperty.lift IsConstructibleCosheaf.{0} (IsRGraph.ι ⋙ intervalComponentsOver)
    isConstructibleCosheaf_intervalComponentsOver

/-- Composed with the inclusion it is interval components on the underlying slice objects. -/
theorem cosheafFunctor_comp_ι :
    cosheafFunctor ⋙ ObjectProperty.ι IsConstructibleCosheaf.{0} =
      IsRGraph.ι ⋙ intervalComponentsOver :=
  rfl

/-- Object formula. -/
theorem cosheafFunctor_obj_obj (A : RGraphCat) :
    (cosheafFunctor.obj A).obj = intervalComponents (overBaseMap A.obj) := rfl

/-- Morphism formula: `componentNatTrans` of the height-preserving map, precomposed with
`toOpensFunctor`. -/
theorem cosheafFunctor_map_hom {A B : RGraphCat} (f : A ⟶ B) :
    (cosheafFunctor.map f).hom =
      Functor.whiskerLeft toOpensFunctor
        (componentNatTrans f.hom.left.hom (overBaseMap_comm f.hom)) :=
  rfl

section comparison

variable {A B : RGraphCat} {m : ℕ} {T : CriticalValues m} {DA DB : FiniteReebData.{0} m}

/-- Over common presentations, the component map of a slice morphism is the realized
transformation of its classified finite map, conjugated by the presentations. -/
theorem intervalComponentsOver_map_eq {X Y : Over (TopCat.of ℝ)} (iX : X ≅ toOver T DA)
    (iY : Y ≅ toOver T DB) (g : X ⟶ Y) :
    intervalComponentsOver.map g =
      Iso.homCongr (intervalComponentsOver.mapIso iX).symm (intervalComponentsOver.mapIso iY).symm
        (realizeNatTrans T (homEquivOfIso iX iY g)) := by
  change _ = intervalComponentsOver.map iX.hom ≫
    intervalComponentsOver.map ((realizationFunctor T).map (homEquivOfIso iX iY g)) ≫
      intervalComponentsOver.map iY.inv
  rw [homEquivOfIso_apply, ← Functor.map_comp, ← Functor.map_comp]
  simp

/-- **Morphism comparison over a common presentation.** -/
theorem cosheafFunctor_map_conj (iA : A.obj ≅ toOver T DA) (iB : B.obj ≅ toOver T DB)
    (f : A ⟶ B) :
    intervalComponentsOver.map iA.inv ≫ (cosheafFunctor.map f).hom ≫
        intervalComponentsOver.map iB.hom =
      realizeNatTrans T (homEquivOfIso iA iB f.hom) := by
  change intervalComponentsOver.map iA.inv ≫ intervalComponentsOver.map f.hom ≫
      intervalComponentsOver.map iB.hom =
    intervalComponentsOver.map ((realizationFunctor T).map (homEquivOfIso iA iB f.hom))
  rw [homEquivOfIso_apply, Functor.map_comp, Functor.map_comp]

/-- **Morphism comparison with the finite incidence data**: on extracted data the conjugated
component transformation is the classified finite map, conjugated by the labels. -/
theorem natTransEquivDiagramHom_cosheafFunctor_map (iA : A.obj ≅ toOver T DA)
    (iB : B.obj ≅ toOver T DB) (f : A ⟶ B) :
    T.natTransEquivDiagramHom (DA.toCosheaf_isConstructibleAt T)
        (DA.toCosheaf_isIntervalCosheaf T) (DB.toCosheaf_isConstructibleAt T)
        (DB.toCosheaf_isIntervalCosheaf T)
        (intervalComponentsOver.map iA.inv ≫ (cosheafFunctor.map f).hom ≫
          intervalComponentsOver.map iB.hom) =
      (DA.fromExtractHom T).comp
        (FiniteReebData.Hom.comp (homEquivOfIso iA iB f.hom) (DB.toExtractHom T)) := by
  exact (congrArg (T.natTransEquivDiagramHom (DA.toCosheaf_isConstructibleAt T)
      (DA.toCosheaf_isIntervalCosheaf T) (DB.toCosheaf_isConstructibleAt T)
      (DB.toCosheaf_isIntervalCosheaf T)) (cosheafFunctor_map_conj iA iB f)).trans
    (natTransEquivDiagramHom_realizeNatTrans T _)

/-- Pointwise vertex form of the comparison. -/
theorem cosheafFunctor_map_conj_vertexLabel (iA : A.obj ≅ toOver T DA)
    (iB : B.obj ≅ toOver T DB) (f : A ⟶ B) (i : Fin (m + 1)) (v : DA.V i) :
    (intervalComponentsOver.map iA.inv ≫ (cosheafFunctor.map f).hom ≫
        intervalComponentsOver.map iB.hom).app (T.J i) (DA.vertexLabel T i v) =
      DB.vertexLabel T i ((homEquivOfIso iA iB f.hom).v i v) := by
  rw [cosheafFunctor_map_conj]
  exact realizeNatTrans_vertexLabel T _ i v

/-- Pointwise edge form of the comparison. -/
theorem cosheafFunctor_map_conj_edgeLabel (iA : A.obj ≅ toOver T DA)
    (iB : B.obj ≅ toOver T DB) (f : A ⟶ B) (e : Fin m) (y : DA.E e) :
    (intervalComponentsOver.map iA.inv ≫ (cosheafFunctor.map f).hom ≫
        intervalComponentsOver.map iB.hom).app (T.K e) (DA.edgeLabel T e y) =
      DB.edgeLabel T e ((homEquivOfIso iA iB f.hom).e e y) := by
  rw [cosheafFunctor_map_conj]
  exact realizeNatTrans_edgeLabel T _ e y

/-- The Hom bijection of the main theorem over chosen common presentations: full subcategory,
the classification `homEquivOfIso`, finite full faithfulness, conjugation by the presentations,
full subcategory. -/
def cosheafHomEquiv (iA : A.obj ≅ toOver T DA) (iB : B.obj ≅ toOver T DB) :
    (A ⟶ B) ≃ (cosheafFunctor.obj A ⟶ cosheafFunctor.obj B) :=
  IsRGraph.fullyFaithfulι.homEquiv.trans <| (homEquivOfIso iA iB).trans <|
    (realizeNatTransEquiv T DA DB).trans <|
      (Iso.homCongr (intervalComponentsOver.mapIso iA).symm
        (intervalComponentsOver.mapIso iB).symm).trans
        ((ObjectProperty.fullyFaithfulι IsConstructibleCosheaf.{0}).homEquiv
          (X := cosheafFunctor.obj A) (Y := cosheafFunctor.obj B)).symm

/-- The bijection is the actual functor map. -/
theorem cosheafHomEquiv_apply (iA : A.obj ≅ toOver T DA) (iB : B.obj ≅ toOver T DB)
    (f : A ⟶ B) : cosheafHomEquiv iA iB f = cosheafFunctor.map f := by
  apply ObjectProperty.hom_ext
  exact (intervalComponentsOver_map_eq iA iB f.hom).symm

end comparison

/-- **Full faithfulness, Hom-set form**: the actual functor map is bijective. -/
theorem cosheafFunctor_map_bijective (A B : RGraphCat) :
    Function.Bijective
      (cosheafFunctor.map : (A ⟶ B) → (cosheafFunctor.obj A ⟶ cosheafFunctor.obj B)) := by
  obtain ⟨m, T, DA, DB, ⟨iA⟩, ⟨iB⟩⟩ := exists_common_presentation A B
  have key : (cosheafFunctor.map : (A ⟶ B) → _) = cosheafHomEquiv iA iB :=
    funext fun f => (cosheafHomEquiv_apply iA iB f).symm
  rw [key]
  exact (cosheafHomEquiv iA iB).bijective

instance cosheafFunctor_full : cosheafFunctor.Full :=
  ⟨fun {A B} => (cosheafFunctor_map_bijective A B).2⟩

instance cosheafFunctor_faithful : cosheafFunctor.Faithful :=
  ⟨fun {A B} => (cosheafFunctor_map_bijective A B).1⟩

/-- **Full faithfulness.** -/
def cosheafFullyFaithful : cosheafFunctor.FullyFaithful := .ofFullyFaithful _

/-! ### Essential surjectivity -/

/-- The graph object of the extracted data of `F` at a witness `S`. -/
abbrev ofCosheaf {n : ℕ} (S : CriticalValues n) {F : OpenInterval ⥤ Type}
    (hF : S.IsConstructibleAt F) : RGraphCat :=
  (toRGraph S).obj (S.extract F hF.finite)

/-- **Essential surjectivity** (DMP Theorem 3.22, proof part (ii), which concludes by
Corollary 3.14): the reconstruction `realizeExtractIso`, which is the uniqueness half of DMP
Proposition 3.18 applied to the extracted data. -/
def cosheafFunctorObjIso {n : ℕ} {S : CriticalValues n} {F : OpenInterval ⥤ Type}
    (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F) (hP : IsConstructibleCosheaf F) :
    cosheafFunctor.obj (ofCosheaf S hF) ≅ ⟨F, hP⟩ :=
  ObjectProperty.isoMk _ (CriticalValues.realizeExtractIso hF hFc)

theorem cosheafFunctorObjIso_hom {n : ℕ} {S : CriticalValues n} {F : OpenInterval ⥤ Type}
    (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F) (hP : IsConstructibleCosheaf F) :
    (cosheafFunctorObjIso hF hFc hP).hom.hom = (CriticalValues.realizeExtractIso hF hFc).hom :=
  rfl

instance cosheafFunctor_essSurj : cosheafFunctor.EssSurj where
  mem_essImage G := by
    obtain ⟨hc, n, S, hS⟩ := G.property
    exact ⟨ofCosheaf S hS, ⟨cosheafFunctorObjIso hS hc G.property⟩⟩

instance cosheafFunctor_isEquivalence : cosheafFunctor.IsEquivalence where

/-- Graph objects extracted at two witnesses are isomorphic. -/
def ofCosheafIso {F : OpenInterval ⥤ Type} {n n' : ℕ} {S : CriticalValues n}
    {S' : CriticalValues n'} (hS : S.IsConstructibleAt F) (hS' : S'.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) : ofCosheaf S hS ≅ ofCosheaf S' hS' :=
  cosheafFullyFaithful.preimageIso
    (cosheafFunctorObjIso hS hFc (.of_isConstructibleAt hS hFc) ≪≫
      (cosheafFunctorObjIso hS' hFc (.of_isConstructibleAt hS hFc)).symm)

/-- The witness comparison is sent to the composite of the two reconstructions. -/
theorem cosheafFunctor_map_ofCosheafIso {F : OpenInterval ⥤ Type} {n n' : ℕ}
    {S : CriticalValues n} {S' : CriticalValues n'} (hS : S.IsConstructibleAt F)
    (hS' : S'.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F) :
    (cosheafFunctor.map (ofCosheafIso hS hS' hFc).hom).hom =
      (CriticalValues.realizeExtractIso hS hFc).hom ≫
        (CriticalValues.realizeExtractIso hS' hFc).inv := by
  rw [ofCosheafIso, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
  rfl

/-! ### The inverse functor -/

/-- The length of a chosen critical witness (choice). -/
def witnessLength (G : ConstructibleCosheafCat.{0}) : ℕ :=
  G.property.exists_isConstructibleAt.choose

/-- A chosen critical witness (choice); only its isomorphism class matters (`ofCosheafIso`). -/
def witness (G : ConstructibleCosheafCat.{0}) : CriticalValues (witnessLength G) :=
  G.property.exists_isConstructibleAt.choose_spec.choose

theorem isConstructibleAt_witness (G : ConstructibleCosheafCat.{0}) :
    (witness G).IsConstructibleAt G.obj :=
  G.property.exists_isConstructibleAt.choose_spec.choose_spec

/-- The reconstruction at the chosen witness. -/
def ofCosheafObjIso (G : ConstructibleCosheafCat.{0}) :
    cosheafFunctor.obj (ofCosheaf (witness G) (isConstructibleAt_witness G)) ≅ G :=
  cosheafFunctorObjIso (isConstructibleAt_witness G) G.property.isIntervalCosheaf G.property

/-- **The inverse direction.** A constructible cosheaf goes to the graph object of its extracted
data at the chosen witness; a transformation goes to the unique graph map whose component
transformation is the given one conjugated by the reconstructions. It is `@[reducible]`, like
`realizationFunctor`, so that `ofCosheafFunctor.obj G` and the extracted graph object unify at
reducible transparency in the unit and counit. -/
@[reducible] def ofCosheafFunctor : ConstructibleCosheafCat.{0} ⥤ RGraphCat where
  obj G := ofCosheaf (witness G) (isConstructibleAt_witness G)
  map {G G'} α :=
    cosheafFullyFaithful.preimage ((ofCosheafObjIso G).hom ≫ α ≫ (ofCosheafObjIso G').inv)
  map_id G := cosheafFullyFaithful.map_injective (by simp)
  map_comp α β := cosheafFullyFaithful.map_injective (by simp)

/-- Object formula of the inverse direction. -/
theorem ofCosheafFunctor_obj (G : ConstructibleCosheafCat.{0}) :
    ofCosheafFunctor.obj G = ofCosheaf (witness G) (isConstructibleAt_witness G) := rfl

/-- Morphism formula of the inverse direction. -/
theorem cosheafFunctor_map_ofCosheafFunctor_map {G G' : ConstructibleCosheafCat.{0}}
    (α : G ⟶ G') :
    cosheafFunctor.map (ofCosheafFunctor.map α) =
      (ofCosheafObjIso G).hom ≫ α ≫ (ofCosheafObjIso G').inv :=
  cosheafFullyFaithful.map_preimage _

/-- The counit: reconstruction at the chosen witness. -/
def ofCosheafCounitIso : ofCosheafFunctor ⋙ cosheafFunctor ≅ 𝟭 ConstructibleCosheafCat.{0} :=
  NatIso.ofComponents ofCosheafObjIso fun α => by
    rw [Functor.comp_map, cosheafFunctor_map_ofCosheafFunctor_map, Functor.id_map,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The unit supplied to `Equivalence.mk`; `cosheafEquivalence.unitIso` is its adjointification.
-/
def ofCosheafUnitIso : 𝟭 RGraphCat ≅ cosheafFunctor ⋙ ofCosheafFunctor :=
  NatIso.ofComponents
    (fun A => cosheafFullyFaithful.preimageIso (ofCosheafObjIso (cosheafFunctor.obj A)).symm)
    fun f => cosheafFullyFaithful.map_injective (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.preimageIso_hom,
        Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage, Functor.comp_map,
        cosheafFunctor_map_ofCosheafFunctor_map, Functor.id_map]
      simp)

/-! ### The equivalence -/

/-- **Graph–constructible-cosheaf equivalence** (DMP Theorem 3.22), at value universe `0`.
`Equivalence.mk` keeps both functors and the counit and adjointifies the unit. -/
def cosheafEquivalence : RGraphCat ≌ ConstructibleCosheafCat.{0} :=
  CategoryTheory.Equivalence.mk cosheafFunctor ofCosheafFunctor ofCosheafUnitIso
    ofCosheafCounitIso

theorem cosheafEquivalence_functor : cosheafEquivalence.functor = cosheafFunctor := rfl

theorem cosheafEquivalence_inverse : cosheafEquivalence.inverse = ofCosheafFunctor := rfl

theorem cosheafEquivalence_counitIso : cosheafEquivalence.counitIso = ofCosheafCounitIso := rfl

/-- At any witness, the inverse is the extracted graph object, up to the canonical isomorphism. -/
def ofCosheafFunctorObjIso (G : ConstructibleCosheafCat.{0}) {n : ℕ} {S : CriticalValues n}
    (hS : S.IsConstructibleAt G.obj) : ofCosheafFunctor.obj G ≅ ofCosheaf S hS :=
  ofCosheafIso (isConstructibleAt_witness G) hS G.property.isIntervalCosheaf

/-- Inverse choices: any equivalence whose functor is isomorphic to `cosheafFunctor` has inverse
naturally isomorphic to `ofCosheafFunctor`. -/
def inverseIsoOfFunctorIso (e : RGraphCat ≌ ConstructibleCosheafCat.{0})
    (i : e.functor ≅ cosheafFunctor) : e.inverse ≅ ofCosheafFunctor :=
  Iso.isoInverseOfIsoFunctor (G' := cosheafEquivalence) i

end RGraph

end

end TDA.Reeb
