import TDA.Reeb.RGraphCosheafEquivalence
import TDA.Reeb.RGraphExamples
import TDA.Reeb.ConstructibleCosheafExamples
import TDA.Reeb.ConstructibleRepresentationExamples
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Fixtures for the graph–constructible-cosheaf equivalence

Fixtures for `TDA.Reeb.RGraph.cosheafEquivalence` on actual graph objects and actual component
transformations:

* the edge swap of two parallel edges over `0 < 1` is a non-identity involutive graph
  automorphism; its image is the identity on stars and exchanges the edge labels on the gap, so it
  is a non-identity automorphism of the cosheaf;
* collapsing two parallel edges onto one edge merges the two gap labels, so its image is not an
  isomorphism;
* the single edge over `0 < 1` and over `0 < 1/2 < 1` give isomorphic cosheaves through the
  refinement isomorphism `refineIso`; the cosheaf is constructible at both lists, and the graph
  objects extracted at the two witnesses are isomorphic through the two reconstructions;
* two points at one level: two components over `ℝ` and exactly four endomorphisms of the cosheaf;
* the empty graph is sent to the zero cosheaf `Examples.Constructible.zeroCosheaf`, which is an
  object through its cosheaf condition and its constructibility at one level, and is initial; the
  inverse direction sends the zero cosheaf to an initial graph object with empty carrier;
* negative boundary: `[0, 1]` at constant height `0`, isomorphic over `ℝ` to the realization of a
  one-piece presentation, and the point, the graph object of the one-vertex data
  `Examples.ConstructibleRepresentation.pt0`, have isomorphic constructible component cosheaves,
  but they are not isomorphic over `ℝ`, and `[0, 1]` is not a graph object. The pinned mathlib has
  no `PathConnectedSpace unitInterval` instance, so a private local instance supplies it here.
-/

open Set Topology CategoryTheory

namespace TDA.Reeb

noncomputable section

namespace Examples.RGraphCosheafEquivalence

open OpenInterval CylinderPresentation FiniteReebData RGraph RGraph.Examples
open TDA.Reeb.Examples.Cylinder
open TDA.Reeb.Examples.ConstructibleCylinder (S0 D0 n0_card_top)

/-! ### A graph automorphism survives as a distinct natural transformation -/

/-- Two parallel edges over `0 < 1` as a graph object. -/
abbrev parallelGraph : RGraphCat := (toRGraph S01).obj parallelData

/-- The edge swap as a graph automorphism. -/
abbrev swapGraph : parallelGraph ⟶ parallelGraph := (toRGraph S01).map swap

theorem swapGraph_ne_id : swapGraph ≠ 𝟙 parallelGraph := fun h =>
  realize_swap_ne_id (congrArg (fun f : parallelGraph ⟶ parallelGraph => f.hom) h)

theorem swapGraph_comp_self : swapGraph ≫ swapGraph = 𝟙 parallelGraph := by
  rw [← Functor.map_comp, swap_swap, CategoryTheory.Functor.map_id]

/-- On the gap, the image of the swap exchanges the two edge labels. -/
theorem swap_cosheaf_edge (b : Bool) :
    (cosheafFunctor.map swapGraph).hom.app (S01.K 0) (parallelData.edgeLabel S01 0 b) =
      parallelData.edgeLabel S01 0 (!b) :=
  realizeNatTrans_edgeLabel S01 swap 0 b

/-- On stars, the image of the swap is the identity. -/
theorem swap_cosheaf_star (i : Fin 2) (x : (parallelData.toCosheaf S01).obj (S01.J i)) :
    (cosheafFunctor.map swapGraph).hom.app (S01.J i) x = x := by
  obtain ⟨v, rfl⟩ := (parallelData.vertexLabel S01 i).surjective x
  exact realizeNatTrans_vertexLabel S01 swap i v

/-- The image of the swap is a non-identity transformation. -/
theorem swap_cosheaf_ne_id : cosheafFunctor.map swapGraph ≠ 𝟙 _ := fun h =>
  Bool.false_ne_true ((parallelData.edgeLabel S01 0).injective ((swap_cosheaf_edge true).symm.trans
    (congrArg (fun α : cosheafFunctor.obj parallelGraph ⟶ cosheafFunctor.obj parallelGraph =>
      α.hom.app (S01.K 0) (parallelData.edgeLabel S01 0 true)) h)))

/-- The image of the swap is an involution, hence an automorphism. -/
theorem swap_cosheaf_comp_self :
    cosheafFunctor.map swapGraph ≫ cosheafFunctor.map swapGraph = 𝟙 _ := by
  rw [← Functor.map_comp, swapGraph_comp_self, CategoryTheory.Functor.map_id]

/-! ### A graph morphism collapsing two parallel edges -/

/-- Collapse two parallel edges onto one edge. -/
def collapseParallel : parallelData ⟶ singleEdge :=
  (⟨fun _ => id, fun _ _ => (), fun _ _ => rfl, fun _ _ => rfl⟩ :
    FiniteReebData.Hom parallelData singleEdge)

/-- A single edge over `0 < 1` as a graph object. -/
abbrev singleGraph : RGraphCat := (toRGraph S01).obj singleEdge

/-- The collapse as a graph morphism. -/
abbrev collapseGraph : parallelGraph ⟶ singleGraph := (toRGraph S01).map collapseParallel

/-- Both edge labels go to the single edge label. -/
theorem collapse_cosheaf_edge (b : Bool) :
    (cosheafFunctor.map collapseGraph).hom.app (S01.K 0) (parallelData.edgeLabel S01 0 b) =
      singleEdge.edgeLabel S01 0 () :=
  realizeNatTrans_edgeLabel S01 collapseParallel 0 b

/-- The gap component of the image merges the two edges. -/
theorem collapse_cosheaf_not_injective :
    ¬ Function.Injective ((cosheafFunctor.map collapseGraph).hom.app (S01.K 0)) := fun h =>
  Bool.false_ne_true ((parallelData.edgeLabel S01 0).injective
    (h ((collapse_cosheaf_edge false).trans (collapse_cosheaf_edge true).symm)))

/-- Hence the image of the collapse is not an isomorphism. -/
theorem collapse_cosheaf_not_isIso : ¬ IsIso (cosheafFunctor.map collapseGraph) := fun _ =>
  collapse_cosheaf_not_injective
    ((isIso_iff_bijective ((cosheafFunctor.map collapseGraph).hom.app (S01.K 0))).1
      inferInstance).1

/-! ### The same graph in two subdivisions -/

/-- The single edge presented over `0 < 1/2 < 1`. -/
abbrev singleHalfGraph : RGraphCat := (toRGraph Shalf).obj (refineData S01_sub_Shalf singleEdge)

/-- The two presentations give isomorphic graph objects (`refineIso`). -/
def subdivisionIso : singleHalfGraph ≅ singleGraph :=
  ObjectProperty.isoMk _ (refineIso S01_sub_Shalf singleEdge)

/-- Its image is an isomorphism of component cosheaves. -/
def subdivisionCosheafIso : cosheafFunctor.obj singleHalfGraph ≅ cosheafFunctor.obj singleGraph :=
  cosheafFunctor.mapIso subdivisionIso

/-- The cosheaf of the single edge is constructible at the coarse list. -/
theorem single_isConstructibleAt_S01 : S01.IsConstructibleAt (singleEdge.toCosheaf S01) :=
  singleEdge.toCosheaf_isConstructibleAt S01

/-- ... and at the subdivided list. -/
theorem single_isConstructibleAt_Shalf : Shalf.IsConstructibleAt (singleEdge.toCosheaf S01) :=
  single_isConstructibleAt_S01.of_refines S01_sub_Shalf

/-- The graph objects extracted at the two witnesses are isomorphic. -/
def single_ofCosheafIso :
    ofCosheaf S01 single_isConstructibleAt_S01 ≅ ofCosheaf Shalf single_isConstructibleAt_Shalf :=
  ofCosheafIso _ _ (singleEdge.toCosheaf_isIntervalCosheaf S01)

/-- The witness comparison is sent to the composite of the two reconstructions. -/
theorem single_ofCosheafIso_image :
    (cosheafFunctor.map single_ofCosheafIso.hom).hom =
      (CriticalValues.realizeExtractIso single_isConstructibleAt_S01
          (singleEdge.toCosheaf_isIntervalCosheaf S01)).hom ≫
        (CriticalValues.realizeExtractIso single_isConstructibleAt_Shalf
          (singleEdge.toCosheaf_isIntervalCosheaf S01)).inv :=
  cosheafFunctor_map_ofCosheafIso _ _ _

/-! ### A disconnected object: two points at one level -/

/-- Two points at level `0` as a graph object. -/
abbrev twoPointGraph : RGraphCat := (toRGraph S0).obj D0

/-- Its cosheaf has two components over `ℝ`. -/
theorem twoPoint_card_top : Nat.card ((cosheafFunctor.obj twoPointGraph).obj.obj ⊤) = 2 :=
  n0_card_top

/-- Endomorphisms of its cosheaf are all functions `Fin 2 → Fin 2`. -/
def twoPoint_endEquiv :
    (cosheafFunctor.obj twoPointGraph ⟶ cosheafFunctor.obj twoPointGraph) ≃ (Fin 2 → Fin 2) :=
  cosheafFullyFaithful.homEquiv.symm.trans <| IsRGraph.fullyFaithfulι.homEquiv.trans <|
    (overHomEquiv S0 D0 D0).trans ((homEquiv S0).symm.trans homEquivZero)

theorem twoPoint_end_card :
    Nat.card (cosheafFunctor.obj twoPointGraph ⟶ cosheafFunctor.obj twoPointGraph) = 4 := by
  rw [Nat.card_congr twoPoint_endEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin]
  rfl

/-! ### The empty object -/

/-- The empty graph over the one-level list. -/
abbrev emptyGraph : RGraphCat := emptyRGraph 0 S0

/-- A precosheaf with empty values is isomorphic to the zero cosheaf
`Examples.Constructible.zeroCosheaf`. -/
def isoZeroOfIsEmpty {F : OpenInterval ⥤ Type} (h : ∀ I, IsEmpty (F.obj I)) :
    F ≅ Examples.Constructible.zeroCosheaf :=
  NatIso.ofComponents
    (fun I =>
      haveI := h I
      haveI := Examples.Constructible.zeroCosheaf_isEmpty I
      Equiv.toIso (Equiv.equivOfIsEmpty (F.obj I) (Examples.Constructible.zeroCosheaf.obj I)))
    (by
      intro I J f
      ext x
      exact (h I).elim x)

/-- The zero cosheaf as an object of the target category: its cosheaf condition and its
constructibility at the one-level list. -/
def zeroObj : ConstructibleCosheafCat.{0} :=
  ⟨Examples.Constructible.zeroCosheaf, IsConstructibleCosheaf.of_isConstructibleAt
    (Examples.Constructible.zeroCosheaf_isConstructibleAt S0)
    Examples.Constructible.zeroCosheaf_isIntervalCosheaf⟩

/-- The empty graph is sent to the zero cosheaf: the cosheaf of the empty data has empty values
everywhere. -/
def emptyGraph_cosheafIso : cosheafFunctor.obj emptyGraph ≅ zeroObj :=
  ObjectProperty.isoMk _
    (isoZeroOfIsEmpty (Examples.ConstructibleRepresentation.emptyData_toCosheaf_isEmpty 0 S0))

/-- The zero cosheaf is initial among constructible cosheaves. -/
def zeroObj_isInitial : Limits.IsInitial zeroObj :=
  Limits.IsInitial.ofUniqueHom
    (fun Y => ObjectProperty.homMk
      { app := fun I => TypeCat.ofHom fun x => (Examples.Constructible.zeroCosheaf_isEmpty I).elim x
        naturality := fun I _ _ => by
          ext x; exact (Examples.Constructible.zeroCosheaf_isEmpty I).elim x })
    (fun _ _ => by ext I x; exact (Examples.Constructible.zeroCosheaf_isEmpty I).elim x)

/-- The inverse direction sends the zero cosheaf to a graph object with empty carrier. -/
theorem ofCosheafFunctor_zeroObj_isEmpty : IsEmpty (ofCosheafFunctor.obj zeroObj).obj.left := by
  have : ∀ i, IsEmpty ((ofFiniteData ((witness zeroObj).extract zeroObj.obj
      (isConstructibleAt_witness zeroObj).finite)).V i) := fun _ =>
    Examples.Constructible.zeroCosheaf_isEmpty _
  exact (ofFiniteData _).isEmpty_realization (witness zeroObj)

/-- That graph object is initial. -/
def ofCosheafFunctor_zeroObj_isInitial : Limits.IsInitial (ofCosheafFunctor.obj zeroObj) :=
  isInitialOfIsEmpty _ ofCosheafFunctor_zeroObj_isEmpty

/-! ### Negative boundary: same cosheaf, not isomorphic over `ℝ` -/

/-- `[0, 1]` is path-connected, by convexity; used only as a local instance in this file. -/
private theorem pathConnectedSpace_unitInterval : PathConnectedSpace unitInterval :=
  isPathConnected_iff_pathConnectedSpace.1
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)

attribute [local instance] pathConnectedSpace_unitInterval

/-- `[0, 1]` at constant height `0`, as an object over `ℝ`. -/
def constInterval : Over (TopCat.of ℝ) :=
  Over.mk (TopCat.ofHom (ContinuousMap.const unitInterval (0 : ℝ)))

/-- The one-piece cylinder presentation with vertex piece `[0, 1]` and no edges. -/
def intervalPres : CylinderPresentation.{0} 0 where
  V _ := unitInterval
  E e := e.elim0
  topE e := e.elim0
  left e := e.elim0
  right e := e.elim0

/-- `constInterval` is isomorphic over `ℝ` to the realization of the one-piece presentation over
`{0}`. -/
def constInterval_iso_realization :
    constInterval ≅ Over.mk (TopCat.ofHom (intervalPres.height S0)) :=
  Over.isoMk (TopCat.isoOfHomeo (homeomorphZero S0 intervalPres))
    (by
      ext x
      change intervalPres.height S0 (homeomorphZero S0 intervalPres x) = 0
      exact height_zero S0 intervalPres _)

/-- The point as a graph object: the one-vertex data `Examples.ConstructibleRepresentation.pt0`
at level `0`. -/
abbrev pointGraph : RGraphCat := (toRGraph S0).obj Examples.ConstructibleRepresentation.pt0

/-- The collapse of `[0, 1]` onto the point, over `ℝ`. -/
def collapseToPoint : constInterval ⟶ pointGraph.obj :=
  Over.homMk (TopCat.ofHom (ContinuousMap.const unitInterval
    ((ofFiniteData Examples.ConstructibleRepresentation.pt0).ofVertex S0 0 ()))) (by ext x; rfl)

/-- Every component map of the collapse is bijective. -/
theorem collapseToPoint_bijective (I : OpenInterval) :
    Function.Bijective ((intervalComponentsOver.map collapseToPoint).app I) := by
  refine ⟨fun c c' _ => ?_, fun d => ?_⟩
  · induction c using ZerothHomotopy.rec with
    | mk x =>
      induction c' using ZerothHomotopy.rec with
      | mk y =>
        obtain ⟨γ⟩ := PathConnectedSpace.joined (X := unitInterval) x.1 y.1
        have hf : Continuous (fun z : unitInterval => (⟨z, x.2⟩ :
            {w : constInterval.left // overBaseMap constInterval w ∈ toOpens I})) :=
          continuous_id.subtype_mk _
        exact ZerothHomotopy.sound (γ.map hf)
  · induction d using ZerothHomotopy.rec with
    | mk q =>
      obtain ⟨v, hv⟩ :=
        ofVertex_surjective_zero S0 (ofFiniteData Examples.ConstructibleRepresentation.pt0) q.1
      have h0 : overBaseMap constInterval (0 : unitInterval) ∈ toOpens I := by
        have := q.2
        rw [← hv] at this
        exact this
      exact ⟨ZerothHomotopy.mk ⟨(0 : unitInterval), h0⟩,
        congrArg ZerothHomotopy.mk (Subtype.ext hv)⟩

instance isIso_collapseToPoint : IsIso (intervalComponentsOver.map collapseToPoint) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro I
  rw [isIso_iff_bijective]
  exact collapseToPoint_bijective I

/-- `[0, 1]` at constant height is not a graph object: its fiber over `0` is the connected
space `[0, 1]`, while every fiber of a graph object is discrete (`discreteTopology_fiber`). -/
theorem constInterval_not_isRGraph : ¬ IsRGraph constInterval := by
  rintro ⟨m, T, D, ⟨i⟩⟩
  have hinv : ∀ x : unitInterval, i.inv.left.hom (i.hom.left.hom x) = x := fun x =>
    congrArg (fun φ : constInterval ⟶ constInterval => φ.left.hom x) i.hom_inv_id
  have hfib : ∀ x : unitInterval, (ofFiniteData D).height T (i.hom.left.hom x) = 0 :=
    fun x => overBaseMap_comm i.hom x
  have := discreteTopology_fiber T D 0
  have hc : Continuous (fun x : unitInterval =>
      (⟨i.hom.left.hom x, hfib x⟩ : (ofFiniteData D).height T ⁻¹' {0})) :=
    i.hom.left.hom.continuous.subtype_mk _
  have h01 := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
  have h01' : (0 : unitInterval) = 1 :=
    (hinv 0).symm.trans
      ((congrArg (fun y => i.inv.left.hom y) (congrArg Subtype.val h01)).trans (hinv 1))
  exact absurd (congrArg Subtype.val h01') (by norm_num)

/-- **Negative boundary**: `[0, 1]` at constant height and the point have isomorphic component
cosheaves, both constructible, but are not isomorphic over `ℝ`; `[0, 1]`, isomorphic to the
realization of a one-piece presentation (`constInterval_iso_realization`), lies outside
`RGraphCat`. -/
theorem negative_boundary :
    Nonempty (intervalComponentsOver.obj constInterval ≅
        intervalComponentsOver.obj pointGraph.obj) ∧
      IsConstructibleCosheaf (intervalComponentsOver.obj constInterval) ∧
      IsEmpty (constInterval ≅ pointGraph.obj) ∧ ¬ IsRGraph constInterval :=
  ⟨⟨asIso (intervalComponentsOver.map collapseToPoint)⟩,
    IsConstructibleCosheaf.of_iso (asIso (intervalComponentsOver.map collapseToPoint)).symm
      (cosheafFunctor.obj pointGraph).property,
    ⟨fun e => constInterval_not_isRGraph ⟨0, S0, Examples.ConstructibleRepresentation.pt0, ⟨e⟩⟩⟩,
    constInterval_not_isRGraph⟩

end Examples.RGraphCosheafEquivalence

end

end TDA.Reeb
