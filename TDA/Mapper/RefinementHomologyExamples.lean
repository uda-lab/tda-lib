import TDA.Mapper.RefinementHomology
import TDA.Mapper.TowerExamples
import TDA.Simplicial.H0Augmentation

/-!
# Refinement homology and persistence fixtures

Over a one-point domain, two selected refinements into duplicated overlapping
members give different Mapper vertex maps and the same nonzero `H₀` map; a
three-stage family of refinements whose direct selector is not the composite
still gives a persistence module equal to the one of the strictly coherent
tower; its first transition collapses an edge; an empty domain gives an empty
Mapper with equal induced maps for every ring and degree.  The negative
control is a pair of simplicial maps from a point to two isolated vertices:
they are not induced by refinements of one family pair, they are not
contiguous, and their `H₀` maps differ over `ZMod 2` while coinciding over the
zero ring `ZMod 1`.
-/

namespace TDA.Mapper.RefinementHomologyExamples

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Mapper.TowerExamples

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Ordered component indices over a subsingleton domain -/

/-- A subsingleton space has at most one path component. -/
theorem subsingleton_zerothHomotopy {Z : Type*} [TopologicalSpace Z] [Subsingleton Z] :
    Subsingleton (ZerothHomotopy Z) :=
  inferInstanceAs (Subsingleton (Quotient (pathSetoid Z)))

/-- Over a subsingleton domain a component index is determined by its cover index,
so a linear order on the cover index type lifts to the component indices. -/
@[instance_reducible]
def componentIndexLinearOrder {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Subsingleton X] [LinearOrder I] (f : C(X, Y)) (U : I → Set Y) :
    LinearOrder (ComponentIndex f U) :=
  LinearOrder.lift' (fun a : ComponentIndex f U => a.1) (by
    intro a b h
    have : ∀ i, Subsingleton (ZerothHomotopy (PullbackSpace f U i)) :=
      fun _ => subsingleton_zerothHomotopy
    exact Sigma.ext h (Subsingleton.helim
      (congrArg (fun i => ZerothHomotopy (PullbackSpace f U i)) h) a.2 b.2))

local instance {I : Type} [LinearOrder I] (U : I → Set Unit) :
    LinearOrder (ComponentIndex threeStageMap U) :=
  componentIndexLinearOrder threeStageMap U

/-- Over a field, the class of a single vertex is nonzero, by the augmentation. -/
private theorem vertexClass_ne_zero {V : Type} [LinearOrder V]
    (K : PreAbstractSimplicialComplex V) (k : Type) [Field k] (σ : Face K 0) :
    simplicialHomologyClass k K 0 (zeroVertexCycle K k σ) ≠ 0 := by
  intro hz
  have hq := congrArg (homologyKernelQuotient k (simplicialChainComplex K k) 0).hom.hom hz
  rw [simplicialHomologyClass_quotient, map_zero] at hq
  exact zeroVertexCycle_not_boundary K k σ ((Submodule.Quotient.mk_eq_zero _).mp hq)

private theorem vertexChainMap_singleton_face {V W : Type} [LinearOrder V] [LinearOrder W]
    {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}
    (g : VertexMap K L) (R : Type) [Ring R] (σ : Face K 0) (τ : Face L 0) (v : V)
    (hσ : σ.1 = {v}) (hτ : τ.1 = {g v}) :
    vertexChainMap R g 0 (Finsupp.single σ 1) = Finsupp.single τ 1 := by
  rw [vertexChainMap_vertex]
  congr 1
  apply Subtype.ext
  rcases σ with ⟨s, hs⟩
  dsimp only at hσ hτ
  subst hσ
  simp [vertexImageFace, tupleFace, hτ, Finset.orderEmbOfFin_singleton]

/-! ## Distinct refinements into duplicated members -/

/-- The unique component index of the one-member source family. -/
def sourceVertex : ComponentIndex threeStageMap selectorSource :=
  ⟨(), ZerothHomotopy.mk ⟨(), Set.mem_univ ()⟩⟩

/-- The component index of a duplicated target member. -/
def targetVertex (b : Bool) : ComponentIndex threeStageMap selectorTarget :=
  ⟨b, ZerothHomotopy.mk ⟨(), Set.mem_univ ()⟩⟩

/-- The source vertex as a degree-zero face. -/
def sourceFace : Face (mapper threeStageMap selectorSource) 0 :=
  ⟨{sourceVertex}, componentIndex_supported _ _ _, by simp⟩

/-- A duplicated target vertex as a degree-zero face. -/
def targetFace (b : Bool) : Face (mapper threeStageMap selectorTarget) 0 :=
  ⟨{targetVertex b}, componentIndex_supported _ _ _, by simp⟩

private theorem mapperMap_select_apply (b : Bool) :
    TDA.Mapper.mapperMap threeStageMap (if b then selectTrue else selectFalse) sourceVertex =
      targetVertex b := by
  cases b <;> rfl

/-- The two selections of a duplicated member give different Mapper vertex maps. -/
theorem select_mapperMap_ne :
    TDA.Mapper.mapperMap threeStageMap selectFalse ≠
      TDA.Mapper.mapperMap threeStageMap selectTrue := by
  intro h
  have happ := congrArg (fun m : VertexMap (mapper threeStageMap selectorSource)
    (mapper threeStageMap selectorTarget) => (m sourceVertex).1) h
  exact Bool.false_ne_true happ

/-- The two selections induce the same map on `H₀` over `ℚ`. -/
theorem select_mapperHomologyMap_eq :
    mapperHomologyMap ℚ threeStageMap selectFalse 0 =
      mapperHomologyMap ℚ threeStageMap selectTrue 0 :=
  mapperHomologyMap_eq ℚ threeStageMap selectFalse selectTrue 0

/-- The common `H₀` map sends the source vertex class to the class of the first
duplicated vertex, which is nonzero. -/
theorem select_mapperHomologyMap_class_ne_zero :
    (mapperHomologyMap ℚ threeStageMap selectFalse 0).hom
        (simplicialHomologyClass ℚ (mapper threeStageMap selectorSource) 0
          (zeroVertexCycle _ ℚ sourceFace)) =
      simplicialHomologyClass ℚ (mapper threeStageMap selectorTarget) 0
        (zeroVertexCycle _ ℚ (targetFace false)) ∧
    (mapperHomologyMap ℚ threeStageMap selectFalse 0).hom
        (simplicialHomologyClass ℚ (mapper threeStageMap selectorSource) 0
          (zeroVertexCycle _ ℚ sourceFace)) ≠ 0 := by
  have hclass := simplicialHomologyMap_class ℚ (TDA.Mapper.mapperMap threeStageMap selectFalse) 0
    (zeroVertexCycle _ ℚ sourceFace) (zeroVertexCycle _ ℚ (targetFace false))
    (vertexChainMap_singleton_face _ ℚ sourceFace (targetFace false) sourceVertex rfl rfl)
  refine ⟨hclass, ?_⟩
  rw [mapperHomologyMap_def, hclass]
  exact vertexClass_ne_zero _ ℚ _

/-! ## A three-stage family of refinements without strict coherence -/

/-- Linear orders on the varying stage index types. -/
instance threeStageIndexLinearOrder : (p : ThreeStage) → LinearOrder (threeStageIndex p)
  | .first => inferInstanceAs (LinearOrder Bool)
  | .middle => inferInstanceAs (LinearOrder Unit)
  | .last => inferInstanceAs (LinearOrder (Fin 2))

/-- Selectors agreeing with the coherent tower on adjacent comparisons, but
choosing vertex `1` on the direct first-to-last comparison. -/
def skewSelector (p q : ThreeStage) (h : p ≤ q) : threeStageIndex p → threeStageIndex q :=
  match p, q with
  | .first, .first => id
  | .first, .middle => fun _ => ()
  | .first, .last => fun _ => (⟨1, Nat.one_lt_succ_succ 0⟩ : Fin 2)
  | .middle, .first => False.elim (by cases h)
  | .middle, .middle => id
  | .middle, .last => fun _ => (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)
  | .last, .first => False.elim (by cases h)
  | .last, .middle => False.elim (by cases h)
  | .last, .last => id

/-- The selected refinements of the skew family. -/
def skewRefinement {p q : ThreeStage} (h : p ≤ q) :
    Refinement (threeStageCover p) (threeStageCover q) where
  selector := skewSelector p q h
  subset _ := by simp [threeStageCover]

/-- The direct selector of the skew family is not the composite of the adjacent
selectors, and the direct Mapper map is not the composite Mapper map. -/
theorem skew_not_coherent :
    (skewRefinement ThreeStageLE.first_last).selector ≠
        (skewRefinement ThreeStageLE.middle_last).selector ∘
          (skewRefinement ThreeStageLE.first_middle).selector ∧
      TDA.Mapper.mapperMap threeStageMap (skewRefinement ThreeStageLE.first_last) ≠
        VertexMap.comp
          (TDA.Mapper.mapperMap threeStageMap (skewRefinement ThreeStageLE.first_middle))
          (TDA.Mapper.mapperMap threeStageMap (skewRefinement ThreeStageLE.middle_last)) := by
  constructor
  · intro h
    have happ := congrFun h false
    exact absurd happ (by decide)
  · intro h
    have happ := congrArg (fun m : VertexMap (mapper threeStageMap (threeStageCover .first))
      (mapper threeStageMap (threeStageCover .last)) =>
        (m (threeStageComponentIndex .first false)).1) h
    exact absurd happ (by decide)

/-- The skew family is a persistence module in `H₀` over `ℚ` whose structure maps
compose, and it equals the module of the strictly coherent three-stage tower. -/
theorem skew_mapperHomologyPModule :
    structureMap (mapperHomologyPModule ℚ threeStageMap threeStageCover skewRefinement 0)
          ThreeStageLE.first_middle ≫
        structureMap (mapperHomologyPModule ℚ threeStageMap threeStageCover skewRefinement 0)
          ThreeStageLE.middle_last =
      structureMap (mapperHomologyPModule ℚ threeStageMap threeStageCover skewRefinement 0)
        ThreeStageLE.first_last ∧
    mapperHomologyPModule ℚ threeStageMap threeStageCover skewRefinement 0 =
      mapperHomologyPModule ℚ threeStageMap threeStageCover threeStageRefinement 0 :=
  ⟨structureMap_comp _ _ _, mapperHomologyPModule_eq ℚ threeStageMap threeStageCover _ 0 _⟩

local instance (q : ThreeStage) :
    LinearOrder (ComponentIndex threeStageMap (threeStageTower.cover q)) :=
  inferInstanceAs (LinearOrder (ComponentIndex threeStageMap (threeStageCover q)))

/-- The persistence module of the coherent three-stage tower has the homology maps of
the tower's strict Mapper maps as its structure maps. -/
theorem threeStageTower_structureMap {p q : ThreeStage} (h : p ≤ q) :
    structureMap (mapperHomologyPModule ℚ threeStageMap threeStageTower.cover
        threeStageTower.refinement 0) h =
      simplicialHomologyMap ℚ (threeStageTower.mapperMap threeStageMap h) 0 :=
  threeStageTower.structureMap_mapperHomologyPModule ℚ threeStageMap 0 h

/-! ## The collapsing first transition -/

/-- The first-stage edge as a degree-one face. -/
def firstEdge : Face (mapper threeStageMap (threeStageCover .first)) 1 :=
  ⟨{threeStageComponentIndex .first false, threeStageComponentIndex .first true}, by
    apply (mem_mapper_iff threeStageMap (threeStageCover .first) _).2
    refine ⟨by simp, (), ?_⟩
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> exact ⟨Set.mem_univ (), rfl⟩, by
    rw [Finset.card_pair]
    intro h
    exact Bool.false_ne_true (congrArg Sigma.fst h)⟩

/-- A first-stage vertex as a degree-zero face. -/
def firstVertexFace (b : Bool) : Face (mapper threeStageMap (threeStageCover .first)) 0 :=
  ⟨{threeStageComponentIndex .first b}, componentIndex_supported _ _ _, by simp⟩

/-- The middle-stage vertex as a degree-zero face. -/
def middleVertexFace : Face (mapper threeStageMap (threeStageCover .middle)) 0 :=
  ⟨{threeStageComponentIndex .middle ()}, componentIndex_supported _ _ _, by simp⟩

private instance : Subsingleton (ComponentIndex threeStageMap (threeStageCover .middle)) :=
  ⟨fun a b => by
    have : ∀ i, Subsingleton (ZerothHomotopy
        (PullbackSpace threeStageMap (threeStageCover .middle) i)) :=
      fun _ => subsingleton_zerothHomotopy
    have h1 : a.1 = b.1 := Subsingleton.elim (α := Unit) a.1 b.1
    exact Sigma.ext h1 (Subsingleton.helim (congrArg (fun i => ZerothHomotopy
      (PullbackSpace threeStageMap (threeStageCover .middle) i)) h1) a.2 b.2)⟩

/-- The first transition collapses the edge: its signed chain map kills the edge
generator in degree one over every ring, while on `H₀` over `ℚ` it sends each
endpoint class to the nonzero class of the middle vertex. -/
theorem skew_first_middle_collapse (R : Type) [Ring R] :
    vertexChainMap R (TDA.Mapper.mapperMap threeStageMap
        (skewRefinement ThreeStageLE.first_middle)) 1 (Finsupp.single firstEdge 1) = 0 ∧
    (∀ b : Bool, (mapperHomologyMap ℚ threeStageMap
        (skewRefinement ThreeStageLE.first_middle) 0).hom
          (simplicialHomologyClass ℚ _ 0 (zeroVertexCycle _ ℚ (firstVertexFace b))) =
        simplicialHomologyClass ℚ _ 0 (zeroVertexCycle _ ℚ middleVertexFace)) ∧
    simplicialHomologyClass ℚ _ 0 (zeroVertexCycle _ ℚ middleVertexFace) ≠ 0 := by
  refine ⟨?_, ?_, vertexClass_ne_zero _ ℚ _⟩
  · apply vertexChainMap_single_of_not_injective
    intro hinj
    have h01 := hinj (Subsingleton.elim
      (TDA.Mapper.mapperMap threeStageMap (skewRefinement ThreeStageLE.first_middle)
        (firstEdge.1.orderEmbOfFin firstEdge.2.2 0))
      (TDA.Mapper.mapperMap threeStageMap (skewRefinement ThreeStageLE.first_middle)
        (firstEdge.1.orderEmbOfFin firstEdge.2.2 1)))
    exact absurd h01 (by decide)
  · intro b
    rw [mapperHomologyMap_def]
    exact simplicialHomologyMap_class ℚ _ 0 _ _
      (vertexChainMap_singleton_face _ ℚ (firstVertexFace b) middleVertexFace
        (threeStageComponentIndex .first b) rfl
        (congrArg (fun a : ComponentIndex threeStageMap (threeStageCover .middle) =>
          ({a} : Finset _)) (Subsingleton.elim _ _)))

/-! ## Empty source Mapper -/

/-- The unique map from the empty domain. -/
def emptyMap : C(Empty, Unit) := ⟨Empty.elim, continuous_of_discreteTopology⟩

/-- A two-member family whose inverse images are empty. -/
def emptySource : Bool → Set Unit := fun _ => Set.univ

/-- A three-member target family. -/
def emptyTarget : Fin 3 → Set Unit := fun _ => Set.univ

/-- Select a fixed target member. -/
def emptySelect (j : Fin 3) : Refinement emptySource emptyTarget where
  selector _ := j
  subset _ := by simp [emptySource, emptyTarget]

local instance {I : Type} [LinearOrder I] (U : I → Set Unit) :
    LinearOrder (ComponentIndex emptyMap U) :=
  componentIndexLinearOrder emptyMap U

instance emptySource_componentIndex_isEmpty : IsEmpty (ComponentIndex emptyMap emptySource) :=
  ⟨fun a => by
    induction a.2 using ZerothHomotopy.rec with
    | mk x => exact x.1.elim⟩

/-- The empty domain leaves every source member with an empty inverse image, so the
Mapper has no faces, every induced chain map vanishes, and any two selected
refinements induce the same homology map over every ring and in every degree. -/
theorem empty_source_mapper (R : Type) [Ring R] (n : ℕ) (j j' : Fin 3) :
    (∀ i : Bool, IsEmpty (PullbackSpace emptyMap emptySource i)) ∧
    IsEmpty (Face (mapper emptyMap emptySource) n) ∧
    vertexChainMap R (TDA.Mapper.mapperMap emptyMap (emptySelect j)) n = 0 ∧
    mapperHomologyMap R emptyMap (emptySelect j) n =
      mapperHomologyMap R emptyMap (emptySelect j') n := by
  have hface : IsEmpty (Face (mapper emptyMap emptySource) n) := ⟨fun σ => by
    obtain ⟨a, _⟩ := ((mem_mapper_iff emptyMap emptySource σ.1).1 σ.2.1).1
    exact isEmptyElim a⟩
  refine ⟨fun _ => ⟨fun x => x.1.elim⟩, hface, ?_, mapperHomologyMap_eq R emptyMap _ _ n⟩
  apply Finsupp.lhom_ext
  intro σ _
  exact isEmptyElim σ

/-! ## Negative control: a point mapped to two isolated vertices -/

private theorem isolatedTarget_no_edges : IsEmpty (Face (nerve isolatedTarget) 1) := ⟨by
  intro σ
  have hcard : σ.1.card = Fintype.card Bool := by rw [σ.2.2]; rfl
  have huniv : σ.1 = Finset.univ := Finset.eq_univ_of_card σ.1 hcard
  obtain ⟨_, x, hx⟩ := (mem_nerve_iff isolatedTarget σ.1).1 σ.2.1
  have hfalse := hx false (by rw [huniv]; exact Finset.mem_univ _)
  have htrue := hx true (by rw [huniv]; exact Finset.mem_univ _)
  simp [isolatedTarget] at hfalse htrue
  exact Bool.false_ne_true (hfalse.symm.trans htrue)⟩

/-- The zero-cycle carried by one vertex, over any ring. -/
private def vertexCycle {V : Type} [LinearOrder V] (K : PreAbstractSimplicialComplex V)
    (R : Type) [Ring R] (σ : Face K 0) : simplicialCycles K R 0 :=
  ⟨Finsupp.single σ 1, by rw [simplicialCycles_zero]; trivial⟩

/-- The unique source vertex of the one-member nerve. -/
def pointFace : Face (nerve oneSource) 0 :=
  ⟨{()}, by simp [mem_nerve_iff, oneSource], by simp⟩

/-- An isolated target vertex. -/
def isolatedFace (b : Bool) : Face (nerve isolatedTarget) 0 :=
  ⟨{b}, by simp [mem_nerve_iff, isolatedTarget], by simp⟩

/-- Sending a point to either of two isolated vertices gives two noncontiguous
simplicial maps whose `H₀` maps differ over `ZMod 2`.  These maps are not the
Mapper maps of two refinements between one pair of families. -/
theorem isolated_vertex_maps_homology_ne :
    ¬ Contiguous (mapToIsolated false) (mapToIsolated true) ∧
    simplicialHomologyMap (ZMod 2) (mapToIsolated false) 0 ≠
      simplicialHomologyMap (ZMod 2) (mapToIsolated true) 0 := by
  refine ⟨isolated_vertex_maps_are_not_contiguous, ?_⟩
  intro he
  have hm₀ := simplicialHomologyMap_class (ZMod 2) (mapToIsolated false) 0
    (vertexCycle _ (ZMod 2) pointFace) (vertexCycle _ (ZMod 2) (isolatedFace false))
    (vertexChainMap_singleton_face _ (ZMod 2) pointFace (isolatedFace false) () rfl rfl)
  have hm₁ := simplicialHomologyMap_class (ZMod 2) (mapToIsolated true) 0
    (vertexCycle _ (ZMod 2) pointFace) (vertexCycle _ (ZMod 2) (isolatedFace true))
    (vertexChainMap_singleton_face _ (ZMod 2) pointFace (isolatedFace true) () rfl rfl)
  have hc := congrArg (fun m => m.hom (simplicialHomologyClass (ZMod 2) (nerve oneSource) 0
    (vertexCycle _ (ZMod 2) pointFace))) he
  rw [hm₀, hm₁] at hc
  have hq := congrArg
    (homologyKernelQuotient (ZMod 2) (simplicialChainComplex (nerve isolatedTarget) (ZMod 2)) 0).hom.hom
    hc
  rw [simplicialHomologyClass_quotient, simplicialHomologyClass_quotient] at hq
  have hb := (Submodule.Quotient.eq _).mp hq
  obtain ⟨c, hcb⟩ := (mem_simplicialBoundaries_iff (ZMod 2) (nerve isolatedTarget) 0 _).mp hb
  have := isolatedTarget_no_edges
  have hz : c = 0 := Finsupp.ext fun σ => isEmptyElim σ
  rw [hz, map_zero] at hcb
  have hv := congrArg (fun c : Chain (nerve isolatedTarget) (ZMod 2) 0 => c (isolatedFace false))
    hcb
  have hne : isolatedFace false ≠ isolatedFace true := by
    intro h
    have := congrArg (fun σ : Face (nerve isolatedTarget) 0 => (false ∈ σ.1)) h
    simp [isolatedFace] at this
  simp [vertexCycle, hne] at hv

/-- Over the zero ring the same two maps coincide on homology. -/
theorem isolated_vertex_maps_homology_eq_zero_ring :
    simplicialHomologyMap (ZMod 1) (mapToIsolated false) 0 =
      simplicialHomologyMap (ZMod 1) (mapToIsolated true) 0 := by
  have : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  have := Module.subsingleton (ZMod 1) (simplicialHomology (nerve isolatedTarget) (ZMod 1) 0)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

end

end TDA.Mapper.RefinementHomologyExamples
