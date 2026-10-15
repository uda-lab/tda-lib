import TDA.Reeb.GraphPLHeight
import TDA.Reeb.IntervalComponents
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Graph components and path components of piecewise-linear height preimages

For `V : Type u`, `G : SimpleGraph V`, `h : V → ℝ` and an open interval `I`, the nodes
`Cell G h I = {v // h v ∈ I} ⊕ {e : G.edgeSet // EdgeActive G h I e}` are the surviving vertices and
the active unoriented edges (`TDA.Reeb.GraphPLHeight`). The incidence graph `cellGraph G h I` is
bipartite: its only adjacencies join a surviving vertex to an active edge containing it, with no
vertex–vertex and no edge–edge adjacency. For `I ≤ J`, `cellInclusion G h hIJ` keeps every vertex
and edge, with identity and composition laws, and `cellComponentFunctor G h : OpenInterval ⥤ Type u`
sends `I` to the connected components of `cellGraph G h I`. No graph homomorphism collapsing an
edge to a vertex is used.

## The comparison

`preimageComponentsEquiv G h I` identifies the path components of the height preimage
`{p : Realization G // plHeight G h p ∈ I}` with the connected components of `cellGraph G h I`.
It assumes no endpoint coverage, finiteness, injectivity of heights, nonemptiness or
decidability. A surviving vertex goes to the class of its vertex node, and an edge point in the
preimage to the class of the node of its unoriented edge; at a surviving endpoint these classes
agree by incidence. The inverse sends a vertex node to the class of the vertex, and an edge node to
the class of any support witness on either dart of the edge (`preimageComponentsEquiv_symm_inr`).
The witness of `cellPoint` is an arbitrary classical choice; only its class enters the laws, and no
canonical representative is provided.

The forward map descends a node label. `optionLabel` is a set-level map on the whole realization,
defined by the universal lift `TDA.Reeb.GraphRealization.lift`: the node class on the preimage and
`none` off it. No continuity of it is claimed. Its restriction `preimageLabel` to the open preimage
`U = plHeight G h ⁻¹' I` is locally constant (`isLocallyConstant_preimageLabel`): the restriction of
the quotient map `quotMk` over `U` is a quotient map
(`Topology.IsQuotientMap.restrictPreimage_isOpen`), and on its domain the raw label is constant on
the trace of each open vertex cell and of each open dart interval. Openness of `quotMk` is not used.
Paths in `U` then preserve the label (`preimageLabel_eq_of_joined`), and an incidence walk gives a
path in `U` through convex edge fragments, so walks of the incidence graph preserve `cellPoint`.

## Naturality

For `I ≤ J`, the map `TDA.Reeb.componentMap (preimageInclusion (plHeight G h) _)` on path components
corresponds to `ConnectedComponent.map (cellInclusion G h hIJ)` on every class
(`preimageComponentsEquiv_componentMap`). The resulting natural isomorphism is
`intervalComponentsIso G h : intervalComponents (plHeight G h) ≅ cellComponentFunctor G h`.

## Vertex-only corollary

`EndpointCoverage G h I` says that every active edge has an endpoint whose height lies in `I`.
Under this hypothesis the incidence components are the components of the graph induced on the
surviving vertices (`cellInducedEquiv`, `preimageInducedEquiv`), and an edge node goes to the class
of any of its surviving endpoints, whichever endpoint `coverEndpoint` chooses. The hypothesis cannot
be dropped: for one edge of heights `0` and `2` and `I = (0, 2)` the preimage is one open arc while
no vertex survives. Coverage holds over the full interval (`endpointCoverage_top`), where the
comparison agrees with `TDA.Reeb.GraphRealization.componentsEquiv` (`full_componentsEquiv`).

`[Finite V]` appears only in `instFiniteCell` and `finite_zerothHomotopy`. `eq_of_walk` states that
a function respecting adjacency is constant along walks. The short name `mk_eq_of_joinedIn` also
occurs as `TDA.Reeb.CylinderPresentation.mk_eq_of_joinedIn`, and the private label helpers
`vertexLabel` and `edgeLabel` share their short names with `TDA.Reeb.FiniteReebData.vertexLabel`
and `TDA.Reeb.FiniteReebData.edgeLabel`.
-/

open SimpleGraph Topology Set CategoryTheory

/-- The reversal of the unit interval; `open unitInterval` would make `I` a token. -/
local notation "σ" => unitInterval.symm

universe u

namespace TDA.Reeb.GraphPL

open TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval

noncomputable section

/-- A function on the vertices that respects adjacency is constant along walks. -/
theorem eq_of_walk {W : Type*} {H : SimpleGraph W} {β : Sort*} {f : W → β}
    (hf : ∀ x y, H.Adj x y → f x = f y) {x y : W} (p : H.Walk x y) : f x = f y := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

section cells

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) (I : OpenInterval)

/-- The nodes of the incidence graph over `I`: surviving vertices and active unoriented edges. -/
def Cell : Type u := {v : V // h v ∈ I} ⊕ {e : G.edgeSet // EdgeActive G h I e}

/-- Vertex–edge incidence, the vertex being a surviving one; there is no vertex–vertex and no
edge–edge adjacency. -/
def CellAdj : Cell G h I → Cell G h I → Prop
  | Sum.inl v, Sum.inr e => (v : V) ∈ (e.1 : Sym2 V)
  | Sum.inr e, Sum.inl v => (v : V) ∈ (e.1 : Sym2 V)
  | Sum.inl _, Sum.inl _ => False
  | Sum.inr _, Sum.inr _ => False

/-- The bipartite incidence graph of surviving vertices and active edges. -/
def cellGraph : SimpleGraph (Cell G h I) where
  Adj := CellAdj G h I
  symm := ⟨fun x y hxy => by cases x <;> cases y <;> exact hxy⟩
  loopless := ⟨fun x hx => by cases x <;> exact hx⟩

variable {G h I}

@[simp] theorem cellGraph_adj_inl_inr {v : {v : V // h v ∈ I}}
    {e : {e : G.edgeSet // EdgeActive G h I e}} :
    (cellGraph G h I).Adj (Sum.inl v) (Sum.inr e) ↔ (v : V) ∈ (e.1 : Sym2 V) := Iff.rfl

@[simp] theorem cellGraph_adj_inr_inl {v : {v : V // h v ∈ I}}
    {e : {e : G.edgeSet // EdgeActive G h I e}} :
    (cellGraph G h I).Adj (Sum.inr e) (Sum.inl v) ↔ (v : V) ∈ (e.1 : Sym2 V) := Iff.rfl

theorem not_cellGraph_adj_inl_inl {v w : {v : V // h v ∈ I}} :
    ¬ (cellGraph G h I).Adj (Sum.inl v) (Sum.inl w) := id

theorem not_cellGraph_adj_inr_inr {e e' : {e : G.edgeSet // EdgeActive G h I e}} :
    ¬ (cellGraph G h I).Adj (Sum.inr e) (Sum.inr e') := id

variable (G h I)

/-- The incidence graph is bipartite between the vertex nodes and the edge nodes. -/
theorem cellGraph_isBipartiteWith :
    (cellGraph G h I).IsBipartiteWith (range Sum.inl) (range Sum.inr) := by
  refine ⟨Set.disjoint_left.2 ?_, fun ⦃x y⦄ hxy => ?_⟩
  · rintro _ ⟨v, rfl⟩ ⟨e, he⟩
    exact Sum.inr_ne_inl he
  · rcases x with v | e <;> rcases y with w | e'
    · exact (hxy : False).elim
    · exact .inl ⟨⟨v, rfl⟩, ⟨e', rfl⟩⟩
    · exact .inr ⟨⟨e, rfl⟩, ⟨w, rfl⟩⟩
    · exact (hxy : False).elim

/-- Incidence: a surviving vertex and an active edge containing it have one class. -/
theorem connectedComponentMk_inl_eq_inr {v : {v : V // h v ∈ I}}
    {e : {e : G.edgeSet // EdgeActive G h I e}} (hv : (v : V) ∈ (e.1 : Sym2 V)) :
    (cellGraph G h I).connectedComponentMk (Sum.inl v) =
      (cellGraph G h I).connectedComponentMk (Sum.inr e) :=
  ConnectedComponent.connectedComponentMk_eq_of_adj hv

/-- Finitely many nodes for a finite vertex type. -/
instance instFiniteCell [Finite V] : Finite (Cell G h I) := by
  classical
  have := Fintype.ofFinite V
  unfold Cell
  infer_instance

end cells

section inclusion

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- For `I ≤ J`, the inclusion keeps each vertex and edge and transports its membership proof. -/
def cellInclusion {I J : OpenInterval} (hIJ : I ≤ J) : cellGraph G h I →g cellGraph G h J where
  toFun := Sum.map (fun v => ⟨v.1, OpenInterval.le_iff_subset.1 hIJ v.2⟩)
    (fun e => ⟨e.1, e.2.mono hIJ⟩)
  map_rel' {x y} hxy := by cases x <;> cases y <;> exact hxy

@[simp] theorem cellInclusion_inl {I J : OpenInterval} (hIJ : I ≤ J) (v : {v : V // h v ∈ I}) :
    cellInclusion G h hIJ (Sum.inl v) = Sum.inl ⟨v.1, OpenInterval.le_iff_subset.1 hIJ v.2⟩ :=
  rfl

@[simp] theorem cellInclusion_inr {I J : OpenInterval} (hIJ : I ≤ J)
    (e : {e : G.edgeSet // EdgeActive G h I e}) :
    cellInclusion G h hIJ (Sum.inr e) = Sum.inr ⟨e.1, e.2.mono hIJ⟩ := rfl

theorem cellInclusion_refl (I : OpenInterval) : cellInclusion G h (le_refl I) = Hom.id :=
  RelHom.ext fun x => by cases x <;> rfl

theorem cellInclusion_comp {I J K : OpenInterval} (hIJ : I ≤ J) (hJK : J ≤ K) :
    (cellInclusion G h hJK).comp (cellInclusion G h hIJ) = cellInclusion G h (hIJ.trans hJK) :=
  RelHom.ext fun x => by cases x <;> rfl

/-- The incidence-component precosheaf `I ↦ π₀(cellGraph G h I)`. -/
def cellComponentFunctor : OpenInterval ⥤ Type u where
  obj I := (cellGraph G h I).ConnectedComponent
  map i := TypeCat.ofHom (ConnectedComponent.map (cellInclusion G h (leOfHom i)))
  map_id I := by
    ext c
    induction c using ConnectedComponent.ind with
    | h x => cases x <;> rfl
  map_comp i j := by
    ext c
    induction c using ConnectedComponent.ind with
    | h x => cases x <;> rfl

theorem cellComponentFunctor_obj (I : OpenInterval) :
    (cellComponentFunctor G h).obj I = (cellGraph G h I).ConnectedComponent := rfl

/-- Bridge: the functor action is `ConnectedComponent.map` of the inclusion. -/
theorem cellComponentFunctor_map_apply {I J : OpenInterval} (i : I ⟶ J)
    (c : (cellGraph G h I).ConnectedComponent) :
    (cellComponentFunctor G h).map i c = c.map (cellInclusion G h (leOfHom i)) := rfl

end inclusion

section label

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) (I : OpenInterval)

open scoped Classical in
/-- Vertex part of the set-level label. -/
private def vertexLabel (v : V) : Option (cellGraph G h I).ConnectedComponent :=
  if hv : h v ∈ I then some ((cellGraph G h I).connectedComponentMk (Sum.inl ⟨v, hv⟩)) else none

open scoped Classical in
/-- Edge part of the set-level label. -/
private def edgeLabel (d : G.Dart) (t : unitInterval) :
    Option (cellGraph G h I).ConnectedComponent :=
  if ht : dartHeight h d t ∈ I then
    some ((cellGraph G h I).connectedComponentMk
      (Sum.inr ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩))
  else none

private theorem vertexLabel_of_mem {v : V} (hv : h v ∈ I) :
    vertexLabel G h I v = some ((cellGraph G h I).connectedComponentMk (Sum.inl ⟨v, hv⟩)) := by
  rw [vertexLabel, dif_pos hv]

private theorem edgeLabel_of_mem {d : G.Dart} {t : unitInterval} (ht : dartHeight h d t ∈ I) :
    edgeLabel G h I d t = some ((cellGraph G h I).connectedComponentMk
      (Sum.inr ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩)) := by
  rw [edgeLabel, dif_pos ht]

/-- Reversal: both orientations represent one unoriented edge. -/
private theorem edgeLabel_symm (d : G.Dart) (t : unitInterval) :
    edgeLabel G h I d.symm (σ t) = edgeLabel G h I d t := by
  by_cases ht : dartHeight h d t ∈ I
  · have ht' : dartHeight h d.symm (σ t) ∈ I := by rwa [dartHeight_symm]
    rw [edgeLabel_of_mem G h I ht, edgeLabel_of_mem G h I ht']
    have he : (⟨dartEdge d.symm, edgeActive_dartEdge_of_mem ht'⟩ :
        {e : G.edgeSet // EdgeActive G h I e}) = ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩ :=
      Subtype.ext (dartEdge_symm d)
    rw [he]
  · have ht' : dartHeight h d.symm (σ t) ∉ I := by rwa [dartHeight_symm]
    rw [edgeLabel, edgeLabel, dif_neg ht, dif_neg ht']

/-- The start: at a surviving endpoint the edge-node and vertex-node classes agree by incidence;
off the preimage both values are `none`. -/
private theorem edgeLabel_zero (d : G.Dart) : edgeLabel G h I d 0 = vertexLabel G h I d.fst := by
  by_cases hv : h d.fst ∈ I
  · have ht : dartHeight h d 0 ∈ I := by rwa [dartHeight_zero]
    rw [edgeLabel_of_mem G h I ht, vertexLabel_of_mem G h I hv]
    exact congrArg some
      (connectedComponentMk_inl_eq_inr G h I (v := ⟨d.fst, hv⟩) (fst_mem_dartEdge d)).symm
  · have ht : dartHeight h d 0 ∉ I := by rwa [dartHeight_zero]
    rw [edgeLabel, vertexLabel, dif_neg ht, dif_neg hv]

/-- The set-level label on the whole realization, by the universal lift `lift`: the node class on
the height preimage and `none` off it. No continuity of this map is claimed. -/
def optionLabel : Realization G → Option (cellGraph G h I).ConnectedComponent :=
  lift G (vertexLabel G h I) (edgeLabel G h I) (edgeLabel_symm G h I) (edgeLabel_zero G h I)

theorem isSome_optionLabel {p : Realization G} (hp : plHeight G h p ∈ I) :
    (optionLabel G h I p).isSome := by
  induction p using ind G with
  | vertex v =>
    show (vertexLabel G h I v).isSome
    rw [vertexLabel_of_mem G h I hp]
    rfl
  | edgePoint d t =>
    show (edgeLabel G h I d t).isSome
    rw [edgeLabel_of_mem G h I hp]
    rfl

/-- The node label on the height preimage. -/
def preimageLabel (p : {p : Realization G // plHeight G h p ∈ I}) :
    (cellGraph G h I).ConnectedComponent :=
  (optionLabel G h I p.1).get (isSome_optionLabel G h I p.2)

theorem some_preimageLabel (p : {p : Realization G // plHeight G h p ∈ I}) :
    some (preimageLabel G h I p) = optionLabel G h I p.1 :=
  Option.some_get _

@[simp] theorem preimageLabel_vertex (v : V) (hv : h v ∈ I) :
    preimageLabel G h I ⟨vertex G v, hv⟩ =
      (cellGraph G h I).connectedComponentMk (Sum.inl ⟨v, hv⟩) :=
  Option.some_injective _ ((some_preimageLabel G h I _).trans (vertexLabel_of_mem G h I hv))

@[simp] theorem preimageLabel_edgePoint (d : G.Dart) (t : unitInterval)
    (ht : dartHeight h d t ∈ I) :
    preimageLabel G h I ⟨edgePoint G d t, ht⟩ =
      (cellGraph G h I).connectedComponentMk
        (Sum.inr ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩) :=
  Option.some_injective _ ((some_preimageLabel G h I _).trans (edgeLabel_of_mem G h I ht))

/-- **Restricted quotient/discrete-label bridge.** The label is locally constant on the open
preimage `U`. The restriction of the actual quotient map over `U` is a quotient map
(`IsQuotientMap.restrictPreimage_isOpen`); on its domain, an open subspace of the cells, the raw
label is constant on the trace of each open vertex cell and of each open dart interval. -/
theorem isLocallyConstant_preimageLabel : IsLocallyConstant (preimageLabel G h I) := by
  let _ : TopologicalSpace (cellGraph G h I).ConnectedComponent := ⊥
  have _ : DiscreteTopology (cellGraph G h I).ConnectedComponent := ⟨rfl⟩
  have hU : IsOpen (plHeight G h ⁻¹' (I : Set ℝ)) := I.isOpen.preimage (plHeight G h).continuous
  have hq := (isQuotientMap_quotMk G).restrictPreimage_isOpen hU
  refine (IsLocallyConstant.iff_continuous _).2 (hq.continuous_iff.2 ?_)
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 ?_)
  let _ : TopologicalSpace V := ⊥
  rintro ⟨c, hc⟩
  rcases c with v | ⟨d, t⟩
  · refine ⟨Subtype.val ⁻¹' {Sum.inl v},
      (isOpen_vertexCell G v).preimage continuous_subtype_val, rfl, ?_⟩
    rintro ⟨c', hc'⟩ (hmem : c' = Sum.inl v)
    subst hmem
    rfl
  · have hd := @isOpen_range_sigmaMk G.Dart (fun _ => unitInterval) _ d
    refine ⟨Subtype.val ⁻¹' (Sum.inr '' range (Sigma.mk d)),
      (isOpenMap_inr (X := V) _ hd).preimage continuous_subtype_val, ?_, ?_⟩
    · exact ⟨⟨d, t⟩, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨c', hc'⟩ ⟨_, ⟨s, rfl⟩, rfl⟩
      exact (preimageLabel_edgePoint G h I d s hc').trans
        (preimageLabel_edgePoint G h I d t hc).symm

/-- The label is constant along paths in the preimage, through `TDA.Reeb.joined_eq_of_discrete`. -/
theorem preimageLabel_eq_of_joined {x y : {p : Realization G // plHeight G h p ∈ I}}
    (hxy : Joined x y) : preimageLabel G h I x = preimageLabel G h I y := by
  let _ : TopologicalSpace (cellGraph G h I).ConnectedComponent := ⊥
  have _ : DiscreteTopology (cellGraph G h I).ConnectedComponent := ⟨rfl⟩
  exact TDA.Reeb.joined_eq_of_discrete (hxy.map (isLocallyConstant_preimageLabel G h I).continuous)

end label

section equiv

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) (I : OpenInterval)

theorem mk_eq_of_joinedIn {x y : Realization G} (hxy : JoinedIn (plHeight G h ⁻¹' (I : Set ℝ)) x y)
    (hx : plHeight G h x ∈ I) (hy : plHeight G h y ∈ I) :
    (ZerothHomotopy.mk ⟨x, hx⟩ : ZerothHomotopy {p : Realization G // plHeight G h p ∈ I}) =
      ZerothHomotopy.mk ⟨y, hy⟩ :=
  TDA.Topology.mk_eq_of_joinedIn (plHeight G h) (I : Set ℝ) hxy hx hy

/-- **Witness and orientation independence.** Parameters on darts representing one edge, both in
the height preimage, give one path component. -/
theorem mk_edgePoint_eq_of_dartEdge_eq {d₁ d₂ : G.Dart} (hd : dartEdge d₁ = dartEdge d₂)
    {t₁ t₂ : unitInterval} (h₁ : dartHeight h d₁ t₁ ∈ I) (h₂ : dartHeight h d₂ t₂ ∈ I) :
    (ZerothHomotopy.mk ⟨edgePoint G d₁ t₁, h₁⟩ :
        ZerothHomotopy {p : Realization G // plHeight G h p ∈ I}) =
      ZerothHomotopy.mk ⟨edgePoint G d₂ t₂, h₂⟩ := by
  rcases dartEdge_eq_iff.1 hd with rfl | rfl
  · exact mk_eq_of_joinedIn G h I (joinedIn_edgePoint d₁ h₁ h₂) _ _
  · have hrev := dartHeight_symm h d₂ (σ t₁)
    rw [unitInterval.symm_symm] at hrev
    have h₁' : dartHeight h d₂ (σ t₁) ∈ I := by rwa [← hrev]
    have hp : edgePoint G d₂.symm t₁ = edgePoint G d₂ (σ t₁) := by
      rw [← edgePoint_symm G d₂ (σ t₁), unitInterval.symm_symm]
    calc (ZerothHomotopy.mk ⟨edgePoint G d₂.symm t₁, h₁⟩ :
            ZerothHomotopy {p : Realization G // plHeight G h p ∈ I})
        = ZerothHomotopy.mk ⟨edgePoint G d₂ (σ t₁), h₁'⟩ :=
          congrArg ZerothHomotopy.mk (Subtype.ext hp)
      _ = ZerothHomotopy.mk ⟨edgePoint G d₂ t₂, h₂⟩ :=
          mk_eq_of_joinedIn G h I (joinedIn_edgePoint d₂ h₁' h₂) _ _

/-- The inverse on nodes: the actual point class of a surviving vertex, and the class of a chosen
interior support witness of an active edge. The witness is an arbitrary classical choice, not a
canonical one; no law depends on it, and `cellPoint_inr` holds for every support witness. -/
def cellPoint : Cell G h I → ZerothHomotopy {p : Realization G // plHeight G h p ∈ I}
  | Sum.inl v => ZerothHomotopy.mk ⟨vertex G v.1, v.2⟩
  | Sum.inr e => ZerothHomotopy.mk ⟨edgePoint G (Classical.choose e.2)
      (Classical.choose (Classical.choose_spec e.2).2),
      (Classical.choose_spec (Classical.choose_spec e.2).2).2.2⟩

theorem cellPoint_inl (v : {v : V // h v ∈ I}) :
    cellPoint G h I (Sum.inl v) = ZerothHomotopy.mk ⟨vertex G v.1, v.2⟩ := rfl

/-- The edge-node value is the class of any support witness, on either orientation. -/
theorem cellPoint_inr (e : {e : G.edgeSet // EdgeActive G h I e}) {d : G.Dart}
    (hd : dartEdge d = e.1) {t : unitInterval} (ht : dartHeight h d t ∈ I) :
    cellPoint G h I (Sum.inr e) = ZerothHomotopy.mk ⟨edgePoint G d t, ht⟩ :=
  mk_edgePoint_eq_of_dartEdge_eq G h I ((Classical.choose_spec e.2).1.trans hd.symm) _ _

theorem cellPoint_inl_eq_inr {v : {v : V // h v ∈ I}} {e : {e : G.edgeSet // EdgeActive G h I e}}
    (hv : (v : V) ∈ (e.1 : Sym2 V)) : cellPoint G h I (Sum.inl v) = cellPoint G h I (Sum.inr e) := by
  obtain ⟨d, hd, hdv⟩ := exists_dartEdge_eq_fst hv
  have h0 : dartHeight h d 0 ∈ I := by rw [dartHeight_zero, hdv]; exact v.2
  rw [cellPoint_inr G h I e hd h0]
  exact congrArg ZerothHomotopy.mk
    (Subtype.ext (show vertex G v.1 = edgePoint G d 0 by rw [edgePoint_zero, hdv]))

theorem cellPoint_eq_of_adj {x y : Cell G h I} (hxy : (cellGraph G h I).Adj x y) :
    cellPoint G h I x = cellPoint G h I y := by
  rcases x with v | e <;> rcases y with w | e'
  · exact (hxy : False).elim
  · exact cellPoint_inl_eq_inr G h I hxy
  · exact (cellPoint_inl_eq_inr G h I hxy).symm
  · exact (hxy : False).elim

/-- **The actual preimage comparison.** Path components of the PL-height preimage of `I` are the
connected components of the incidence graph; no endpoint coverage is assumed. -/
def preimageComponentsEquiv :
    ZerothHomotopy {p : Realization G // plHeight G h p ∈ I} ≃
      (cellGraph G h I).ConnectedComponent where
  toFun := ZerothHomotopy.lift (preimageLabel G h I) fun _ _ γ =>
    preimageLabel_eq_of_joined G h I ⟨γ⟩
  invFun := ConnectedComponent.lift (cellPoint G h I) fun _ _ p _ =>
    eq_of_walk (fun _ _ => cellPoint_eq_of_adj G h I) p
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x =>
      obtain ⟨p, hp⟩ := x
      induction p using ind G with
      | vertex v =>
        show ConnectedComponent.lift (cellPoint G h I) _ (preimageLabel G h I ⟨vertex G v, hp⟩) = _
        rw [preimageLabel_vertex G h I v hp]
        rfl
      | edgePoint d t =>
        show ConnectedComponent.lift (cellPoint G h I) _
          (preimageLabel G h I ⟨edgePoint G d t, hp⟩) = _
        rw [preimageLabel_edgePoint G h I d t hp]
        exact cellPoint_inr G h I _ rfl hp
  right_inv c := by
    induction c using ConnectedComponent.ind with
    | h x =>
      rcases x with v | e
      · exact preimageLabel_vertex G h I v.1 v.2
      · obtain ⟨d, hd, t, -, -, ht⟩ := e.2
        show ZerothHomotopy.lift (preimageLabel G h I) _ (cellPoint G h I (Sum.inr e)) = _
        rw [cellPoint_inr G h I e hd ht]
        show preimageLabel G h I ⟨edgePoint G d t, ht⟩ = _
        rw [preimageLabel_edgePoint G h I d t ht]
        exact congrArg _ (congrArg Sum.inr (Subtype.ext hd))

/-- A surviving vertex class goes to its vertex-node class. -/
@[simp] theorem preimageComponentsEquiv_mk_vertex (v : V) (hv : h v ∈ I) :
    preimageComponentsEquiv G h I (ZerothHomotopy.mk ⟨vertex G v, hv⟩) =
      (cellGraph G h I).connectedComponentMk (Sum.inl ⟨v, hv⟩) :=
  preimageLabel_vertex G h I v hv

/-- An edge point in the preimage goes to the node class of its unoriented edge. -/
@[simp] theorem preimageComponentsEquiv_mk_edgePoint (d : G.Dart) (t : unitInterval)
    (ht : dartHeight h d t ∈ I) :
    preimageComponentsEquiv G h I (ZerothHomotopy.mk ⟨edgePoint G d t, ht⟩) =
      (cellGraph G h I).connectedComponentMk
        (Sum.inr ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩) :=
  preimageLabel_edgePoint G h I d t ht

/-- Endpoint compatibility: if the start of a dart survives, its edge points in the preimage go to
the start's vertex-node class. -/
theorem preimageComponentsEquiv_mk_edgePoint_of_fst_mem {d : G.Dart} {t : unitInterval}
    (ht : dartHeight h d t ∈ I) (hv : h d.fst ∈ I) :
    preimageComponentsEquiv G h I (ZerothHomotopy.mk ⟨edgePoint G d t, ht⟩) =
      (cellGraph G h I).connectedComponentMk (Sum.inl ⟨d.fst, hv⟩) := by
  rw [preimageComponentsEquiv_mk_edgePoint]
  exact (connectedComponentMk_inl_eq_inr G h I (fst_mem_dartEdge d)).symm

/-- Endpoint compatibility at the other end. -/
theorem preimageComponentsEquiv_mk_edgePoint_of_snd_mem {d : G.Dart} {t : unitInterval}
    (ht : dartHeight h d t ∈ I) (hv : h d.snd ∈ I) :
    preimageComponentsEquiv G h I (ZerothHomotopy.mk ⟨edgePoint G d t, ht⟩) =
      (cellGraph G h I).connectedComponentMk (Sum.inl ⟨d.snd, hv⟩) := by
  rw [preimageComponentsEquiv_mk_edgePoint]
  exact (connectedComponentMk_inl_eq_inr G h I (snd_mem_dartEdge d)).symm

@[simp] theorem preimageComponentsEquiv_symm_inl (v : {v : V // h v ∈ I}) :
    (preimageComponentsEquiv G h I).symm ((cellGraph G h I).connectedComponentMk (Sum.inl v)) =
      ZerothHomotopy.mk ⟨vertex G v.1, v.2⟩ := rfl

/-- The inverse on an edge node is the class of any support witness, on either orientation. -/
theorem preimageComponentsEquiv_symm_inr (e : {e : G.edgeSet // EdgeActive G h I e})
    {d : G.Dart} (hd : dartEdge d = e.1) {t : unitInterval} (ht : dartHeight h d t ∈ I) :
    (preimageComponentsEquiv G h I).symm ((cellGraph G h I).connectedComponentMk (Sum.inr e)) =
      ZerothHomotopy.mk ⟨edgePoint G d t, ht⟩ :=
  cellPoint_inr G h I e hd ht

/-- Finitely many path components for a finite graph. -/
theorem finite_zerothHomotopy [Finite V] :
    Finite (ZerothHomotopy {p : Realization G // plHeight G h p ∈ I}) :=
  Finite.of_equiv _ (preimageComponentsEquiv G h I).symm

end equiv

section naturality

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- **Naturality.** For `I ≤ J`, the map `TDA.Reeb.componentMap` on path components of the
preimage inclusion corresponds to `ConnectedComponent.map` of the incidence-graph inclusion. -/
theorem preimageComponentsEquiv_componentMap {I J : OpenInterval} (hIJ : I ≤ J)
    (c : ZerothHomotopy {p : Realization G // plHeight G h p ∈ I}) :
    preimageComponentsEquiv G h J
        (TDA.Reeb.componentMap (preimageInclusion (plHeight G h) (toOpens_le_iff.2 hIJ)) c) =
      (preimageComponentsEquiv G h I c).map (cellInclusion G h hIJ) := by
  induction c using ZerothHomotopy.rec with
  | mk x =>
    obtain ⟨p, hp⟩ := x
    induction p using ind G with
    | vertex v =>
      rw [preimageComponentsEquiv_mk_vertex G h I v hp]
      exact preimageComponentsEquiv_mk_vertex G h J v _
    | edgePoint d t =>
      rw [preimageComponentsEquiv_mk_edgePoint G h I d t hp]
      exact preimageComponentsEquiv_mk_edgePoint G h J d t _

theorem preimageComponentsEquiv_comp_componentMap {I J : OpenInterval} (hIJ : I ≤ J) :
    preimageComponentsEquiv G h J ∘
        TDA.Reeb.componentMap (preimageInclusion (plHeight G h) (toOpens_le_iff.2 hIJ)) =
      ConnectedComponent.map (cellInclusion G h hIJ) ∘ preimageComponentsEquiv G h I :=
  _root_.funext (preimageComponentsEquiv_componentMap G h hIJ)

/-- **Functor packaging.** The interval path-component precosheaf of the PL height is naturally
isomorphic to the incidence-component precosheaf. -/
def intervalComponentsIso : intervalComponents (plHeight G h) ≅ cellComponentFunctor G h :=
  NatIso.ofComponents (fun I => (preimageComponentsEquiv G h I).toIso) fun {I J} i => by
    ext c
    exact preimageComponentsEquiv_componentMap G h (leOfHom i) c

@[simp] theorem intervalComponentsIso_hom_app (I : OpenInterval)
    (c : (intervalComponents (plHeight G h)).obj I) :
    (intervalComponentsIso G h).hom.app I c = preimageComponentsEquiv G h I c := rfl

@[simp] theorem intervalComponentsIso_inv_app (I : OpenInterval)
    (c : (cellComponentFunctor G h).obj I) :
    (intervalComponentsIso G h).inv.app I c = (preimageComponentsEquiv G h I).symm c := rfl

end naturality

section coverage

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) (I : OpenInterval)

/-- Endpoint coverage at `I`: every active edge has an endpoint whose height lies in `I`. -/
def EndpointCoverage : Prop :=
  ∀ e : G.edgeSet, EdgeActive G h I e → ∃ v ∈ (e : Sym2 V), h v ∈ I

/-- Adjacent surviving vertices have one incidence class, through their active edge. -/
theorem connectedComponentMk_inl_eq_of_adj {u w : ↥(h ⁻¹' (I : Set ℝ))} (huw : G.Adj u w) :
    (cellGraph G h I).connectedComponentMk (Sum.inl u) =
      (cellGraph G h I).connectedComponentMk (Sum.inl w) :=
  (connectedComponentMk_inl_eq_inr G h I (e := ⟨⟨s(u.1, w.1), huw⟩,
      edgeActive_of_mem (Sym2.mem_mk_left _ _) u.2⟩) (Sym2.mem_mk_left _ _)).trans
    (connectedComponentMk_inl_eq_inr G h I (Sym2.mem_mk_right _ _)).symm

/-- Induced-graph components to incidence components: each vertex goes to its node class. No
endpoint coverage is used; this is a component map, not a graph homomorphism. -/
def inducedToCell :
    (G.induce (h ⁻¹' (I : Set ℝ))).ConnectedComponent → (cellGraph G h I).ConnectedComponent :=
  ConnectedComponent.lift (fun v => (cellGraph G h I).connectedComponentMk (Sum.inl v))
    fun _ _ p _ => eq_of_walk (fun _ _ huw => connectedComponentMk_inl_eq_of_adj G h I huw) p

/-- Two surviving endpoints of one edge lie in one component of the induced graph. -/
theorem induce_mk_eq_of_mem {e : G.edgeSet} {u w : ↥(h ⁻¹' (I : Set ℝ))}
    (hu : (u : V) ∈ (e : Sym2 V)) (hw : (w : V) ∈ (e : Sym2 V)) :
    (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk u =
      (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk w := by
  by_cases huw : (u : V) = w
  · rw [Subtype.ext huw]
  · have he : (e : Sym2 V) = s(u.1, w.1) := (Sym2.mem_and_mem_iff huw).1 ⟨hu, hw⟩
    have hadj : G.Adj u w := by
      have := e.2
      rw [he] at this
      exact this
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hadj

/-- A chosen surviving endpoint of an active edge. The choice is an arbitrary classical one, not a
canonical endpoint; only its induced-graph class enters the laws (`cellInducedEquiv_inr`). -/
def coverEndpoint (hcov : EndpointCoverage G h I) (e : {e : G.edgeSet // EdgeActive G h I e}) :
    ↥(h ⁻¹' (I : Set ℝ)) :=
  ⟨Classical.choose (hcov e.1 e.2), (Classical.choose_spec (hcov e.1 e.2)).2⟩

theorem coverEndpoint_mem (hcov : EndpointCoverage G h I)
    (e : {e : G.edgeSet // EdgeActive G h I e}) :
    (coverEndpoint G h I hcov e : V) ∈ (e.1 : Sym2 V) :=
  (Classical.choose_spec (hcov e.1 e.2)).1

/-- The node map to induced-graph components under endpoint coverage, through `coverEndpoint`
on edge nodes. -/
def coverNode (hcov : EndpointCoverage G h I) :
    Cell G h I → (G.induce (h ⁻¹' (I : Set ℝ))).ConnectedComponent
  | Sum.inl v => (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk v
  | Sum.inr e => (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk (coverEndpoint G h I hcov e)

theorem coverNode_eq_of_adj (hcov : EndpointCoverage G h I) {x y : Cell G h I}
    (hxy : (cellGraph G h I).Adj x y) : coverNode G h I hcov x = coverNode G h I hcov y := by
  rcases x with v | e <;> rcases y with w | e'
  · exact (hxy : False).elim
  · exact induce_mk_eq_of_mem G h I hxy (coverEndpoint_mem G h I hcov e')
  · exact induce_mk_eq_of_mem G h I (coverEndpoint_mem G h I hcov e) hxy
  · exact (hxy : False).elim

/-- **Vertex-only corollary.** Under endpoint coverage, incidence components are the components of
the graph induced on the surviving vertices. -/
def cellInducedEquiv (hcov : EndpointCoverage G h I) :
    (cellGraph G h I).ConnectedComponent ≃ (G.induce (h ⁻¹' (I : Set ℝ))).ConnectedComponent where
  toFun := ConnectedComponent.lift (coverNode G h I hcov) fun _ _ p _ =>
    eq_of_walk (fun _ _ => coverNode_eq_of_adj G h I hcov) p
  invFun := inducedToCell G h I
  left_inv c := by
    induction c using ConnectedComponent.ind with
    | h x =>
      rcases x with v | e
      · rfl
      · exact connectedComponentMk_inl_eq_inr G h I (coverEndpoint_mem G h I hcov e)
  right_inv c := by
    induction c using ConnectedComponent.ind with
    | h v => rfl

@[simp] theorem cellInducedEquiv_inl (hcov : EndpointCoverage G h I) (v : {v : V // h v ∈ I}) :
    cellInducedEquiv G h I hcov ((cellGraph G h I).connectedComponentMk (Sum.inl v)) =
      (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk v := rfl

/-- **Choice independence.** An edge node goes to the class of any of its surviving endpoints. -/
theorem cellInducedEquiv_inr (hcov : EndpointCoverage G h I)
    (e : {e : G.edgeSet // EdgeActive G h I e}) {w : ↥(h ⁻¹' (I : Set ℝ))}
    (hw : (w : V) ∈ (e.1 : Sym2 V)) :
    cellInducedEquiv G h I hcov ((cellGraph G h I).connectedComponentMk (Sum.inr e)) =
      (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk w :=
  induce_mk_eq_of_mem G h I (coverEndpoint_mem G h I hcov e) hw

@[simp] theorem cellInducedEquiv_symm_mk (hcov : EndpointCoverage G h I)
    (v : ↥(h ⁻¹' (I : Set ℝ))) :
    (cellInducedEquiv G h I hcov).symm ((G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk v) =
      (cellGraph G h I).connectedComponentMk (Sum.inl v) := rfl

/-- The vertex-only comparison of preimage path components, under endpoint coverage. -/
def preimageInducedEquiv (hcov : EndpointCoverage G h I) :
    ZerothHomotopy {p : Realization G // plHeight G h p ∈ I} ≃
      (G.induce (h ⁻¹' (I : Set ℝ))).ConnectedComponent :=
  (preimageComponentsEquiv G h I).trans (cellInducedEquiv G h I hcov)

@[simp] theorem preimageInducedEquiv_mk_vertex (hcov : EndpointCoverage G h I) (v : V)
    (hv : h v ∈ I) :
    preimageInducedEquiv G h I hcov (ZerothHomotopy.mk ⟨vertex G v, hv⟩) =
      (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk ⟨v, hv⟩ := by
  show cellInducedEquiv G h I hcov (preimageComponentsEquiv G h I _) = _
  rw [preimageComponentsEquiv_mk_vertex]
  rfl

/-- An edge point goes to the class of any surviving endpoint of its edge. -/
theorem preimageInducedEquiv_mk_edgePoint (hcov : EndpointCoverage G h I) (d : G.Dart)
    (t : unitInterval) (ht : dartHeight h d t ∈ I) {w : V} (hw : w ∈ (dartEdge d : Sym2 V))
    (hwI : h w ∈ I) :
    preimageInducedEquiv G h I hcov (ZerothHomotopy.mk ⟨edgePoint G d t, ht⟩) =
      (G.induce (h ⁻¹' (I : Set ℝ))).connectedComponentMk ⟨w, hwI⟩ := by
  show cellInducedEquiv G h I hcov (preimageComponentsEquiv G h I _) = _
  rw [preimageComponentsEquiv_mk_edgePoint]
  exact cellInducedEquiv_inr G h I hcov _ (w := ⟨w, hwI⟩) hw

end coverage

section full

variable {V : Type*} (G : SimpleGraph V) (h : V → ℝ)

theorem endpointCoverage_top : EndpointCoverage G h ⊤ := fun e _ => by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  exact ⟨d.fst, fst_mem_dartEdge d, trivial⟩

/-- **Full interval.** Through the full incidence graph, the comparison agrees with
`componentsEquiv` of the whole realization. -/
theorem full_componentsEquiv
    (c : ZerothHomotopy {p : Realization G // plHeight G h p ∈ (⊤ : OpenInterval)}) :
    componentsEquiv G (TDA.Reeb.componentMap ⟨Subtype.val, continuous_subtype_val⟩ c) =
      (preimageInducedEquiv G h ⊤ (endpointCoverage_top G h) c).map
        (Embedding.induce (G := G) _).toHom := by
  induction c using ZerothHomotopy.rec with
  | mk x =>
    obtain ⟨p, hp⟩ := x
    induction p using ind G with
    | vertex v =>
      rw [preimageInducedEquiv_mk_vertex G h ⊤ _ v hp]
      rfl
    | edgePoint d t =>
      rw [preimageInducedEquiv_mk_edgePoint G h ⊤ _ d t hp (fst_mem_dartEdge d) trivial]
      rfl

end full

end

end TDA.Reeb.GraphPL
