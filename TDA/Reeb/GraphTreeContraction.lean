import TDA.Reeb.GraphCycleObstruction
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Algebra.Algebra

/-!
# Contractible realizations of finite trees

For `V : Type u`, `G : SimpleGraph V` and a vertex `ℓ`, `deleteVertexInclusion G ℓ` is the map of
realizations induced by the embedding of the graph `G.induce {ℓ}ᶜ` induced on the other vertices.
Let `ℓ` be a leaf with neighbour `m`: `G.Adj ℓ m`, and every neighbour of `ℓ` is `m`. The leaf
collapse `leafCollapse` sends `ℓ` and every point of the edge `ℓ — m` to `m` and every other vertex
and edge point to itself. Collapsing after including is the identity
(`leafCollapse_comp_deleteVertexInclusion`). Including after collapsing is homotopic to the identity
by the leaf slide `leafHomotopy`: at time `s` the leaf sits at parameter `s` of the dart `ℓ → m`,
the leaf edge runs from that point to `m`, and every other vertex and edge point is fixed. Hence
`leafHomotopyEquiv` is a homotopy equivalence from the realization of `G` to that of
`G.induce {ℓ}ᶜ`. The leaf step uses no finiteness.

The slide is the continuous lift (`TDA.Reeb.GraphRealization.continuousLift`) of vertex tracks and
curried edge tracks into `C(unitInterval, Realization G)`, uncurried by
`ContinuousMap.continuous_uncurry_of_continuous` because the unit interval is locally compact. No
product of quotient maps is used.

## Finite trees

A tree with at least two vertices, finitely many, has a leaf
(`SimpleGraph.IsTree.exists_ne_and_degree_eq_one`), and deleting a leaf leaves a tree
(`SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`, `SimpleGraph.IsAcyclic.induce`).
A tree with one vertex has no edge, so its realization is a point. Induction on the number of
vertices shows that the realization of a tree on a finite vertex type is contractible
(`contractibleSpace_realization_of_isTree`), hence simply connected
(`simplyConnectedSpace_realization_of_isTree`). With the necessary condition
`TDA.Reeb.GraphCycleObstruction.isTree_of_simplyConnectedSpace`, a graph on a finite vertex type is
a tree exactly when its realization is simply connected
(`isTree_iff_simplyConnectedSpace_realization`), and exactly when its realization is contractible
(`isTree_iff_contractibleSpace_realization`). On an empty vertex type both sides are false. Trees on
infinite vertex types are outside these statements.

## Source

Adapted from `uda-lab/reeb-ordering`, `ReebOrdering/GraphRealisation.lean` at commit
`aa7d10f4f7dc0474b76f17ea81afcab5a230d521` (blob `6b79160f368a9d6fd63f2d52f1db4d9c5697cfa8`),
Copyright 2026 Tomoki Uda, licensed under the Apache License, Version 2.0. The adapted declarations,
with source names and lines, are `deleteVertexInclusion` (`leafIncl`, 473–474), `leafCollapse` with
its evaluation lemmas (`leafCollapse`, `leafCollapseVertex`, `leafCollapseEdge` and their lemmas,
388–491), `leafCollapse_comp_deleteVertexInclusion` (`leafCollapse_comp_leafIncl`, 498–527),
`leafHomotopy` (`leafDart`, `leafHomotopy`, `leafHomotopyVertex`, `leafHomotopyEdge` and their
lemmas, 372–386 and 529–738), `leafHomotopyEquiv` (740–748),
`contractibleSpace_realization_of_isTree` (`contractibleSpace_realisation_of_isTree`, 750–799),
`simplyConnectedSpace_realization_of_isTree` (`simplyConnectedSpace_of_isTree`, 801–804) and
`isTree_iff_simplyConnectedSpace_realization`
(`SimpleGraph.isTree_iff_simplyConnectedSpace_realisation`, 812–815). Changes: names; public
visibility of the inclusion, collapse, slide and equivalence; the leaf dart oriented away from the
leaf (the source's `leafDart` is `m → ℓ`), and edge tracks chosen by whether a dart leaves or enters
the leaf rather than by equality with the leaf dart; continuity of the slide through curried edge
tracks in place of the source's `liftProd` and `continuous_liftProd` (112–153), which rest on a
product-of-quotient-maps lemma absent here; and the induction stated for `n + 1` vertices.
`isTree_iff_contractibleSpace_realization` and the evaluation lemmas of the inclusion and the slide
are new. The source's Hasse-order result is not ported. The source is not imported.
-/

open SimpleGraph unitInterval Topology
open scoped ContinuousMap

namespace TDA.Reeb.GraphTreeContraction

open TDA.Reeb.GraphRealization TDA.Reeb.GraphCycleObstruction

universe u

noncomputable section

variable {V : Type u} (G : SimpleGraph V)

/-! ### Deleting a vertex -/

/-- The inclusion of the realization of the graph induced on the complement of `ℓ`. -/
def deleteVertexInclusion (ℓ : V) : C(Realization (G.induce ({ℓ}ᶜ : Set V)), Realization G) :=
  realizationMap (Embedding.induce ({ℓ}ᶜ : Set V)).toHom

@[simp] theorem deleteVertexInclusion_vertex (ℓ : V) (v : ({ℓ}ᶜ : Set V)) :
    deleteVertexInclusion G ℓ (vertex _ v) = vertex G v := rfl

@[simp] theorem deleteVertexInclusion_edgePoint (ℓ : V) (d : (G.induce ({ℓ}ᶜ : Set V)).Dart)
    (t : unitInterval) :
    deleteVertexInclusion G ℓ (edgePoint _ d t) =
      edgePoint G ⟨(d.fst.1, d.snd.1), d.adj⟩ t := rfl

/-- A dart avoiding `ℓ`, as a dart of the induced graph. -/
private def restrictDart {ℓ : V} (d : G.Dart) (h₁ : d.fst ≠ ℓ) (h₂ : d.snd ≠ ℓ) :
    (G.induce ({ℓ}ᶜ : Set V)).Dart :=
  ⟨(⟨d.fst, h₁⟩, ⟨d.snd, h₂⟩), d.adj⟩

/-! ### The leaf collapse -/

section collapse

variable {G} {ℓ m : V} (hadj : G.Adj ℓ m) (huniq : ∀ w, G.Adj ℓ w → w = m)

open Classical in
private def collapseVertex (v : V) : Realization (G.induce ({ℓ}ᶜ : Set V)) :=
  if h : v = ℓ then vertex _ ⟨m, hadj.ne'⟩ else vertex _ ⟨v, h⟩

open Classical in
private def collapseEdge (d : G.Dart) : C(unitInterval, Realization (G.induce ({ℓ}ᶜ : Set V))) :=
  if h : d.fst ≠ ℓ ∧ d.snd ≠ ℓ then
    ⟨edgePoint _ (restrictDart G d h.1 h.2), continuous_edgePoint _ _⟩
  else ContinuousMap.const _ (vertex _ ⟨m, hadj.ne'⟩)

private theorem collapseEdge_of_ne (d : G.Dart) (h₁ : d.fst ≠ ℓ) (h₂ : d.snd ≠ ℓ)
    (t : unitInterval) :
    collapseEdge hadj d t = edgePoint _ (restrictDart G d h₁ h₂) t := by
  simp [collapseEdge, h₁, h₂]

private theorem collapseEdge_of_not (d : G.Dart) (h : ¬ (d.fst ≠ ℓ ∧ d.snd ≠ ℓ))
    (t : unitInterval) : collapseEdge hadj d t = vertex _ ⟨m, hadj.ne'⟩ := by
  simp only [collapseEdge, dif_neg h, ContinuousMap.const_apply]

private theorem collapseEdge_symm (d : G.Dart) (t : unitInterval) :
    collapseEdge hadj d.symm (σ t) = collapseEdge hadj d t := by
  by_cases h : d.fst ≠ ℓ ∧ d.snd ≠ ℓ
  · rw [collapseEdge_of_ne hadj d.symm h.2 h.1, collapseEdge_of_ne hadj d h.1 h.2]
    exact edgePoint_symm _ (restrictDart G d h.1 h.2) t
  · rw [collapseEdge_of_not hadj d.symm (fun h' => h ⟨h'.2, h'.1⟩), collapseEdge_of_not hadj d h]

include huniq in
private theorem collapseEdge_zero (d : G.Dart) :
    collapseEdge hadj d 0 = collapseVertex hadj d.fst := by
  by_cases h : d.fst ≠ ℓ ∧ d.snd ≠ ℓ
  · rw [collapseEdge_of_ne hadj d h.1 h.2, edgePoint_zero]
    simp [collapseVertex, h.1, restrictDart]
  · rw [collapseEdge_of_not hadj d h]
    by_cases hf : d.fst = ℓ
    · simp [collapseVertex, hf]
    · have hs : d.snd = ℓ := by
        by_contra hs
        exact h ⟨hf, hs⟩
      have hfm : d.fst = m := huniq d.fst (hs ▸ d.adj.symm)
      simp only [collapseVertex, dif_neg hf]
      exact congrArg (vertex _) (Subtype.ext hfm.symm)

/-- The leaf collapse: for a vertex `ℓ` whose only neighbour is `m`, the map sending `ℓ` and the
edge `ℓ — m` to `m`, and every other cell to itself. -/
def leafCollapse : C(Realization G, Realization (G.induce ({ℓ}ᶜ : Set V))) :=
  continuousLift G (collapseVertex hadj) (collapseEdge hadj) (collapseEdge_symm hadj)
    (collapseEdge_zero hadj huniq)

theorem leafCollapse_vertex_self :
    leafCollapse hadj huniq (vertex G ℓ) = vertex _ ⟨m, hadj.ne'⟩ := by
  simp [leafCollapse, collapseVertex]

theorem leafCollapse_vertex_of_ne {v : V} (h : v ≠ ℓ) :
    leafCollapse hadj huniq (vertex G v) = vertex _ ⟨v, h⟩ := by
  simp [leafCollapse, collapseVertex, h]

theorem leafCollapse_edgePoint_of_ne (d : G.Dart) (h₁ : d.fst ≠ ℓ) (h₂ : d.snd ≠ ℓ)
    (t : unitInterval) :
    leafCollapse hadj huniq (edgePoint G d t) =
      edgePoint _ ⟨(⟨d.fst, h₁⟩, ⟨d.snd, h₂⟩), d.adj⟩ t :=
  collapseEdge_of_ne hadj d h₁ h₂ t

theorem leafCollapse_edgePoint_of_eq (d : G.Dart) (h : d.fst = ℓ ∨ d.snd = ℓ)
    (t : unitInterval) :
    leafCollapse hadj huniq (edgePoint G d t) = vertex _ ⟨m, hadj.ne'⟩ :=
  collapseEdge_of_not hadj d (fun h' => h.elim h'.1 h'.2) t

/-- Collapsing after including the induced realization is the identity. -/
theorem leafCollapse_comp_deleteVertexInclusion :
    (leafCollapse hadj huniq).comp (deleteVertexInclusion G ℓ) = ContinuousMap.id _ := by
  refine hom_ext _ (fun v => ?_) fun d t => ?_
  · exact leafCollapse_vertex_of_ne hadj huniq v.2
  · exact leafCollapse_edgePoint_of_ne hadj huniq ⟨(d.fst.1, d.snd.1), d.adj⟩ d.fst.2 d.snd.2 t

end collapse

/-! ### The sliding homotopy -/

section homotopy

variable {G} {ℓ m : V} (hadj : G.Adj ℓ m) (huniq : ∀ w, G.Adj ℓ w → w = m)

include huniq in
/-- A dart leaving the leaf is the leaf dart `ℓ → m`. -/
private theorem dart_eq_of_fst_eq {d : G.Dart} (hd : d.fst = ℓ) : d = ⟨(ℓ, m), hadj⟩ :=
  Dart.ext _ _ (Prod.ext hd (huniq _ (hd ▸ d.adj)))

include huniq in
/-- A dart entering the leaf starts at `m`. -/
private theorem fst_eq_of_snd_eq {d : G.Dart} (hd : d.snd = ℓ) : d.fst = m :=
  huniq _ (hd ▸ d.adj.symm)

open Classical in
/-- The edge parameter of the slide at time `s`: `t ↦ 1 - (1 - t)(1 - s)` on a dart leaving `ℓ`,
`t ↦ t (1 - s)` on a dart entering `ℓ`, and `t ↦ t` on every other dart. -/
private def slideParam (ℓ : V) (d : G.Dart) : C(unitInterval × unitInterval, unitInterval) :=
  if d.fst = ℓ then
    ⟨fun p => σ (σ p.1 * σ p.2), continuous_symm.comp (continuous_mul.comp
      ((continuous_symm.comp continuous_fst).prodMk (continuous_symm.comp continuous_snd)))⟩
  else if d.snd = ℓ then
    ⟨fun p => p.1 * σ p.2, continuous_mul.comp
      (continuous_fst.prodMk (continuous_symm.comp continuous_snd))⟩
  else ContinuousMap.fst

private theorem slideParam_of_fst_eq {d : G.Dart} (hd : d.fst = ℓ) (t s : unitInterval) :
    slideParam ℓ d (t, s) = σ (σ t * σ s) := by
  simp [slideParam, hd]

private theorem slideParam_of_snd_eq {d : G.Dart} (hd : d.snd = ℓ) (t s : unitInterval) :
    slideParam ℓ d (t, s) = t * σ s := by
  have hf : d.fst ≠ ℓ := fun hf => d.adj.ne (hf.trans hd.symm)
  simp [slideParam, hd, hf]

private theorem slideParam_of_ne {d : G.Dart} (h₁ : d.fst ≠ ℓ) (h₂ : d.snd ≠ ℓ)
    (t s : unitInterval) : slideParam ℓ d (t, s) = t := by
  simp [slideParam, h₁, h₂]

open Classical in
/-- The track of a vertex: the leaf moves along its edge to `m`, every other vertex stays. -/
private def slideVertex (v : V) : C(unitInterval, Realization G) :=
  if v = ℓ then ⟨edgePoint G ⟨(ℓ, m), hadj⟩, continuous_edgePoint _ _⟩
  else ContinuousMap.const _ (vertex G v)

private theorem slideVertex_self (s : unitInterval) :
    slideVertex hadj ℓ s = edgePoint G ⟨(ℓ, m), hadj⟩ s := by
  simp [slideVertex]

private theorem slideVertex_of_ne {v : V} (h : v ≠ ℓ) (s : unitInterval) :
    slideVertex hadj v s = vertex G v := by
  simp [slideVertex, h]

/-- The track of an edge point, curried in the time parameter. -/
private def slideEdge (ℓ : V) (d : G.Dart) : C(unitInterval, C(unitInterval, Realization G)) :=
  (ContinuousMap.comp ⟨edgePoint G d, continuous_edgePoint _ _⟩ (slideParam ℓ d)).curry

private theorem slideEdge_apply (d : G.Dart) (t s : unitInterval) :
    slideEdge ℓ d t s = edgePoint G d (slideParam ℓ d (t, s)) := rfl

private theorem slideEdge_symm (d : G.Dart) (t : unitInterval) :
    slideEdge ℓ d.symm (σ t) = slideEdge ℓ d t := by
  ext s
  rw [slideEdge_apply, slideEdge_apply]
  by_cases h₁ : d.fst = ℓ
  · rw [slideParam_of_snd_eq (d := d.symm) h₁, slideParam_of_fst_eq h₁,
      ← edgePoint_symm G d, symm_symm]
  · by_cases h₂ : d.snd = ℓ
    · rw [slideParam_of_fst_eq (d := d.symm) h₂, slideParam_of_snd_eq h₂, symm_symm,
        edgePoint_symm]
    · rw [slideParam_of_ne (d := d.symm) h₂ h₁, slideParam_of_ne h₁ h₂, edgePoint_symm]

include huniq in
private theorem slideEdge_zero (d : G.Dart) : slideEdge ℓ d 0 = slideVertex hadj d.fst := by
  ext s
  rw [slideEdge_apply]
  by_cases h₁ : d.fst = ℓ
  · rw [slideParam_of_fst_eq h₁, symm_zero, one_mul, symm_symm, h₁, slideVertex_self,
      dart_eq_of_fst_eq hadj huniq h₁]
  · rw [slideVertex_of_ne hadj h₁]
    by_cases h₂ : d.snd = ℓ
    · rw [slideParam_of_snd_eq h₂, zero_mul, edgePoint_zero]
    · rw [slideParam_of_ne h₁ h₂, edgePoint_zero]

/-- The slide as a map into paths of the realization. -/
private def slide : C(Realization G, C(unitInterval, Realization G)) :=
  continuousLift G (slideVertex hadj) (slideEdge ℓ) slideEdge_symm (slideEdge_zero hadj huniq)

private theorem slide_zero (x : Realization G) : slide hadj huniq x 0 = x := by
  induction x using ind G with
  | vertex v =>
    change slideVertex hadj v 0 = _
    by_cases h : v = ℓ
    · subst h
      rw [slideVertex_self, edgePoint_zero]
    · rw [slideVertex_of_ne hadj h]
  | edgePoint d t =>
    change slideEdge ℓ d t 0 = _
    rw [slideEdge_apply]
    by_cases h₁ : d.fst = ℓ
    · rw [slideParam_of_fst_eq h₁, symm_zero, mul_one, symm_symm]
    · by_cases h₂ : d.snd = ℓ
      · rw [slideParam_of_snd_eq h₂, symm_zero, mul_one]
      · rw [slideParam_of_ne h₁ h₂]

private theorem slide_one (x : Realization G) :
    slide hadj huniq x 1 = deleteVertexInclusion G ℓ (leafCollapse hadj huniq x) := by
  induction x using ind G with
  | vertex v =>
    change slideVertex hadj v 1 = _
    by_cases h : v = ℓ
    · subst h
      rw [slideVertex_self, edgePoint_one, leafCollapse_vertex_self, deleteVertexInclusion_vertex]
    · rw [slideVertex_of_ne hadj h, leafCollapse_vertex_of_ne hadj huniq h,
        deleteVertexInclusion_vertex]
  | edgePoint d t =>
    change slideEdge ℓ d t 1 = _
    rw [slideEdge_apply]
    by_cases h₁ : d.fst = ℓ
    · rw [slideParam_of_fst_eq h₁, symm_one, mul_zero, symm_zero, edgePoint_one,
        leafCollapse_edgePoint_of_eq hadj huniq d (.inl h₁), deleteVertexInclusion_vertex,
        dart_eq_of_fst_eq hadj huniq h₁]
    · by_cases h₂ : d.snd = ℓ
      · rw [slideParam_of_snd_eq h₂, symm_one, mul_zero, edgePoint_zero,
          leafCollapse_edgePoint_of_eq hadj huniq d (.inr h₂), deleteVertexInclusion_vertex,
          fst_eq_of_snd_eq huniq h₂]
      · rw [slideParam_of_ne h₁ h₂, leafCollapse_edgePoint_of_ne hadj huniq d h₁ h₂,
          deleteVertexInclusion_edgePoint]

/-- The leaf slide: at time `s` the leaf `ℓ` sits at parameter `s` on the dart `ℓ → m`, the leaf
edge is the segment from there to `m`, and every other cell is fixed. It runs from the identity
to the collapse followed by the inclusion. -/
def leafHomotopy :
    (ContinuousMap.id (Realization G)).Homotopy
      ((deleteVertexInclusion G ℓ).comp (leafCollapse hadj huniq)) where
  toFun p := slide hadj huniq p.2 p.1
  continuous_toFun :=
    (ContinuousMap.continuous_uncurry_of_continuous (slide hadj huniq)).comp continuous_swap
  map_zero_left := slide_zero hadj huniq
  map_one_left := slide_one hadj huniq

theorem leafHomotopy_vertex_self (s : unitInterval) :
    leafHomotopy hadj huniq (s, vertex G ℓ) = edgePoint G ⟨(ℓ, m), hadj⟩ s :=
  slideVertex_self hadj s

theorem leafHomotopy_vertex_of_ne {v : V} (h : v ≠ ℓ) (s : unitInterval) :
    leafHomotopy hadj huniq (s, vertex G v) = vertex G v :=
  slideVertex_of_ne hadj h s

theorem leafHomotopy_edgePoint_of_fst_eq {d : G.Dart} (hd : d.fst = ℓ) (s t : unitInterval) :
    leafHomotopy hadj huniq (s, edgePoint G d t) = edgePoint G d (σ (σ t * σ s)) :=
  (congrArg (edgePoint G d) (slideParam_of_fst_eq hd t s) :)

theorem leafHomotopy_edgePoint_of_snd_eq {d : G.Dart} (hd : d.snd = ℓ) (s t : unitInterval) :
    leafHomotopy hadj huniq (s, edgePoint G d t) = edgePoint G d (t * σ s) :=
  (congrArg (edgePoint G d) (slideParam_of_snd_eq hd t s) :)

theorem leafHomotopy_edgePoint_of_ne {d : G.Dart} (h₁ : d.fst ≠ ℓ) (h₂ : d.snd ≠ ℓ)
    (s t : unitInterval) : leafHomotopy hadj huniq (s, edgePoint G d t) = edgePoint G d t :=
  (congrArg (edgePoint G d) (slideParam_of_ne h₁ h₂ t s) :)

/-- **Leaf removal.** The leaf collapse is a homotopy equivalence with homotopy inverse the
inclusion of the realization of the graph induced on the other vertices. -/
def leafHomotopyEquiv : Realization G ≃ₕ Realization (G.induce ({ℓ}ᶜ : Set V)) where
  toFun := leafCollapse hadj huniq
  invFun := deleteVertexInclusion G ℓ
  left_inv := ⟨(leafHomotopy hadj huniq).symm⟩
  right_inv := by rw [leafCollapse_comp_deleteVertexInclusion hadj huniq]

end homotopy

/-! ### Finite trees -/

/-- **Finite trees.** The realization of a tree on a finite vertex type is contractible. -/
theorem contractibleSpace_realization_of_isTree [Finite V] (h : G.IsTree) :
    ContractibleSpace (Realization G) := by
  suffices key : ∀ (n : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V), Nat.card V = n + 1 →
      G.IsTree → ContractibleSpace (Realization G) by
    have hpos : 0 < Nat.card V := Finite.card_pos_iff.2 h.connected.nonempty
    exact key (Nat.card V - 1) G (by omega) h
  intro n
  induction n with
  | zero =>
    intro V _ G hcard h
    have : Subsingleton V := Finite.card_le_one_iff_subsingleton.1 hcard.le
    have : Nonempty V := h.connected.nonempty
    have : Subsingleton (Realization G) := by
      refine ⟨fun x y => ?_⟩
      have key : ∀ z : Realization G, z = vertex G (Classical.arbitrary V) := fun z => by
        induction z using ind G with
        | vertex v => exact congrArg _ (Subsingleton.elim _ _)
        | edgePoint d t => exact (d.adj.ne (Subsingleton.elim _ _)).elim
      rw [key x, key y]
    infer_instance
  | succ n ih =>
    intro V _ G hcard h
    classical
    have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    have : G.LocallyFinite := fun _ => Fintype.ofFinite _
    obtain ⟨ℓ, -, -, hdeg, -⟩ := h.exists_ne_and_degree_eq_one
    obtain ⟨m, hadj, huniq⟩ := degree_eq_one_iff_existsUnique_adj.1 hdeg
    have htree : (G.induce ({ℓ}ᶜ : Set V)).IsTree :=
      ⟨h.connected.induce_compl_singleton_of_degree_eq_one hdeg, h.isAcyclic.induce _⟩
    have hcard' : Nat.card ({ℓ}ᶜ : Set V) = n + 1 := by
      rw [Nat.card_coe_set_eq]
      exact Set.ncard_compl_of_ncard_eq_add _ (by rw [Set.ncard_singleton]; omega)
    have := ih (G.induce ({ℓ}ᶜ : Set V)) hcard' htree
    exact (leafHomotopyEquiv hadj huniq).contractibleSpace

/-- The realization of a tree on a finite vertex type is simply connected. -/
theorem simplyConnectedSpace_realization_of_isTree [Finite V] (h : G.IsTree) :
    SimplyConnectedSpace (Realization G) :=
  have := contractibleSpace_realization_of_isTree G h
  inferInstance

/-- **Tree criterion.** A graph on a finite vertex type is a tree exactly when its realization is
simply connected. -/
theorem isTree_iff_simplyConnectedSpace_realization [Finite V] :
    G.IsTree ↔ SimplyConnectedSpace (Realization G) :=
  ⟨simplyConnectedSpace_realization_of_isTree G, isTree_of_simplyConnectedSpace G⟩

/-- A graph on a finite vertex type is a tree exactly when its realization is contractible. -/
theorem isTree_iff_contractibleSpace_realization [Finite V] :
    G.IsTree ↔ ContractibleSpace (Realization G) :=
  ⟨contractibleSpace_realization_of_isTree G, fun _ =>
    isTree_of_simplyConnectedSpace G inferInstance⟩

end

end TDA.Reeb.GraphTreeContraction
