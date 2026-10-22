import TDA.Reeb.GraphPLComponents
import TDA.Reeb.GraphPLHeightExamples
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Fixtures for graph components of piecewise-linear height preimages

Acceptance fixtures for `TDA.Reeb.GraphPLComponents`:

* **Empty interval and empty vertex type.** For every graph, the empty interval has no node, no
  incidence component and no preimage path component. For every graph on an empty vertex type
  (`[IsEmpty V]`), there is no node over any interval, and the preimage has no path component; the
  latter is obtained through the comparison, and also follows from the emptiness of the realization
  of an empty vertex type.
* **One edge of heights `0` and `2`.** Over every interval containing `1` but neither `0` nor `2`,
  instantiated at `(0, 2)` and `(1/2, 3/2)`: no vertex survives, exactly one unoriented edge is
  active, the only node is that edge node, and the preimage has exactly one path component. The
  two darts do not give two components: edge points of both orientations lie in one class, and at
  `t = 1/3` they are two distinct points of one class. Endpoint coverage fails, the induced graph
  on the surviving vertices has no component, and no equivalence of the preimage path components
  with its components exists, which refutes the unconditional vertex-only comparison.
* **Horizontal edge.** With constant height `1`, over `(0, 2)` every node lies in the class of the
  edge node and the preimage has one path component; over `(2, 3)` both the preimage and the node
  type are empty.
* **Ray.** Over `(1, ∞)`, exactly one endpoint survives and the edge is truncated to the parameters
  above `1/2`. Endpoint coverage holds, the preimage has one path component, and every truncated
  edge point lies in the class of the surviving vertex.
* **4-cycle.** On `cycleGraph 4` with heights `0, 1, 2, 1` and `I = (1/2, 3/2)`, the surviving
  vertices are exactly `1` and `3`. Their incidence classes are distinct, by a side function that
  every adjacency preserves, and every class is one of them; the preimage classes `x1` and
  `x3` of the two vertices are therefore distinct and exhaustive, and the edge points at parameter
  `3/4` of the darts `0 → 1` and `2 → 3` lie in the classes of `1` and `3`.
* **Proper inclusion.** For `I < J = (-1/2, 5/2)`, the two classes merge on both sides of the
  naturality square: through `TDA.Reeb.componentMap (preimageInclusion …)`, through
  `ConnectedComponent.map (cellInclusion …)`, and through the packaged functors.
* **Vertex-only corollary.** It holds on the 4-cycle, where the two induced-graph classes of `1`
  and `3` are distinct, and on the ray; the single edge above is the counterexample to its
  unconditional version.

The comparison over the full interval with the realization's `componentsEquiv` is the production
theorem `TDA.Reeb.GraphPL.full_componentsEquiv`. The short name `d01` also occurs in
`TDA.Reeb.Examples.GraphRealization`.
-/

open SimpleGraph Topology Set CategoryTheory

/-- The reversal of the unit interval; `open unitInterval` would make `I` a token. -/
local notation "σ" => unitInterval.symm

namespace TDA.Reeb.Examples.GraphPL

open TDA.Reeb.GraphRealization TDA.Reeb.GraphPL TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ edgeGraph_dart half edge_param_injective)

noncomputable section

/-! ### Empty interval and empty vertex type, for every graph -/

section General

variable {V : Type*} (G : SimpleGraph V) (h : V → ℝ)

/-- The empty interval: no node. -/
theorem cell_bot_isEmpty : IsEmpty (Cell G h ⊥) :=
  ⟨fun x => by
    rcases x with ⟨v, hv⟩ | ⟨e, d, -, t, -, -, ht⟩
    · exact hv
    · exact ht⟩

theorem cellComponents_bot_isEmpty : IsEmpty (cellGraph G h ⊥).ConnectedComponent :=
  haveI := cell_bot_isEmpty G h
  inferInstance

/-- The empty interval on the preimage side, from `intervalComponents_obj_bot_isEmpty`. -/
theorem preimage_bot_isEmpty :
    IsEmpty (ZerothHomotopy {p : Realization G // plHeight G h p ∈ (⊥ : OpenInterval)}) :=
  intervalComponents_obj_bot_isEmpty (plHeight G h)

/-- The empty graph, on an empty vertex type: no node over any interval. -/
theorem cell_isEmpty_of_isEmpty [IsEmpty V] (I : OpenInterval) : IsEmpty (Cell G h I) :=
  ⟨fun x => by
    rcases x with ⟨v, -⟩ | ⟨e, -⟩
    · exact isEmptyElim v
    · obtain ⟨d, -⟩ := exists_dartEdge_eq e
      exact isEmptyElim d.fst⟩

theorem preimage_isEmpty_of_isEmpty [IsEmpty V] (I : OpenInterval) :
    IsEmpty (ZerothHomotopy {p : Realization G // plHeight G h p ∈ I}) :=
  (preimageComponentsEquiv G h I).isEmpty_congr.2
    (haveI := cell_isEmpty_of_isEmpty G h I
     inferInstance)

end General

/-! ### One edge of heights `0` and `2` over an interval containing `1` but neither endpoint -/

section SingleEdge

variable {I : OpenInterval}

theorem single_no_vertex (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) :
    IsEmpty {v : Bool // h02 v ∈ I} :=
  ⟨fun ⟨v, hv⟩ => by cases v; exacts [h0 hv, h2 hv]⟩

theorem single_half_mem (h1 : (1 : ℝ) ∈ I) : dartHeight h02 d₀ half ∈ I := by
  rw [dartHeight_d₀, coe_half]
  convert h1 using 1
  norm_num

theorem single_active (h1 : (1 : ℝ) ∈ I) : EdgeActive edgeGraph h02 I (dartEdge d₀) :=
  edgeActive_dartEdge_of_mem (single_half_mem h1)

/-- Exactly one active unoriented edge: opposite darts give the same edge. -/
theorem single_activeEdge_eq (h1 : (1 : ℝ) ∈ I)
    (e : {e : edgeGraph.edgeSet // EdgeActive edgeGraph h02 I e}) :
    e = ⟨dartEdge d₀, single_active h1⟩ :=
  Subtype.ext (edgeGraph_edge_eq e.1)

theorem single_cell_eq (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) (h1 : (1 : ℝ) ∈ I)
    (x : Cell edgeGraph h02 I) : x = Sum.inr ⟨dartEdge d₀, single_active h1⟩ := by
  rcases x with v | e
  · exact (single_no_vertex h0 h2).elim v
  · exact congrArg Sum.inr (single_activeEdge_eq h1 e)

theorem single_cellComponents_subsingleton (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I)
    (h1 : (1 : ℝ) ∈ I) : Subsingleton (cellGraph edgeGraph h02 I).ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun x y => by
    rw [single_cell_eq h0 h2 h1 x, single_cell_eq h0 h2 h1 y]⟩

theorem single_card_cell (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) (h1 : (1 : ℝ) ∈ I) :
    Nat.card (cellGraph edgeGraph h02 I).ConnectedComponent = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨single_cellComponents_subsingleton h0 h2 h1,
    ⟨(cellGraph edgeGraph h02 I).connectedComponentMk
      (Sum.inr ⟨dartEdge d₀, single_active h1⟩)⟩⟩

/-- Exactly one preimage path component. -/
theorem single_card_preimage (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) (h1 : (1 : ℝ) ∈ I) :
    Nat.card (ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ I}) = 1 :=
  (Nat.card_congr (preimageComponentsEquiv edgeGraph h02 I)).trans (single_card_cell h0 h2 h1)

/-- Opposite darts do not give two components. -/
theorem single_opposite_darts (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) (h1 : (1 : ℝ) ∈ I)
    {s t : unitInterval} (hs : dartHeight h02 d₀ s ∈ I) (ht : dartHeight h02 d₀.symm t ∈ I) :
    (ZerothHomotopy.mk ⟨edgePoint edgeGraph d₀ s, hs⟩ :
        ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ I}) =
      ZerothHomotopy.mk ⟨edgePoint edgeGraph d₀.symm t, ht⟩ :=
  (preimageComponentsEquiv edgeGraph h02 I).injective
    (@Subsingleton.elim _ (single_cellComponents_subsingleton h0 h2 h1) _ _)

theorem single_not_endpointCoverage (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) (h1 : (1 : ℝ) ∈ I) :
    ¬ EndpointCoverage edgeGraph h02 I := fun hcov => by
  obtain ⟨v, -, hv⟩ := hcov (dartEdge d₀) (single_active h1)
  exact (single_no_vertex h0 h2).false ⟨v, hv⟩

theorem single_induce_isEmpty (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) :
    IsEmpty (edgeGraph.induce (h02 ⁻¹' (I : Set ℝ))).ConnectedComponent :=
  haveI : IsEmpty ↥(h02 ⁻¹' (I : Set ℝ)) := single_no_vertex h0 h2
  inferInstance

/-- The unconditional vertex-only comparison fails: the preimage has a path component, while the
graph induced on the surviving vertices has none. -/
theorem single_no_vertexOnly_equiv (h0 : (0 : ℝ) ∉ I) (h2 : (2 : ℝ) ∉ I) (h1 : (1 : ℝ) ∈ I) :
    IsEmpty (ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ I} ≃
      (edgeGraph.induce (h02 ⁻¹' (I : Set ℝ))).ConnectedComponent) :=
  ⟨fun φ => (single_induce_isEmpty h0 h2).false
    (φ (ZerothHomotopy.mk ⟨edgePoint edgeGraph d₀ half, single_half_mem h1⟩))⟩

end SingleEdge

section SingleEdgeCases

theorem ioo_zero_two_zero : (0 : ℝ) ∉ ioo 0 2 := by rw [mem_ioo]; norm_num
theorem ioo_zero_two_two : (2 : ℝ) ∉ ioo 0 2 := by rw [mem_ioo]; norm_num
theorem ioo_zero_two_one : (1 : ℝ) ∈ ioo 0 2 := by rw [mem_ioo]; norm_num
theorem ioo_half_zero : (0 : ℝ) ∉ ioo (1 / 2) (3 / 2) := by rw [mem_ioo]; norm_num
theorem ioo_half_two : (2 : ℝ) ∉ ioo (1 / 2) (3 / 2) := by rw [mem_ioo]; norm_num
theorem ioo_half_one : (1 : ℝ) ∈ ioo (1 / 2) (3 / 2) := by rw [mem_ioo]; norm_num

/-- `I = (0, 2)`: no surviving vertex. -/
theorem zeroTwo_no_vertex : IsEmpty {v : Bool // h02 v ∈ ioo 0 2} :=
  single_no_vertex ioo_zero_two_zero ioo_zero_two_two

/-- `I = (0, 2)`: exactly one active unoriented edge. -/
theorem zeroTwo_activeEdge_eq (e : {e : edgeGraph.edgeSet // EdgeActive edgeGraph h02 (ioo 0 2) e}) :
    e = ⟨dartEdge d₀, single_active ioo_zero_two_one⟩ :=
  single_activeEdge_eq ioo_zero_two_one e

/-- `I = (0, 2)`: exactly one preimage path component. -/
theorem zeroTwo_card_preimage :
    Nat.card (ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioo 0 2})
      = 1 :=
  single_card_preimage ioo_zero_two_zero ioo_zero_two_two ioo_zero_two_one

theorem zeroTwo_not_endpointCoverage : ¬ EndpointCoverage edgeGraph h02 (ioo 0 2) :=
  single_not_endpointCoverage ioo_zero_two_zero ioo_zero_two_two ioo_zero_two_one

theorem zeroTwo_no_vertexOnly_equiv :
    IsEmpty (ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioo 0 2} ≃
      (edgeGraph.induce (h02 ⁻¹' ((ioo 0 2 : OpenInterval) : Set ℝ))).ConnectedComponent) :=
  single_no_vertexOnly_equiv ioo_zero_two_zero ioo_zero_two_two ioo_zero_two_one

/-- `I = (1/2, 3/2)`: no surviving vertex. -/
theorem half_no_vertex : IsEmpty {v : Bool // h02 v ∈ ioo (1 / 2) (3 / 2)} :=
  single_no_vertex ioo_half_zero ioo_half_two

theorem half_activeEdge_eq
    (e : {e : edgeGraph.edgeSet // EdgeActive edgeGraph h02 (ioo (1 / 2) (3 / 2)) e}) :
    e = ⟨dartEdge d₀, single_active ioo_half_one⟩ :=
  single_activeEdge_eq ioo_half_one e

theorem half_card_preimage :
    Nat.card (ZerothHomotopy
      {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioo (1 / 2) (3 / 2)}) = 1 :=
  single_card_preimage ioo_half_zero ioo_half_two ioo_half_one

theorem half_not_endpointCoverage : ¬ EndpointCoverage edgeGraph h02 (ioo (1 / 2) (3 / 2)) :=
  single_not_endpointCoverage ioo_half_zero ioo_half_two ioo_half_one

theorem half_no_vertexOnly_equiv :
    IsEmpty (ZerothHomotopy
        {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioo (1 / 2) (3 / 2)} ≃
      (edgeGraph.induce
        (h02 ⁻¹' ((ioo (1 / 2) (3 / 2) : OpenInterval) : Set ℝ))).ConnectedComponent) :=
  single_no_vertexOnly_equiv ioo_half_zero ioo_half_two ioo_half_one

/-- The parameter `1/3`. -/
def third : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩

theorem third_mem : dartHeight h02 d₀ third ∈ ioo (1 / 2) (3 / 2) := by
  rw [dartHeight_d₀, mem_ioo]; show (1 / 2 : ℝ) < 2 * (1 / 3) ∧ 2 * (1 / 3) < (3 / 2 : ℝ)
  norm_num

theorem third_symm_mem : dartHeight h02 d₀.symm third ∈ ioo (1 / 2) (3 / 2) := by
  rw [dartHeight_d₀_symm, mem_ioo]; show (1 / 2 : ℝ) < 2 - 2 * (1 / 3) ∧ 2 - 2 * (1 / 3) < (3 / 2 : ℝ)
  norm_num

/-- The opposite darts at the parameter `1/3` give two distinct points... -/
theorem opposite_points_ne : edgePoint edgeGraph d₀ third ≠ edgePoint edgeGraph d₀.symm third := by
  intro hpt
  have hp : edgePoint edgeGraph d₀.symm third = edgePoint edgeGraph d₀ (σ third) := by
    rw [← edgePoint_symm edgeGraph d₀ (σ third), unitInterval.symm_symm]
  rw [hp] at hpt
  have := congrArg Subtype.val (edge_param_injective hpt)
  rw [unitInterval.coe_symm_eq] at this
  change (1 / 3 : ℝ) = 1 - 1 / 3 at this
  norm_num at this

/-- ...in one preimage path component. -/
theorem opposite_points_same_class :
    (ZerothHomotopy.mk ⟨edgePoint edgeGraph d₀ third, third_mem⟩ : ZerothHomotopy
        {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioo (1 / 2) (3 / 2)}) =
      ZerothHomotopy.mk ⟨edgePoint edgeGraph d₀.symm third, third_symm_mem⟩ :=
  single_opposite_darts ioo_half_zero ioo_half_two ioo_half_one third_mem third_symm_mem

end SingleEdgeCases

/-! ### A horizontal edge -/

section Horizontal

theorem plHeight_hconst (p : Realization edgeGraph) : plHeight edgeGraph hconst p = 1 := by
  induction p using ind edgeGraph with
  | vertex v => rfl
  | edgePoint d t => exact dartHeight_of_eq hconst rfl t

theorem horizontal_inside_mem (p : Realization edgeGraph) : plHeight edgeGraph hconst p ∈ ioo 0 2 := by
  rw [plHeight_hconst, mem_ioo]; norm_num

/-- Inside: every node lies in the class of the edge node. -/
theorem horizontal_cell_class (x : Cell edgeGraph hconst (ioo 0 2)) :
    (cellGraph edgeGraph hconst (ioo 0 2)).connectedComponentMk x =
      (cellGraph edgeGraph hconst (ioo 0 2)).connectedComponentMk
        (Sum.inr ⟨dartEdge d₀, horizontal_inside_active⟩) := by
  rcases x with ⟨v, hv⟩ | e
  · apply connectedComponentMk_inl_eq_inr
    cases v
    · exact fst_mem_dartEdge d₀
    · exact snd_mem_dartEdge d₀
  · exact congrArg _ (congrArg Sum.inr (Subtype.ext (edgeGraph_edge_eq e.1)))

theorem horizontal_inside_card_cell :
    Nat.card (cellGraph edgeGraph hconst (ioo 0 2)).ConnectedComponent = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨⟨ConnectedComponent.ind₂ fun x y => by
      rw [horizontal_cell_class x, horizontal_cell_class y]⟩,
    ⟨(cellGraph edgeGraph hconst (ioo 0 2)).connectedComponentMk
      (Sum.inr ⟨dartEdge d₀, horizontal_inside_active⟩)⟩⟩

/-- Inside: one connected edge component. -/
theorem horizontal_inside_card :
    Nat.card (ZerothHomotopy
      {p : Realization edgeGraph // plHeight edgeGraph hconst p ∈ ioo 0 2}) = 1 :=
  (Nat.card_congr (preimageComponentsEquiv edgeGraph hconst (ioo 0 2))).trans
    horizontal_inside_card_cell

/-- Outside: empty preimage. -/
theorem horizontal_outside_preimage_isEmpty :
    IsEmpty {p : Realization edgeGraph // plHeight edgeGraph hconst p ∈ ioo 2 3} :=
  ⟨fun ⟨p, hp⟩ => by
    rw [plHeight_hconst, mem_ioo] at hp
    norm_num at hp⟩

/-- Outside: empty cell graph. -/
theorem horizontal_outside_cell_isEmpty : IsEmpty (Cell edgeGraph hconst (ioo 2 3)) :=
  ⟨fun x => by
    rcases x with ⟨v, hv⟩ | ⟨e, he⟩
    · rw [mem_ioo] at hv
      norm_num [hconst] at hv
    · rw [edgeGraph_edge_eq e] at he
      exact horizontal_outside_inactive he⟩

end Horizontal

/-! ### A ray with exactly one surviving endpoint and a truncated edge -/

section Ray

theorem ray_true : h02 true ∈ ioi 1 := by rw [mem_ioi]; norm_num [h02]

theorem ray_false : h02 false ∉ ioi 1 := by rw [mem_ioi]; norm_num [h02]

/-- The edge is truncated: its points in the preimage are those of parameter above `1/2`. -/
theorem ray_truncated (t : unitInterval) :
    plHeight edgeGraph h02 (edgePoint edgeGraph d₀ t) ∈ ioi 1 ↔ 1 / 2 < (t : ℝ) := by
  rw [plHeight_edgePoint, dartHeight_d₀, mem_ioi]
  constructor <;> intro ht <;> linarith

theorem ray_endpointCoverage : EndpointCoverage edgeGraph h02 (ioi 1) := fun e _ => by
  rw [edgeGraph_edge_eq e]
  exact ⟨true, snd_mem_dartEdge d₀, ray_true⟩

/-- The only surviving vertex. -/
def rayVertex : ↥(h02 ⁻¹' ((ioi 1 : OpenInterval) : Set ℝ)) := ⟨true, ray_true⟩

theorem ray_vertex_eq (v : ↥(h02 ⁻¹' ((ioi 1 : OpenInterval) : Set ℝ))) : v = rayVertex := by
  obtain ⟨v, hv⟩ := v
  cases v
  · exact absurd hv ray_false
  · rfl

theorem ray_card_induced :
    Nat.card (edgeGraph.induce (h02 ⁻¹' ((ioi 1 : OpenInterval) : Set ℝ))).ConnectedComponent
      = 1 :=
  Nat.card_eq_one_iff_unique.2 ⟨⟨ConnectedComponent.ind₂ fun x y => by
      rw [ray_vertex_eq x, ray_vertex_eq y]⟩,
    ⟨(edgeGraph.induce _).connectedComponentMk rayVertex⟩⟩

/-- One preimage path component, through the vertex-only corollary. -/
theorem ray_card :
    Nat.card (ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioi 1})
      = 1 :=
  (Nat.card_congr (preimageInducedEquiv edgeGraph h02 (ioi 1) ray_endpointCoverage)).trans
    ray_card_induced

/-- A truncated edge point goes to the surviving endpoint's class. -/
theorem ray_edgePoint (t : unitInterval) (ht : dartHeight h02 d₀ t ∈ ioi 1) :
    preimageInducedEquiv edgeGraph h02 (ioi 1) ray_endpointCoverage
        (ZerothHomotopy.mk ⟨edgePoint edgeGraph d₀ t, ht⟩) =
      (edgeGraph.induce _).connectedComponentMk rayVertex :=
  preimageInducedEquiv_mk_edgePoint edgeGraph h02 (ioi 1) _ d₀ t ht (snd_mem_dartEdge d₀) ray_true

theorem ray_edge_class (t : unitInterval) (ht : dartHeight h02 d₀ t ∈ ioi 1) :
    (ZerothHomotopy.mk ⟨edgePoint edgeGraph d₀ t, ht⟩ :
        ZerothHomotopy {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioi 1}) =
      ZerothHomotopy.mk ⟨vertex edgeGraph true, ray_true⟩ :=
  (preimageInducedEquiv edgeGraph h02 (ioi 1) ray_endpointCoverage).injective
    ((ray_edgePoint t ht).trans
      (preimageInducedEquiv_mk_vertex edgeGraph h02 (ioi 1) _ true ray_true).symm)

end Ray

/-! ### The 4-cycle with heights `0, 1, 2, 1` -/

section Cycle

/-- The 4-cycle `0 — 1 — 2 — 3 — 0`. -/
abbrev C4 : SimpleGraph (Fin 4) := cycleGraph 4

/-- Heights `0, 1, 2, 1`. -/
def h4 : Fin 4 → ℝ := ![0, 1, 2, 1]

/-- `I = (1/2, 3/2)`. -/
abbrev I4 : OpenInterval := ioo (1 / 2) (3 / 2)

/-- `J = (-1/2, 5/2)`. -/
abbrev J4 : OpenInterval := ioo (-1 / 2) (5 / 2)

@[simp] theorem h4_zero : h4 0 = 0 := rfl

@[simp] theorem h4_one : h4 1 = 1 := rfl

@[simp] theorem h4_two : h4 2 = 2 := rfl

@[simp] theorem h4_three : h4 3 = 1 := rfl

theorem h4_mem_I4 {v : Fin 4} : h4 v ∈ I4 ↔ v = 1 ∨ v = 3 := by
  fin_cases v <;> norm_num [h4, mem_ioo] <;> decide

theorem h4_mem_J4 (v : Fin 4) : h4 v ∈ J4 := by
  fin_cases v <;> norm_num [h4, mem_ioo]

theorem I4_le_J4 : I4 ≤ J4 := OpenInterval.le_iff_subset.2 fun x hx => by
  obtain ⟨h₁, h₂⟩ := hx
  show (-1 / 2 : ℝ) < x ∧ x < 5 / 2
  constructor <;> linarith

/-- The inclusion is proper. -/
theorem I4_lt_J4 : I4 < J4 :=
  lt_of_le_of_ne I4_le_J4 fun hIJ => by
    have h0 : (0 : ℝ) ∈ J4 := by rw [mem_ioo]; norm_num
    rw [← hIJ, mem_ioo] at h0
    norm_num at h0

theorem one_mem_I4 : h4 1 ∈ I4 := h4_mem_I4.2 (.inl rfl)

theorem three_mem_I4 : h4 3 ∈ I4 := h4_mem_I4.2 (.inr rfl)

theorem C4_not_adj_one_three : ¬ C4.Adj 1 3 := by decide

theorem C4_adj_endpoint : ∀ a b : Fin 4, C4.Adj a b → (a = 1 ∨ a = 3) ∨ (b = 1 ∨ b = 3) := by
  decide

/-- Every edge of the 4-cycle has an endpoint `1` or `3`. -/
theorem C4_edge_endpoint (d : C4.Dart) :
    ∃ w : Fin 4, w ∈ (dartEdge d : Sym2 (Fin 4)) ∧ (w = 1 ∨ w = 3) := by
  rcases C4_adj_endpoint d.fst d.snd d.adj with hw | hw
  · exact ⟨d.fst, fst_mem_dartEdge d, hw⟩
  · exact ⟨d.snd, snd_mem_dartEdge d, hw⟩

/-- The surviving vertex `1`. -/
def n1 : Cell C4 h4 I4 := Sum.inl ⟨1, one_mem_I4⟩

/-- The surviving vertex `3`. -/
def n3 : Cell C4 h4 I4 := Sum.inl ⟨3, three_mem_I4⟩

/-- The side of a node: whether it is the vertex `1` or an edge at `1`. -/
def c4Side : Cell C4 h4 I4 → Prop
  | Sum.inl v => (v : Fin 4) = 1
  | Sum.inr e => (1 : Fin 4) ∈ (e.1 : Sym2 (Fin 4))

theorem c4Side_inl_iff_inr {v : {v : Fin 4 // h4 v ∈ I4}}
    {e : {e : C4.edgeSet // EdgeActive C4 h4 I4 e}} (hv : (v : Fin 4) ∈ (e.1 : Sym2 (Fin 4))) :
    (v : Fin 4) = 1 ↔ (1 : Fin 4) ∈ (e.1 : Sym2 (Fin 4)) := by
  constructor
  · intro hv1
    rwa [← hv1]
  · intro h1
    rcases h4_mem_I4.1 v.2 with hv1 | hv3
    · exact hv1
    · exfalso
      have he : (e.1 : Sym2 (Fin 4)) = s(1, 3) :=
        (Sym2.mem_and_mem_iff (by decide)).1 ⟨h1, hv3 ▸ hv⟩
      have hadj : C4.Adj 1 3 := by
        have := e.1.2
        rw [he] at this
        exact this
      exact C4_not_adj_one_three hadj

theorem c4Side_adj {x y : Cell C4 h4 I4} (hxy : (cellGraph C4 h4 I4).Adj x y) :
    c4Side x = c4Side y := by
  rcases x with v | e <;> rcases y with w | e'
  · exact (hxy : False).elim
  · exact propext (c4Side_inl_iff_inr hxy)
  · exact (propext (c4Side_inl_iff_inr hxy)).symm
  · exact (hxy : False).elim

/-- The two incidence classes over `I` are distinct. -/
theorem c4_cell_ne :
    (cellGraph C4 h4 I4).connectedComponentMk n1 ≠ (cellGraph C4 h4 I4).connectedComponentMk n3 :=
  fun hc => by
    obtain ⟨p⟩ := ConnectedComponent.exact hc
    have hs : c4Side n1 = c4Side n3 := eq_of_walk (fun _ _ => c4Side_adj) p
    have h31 : (3 : Fin 4) = 1 := Eq.mp hs rfl
    exact absurd h31 (by decide)

/-- Exhaustive classification of the incidence classes over `I`. -/
theorem c4_cell_classification (c : (cellGraph C4 h4 I4).ConnectedComponent) :
    c = (cellGraph C4 h4 I4).connectedComponentMk n1 ∨
      c = (cellGraph C4 h4 I4).connectedComponentMk n3 := by
  induction c using ConnectedComponent.ind with
  | h x =>
    rcases x with ⟨v, hv⟩ | ⟨e, he⟩
    · rcases h4_mem_I4.1 hv with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
    · obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
      obtain ⟨w, hw, rfl | rfl⟩ := C4_edge_endpoint d
      · exact .inl (connectedComponentMk_inl_eq_inr C4 h4 I4 (v := ⟨1, one_mem_I4⟩) hw).symm
      · exact .inr (connectedComponentMk_inl_eq_inr C4 h4 I4 (v := ⟨3, three_mem_I4⟩) hw).symm

theorem c4_card_cell : Nat.card (cellGraph C4 h4 I4).ConnectedComponent = 2 :=
  Nat.card_eq_two_iff.2 ⟨_, _, c4_cell_ne, Set.eq_univ_of_forall fun c => by
    rcases c4_cell_classification c with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl⟩

/-- The preimage class of the vertex `1`. -/
def x1 : ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4} :=
  ZerothHomotopy.mk ⟨vertex C4 1, one_mem_I4⟩

/-- The preimage class of the vertex `3`. -/
def x3 : ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4} :=
  ZerothHomotopy.mk ⟨vertex C4 3, three_mem_I4⟩

theorem c4_equiv_x1 :
    preimageComponentsEquiv C4 h4 I4 x1 = (cellGraph C4 h4 I4).connectedComponentMk n1 :=
  preimageComponentsEquiv_mk_vertex C4 h4 I4 1 one_mem_I4

theorem c4_equiv_x3 :
    preimageComponentsEquiv C4 h4 I4 x3 = (cellGraph C4 h4 I4).connectedComponentMk n3 :=
  preimageComponentsEquiv_mk_vertex C4 h4 I4 3 three_mem_I4

/-- Two distinct preimage classes. -/
theorem c4_x1_ne_x3 : x1 ≠ x3 := fun hx =>
  c4_cell_ne (by rw [← c4_equiv_x1, ← c4_equiv_x3, hx])

/-- Exhaustive classification of the preimage classes. -/
theorem c4_preimage_classification
    (c : ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4}) : c = x1 ∨ c = x3 := by
  rcases c4_cell_classification (preimageComponentsEquiv C4 h4 I4 c) with hc | hc
  · left
    rw [← (preimageComponentsEquiv C4 h4 I4).symm_apply_apply c, hc]
    rfl
  · right
    rw [← (preimageComponentsEquiv C4 h4 I4).symm_apply_apply c, hc]
    rfl

theorem c4_card_preimage :
    Nat.card (ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4}) = 2 :=
  (Nat.card_congr (preimageComponentsEquiv C4 h4 I4)).trans c4_card_cell

/-- The dart `0 → 1`. -/
def d01 : C4.Dart := ⟨(0, 1), by decide⟩

/-- The dart `2 → 3`. -/
def d23 : C4.Dart := ⟨(2, 3), by decide⟩

/-- The parameter `3/4`. -/
def threeQuarter : unitInterval := ⟨3 / 4, by norm_num, by norm_num⟩

theorem d01_mem : dartHeight h4 d01 threeQuarter ∈ I4 := by
  show (1 / 2 : ℝ) < (1 - 3 / 4) * h4 0 + 3 / 4 * h4 1 ∧ (1 - 3 / 4) * h4 0 + 3 / 4 * h4 1 < 3 / 2
  norm_num [h4_zero, h4_one]

theorem d23_mem : dartHeight h4 d23 threeQuarter ∈ I4 := by
  show (1 / 2 : ℝ) < (1 - 3 / 4) * h4 2 + 3 / 4 * h4 3 ∧ (1 - 3 / 4) * h4 2 + 3 / 4 * h4 3 < 3 / 2
  norm_num [h4_two, h4_three]

/-- Corresponding classes: an interior point of the edge `0 — 1` lies in the class of `1`... -/
theorem c4_d01_class :
    (ZerothHomotopy.mk ⟨edgePoint C4 d01 threeQuarter, d01_mem⟩ :
      ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4}) = x1 :=
  (preimageComponentsEquiv C4 h4 I4).injective
    ((preimageComponentsEquiv_mk_edgePoint_of_snd_mem C4 h4 I4 d01_mem one_mem_I4).trans
      c4_equiv_x1.symm)

/-- ...and one of the edge `2 — 3` in the class of `3`. -/
theorem c4_d23_class :
    (ZerothHomotopy.mk ⟨edgePoint C4 d23 threeQuarter, d23_mem⟩ :
      ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4}) = x3 :=
  (preimageComponentsEquiv C4 h4 I4).injective
    ((preimageComponentsEquiv_mk_edgePoint_of_snd_mem C4 h4 I4 d23_mem three_mem_I4).trans
      c4_equiv_x3.symm)

/-- Over `J`, the inclusion merges the two incidence classes. -/
theorem c4_J_cell_merge :
    ((cellGraph C4 h4 I4).connectedComponentMk n1).map (cellInclusion C4 h4 I4_le_J4) =
      ((cellGraph C4 h4 I4).connectedComponentMk n3).map (cellInclusion C4 h4 I4_le_J4) := by
  have a12 : C4.Adj 1 2 := by decide
  have a23 : C4.Adj 2 3 := by decide
  show (cellGraph C4 h4 J4).connectedComponentMk (Sum.inl ⟨1, h4_mem_J4 1⟩) =
    (cellGraph C4 h4 J4).connectedComponentMk (Sum.inl ⟨3, h4_mem_J4 3⟩)
  calc (cellGraph C4 h4 J4).connectedComponentMk (Sum.inl ⟨1, h4_mem_J4 1⟩)
      = (cellGraph C4 h4 J4).connectedComponentMk
          (Sum.inl ⟨2, h4_mem_J4 2⟩) :=
        connectedComponentMk_inl_eq_of_adj C4 h4 J4 (u := ⟨1, h4_mem_J4 1⟩)
          (w := ⟨2, h4_mem_J4 2⟩) a12
    _ = (cellGraph C4 h4 J4).connectedComponentMk (Sum.inl ⟨3, h4_mem_J4 3⟩) :=
        connectedComponentMk_inl_eq_of_adj C4 h4 J4 (u := ⟨2, h4_mem_J4 2⟩)
          (w := ⟨3, h4_mem_J4 3⟩) a23

/-- Over `J`, the map `TDA.Reeb.componentMap` of the preimage inclusion merges the two preimage
classes. -/
theorem c4_J_preimage_merge :
    TDA.Reeb.componentMap (preimageInclusion (plHeight C4 h4) (toOpens_le_iff.2 I4_le_J4)) x1 =
      TDA.Reeb.componentMap (preimageInclusion (plHeight C4 h4) (toOpens_le_iff.2 I4_le_J4)) x3 :=
  (preimageComponentsEquiv C4 h4 J4).injective (by
    have e1 := preimageComponentsEquiv_componentMap C4 h4 I4_le_J4 x1
    have e3 := preimageComponentsEquiv_componentMap C4 h4 I4_le_J4 x3
    rw [c4_equiv_x1] at e1
    rw [c4_equiv_x3] at e3
    exact e1.trans (c4_J_cell_merge.trans e3.symm))

/-- The naturality square at `x1`, both sides computed. -/
theorem c4_square_x1 :
    preimageComponentsEquiv C4 h4 J4
        (TDA.Reeb.componentMap (preimageInclusion (plHeight C4 h4) (toOpens_le_iff.2 I4_le_J4)) x1) =
      ((cellGraph C4 h4 I4).connectedComponentMk n1).map (cellInclusion C4 h4 I4_le_J4) := by
  rw [preimageComponentsEquiv_componentMap, c4_equiv_x1]

/-- The naturality square at `x3`, both sides computed. -/
theorem c4_square_x3 :
    preimageComponentsEquiv C4 h4 J4
        (TDA.Reeb.componentMap (preimageInclusion (plHeight C4 h4) (toOpens_le_iff.2 I4_le_J4)) x3) =
      ((cellGraph C4 h4 I4).connectedComponentMk n3).map (cellInclusion C4 h4 I4_le_J4) := by
  rw [preimageComponentsEquiv_componentMap, c4_equiv_x3]

/-- The same merge through the packaged functors. -/
theorem c4_functor_merge :
    (intervalComponents (plHeight C4 h4)).map (homOfLE I4_le_J4) x1 =
        (intervalComponents (plHeight C4 h4)).map (homOfLE I4_le_J4) x3 ∧
      (cellComponentFunctor C4 h4).map (homOfLE I4_le_J4)
          ((intervalComponentsIso C4 h4).hom.app I4 x1) =
        (cellComponentFunctor C4 h4).map (homOfLE I4_le_J4)
          ((intervalComponentsIso C4 h4).hom.app I4 x3) :=
  ⟨c4_J_preimage_merge, by
    have hm := c4_J_cell_merge
    rw [← c4_equiv_x1, ← c4_equiv_x3] at hm
    exact hm⟩

/-- Endpoint coverage holds for the 4-cycle over `I`. -/
theorem c4_endpointCoverage : EndpointCoverage C4 h4 I4 := fun e _ => by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
  obtain ⟨w, hw, hw'⟩ := C4_edge_endpoint d
  exact ⟨w, hw, h4_mem_I4.2 hw'⟩

/-- The vertex-only corollary on a valid case. -/
theorem c4_vertexOnly_x1 :
    preimageInducedEquiv C4 h4 I4 c4_endpointCoverage x1 =
      (C4.induce (h4 ⁻¹' (I4 : Set ℝ))).connectedComponentMk ⟨1, one_mem_I4⟩ :=
  preimageInducedEquiv_mk_vertex C4 h4 I4 _ 1 one_mem_I4

theorem c4_vertexOnly_x3 :
    preimageInducedEquiv C4 h4 I4 c4_endpointCoverage x3 =
      (C4.induce (h4 ⁻¹' (I4 : Set ℝ))).connectedComponentMk ⟨3, three_mem_I4⟩ :=
  preimageInducedEquiv_mk_vertex C4 h4 I4 _ 3 three_mem_I4

theorem c4_vertexOnly_ne :
    (C4.induce (h4 ⁻¹' (I4 : Set ℝ))).connectedComponentMk ⟨1, one_mem_I4⟩ ≠
      (C4.induce (h4 ⁻¹' (I4 : Set ℝ))).connectedComponentMk ⟨3, three_mem_I4⟩ := fun hc =>
  c4_x1_ne_x3 ((preimageInducedEquiv C4 h4 I4 c4_endpointCoverage).injective
    (by rw [c4_vertexOnly_x1, c4_vertexOnly_x3, hc]))

end Cycle

end

end TDA.Reeb.Examples.GraphPL
