import TDA.Reeb.GraphCycleObstruction
import TDA.Reeb.GraphRealizationExamples
import Mathlib.Analysis.Convex.Contractible

/-!
# Fixtures for cycle obstructions

Acceptance fixtures for `TDA.Reeb.GraphCycleObstruction`:

* **Triangle.** For `⊤ : SimpleGraph (Fin 3)`, the dart `0 → 1` and the walk `1 → 2 → 0` in the
  graph with the edge `0 — 1` deleted: both darts of the deleted edge are absent, the return loop
  is the concatenation of the three edge paths, the winding map is the class of `min (2 * s) 1`
  along it and vanishes on the other two edges, and the loop is not null-homotopic, an instance of
  `not_homotopic_returnLoop`. Hence the realization is not simply connected. That the triangle is
  not a tree is proved independently, from the same walk and the bridge criterion.
* **Orientation control.** At the non-midpoint parameter `1/4`, the selected dart has winding value
  the class of `1/4` and its reversal the class of `3/4`; these differ, so the two points differ.
  All four endpoint values and every vertex value are `0`.
* **Two isolated vertices.** `⊥ : SimpleGraph Bool` is acyclic, but not connected, so its
  realization is not path connected, hence not simply connected, and the graph is not a tree.
* **Empty vertex type.** For every `[IsEmpty V]` the graph is acyclic but not a tree, because
  connectedness includes nonemptiness, and the empty realization is not simply connected.
* **Positive controls.** The realization of one isolated vertex is a point, and that of one edge is
  homeomorphic to the unit interval; both are contractible, hence simply connected, and the
  necessary condition gives that both graphs are trees.
-/

open SimpleGraph unitInterval Topology

namespace TDA.Reeb.Examples.GraphCycleObstruction

open TDA.Reeb.GraphRealization TDA.Reeb.GraphCycleObstruction

noncomputable section

/-! ### Triangle -/

/-- The triangle. -/
abbrev triangle : SimpleGraph (Fin 3) := ⊤

/-- The selected dart `0 → 1`. -/
def d01 : triangle.Dart := ⟨(0, 1), by simp⟩

/-- The dart `1 → 2`. -/
def d12 : triangle.Dart := ⟨(1, 2), by simp⟩

/-- The dart `2 → 0`. -/
def d20 : triangle.Dart := ⟨(2, 0), by simp⟩

/-- The triangle with the edge `0 — 1` deleted. -/
abbrev deleted : SimpleGraph (Fin 3) := triangle.deleteEdges {d01.edge}

theorem deleted_adj_12 : deleted.Adj 1 2 := by
  simp [deleted, d01, Dart.edge]

theorem deleted_adj_20 : deleted.Adj 2 0 := by
  simp [deleted, d01, Dart.edge]

/-- Deleting the unoriented edge removes both darts `0 → 1` and `1 → 0`. -/
theorem deleted_not_adj_01 : ¬ deleted.Adj 0 1 := by
  simp [deleted, d01, Dart.edge]

theorem deleted_not_adj_10 : ¬ deleted.Adj 1 0 := by
  simp [deleted, d01, Dart.edge, Sym2.eq_swap]

/-- The explicit return walk `1 → 2 → 0` avoiding the edge `0 — 1`. -/
def returnWalk : deleted.Walk d01.snd d01.fst :=
  Walk.cons deleted_adj_12 (Walk.cons deleted_adj_20 Walk.nil)

/-- The return loop of the triangle. -/
def triangleLoop : Path (vertex triangle 0) (vertex triangle 0) :=
  returnLoop triangle d01 returnWalk

/-- The loop: the three edge paths `0 → 1`, `1 → 2`, `2 → 0`, then the constant path. -/
theorem triangleLoop_eq :
    triangleLoop = (edgePath triangle d01).trans
      ((edgePath triangle d12).trans ((edgePath triangle d20).trans (Path.refl _))) := rfl

/-- Along the loop, the winding map is the class of `min (2 * s) 1`. -/
theorem triangle_winding (s : unitInterval) :
    edgeWinding triangle d01 (triangleLoop s) = ((min (2 * (s : ℝ)) 1 : ℝ) : AddCircle (1 : ℝ)) :=
  edgeWinding_returnLoop triangle d01 returnWalk s

/-- The winding map vanishes on the edge `1 — 2`. -/
theorem triangle_winding_d12 (t : unitInterval) :
    edgeWinding triangle d01 (edgePoint triangle d12 t) = 0 :=
  edgeWinding_edgePoint_of_edge_ne triangle d01 d12 (by simp [d01, d12, Dart.edge]) t

/-- The winding map vanishes on the edge `2 — 0`. -/
theorem triangle_winding_d20 (t : unitInterval) :
    edgeWinding triangle d01 (edgePoint triangle d20 t) = 0 :=
  edgeWinding_edgePoint_of_edge_ne triangle d01 d20 (by simp [d01, d20, Dart.edge]) t

/-- The triangle loop is not null-homotopic: the instance of the witness theorem. -/
theorem triangle_not_homotopic : ¬ triangleLoop.Homotopic (Path.refl (vertex triangle 0)) :=
  not_homotopic_returnLoop triangle d01 returnWalk

/-- The realization of the triangle is not simply connected, by the non-null-homotopic loop. -/
theorem triangle_not_simplyConnectedSpace : ¬ SimplyConnectedSpace (Realization triangle) :=
  fun _ => triangle_not_homotopic (SimplyConnectedSpace.paths_homotopic _ _)

/-- The edge `0 — 1` is not a bridge: the reversed return walk joins `0` to `1` without it. -/
theorem triangle_not_isBridge : ¬ triangle.IsBridge s(0, 1) := by
  rw [isBridge_iff]
  exact fun h => h ⟨returnWalk.reverse⟩

/-- The triangle is not acyclic, by the bridge criterion. -/
theorem triangle_not_isAcyclic : ¬ triangle.IsAcyclic := fun h =>
  triangle_not_isBridge (isAcyclic_iff_forall_adj_isBridge.1 h d01.adj)

/-- The triangle is not a tree, independently of the realization. -/
theorem triangle_not_isTree : ¬ triangle.IsTree := fun h =>
  triangle_not_isAcyclic h.isAcyclic

/-! ### Orientation control -/

/-- The non-midpoint parameter `1/4`. -/
def quarter : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

theorem triangle_winding_quarter :
    edgeWinding triangle d01 (edgePoint triangle d01 quarter) =
      ((1 / 4 : ℝ) : AddCircle (1 : ℝ)) :=
  edgeWinding_edgePoint_self triangle d01 quarter

theorem triangle_winding_symm_quarter :
    edgeWinding triangle d01 (edgePoint triangle d01.symm quarter) =
      ((3 / 4 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [edgeWinding_edgePoint_symm_self]
  norm_num [quarter]

theorem quarter_ne_threeQuarter :
    ((1 / 4 : ℝ) : AddCircle (1 : ℝ)) ≠ ((3 / 4 : ℝ) : AddCircle (1 : ℝ)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  rw [Ne, AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩]
  norm_num

/-- The two orientations have different winding values at `1/4`. -/
theorem triangle_winding_orientation_ne :
    edgeWinding triangle d01 (edgePoint triangle d01 quarter) ≠
      edgeWinding triangle d01 (edgePoint triangle d01.symm quarter) := by
  rw [triangle_winding_quarter, triangle_winding_symm_quarter]
  exact quarter_ne_threeQuarter

theorem triangle_quarter_points_ne :
    edgePoint triangle d01 quarter ≠ edgePoint triangle d01.symm quarter := fun h =>
  triangle_winding_orientation_ne (congrArg _ h)

theorem triangle_winding_endpoints :
    edgeWinding triangle d01 (edgePoint triangle d01 0) = 0 ∧
      edgeWinding triangle d01 (edgePoint triangle d01 1) = 0 ∧
      edgeWinding triangle d01 (edgePoint triangle d01.symm 0) = 0 ∧
      edgeWinding triangle d01 (edgePoint triangle d01.symm 1) = 0 :=
  ⟨edgeWinding_edgePoint_self_zero _ _, edgeWinding_edgePoint_self_one _ _,
    edgeWinding_edgePoint_symm_self_zero _ _, edgeWinding_edgePoint_symm_self_one _ _⟩

theorem triangle_winding_vertex (v : Fin 3) : edgeWinding triangle d01 (vertex triangle v) = 0 :=
  edgeWinding_vertex _ _ v

/-! ### Two isolated vertices -/

/-- Two vertices and no edge. -/
abbrev twoPoints : SimpleGraph Bool := ⊥

theorem twoPoints_isAcyclic : twoPoints.IsAcyclic := isAcyclic_bot

theorem twoPoints_not_connected : ¬ twoPoints.Connected := fun h =>
  Bool.false_ne_true (reachable_bot.1 (h.preconnected false true))

theorem twoPoints_not_pathConnectedSpace : ¬ PathConnectedSpace (Realization twoPoints) :=
  fun h => twoPoints_not_connected ((connected_iff_pathConnectedSpace _).2 h)

/-- Not simply connected, through failed connectedness although the graph is acyclic. -/
theorem twoPoints_not_simplyConnectedSpace : ¬ SimplyConnectedSpace (Realization twoPoints) :=
  fun _ => twoPoints_not_pathConnectedSpace inferInstance

theorem twoPoints_not_isTree : ¬ twoPoints.IsTree := fun h =>
  twoPoints_not_connected h.connected

/-! ### Empty vertex type -/

section Empty

variable {V : Type*} [IsEmpty V] (G : SimpleGraph V)

theorem empty_isAcyclic : G.IsAcyclic := IsAcyclic.of_subsingleton

/-- Not a tree: connectedness includes nonemptiness. -/
theorem empty_not_isTree : ¬ G.IsTree := fun h =>
  isEmptyElim (Classical.choice h.connected.nonempty)

/-- The empty realization is not simply connected: simple connectivity includes nonemptiness. -/
theorem empty_not_simplyConnectedSpace : ¬ SimplyConnectedSpace (Realization G) := fun _ =>
  isEmptyElim (Classical.choice (PathConnectedSpace.nonempty (X := Realization G)))

end Empty

/-! ### Positive controls -/

open TDA.Reeb.Examples.GraphRealization in
theorem point_simplyConnectedSpace : SimplyConnectedSpace (Realization pointGraph) :=
  inferInstance

open TDA.Reeb.Examples.GraphRealization in
theorem point_isTree : pointGraph.IsTree :=
  isTree_of_simplyConnectedSpace _ point_simplyConnectedSpace

theorem unitInterval_contractibleSpace : ContractibleSpace unitInterval :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num, by norm_num⟩

open TDA.Reeb.Examples.GraphRealization in
theorem edge_contractibleSpace : ContractibleSpace (Realization edgeGraph) :=
  haveI := unitInterval_contractibleSpace
  edgeHomeomorph.contractibleSpace

open TDA.Reeb.Examples.GraphRealization in
theorem edge_simplyConnectedSpace : SimplyConnectedSpace (Realization edgeGraph) :=
  haveI := edge_contractibleSpace
  inferInstance

open TDA.Reeb.Examples.GraphRealization in
theorem edge_isTree : edgeGraph.IsTree :=
  isTree_of_simplyConnectedSpace _ edge_simplyConnectedSpace

end

end TDA.Reeb.Examples.GraphCycleObstruction
