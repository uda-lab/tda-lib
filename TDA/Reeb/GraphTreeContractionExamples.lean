import TDA.Reeb.GraphTreeContraction
import TDA.Reeb.GraphCycleObstructionExamples
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Fixtures for contractible realizations of finite trees

Acceptance fixtures for `TDA.Reeb.GraphTreeContraction`:

* **Empty vertex type.** For every `[IsEmpty V]` the realization is empty, hence not contractible.
  The graph is not a tree and the realization is not simply connected
  (`TDA.Reeb.Examples.GraphCycleObstruction.empty_not_isTree`, `empty_not_simplyConnectedSpace`),
  so both tree criteria hold with both sides false.
* **One vertex.** The realization of the one-vertex graph is contractible by the finite-tree
  theorem, from `SimpleGraph.IsTree.of_subsingleton`.
* **The path on three vertices.** `pathGraph 3` is the star centred at `1`, hence a tree, and its
  realization is contractible and simply connected. At the leaf `0` with neighbour `1` the slide
  moves `0` along the dart `0 → 1`, shortens that dart to `t ↦ 1 - (1 - t)(1 - s)`, and fixes the
  vertex `2` and the edge `1 — 2`; the collapse sends `0` to `1`. Through the leaf step the
  remaining edge `1 — 2` also has contractible realization.
* **The star with three leaves.** For `starGraph (0 : Fin 4)` the realization is contractible, and
  simply connected through the tree criterion.
* **The triangle.** `⊤ : SimpleGraph (Fin 3)` is not a tree
  (`TDA.Reeb.Examples.GraphCycleObstruction.triangle_not_isTree`), so by the two criteria its
  realization is neither simply connected nor contractible.

The star `starGraph (0 : ℕ)` is a tree on an infinite vertex type; the finite-tree theorems do not
apply to it, and no statement about its realization is made.
-/

open SimpleGraph unitInterval Topology
open scoped ContinuousMap

namespace TDA.Reeb.Examples.GraphTreeContraction

open TDA.Reeb.GraphRealization TDA.Reeb.GraphCycleObstruction TDA.Reeb.GraphTreeContraction

noncomputable section

/-! ### Empty vertex type -/

/-- The empty realization is not contractible: contractibility includes nonemptiness. Both sides
of the tree criteria are false here (`GraphCycleObstruction.empty_not_isTree`). -/
theorem empty_not_contractibleSpace {V : Type*} [IsEmpty V] (G : SimpleGraph V) :
    ¬ ContractibleSpace (Realization G) := fun _ =>
  isEmptyElim (Classical.choice (PathConnectedSpace.nonempty (X := Realization G)))

/-! ### One vertex -/

open TDA.Reeb.Examples.GraphRealization in
theorem point_contractibleSpace : ContractibleSpace (Realization pointGraph) :=
  contractibleSpace_realization_of_isTree _ IsTree.of_subsingleton

/-! ### The path on three vertices -/

open TDA.Reeb.Examples.GraphRealization

/-- The path `0 — 1 — 2` is the star centred at `1`. -/
theorem path3_eq_starGraph : path3 = starGraph 1 := by
  ext u v
  simp only [pathGraph_adj, starGraph_adj]
  revert u v
  decide

theorem path3_isTree : path3.IsTree := path3_eq_starGraph ▸ isTree_starGraph 1

theorem path3_contractibleSpace : ContractibleSpace (Realization path3) :=
  contractibleSpace_realization_of_isTree _ path3_isTree

theorem path3_simplyConnectedSpace : SimplyConnectedSpace (Realization path3) :=
  simplyConnectedSpace_realization_of_isTree _ path3_isTree

theorem path3_adj_01 : path3.Adj 0 1 := d01.adj

/-- The end `0` is a leaf with neighbour `1`. -/
theorem path3_eq_one_of_adj_zero : ∀ w, path3.Adj 0 w → w = 1 := by
  simp only [pathGraph_adj]
  decide

/-- The leaf step at `0`: the realization of the path is homotopy equivalent to the realization of
the edge `1 — 2`. -/
def path3LeafEquiv : Realization path3 ≃ₕ Realization (path3.induce ({0}ᶜ : Set (Fin 3))) :=
  leafHomotopyEquiv path3_adj_01 path3_eq_one_of_adj_zero

/-- Along the leaf slide the leaf `0` travels along the dart `0 → 1`. -/
theorem path3_slide_leaf (s : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, vertex path3 0) =
      edgePoint path3 d01 s :=
  leafHomotopy_vertex_self _ _ s

/-- The dart `0 → 1` is shortened towards `1`. -/
theorem path3_slide_d01 (s t : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, edgePoint path3 d01 t) =
      edgePoint path3 d01 (σ (σ t * σ s)) :=
  leafHomotopy_edgePoint_of_fst_eq _ _ rfl s t

/-- The far end `2` stays fixed. -/
theorem path3_slide_two (s : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, vertex path3 2) = vertex path3 2 :=
  leafHomotopy_vertex_of_ne _ _ (by decide) s

/-- The edge `1 — 2` is fixed pointwise. -/
theorem path3_slide_d12 (s t : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, edgePoint path3 d12 t) =
      edgePoint path3 d12 t :=
  leafHomotopy_edgePoint_of_ne _ _ (by decide) (by decide) s t

/-- The collapse sends the leaf to its neighbour. -/
theorem path3_collapse_leaf :
    leafCollapse path3_adj_01 path3_eq_one_of_adj_zero (vertex path3 0) =
      vertex _ ⟨1, by decide⟩ :=
  leafCollapse_vertex_self _ _

/-- The remaining edge `1 — 2` has contractible realization, through the leaf step. -/
theorem path3_remainder_contractibleSpace :
    ContractibleSpace (Realization (path3.induce ({0}ᶜ : Set (Fin 3)))) :=
  have := path3_contractibleSpace
  path3LeafEquiv.symm.contractibleSpace

/-! ### The star with three leaves -/

/-- The star on `Fin 4` centred at `0`. -/
abbrev star4 : SimpleGraph (Fin 4) := starGraph 0

theorem star4_contractibleSpace : ContractibleSpace (Realization star4) :=
  contractibleSpace_realization_of_isTree _ (isTree_starGraph 0)

theorem star4_simplyConnectedSpace : SimplyConnectedSpace (Realization star4) :=
  (isTree_iff_simplyConnectedSpace_realization _).1 (isTree_starGraph 0)

/-! ### The triangle -/

open TDA.Reeb.Examples.GraphCycleObstruction (triangle triangle_not_isTree)

/-- The triangle is not a tree, so its realization is not simply connected by the tree criterion. -/
theorem triangle_not_simplyConnectedSpace : ¬ SimplyConnectedSpace (Realization triangle) :=
  (isTree_iff_simplyConnectedSpace_realization _).not.1 triangle_not_isTree

theorem triangle_not_contractibleSpace : ¬ ContractibleSpace (Realization triangle) :=
  (isTree_iff_contractibleSpace_realization _).not.1 triangle_not_isTree

end

end TDA.Reeb.Examples.GraphTreeContraction
