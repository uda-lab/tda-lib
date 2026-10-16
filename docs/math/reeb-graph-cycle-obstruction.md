# Cycle obstructions in graph realizations

Consulted manifestations, attribution and rights: [ReebOrdering-aa7d10f](references.md#ReebOrdering-aa7d10f), [mathlib-0df444a](references.md#mathlib-0df444a).

This digest builds on the realization of simple graphs in
[reeb-graph-realization.md](reeb-graph-realization.md) and proves its necessary tree condition:
a graph whose realization is simply connected is a tree. The converse is not proved.

## The one-edge winding map

For `V : Type u`, `G : SimpleGraph V` and a dart `d₀ : G.Dart`, the edge data

```lean
edgeWindingCell G d₀ d t = (t : AddCircle 1)       -- d = d₀
edgeWindingCell G d₀ d t = (1 - t : AddCircle 1)   -- d = d₀.symm
edgeWindingCell G d₀ d t = 0                       -- otherwise
```

(`edgeWindingCell_self`, `edgeWindingCell_symm_self`, `edgeWindingCell_of_ne`) are continuous.
They respect reversal, since `1 - (1 - t) = t` (`edgeWindingCell_symm`), and start at `0` on
every dart, since the class of `1 - 0` is the class of the period (`edgeWindingCell_zero`). The
first two cases do not overlap because a dart of a simple graph is not its own reversal. With
vertex value `0` the merged bundled lift gives

```lean
edgeWinding G d₀ : C(Realization G, AddCircle (1 : ℝ))
edgeWinding G d₀ (vertex G v)             = 0
edgeWinding G d₀ (edgePoint G d₀ t)       = t
edgeWinding G d₀ (edgePoint G d₀.symm t)  = 1 - t
edgeWinding G d₀ (edgePoint G d t)        = 0     -- d ≠ d₀, d ≠ d₀.symm
```

(`edgeWinding_vertex`, `edgeWinding_edgePoint_self`, `edgeWinding_edgePoint_symm_self`,
`edgeWinding_edgePoint_of_ne`, and `edgeWinding_edgePoint_of_edge_ne` for darts whose unoriented
edge differs from `d₀.edge`). All four endpoint values on the selected edge are `0`
(`edgeWinding_edgePoint_self_zero`, `_self_one`, `_symm_self_zero`, `_symm_self_one`), because
`0` and `1` have the same class. The map winds the edge of `d₀` once around the circle; it is not
induced by a graph homomorphism.

## The return loop and its lift

A walk `q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst` need not be simple. Deleting the
unoriented edge excludes both `d₀` and `d₀.symm`; excluding only the forward dart would admit the
backtrack along `d₀.symm`, whose loop is null-homotopic. Mapped into `G` along `deleteEdges_le`,
every dart traversed by `q` has edge different from `d₀.edge`, so the winding map vanishes along
the mapped walk path (`edgeWinding_walkPath_deleteEdges`, by induction on `q`). The loop

```lean
returnLoop G d₀ q = (edgePath G d₀).trans (walkPath G (q.mapLe (G.deleteEdges_le {d₀.edge})))
```

at `vertex G d₀.fst` traverses the selected edge first, under mathlib's `Path.trans` convention.
Along it the winding map is the class of

```lean
returnLift s = min (2 * s) 1      -- = 2 * s for s ≤ 1/2, = 1 for 1/2 ≤ s
```

(`edgeWinding_returnLoop`, `returnLift_of_le`, `returnLift_of_ge`), with `returnLift 0 = 0` and
`returnLift 1 = 1`. By uniqueness of path lifts through the covering
`ℝ → AddCircle (1 : ℝ)` (`AddCircle.isCoveringMap_coe`, `IsCoveringMap.eq_liftPath_iff'`),
`returnLift` is the lift of the winding of the loop starting at `0` (`returnLift_eq_liftPath`).

**Non-null-homotopy** (`not_homotopic_returnLoop`).
`¬ (returnLoop G d₀ q).Homotopic (Path.refl (vertex G d₀.fst))`. An endpoint-fixed homotopy maps
along the winding map to a homotopy of the circle paths relative to `{0, 1}`. Such paths, lifted
from the same initial point, have the same final point
(`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`). The return loop lifts to the endpoint
`1`, while the constant loop maps to the constant path at `0` and lifts to the endpoint `0`; this
gives `1 = 0`. The obstruction is this lift computation, not a component count or a quoted
winding number. No local path connectedness of the realization and no fundamental-group
computation are used.

## Graph consequences

```lean
not_simplyConnectedSpace_of_returnWalk : ¬ SimplyConnectedSpace (Realization G)   -- given q
isAcyclic_of_simplyConnectedSpace     : SimplyConnectedSpace (Realization G) → G.IsAcyclic
isTree_of_simplyConnectedSpace        : SimplyConnectedSpace (Realization G) → G.IsTree
not_simplyConnectedSpace_of_not_isTree : ¬ G.IsTree → ¬ SimplyConnectedSpace (Realization G)
```

In a simply connected space every loop is endpoint-homotopic to the constant loop
(`SimplyConnectedSpace.paths_homotopic`), so no edge `u — v` has a return walk avoiding it. By
`isBridge_iff` every edge is a bridge, and by `isAcyclic_iff_forall_adj_isBridge` the graph is
acyclic. A simply connected space is path connected, and the merged
`connected_iff_pathConnectedSpace` gives graph connectedness. Both sides of that equivalence
include nonemptiness, so the empty graph is correctly excluded and no implication from "all loops
are null-homotopic" to nonemptiness is used. No finiteness, local finiteness, decidable
adjacency, vertex topology or nonemptiness hypothesis is assumed; the dart case distinction of
the winding data is a local classical choice.

## Names and universes

The results live in namespace `TDA.Reeb.GraphCycleObstruction`
(`TDA/Reeb/GraphCycleObstruction.lean`) and the fixtures in
`TDA.Reeb.Examples.GraphCycleObstruction` (`TDA/Reeb/GraphCycleObstructionExamples.lean`). The
vertex type has an arbitrary universe `u` and the graph is an explicit argument throughout. There
are no private declarations. Among the fixtures, `d01`, `d12` and `quarter` also occur in other
fixture namespaces.

## Fixtures

The module `TDA/Reeb/GraphCycleObstructionExamples.lean` proves:

- **Triangle.** For `⊤ : SimpleGraph (Fin 3)`, the dart `0 → 1` and the explicit return walk
  `1 → 2 → 0` in the graph with the edge `0 — 1` deleted: both `0 — 1` orientations are absent
  and `1 — 2`, `2 — 0` are present (`deleted_not_adj_01`, `deleted_not_adj_10`,
  `deleted_adj_12`, `deleted_adj_20`). The return loop is the concatenation of the three edge
  paths and the constant path (`triangleLoop_eq`, by `rfl`), the winding map along it is the class
  of `min (2 * s) 1` and vanishes on the two other edges (`triangle_winding`,
  `triangle_winding_d12`, `triangle_winding_d20`). The loop is not null-homotopic as an instance
  of `not_homotopic_returnLoop` (`triangle_not_homotopic`), so the realization is not simply
  connected (`triangle_not_simplyConnectedSpace`). Independently of the realization, the reversed
  walk shows that `0 — 1` is not a bridge, so the triangle is neither acyclic nor a tree
  (`triangle_not_isBridge`, `triangle_not_isAcyclic`, `triangle_not_isTree`).
- **Orientation control.** At the non-midpoint parameter `1/4`, the selected dart has winding
  value the class of `1/4` and its reversal the class of `3/4`; these classes differ, hence so do
  the two edge points (`triangle_winding_quarter`, `triangle_winding_symm_quarter`,
  `triangle_winding_orientation_ne`, `triangle_quarter_points_ne`). All four endpoint values and
  all vertex values are `0` (`triangle_winding_endpoints`, `triangle_winding_vertex`).
- **Two isolated vertices.** `⊥ : SimpleGraph Bool` is acyclic but not connected; its realization
  is not path connected, hence not simply connected, and the graph is not a tree
  (`twoPoints_isAcyclic`, `twoPoints_not_connected`, `twoPoints_not_simplyConnectedSpace`,
  `twoPoints_not_isTree`). This separates acyclicity from the tree condition.
- **Empty vertex type.** For every `[IsEmpty V]`, the graph is acyclic but not a tree, since
  connectedness includes nonemptiness, and the empty realization is not simply connected, since
  simple connectivity includes path connectedness and hence nonemptiness (`empty_isAcyclic`,
  `empty_not_isTree`, `empty_not_simplyConnectedSpace`).
- **Positive controls.** The realization of one isolated vertex is a point and that of one edge is
  homeomorphic to the unit interval (`pointUnique`, `edgeHomeomorph` from the realization
  fixtures). Both are contractible, hence simply connected, and the necessary condition yields
  that both graphs are trees (`point_simplyConnectedSpace`, `point_isTree`,
  `edge_simplyConnectedSpace`, `edge_isTree`). These are bounded controls, not the converse.

## Source correspondence

**Source.** The winding map, its vanishing on deleted-edge walks and the lift argument for
acyclicity are adapted from `uda-lab/reeb-ordering`,
[`ReebOrdering/GraphRealisation.lean`](https://github.com/uda-lab/reeb-ordering/blob/aa7d10f4f7dc0474b76f17ea81afcab5a230d521/ReebOrdering/GraphRealisation.lean#L222-L377)
at commit `aa7d10f4f7dc0474b76f17ea81afcab5a230d521` (blob
`6b79160f368a9d6fd63f2d52f1db4d9c5697cfa8`), Copyright 2026 Tomoki Uda, licensed under the
[Apache License, Version 2.0](https://github.com/uda-lab/reeb-ordering/blob/aa7d10f4f7dc0474b76f17ea81afcab5a230d521/LICENSE).
The source is not imported and is not a dependency.

| Library declaration | Source declaration | Lines |
|---|---|---|
| `edgeWindingCell`, `edgeWindingCell_symm`, `edgeWindingCell_zero` | `windEdge`, `windEdge_symm`, `windEdge_zero`, `continuous_windEdge` | 223–261 |
| `edgeWinding`, `edgeWinding_vertex`, `edgeWinding_edgePoint_self`, `edgeWinding_edgePoint_of_ne` | `windMap` and its evaluation lemmas | 262–279 |
| `edgeWinding_walkPath_deleteEdges` | `windMap_walkPath_deleteEdges` | 281–307 |
| `returnLoop`, `returnLift`, `edgeWinding_returnLoop`, `returnLift_eq_liftPath`, `not_homotopic_returnLoop`, `isAcyclic_of_simplyConnectedSpace` | the lift argument of `isAcyclic_of_simplyConnectedSpace` | 309–364 |

Changes: the names; public visibility; bundled edge data through the merged `continuousLift`;
the return loop, its lift and its non-null-homotopy as separate public declarations; the
reversed-dart formula and the endpoint values as statements; and graph connectedness from the
merged `connected_iff_pathConnectedSpace` in place of the source's private connectedness lemma.
Every other declaration, including every fixture, is new. The source's finite-tree and Hasse-order
results are not ported.

**de Silva, Munch and Patel.** The arbitrary-graph theorem here is not a result of *Categorified
Reeb Graphs*; its Notation 2.7 is context for the realization only, as recorded in
[reeb-graph-realization.md](reeb-graph-realization.md).

**Mathlib and TauCeti.** Pinned mathlib has the covering `AddCircle.isCoveringMap_coe`, path
lifting and its homotopy invariance (`Mathlib/Topology/Homotopy/Lifting.lean`) and the bridge
criterion for acyclic graphs, but no realization of simple graphs and no statement relating
acyclicity to simple connectivity. The search of TauCeti recorded in
[reeb-graph-realization.md](reeb-graph-realization.md) applies with the same limits; nothing from
TauCeti is used.

Not claimed here: the converse, that the realization of a tree is simply connected; contractibility
or leaf collapse of finite trees; fundamental groups of realizations; Hasse-order results; flows.

Sources: [pinned mathlib path lifting](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Homotopy/Lifting.lean),
[the circle covering](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Covering/AddCircle.lean),
[simply connected spaces](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean)
and [acyclic graphs](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean).
