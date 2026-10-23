# Contractible realizations of finite trees

Consulted manifestations, attribution and rights: [ReebOrdering-aa7d10f](references.md#ReebOrdering-aa7d10f), [mathlib-0df444a](references.md#mathlib-0df444a).

This digest builds on the realization of simple graphs in
[reeb-graph-realization.md](reeb-graph-realization.md) and on the necessary tree condition in
[reeb-graph-cycle-obstruction.md](reeb-graph-cycle-obstruction.md). It proves the converse for
finite vertex types: the realization of a finite tree is contractible. Hence a graph on a finite
vertex type is a tree exactly when its realization is simply connected, and exactly when it is
contractible.

## Removing a leaf

For `V : Type u`, `G : SimpleGraph V` and a vertex `ℓ`, the embedding of the induced graph
`G.induce {ℓ}ᶜ` gives

```lean
deleteVertexInclusion G ℓ : C(Realization (G.induce {ℓ}ᶜ), Realization G)
deleteVertexInclusion G ℓ (vertex _ v)      = vertex G v
deleteVertexInclusion G ℓ (edgePoint _ d t) = edgePoint G ⟨(d.fst, d.snd), d.adj⟩ t
```

Let `ℓ` be a leaf with neighbour `m`: `hadj : G.Adj ℓ m` and `huniq : ∀ w, G.Adj ℓ w → w = m`.
The leaf collapse is

```lean
leafCollapse hadj huniq : C(Realization G, Realization (G.induce {ℓ}ᶜ))
leafCollapse (vertex G ℓ)        = vertex _ m
leafCollapse (vertex G v)        = vertex _ v          -- v ≠ ℓ
leafCollapse (edgePoint G d t)   = edgePoint _ d t     -- d.fst ≠ ℓ, d.snd ≠ ℓ
leafCollapse (edgePoint G d t)   = vertex _ m          -- d.fst = ℓ or d.snd = ℓ
```

(`leafCollapse_vertex_self`, `leafCollapse_vertex_of_ne`, `leafCollapse_edgePoint_of_ne`,
`leafCollapse_edgePoint_of_eq`). A dart touching `ℓ` is `ℓ → m` or `m → ℓ`, so the start equation
of the lift holds on both. Collapsing after including is the identity
(`leafCollapse_comp_deleteVertexInclusion`, by `hom_ext`).

Including after collapsing is homotopic to the identity by the leaf slide. At time `s`,

```lean
leafHomotopy (s, vertex G ℓ)        = edgePoint G (ℓ → m) s
leafHomotopy (s, vertex G v)        = vertex G v                         -- v ≠ ℓ
leafHomotopy (s, edgePoint G d t)   = edgePoint G d (1 - (1 - t)(1 - s))  -- d.fst = ℓ
leafHomotopy (s, edgePoint G d t)   = edgePoint G d (t (1 - s))           -- d.snd = ℓ
leafHomotopy (s, edgePoint G d t)   = edgePoint G d t                     -- otherwise
```

(`leafHomotopy_vertex_self`, `leafHomotopy_vertex_of_ne`, `leafHomotopy_edgePoint_of_fst_eq`,
`leafHomotopy_edgePoint_of_snd_eq`, `leafHomotopy_edgePoint_of_ne`). The two leaf-edge formulas
agree under reversal: the point of `m → ℓ` at `(1 - t)(1 - s)` is the point of `ℓ → m` at
`1 - (1 - t)(1 - s)`. At `t = 0` they give the track of `ℓ` and the fixed vertex `m`.
At `s = 0` every formula is the identity; at `s = 1` the leaf edge and `ℓ` are at `m`, which is the collapse followed by the
inclusion. The dart leaving the leaf is determined by `huniq`, while the two cases are told apart by
`d.fst = ℓ` and `d.snd = ℓ` alone, which cannot both hold.

Continuity: the vertex tracks and the curried edge tracks are continuous maps into
`C(unitInterval, Realization G)` satisfying the reversal and start equations, so the bundled lift
`continuousLift` is a continuous map `Realization G → C(unitInterval, Realization G)`. Since the
unit interval is locally compact, its uncurried form is continuous on
`Realization G × unitInterval` (`ContinuousMap.continuous_uncurry_of_continuous`). No statement
that a product of the quotient map with the unit interval is a quotient map is used.

The result is `leafHomotopyEquiv hadj huniq : Realization G ≃ₕ Realization (G.induce {ℓ}ᶜ)` with
forward map the collapse and inverse the inclusion. The leaf step assumes no finiteness.

## Finite trees

```lean
contractibleSpace_realization_of_isTree    [Finite V] : G.IsTree → ContractibleSpace (Realization G)
simplyConnectedSpace_realization_of_isTree [Finite V] : G.IsTree → SimplyConnectedSpace (Realization G)
isTree_iff_simplyConnectedSpace_realization [Finite V] : G.IsTree ↔ SimplyConnectedSpace (Realization G)
isTree_iff_contractibleSpace_realization    [Finite V] : G.IsTree ↔ ContractibleSpace (Realization G)
```

The first is proved for every `V : Type u` with `n + 1` elements by induction on `n`. With one
vertex there is no edge, since a dart would join a vertex to itself, so the realization is a single
point. With at least two vertices, a finite tree has a vertex `ℓ` of degree one
(`SimpleGraph.IsTree.exists_ne_and_degree_eq_one`, with the edge-set finiteness and local
finiteness obtained classically from `Finite V`), whose neighbour `m` is unique
(`SimpleGraph.degree_eq_one_iff_existsUnique_adj`). The graph induced on `{ℓ}ᶜ` is connected
(`SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one`) and acyclic
(`SimpleGraph.IsAcyclic.induce`), hence a tree, on `n` vertices
(`Set.ncard_compl_of_ncard_eq_add`). Contractibility transfers back along the leaf homotopy
equivalence (`ContinuousMap.HomotopyEquiv.contractibleSpace`). A contractible space is simply
connected (`SimplyConnectedSpace.ofContractible`), and the reverse directions are the necessary
condition `isTree_of_simplyConnectedSpace`, which assumes no finiteness.

The hypothesis is `[Finite V]`; decidability and `Fintype` instances are chosen inside the proof.
Every vertex of a tree with at least two vertices lies on an edge, so a tree with finitely many
edges has finitely many vertices, and assuming only a finite edge set would cover no further trees.

## Names and universes

The results live in namespace `TDA.Reeb.GraphTreeContraction` (`TDA/Reeb/GraphTreeContraction.lean`)
and the fixtures in `TDA.Reeb.Examples.GraphTreeContraction`
(`TDA/Reeb/GraphTreeContractionExamples.lean`). The vertex type has an arbitrary universe `u`. The
graph is explicit in `deleteVertexInclusion` and the tree theorems and implicit, through `hadj`, in
the collapse, the slide and the equivalence. The cellwise data of the collapse and the slide are
private.

## Fixtures

The module `TDA/Reeb/GraphTreeContractionExamples.lean` proves:

- **Empty vertex type.** For every `[IsEmpty V]` the realization is not contractible
  (`empty_not_contractibleSpace`). With `empty_not_isTree` and `empty_not_simplyConnectedSpace` of
  the cycle-obstruction fixtures, both criteria hold with both sides false.
- **One vertex.** The realization of the one-vertex graph is contractible by the finite-tree
  theorem, from `SimpleGraph.IsTree.of_subsingleton` (`point_contractibleSpace`).
- **Path on three vertices.** `pathGraph 3` equals the star centred at `1`, so it is a tree
  (`path3_eq_starGraph`, `path3_isTree`), and its realization is contractible and simply connected
  (`path3_contractibleSpace`, `path3_simplyConnectedSpace`). The vertex `0` is a leaf with neighbour
  `1` (`path3_adj_01`, `path3_eq_one_of_adj_zero`). Its leaf step `path3LeafEquiv` slides `0`
  along the dart `0 → 1`, shortens that dart, and fixes the vertex `2` and the edge `1 — 2`
  (`path3_slide_leaf`, `path3_slide_d01`, `path3_slide_two`, `path3_slide_d12`); the collapse sends
  `0` to `1` (`path3_collapse_leaf`). Through the equivalence the remaining edge `1 — 2` has
  contractible realization (`path3_remainder_contractibleSpace`).
- **Star with three leaves.** For `star4 = starGraph (0 : Fin 4)` the realization is contractible
  and, through the tree criterion, simply connected (`star4_contractibleSpace`,
  `star4_simplyConnectedSpace`).
- **Triangle.** The triangle `⊤ : SimpleGraph (Fin 3)` is not a tree (`triangle_not_isTree` of the
  cycle-obstruction fixtures), so by the two criteria its realization is neither simply connected
  nor contractible (`triangle_not_simplyConnectedSpace`, `triangle_not_contractibleSpace`).

## Source correspondence

**Source.** The leaf collapse, the leaf slide, the leaf homotopy equivalence and the induction on
the number of vertices are adapted from `uda-lab/reeb-ordering`,
[`ReebOrdering/GraphRealisation.lean`](https://github.com/uda-lab/reeb-ordering/blob/aa7d10f4f7dc0474b76f17ea81afcab5a230d521/ReebOrdering/GraphRealisation.lean#L372-L815)
at commit `aa7d10f4f7dc0474b76f17ea81afcab5a230d521` (blob
`6b79160f368a9d6fd63f2d52f1db4d9c5697cfa8`), Copyright 2026 Tomoki Uda, licensed under the
[Apache License, Version 2.0](https://github.com/uda-lab/reeb-ordering/blob/aa7d10f4f7dc0474b76f17ea81afcab5a230d521/LICENSE).
The source is not imported and is not a dependency.

| Library declaration | Source declaration | Lines |
|---|---|---|
| `deleteVertexInclusion` | `leafIncl` | 473–474 |
| `leafCollapse` and its evaluation lemmas | `leafCollapse`, `leafCollapseVertex`, `leafCollapseEdge` and their lemmas | 388–491 |
| `leafCollapse_comp_deleteVertexInclusion` | `leafCollapse_comp_leafIncl` | 498–527 |
| `leafHomotopy` | `leafDart`, `leafHomotopy`, `leafHomotopyVertex`, `leafHomotopyEdge` and their lemmas | 372–386, 529–738 |
| `leafHomotopyEquiv` | `leafHomotopyEquiv` | 740–748 |
| `contractibleSpace_realization_of_isTree` | `contractibleSpace_realisation_of_isTree` | 750–799 |
| `simplyConnectedSpace_realization_of_isTree` | `simplyConnectedSpace_of_isTree` | 801–804 |
| `isTree_iff_simplyConnectedSpace_realization` | `SimpleGraph.isTree_iff_simplyConnectedSpace_realisation` | 812–815 |

Changes: the names; public visibility of the inclusion, collapse, slide and equivalence; the leaf
dart oriented away from the leaf (the source's `leafDart` is `m → ℓ`) and the edge tracks chosen by
whether a dart leaves or enters the leaf, rather than by equality with the leaf dart; continuity of
the slide through curried edge tracks and `continuousLift`, in place of the source's `liftProd` and
`continuous_liftProd` (112–153), which rest on a product-of-quotient-maps lemma that neither this
library nor pinned mathlib provides; the induction stated for `n + 1` vertices; and the necessary
direction from `isTree_of_simplyConnectedSpace`
([reeb-graph-cycle-obstruction.md](reeb-graph-cycle-obstruction.md)).
`isTree_iff_contractibleSpace_realization`, the evaluation lemmas of the inclusion and the slide,
and every fixture are new. The source's Hasse-order result (817–830) is not ported.

**Mathlib and TauCeti.** Pinned mathlib has leaves of finite trees and connectedness after deleting
a leaf (`Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`), contractible spaces and their transfer
along homotopy equivalences (`Mathlib/Topology/Homotopy/Contractible.lean`) and the instance from
contractible to simply connected, but no realization of simple graphs. The search of TauCeti
recorded in [reeb-graph-realization.md](reeb-graph-realization.md) applies with the same limits;
nothing from TauCeti is used.

Not claimed here: contractibility or simple connectivity of realizations of trees on infinite
vertex types, which leaf removal does not reach; for example `starGraph (0 : ℕ)` is a tree to which
these theorems do not apply. Also not claimed: fundamental groups of realizations of graphs with
cycles; Hasse-order results.

Sources: [pinned mathlib acyclic graphs](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/SimpleGraph/Acyclic.lean),
[contractible spaces](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Homotopy/Contractible.lean),
[simply connected spaces](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean)
and [the compact-open uncurrying](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/CompactOpen.lean).
