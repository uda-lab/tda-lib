# Constructible Reeb quotients and their component graphs

## Setting

Levels are `S : CriticalValues n` with `a 0 < ⋯ < a n` and gaps `K e = (a e, a (e+1))` (see
`reeb-constructible-cosheaf.md`). A presentation `P : CylinderPresentation n` has arbitrary
topological vertex pieces `V i`, edge pieces `E e` and continuous endpoint maps
`left e : E e → V e.castSucc` and `right e : E e → V e.succ`. Its realization `X = P.Realization S`
glues the vertex pieces at the levels and the cylinders `E e × [a e, a (e+1)]` along the endpoint
maps, with height `h` (see `reeb-constructible-space.md`). The Reeb quotient `Q = ReebQuotient h`
identifies each path component of each fiber of `h` to a point, and `h̄` is the descended height
(see `reeb-quotient.md`).

The component data `P.componentData : FiniteReebData n` have vertex sets `π₀ (V i)`, edge sets
`π₀ (E e)` and endpoint maps `π₀ (left e)` and `π₀ (right e)`. Their finite realization
`G = (ofFiniteData P.componentData).Realization S` gives every vertex and edge set the discrete
topology (see `reeb-rgraph.md`). The class maps `vertexClass i : V i → π₀ (V i)` and
`edgeClass e : E e → π₀ (E e)` send a point to its path component, as a point of the vertex or
edge set of `G`. Two points have the same class exactly when a path joins them
(`vertexClass_eq_iff`, `edgeClass_eq_iff`).

## Hypotheses

Each result about a presentation uses the hypotheses of one of three cumulative layers; the
compactness of `Q` (`compactSpace_reebQuotient`) needs only compactness of the pieces.

1. **Finitely many path components** of every piece. This suffices for the component data, the
   class maps and their endpoint formulas, and for the component data map `componentDataHom` of a
   height-preserving map, with its independence of the regular height and its identity and
   composition laws.
2. **Local path-connectedness** of every piece, in addition. The vertex set of `G` at `i` has the
   carrier `π₀ (V i)` with the discrete topology, while `π₀ (V i)` itself carries the quotient
   topology of `V i`; likewise for edges. Unfolding `ofFiniteData` identifies the carriers, not the
   topologies. The two topologies agree exactly when the quotient topology is discrete, which
   holds when the piece is locally path-connected, because its path components are then open. This
   layer gives continuity of the class maps (`continuous_vertexClass`, `continuous_edgeClass`),
   the continuous comparison and its descent, the fiber normal form, bijectivity and the pointwise
   naturality squares.
3. **Compactness and local path-connectedness** of every piece. This gives the homeomorphism, the
   Hausdorff property of `Q`, the slice isomorphisms, transport, the comparison squares across
   critical lists and the constructible ℝ-spaces. Finiteness of the component sets follows from
   compactness and local path-connectedness.

No layer assumes Hausdorff pieces, or injectivity, surjectivity or an embedding property of the
endpoint maps. Statements outside the real slice hold in every universe; the slice statements, like
the slice itself, are in universe `0`.

## The comparison map

The maps `v ↦ (i, [v])` on vertex pieces and `(y, t) ↦ (e, [y], t)` on cylinders are continuous
under layer 2. They agree on the glued ends because `π₀ (left e) [y] = [left e y]`, and likewise
for `right`. The universal property of the realization therefore gives a continuous
height-preserving `Φ = componentGraphMap : X → G` (`height_componentGraphMap`). It is surjective,
since every point of `G` is `(i, [v])` or `(e, [y], t)`.

**Fiber normal form** (`componentGraphMap_eq_iff`): `Φ x = Φ x'` exactly when `x` and `x'` lie in
one path component of a fiber of `h`.

- If they do, a path of constant height from `x` to `x'` maps to a path of constant height in `G`.
  The fibers of `G` are finite and discrete, so that path is constant and the images agree
  (`RGraph.apply_eq_of_reebRel`).
- Conversely, every point of `X` is a vertex point `ofVertex i v` or an open-strip point
  `ofStrip e (y, t)`, and points of the two kinds have different images. Equal images of vertex
  points force the same level and `[v] = [v']`. Equal images of strip points force the same height,
  hence the same gap, and `[y] = [y']`. A path joining `v` to `v'` in `V i`, or `y` to `y'` in
  `E e`, pushed into `X` at fixed height, joins `x` to `x'` inside one fiber.

## The homeomorphism

`Φ` is constant on Reeb classes, so it descends to `quotientComponentGraphMap : C(Q, G)`. The
descended map is injective by the fiber normal form and surjective because `Φ` is. With compact
pieces `X` is compact, so `Q` is compact as a continuous image (`compactSpace_reebQuotient`), and
`G` is Hausdorff. A continuous bijection from a compact space to a Hausdorff space is a
homeomorphism, which gives

```text
quotientComponentGraphHomeomorph S P : ReebQuotient (P.height S) ≃ₜ G
```

Continuity of the inverse comes from this compact-to-Hausdorff argument, not from bijectivity. No
Hausdorff assumption on the pieces is used. As a consequence `Q` is Hausdorff
(`t2Space_reebQuotient`); this is a theorem under the hypotheses of layer 3, and no Hausdorff
instance is declared for Reeb quotients in general.

Writing `Θ` for the homeomorphism and `ρ` for the quotient projection:

- generators: `Θ [ofVertex i v] = (i, [v])`, `Θ [ofCylinder e (y, t)] = (e, [y], t)` and
  `Θ [ofStrip e (y, t)] = (e, [y], t)`, with the corresponding formulas for `Θ⁻¹`;
- height: `height_G ∘ Θ = h̄` and `h̄ ∘ Θ⁻¹ = height_G` pointwise, and the first also as continuous
  maps;
- projection: `Θ ∘ ρ = Φ`;
- fibers: a point over a level `a i` goes to the class in `V i` of its preimage under the
  critical-fiber homeomorphism, and a point over a regular height `t ∈ K e` goes to the class in
  `E e` of its preimage under the regular-fiber homeomorphism, at height `t` (see
  `reeb-constructible-space.md`).

## Naturality over a common list of levels

Let `P` and `P'` be presentations over a common `S`, and let `φ : X → X'` be an arbitrary continuous
map with `h' ∘ φ = h`. No cellular condition is imposed; `φ` may vary with the height inside a
cylinder.

- **Component data map** (layer 1). `componentDataHom S φ hφ` has vertex maps
  `π₀ (vertexFiberMap φ i)` and edge maps `π₀ (regularFiberMap φ e t)`. The edge map is read at the
  base point `basePt S e`, and it does not depend on the regular height `t` (`componentDataHom_e`).
  Its incidence squares are the incidence theorems for the component bijections of the
  realizations, transported by their naturality (see `reeb-constructible-cylinder.md`). It
  preserves identities and composition (`componentDataHom_id`, `componentDataHom_comp`).
- **Square** (layer 2). For the descended comparison `θ = quotientComponentGraphMap`, the map
  underlying `Θ`, the square `θ' ∘ Q φ = realize (componentDataHom φ) ∘ θ` holds pointwise on `Q`
  (`quotientComponentGraphMap_natural`), and the corresponding square for `Φ` holds on `X`
  (`componentGraphMap_natural`).
- **Slice** (layer 3). `quotientOverIso S P` is the homeomorphism as an isomorphism of the real
  slice, from the quotient object of `(X, h)` to `toOver S P.componentData`. The square holds for
  every slice morphism between realizations (`quotientOverIso_natural`). The data map is the unique
  finite map whose realization is the conjugated graph map, by the classification of
  `reeb-rgraph.md` (`componentDataHom_eq_preimage`).

## Transport and different lists of levels

A constructible object need not be a realization. For `iA : A ≅ (X, h)` in the real slice,
`quotientIsoOfIso S P iA` applies the quotient functor to `iA` and composes with the slice
comparison. Hence `Q A ≅ toOver S P.componentData`, and `Q A` is a graph object
(`RGraph.isRGraph_quotient`). For objects presented over a common `S`, this isomorphism is natural
in every slice morphism (`quotientIsoOfIso_natural`).

For objects presented over different lists, `iA` over `S` and `iB` over `S'`, write
`ΘA = quotientIsoOfIso S P iA` and `ΘB = quotientIsoOfIso S' P' iB`. Every slice morphism
`g : A ⟶ B` induces the graph map

```text
inducedGraphMap S S' iA iB g = ΘA⁻¹ ≫ Q g ≫ ΘB : toOver S P.componentData ⟶ toOver S' P'.componentData
```

and the comparison square `Q g ≫ ΘB = ΘA ≫ inducedGraphMap S S' iA iB g` holds
(`inducedGraphMap_square`). Over a common list, the induced map is the realization of the component
data map of the conjugated height-preserving map (`inducedGraphMap_eq_componentDataHom`). Over
different lists it is a morphism of graph objects, so after a common refinement of `S` and `S'` it
has a finite description by the classification of `reeb-rgraph.md`.

## Constructible ℝ-spaces

`IsConstructibleSpace A` holds when `A` is isomorphic in the real slice to `(X, h)` for some `n`,
`S` and presentation `P` with compact locally path-connected pieces. `ConstructibleSpaceCat` is the
full subcategory on these objects, so its morphisms are all continuous height-preserving maps. The
Reeb quotient of every constructible object is a graph object
(`isRGraph_quotient_of_isConstructibleSpace`), and the quotient functor restricts to

```text
quotientRGraphFunctor : ConstructibleSpaceCat ⥤ RGraphCat
```

on all morphisms, including those between objects presented over different lists of levels. Graph
objects are constructible, with discrete pieces (`isConstructibleSpace_of_isRGraph`).

## The graph case

For finite data `D`, the canonical map `D.toComponentData : D ⟶ (ofFiniteData D).componentData`,
`x ↦ [x]`, has bijective components because the pieces are discrete
(`toComponentData_v_bijective`, `toComponentData_e_bijective`), and `toComponentDataIso` is
the resulting isomorphism. The projection homeomorphism of `reeb-rgraph.md` followed by `Θ` is the
realization of `D.toComponentData` (`quotientComponentGraphMap_projHomeomorph`). In the slice,
`ρ ≫ Θ` is the image of `D.toComponentData` under the realization functor
(`projNatTrans_comp_quotientOverIso`).

## Fixtures

`TDA.Reeb.ConstructibleQuotientExamples` works with actual presentations, realizations and slice
morphisms. `[0, 1]` is locally path-connected and path-connected; the pinned mathlib has no such
instances for `unitInterval`, so they are local instances there. Thickening finite data `D` by
`[0, 1]` replaces every label `x` by `x × [0, 1]`, with the endpoint maps acting on labels. The
pieces are then positive-dimensional, compact and locally path-connected, the component data are
isomorphic to `D`, and the Reeb quotient is the graph object of `D`.

- A constant-height interval `[0, 1]` at a single level has distinct raw points `0` and `1` but one
  Reeb class, so the quotient is a point.
- Two disjoint intervals at one level, attached to nothing, remain two vertices.
- With empty pieces the Reeb quotient is empty and isomorphic to the empty graph.
- In the thickened pinch, the left endpoint map sends both edge pieces to one vertex piece, so it is
  not injective on points or on components. Two different raw bottom ends share a Reeb class, while
  the two edges at a regular height and the two top vertices stay apart. The quotient is the pinch
  graph.
- In the thickened parallel edges, both edge components have the same endpoints and stay apart at
  every regular height and interval coordinate. The quotient is not isomorphic to a single edge.
- The single edge refined over `0 < 1/2 < 1` is presented over `0 < 1` through the refinement
  isomorphism, so its quotient is a graph object. With its own presentation over `0 < 1/2 < 1`, its
  identity induces a graph map across the two lists, and the comparison square holds.
- A self-map of the thickened parallel edges swaps the two edges and, at height `t`, moves the
  interval coordinate `s` to `s + t (1 - t) (1 - s)`. Its regular fiber maps at `1/2` and `3/4`
  differ pointwise, while its component data map is the edge swap. The naturality square is
  computed on strip points and holds in the slice.
- On the thickened pinch, the forward strip and cylinder formulas and the inverse vertex formula
  hold together with their heights.
- For the parallel edges, the projection followed by the comparison is the realization of the
  canonical data isomorphism, pointwise and in the slice. The functor to graph objects is applied
  to the thickened pinch.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*:

- §2.2: an object of ℝ-**Top**ᶜ is an ℝ-space isomorphic to the quotient of the vertex pieces
  `𝕍ᵢ × {aᵢ}` and the cylinders `𝔼ᵢ × [aᵢ, aᵢ₊₁]` by the endpoint identifications, with compact
  locally path-connected pieces, and its morphisms are those of ℝ-**Top**. Here this is
  `IsConstructibleSpace` with the full subcategory `ConstructibleSpaceCat`. Compactness and local
  path-connectedness are hypotheses on the pieces, not fields of a presentation.
- §2.4, Proposition 2.12: the Reeb functor carries constructible ℝ-spaces to ℝ-graphs. Its proof
  takes `Vᵢ = π₀(𝕍ᵢ)`, `Eᵢ = π₀(𝔼ᵢ)`, `ℓᵢ = π₀[𝕝ᵢ]` and `rᵢ = π₀[𝕣ᵢ]` (`componentData`). It uses the
  levelset-preserving bijection from the Reeb graph to this graph, which is
  `quotientComponentGraphMap` in the same direction. It proves continuity through the disjoint
  union of the pieces and two quotient maps, because path components of a locally path-connected
  space are open; here this is `componentGraphMap`, descended through the universal property of
  the quotient. It concludes by the compact-to-Hausdorff theorem
  (`quotientComponentGraphHomeomorph`). The source calls the bijection tautological, since the
  points of the graph are the path components of the levelsets; here that identification is the
  fiber normal form `componentGraphMap_eq_iff`, proved from the normal form of points of the
  realization.
- §2.4, after Proposition 2.13: the Reeb functor is read as a functor ℝ-**Top**ᶜ → **Reeb**. Here
  this is `quotientRGraphFunctor` into `RGraphCat`.
- §2.2, Lemma 2.4: the incidence diagrams (2.5) and their naturality (2.6) on path components give
  the incidence squares of `componentDataHom`.
- §2.3, remark after Proposition 2.8: the union of critical sets is a common critical set. Maps
  between objects presented over different lists are covered by the induced graph map and its
  comparison square, and their finite description over a common refinement is the classification
  of `reeb-rgraph.md`.

Not claimed here: refinement of presentations with non-discrete pieces; a component data map or a
data-level formula for maps between presentations over different lists of levels; a `T2Space` or
`CompactSpace` instance for Reeb quotients in general; a minimal or canonical critical set; the
packaging in universes other than `0`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/html/1501.04147v1).
