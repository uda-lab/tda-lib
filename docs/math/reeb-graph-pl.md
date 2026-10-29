# Piecewise-linear heights and incidence components of graph realizations

## Piecewise-linear height

For `V : Type u`, `G : SimpleGraph V` and vertex heights `h : V → ℝ`, the affine height of a dart
`d` at `t : unitInterval` is

```lean
dartHeight h d t = (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd
```

It satisfies the reversal equation `dartHeight h d.symm (σ t) = dartHeight h d t` at every `t`
(`dartHeight_symm`) and the start equation `dartHeight h d 0 = h d.fst`, the two compatibilities of
the universal lift of the realization (`reeb-graph-realization.md`); the end equation
`dartHeight h d 1 = h d.snd` also holds. Hence

```lean
plHeight G h : C(Realization G, ℝ)
plHeight G h (vertex G v)      = h v
plHeight G h (edgePoint G d t) = dartHeight h d t
```

both by `rfl`, and `plHeight G h` is the only continuous map with these values
(`plHeight_unique`). By uniqueness, translating every vertex height by `c` translates the
piecewise-linear height: `plHeight G (fun v => h v + c) = plHeight G h + ContinuousMap.const _ c`
(`plHeight_add_const`, pointwise `plHeight_add_const_apply`). Equal endpoint heights are allowed; a horizontal dart has constant height
(`dartHeight_of_eq`). For an order-convex set `s ⊆ ℝ`, the real parameters `r` with
`(1 - r) h d.fst + r h d.snd ∈ s` form an order-convex set, also when the dart is horizontal
(`ordConnected_preimage_lineHeight`); intersected with `[0, 1]` it is convex.

For any `s t r : unitInterval`, `plHeight_edgeSegment_bounds` bounds the height at
`edgeSegment G d s t r` between its values at `edgePoint G d s` and `edgePoint G d t`. It needs no
ordering or distinctness assumption on the endpoint parameters or heights.

## Unoriented edges and support

An unoriented edge is an element of mathlib's edge set `G.edgeSet`, not a dart. The edge of a dart
is `dartEdge d = ⟨d.edge, d.edge_mem⟩`, and two darts have the same edge exactly when they are
equal or opposite (`dartEdge_eq_iff`, from mathlib's `dart_edge_eq_iff`). Every edge is the edge of
a dart, and every endpoint of an edge is the start of one of its darts (`exists_dartEdge_eq`,
`exists_dartEdge_eq_fst`).

For an open interval `I : OpenInterval` (possibly `⊥`, a ray or `⊤`),

```lean
EdgeActive G h I e ↔ ∃ d, dartEdge d = e ∧ ∃ t, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ I
```

holds by definition: some dart of `e` has an interior parameter in the height preimage. The other
forms are theorems:

- **Orientation independence.** Any one dart of an active edge has such a parameter
  (`edgeActive_dartEdge_iff`, `EdgeActive.exists_mem`); the opposite dart uses the reversed
  parameter `σ t`, which is again interior.
- **Monotonicity.** `I ≤ J` and activity over `I` give activity over `J` (`EdgeActive.mono`).
- **Nonempty parameter set.** `EdgeActive G h I (dartEdge d)` is equivalent to
  `Nonempty {t : unitInterval // dartHeight h d t ∈ I}` (`edgeActive_dartEdge_iff_nonempty`). The
  direction from a parameter that may be an endpoint uses the openness of `I`: the preimage of `I`
  under the continuous affine map is a neighbourhood of `t ∈ [0, 1] = closure (0, 1)`, so it meets
  `(0, 1)` (`exists_interior_of_mem`).
- **Surviving endpoints.** If an endpoint of `e` has its height in `I`, then `e` is active
  (`edgeActive_of_mem`).
- **Horizontal edges.** An edge with `h d.fst = h d.snd` is active exactly when that common height
  lies in `I` (`edgeActive_dartEdge_iff_of_eq`).

Two parameters of one dart whose heights lie in `I` are joined by a path inside
`plHeight G h ⁻¹' I`: the convex parameter set is path connected, and its paths are mapped by the
edge map after `projIcc` (`joinedIn_edgePoint`).

## The incidence graph

The nodes over `I` are

```lean
Cell G h I = {v : V // h v ∈ I} ⊕ {e : G.edgeSet // EdgeActive G h I e}
```

the surviving vertices and the active unoriented edges. In `cellGraph G h I` a vertex node `v` and
an edge node `e` are adjacent exactly when `↑v ∈ ↑↑e`; there is no vertex–vertex and no edge–edge
adjacency (`not_cellGraph_adj_inl_inl`, `not_cellGraph_adj_inr_inr`), and the graph is bipartite
between the two summands (`cellGraph_isBipartiteWith`). An edge node can be adjacent only to
surviving endpoints, so an active edge with no surviving endpoint is an isolated node. For a finite
vertex type there are finitely many nodes (`instFiniteCell`).

For `I ≤ J`, `cellInclusion G h hIJ : cellGraph G h I →g cellGraph G h J` keeps each vertex and edge
and transports its membership proof (`cellInclusion_inl`, `cellInclusion_inr`, both `rfl`), with
`cellInclusion_refl` and `cellInclusion_comp`. It keeps the summand, so no edge goes to a vertex.
The incidence-component precosheaf is

```lean
cellComponentFunctor G h : OpenInterval ⥤ Type u
(cellComponentFunctor G h).obj I = (cellGraph G h I).ConnectedComponent
(cellComponentFunctor G h).map i c = c.map (cellInclusion G h (leOfHom i))
```

## Path components of interval preimages

```lean
preimageComponentsEquiv G h I :
    ZerothHomotopy {p : Realization G // plHeight G h p ∈ I} ≃ (cellGraph G h I).ConnectedComponent
```

has no endpoint-coverage, finiteness, injectivity, nonemptiness or decidability hypothesis. Its
formulas are:

- the class of a surviving vertex `vertex G v` goes to the class of its vertex node
  (`preimageComponentsEquiv_mk_vertex`);
- the class of an edge point `edgePoint G d t` in the preimage, endpoints included, goes to the
  class of the node of `dartEdge d` (`preimageComponentsEquiv_mk_edgePoint`);
- if the start or end of `d` survives, that edge point also goes to the class of the endpoint's
  vertex node (`preimageComponentsEquiv_mk_edgePoint_of_fst_mem`, `_of_snd_mem`); the vertex and
  edge nodes are adjacent (`connectedComponentMk_inl_eq_inr`);
- the inverse sends a vertex node to the class of the vertex, by `rfl`
  (`preimageComponentsEquiv_symm_inl`), and an edge node to the class of `edgePoint G d t` for
  every dart `d` of the edge and every `t` with `dartHeight h d t ∈ I`
  (`preimageComponentsEquiv_symm_inr`).

Both inverse laws are fields of the equivalence. For a finite vertex type the preimage has
finitely many path components (`finite_zerothHomotopy`).

**Forward map.** `optionLabel G h I : Realization G → Option (cellGraph G h I).ConnectedComponent`
is defined by the set-level universal lift `lift`. A vertex gets the class of its node if it
survives and `none` otherwise; an edge point `(d, t)` gets the class of the node of `dartEdge d` if
`dartHeight h d t ∈ I` and `none` otherwise. The reversal generator holds because
`dartEdge d.symm = dartEdge d` and the height is reversal invariant; the start generator holds
because both values are `none` or the two nodes are adjacent. The descent therefore checks only
the two generators, for every representative, and no chain of the generated equivalence relation
is examined. No continuity of `optionLabel` is claimed, and a continuous extension off the
preimage need not exist.

On the preimage the label is `some`, and `preimageLabel G h I` is its value. Continuity uses only
the open preimage `U = plHeight G h ⁻¹' I`. The restriction of the quotient map `quotMk` over `U` is
a quotient map (`Topology.IsQuotientMap.restrictPreimage_isOpen`), so it suffices that the raw
label is locally constant on the subspace `quotMk ⁻¹' U` of the cells. It is constant on the trace
of each open vertex cell `{inl v}` and of each open dart interval `inr '' range (Sigma.mk d)`
(`isLocallyConstant_preimageLabel`). Openness of `quotMk` is not used and does not hold in general:
the open vertex cell `{inl v}` maps to the point `vertex G v`, which is not open when `v` has an
incident edge. With the discrete topology chosen
locally on the component type, `TDA.Reeb.joined_eq_of_discrete` makes the label constant along
paths in `U` (`preimageLabel_eq_of_joined`), and the forward map is its lift to path components.

**Inverse.** `cellPoint G h I` sends a vertex node to the class of its point and an edge node to the
class of an interior support witness chosen by `Classical.choose`. The choice is arbitrary and not
canonical. Different witnesses, on either dart of the edge, give one class
(`mk_edgePoint_eq_of_dartEdge_eq`): an opposite dart is rewritten by `edgePoint_symm`, and two
parameters of one dart are joined in its convex fragment. Hence the value is the class of every
support witness (`cellPoint_inr`), and adjacent nodes have equal values, since a dart starting at a
surviving vertex is a witness at the parameter `0`. Walk induction (`eq_of_walk`) makes `cellPoint`
descend to graph components. The left inverse law is induction on the realization (`ind`); the
right inverse law is `ConnectedComponent.ind`.

## Naturality and the functor

For `I ≤ J` and every class `c`,

```lean
preimageComponentsEquiv G h J
    (TDA.Reeb.componentMap (preimageInclusion (plHeight G h) (toOpens_le_iff.2 hIJ)) c) =
  (preimageComponentsEquiv G h I c).map (cellInclusion G h hIJ)
```

(`preimageComponentsEquiv_componentMap`, and as an equation of functions
`preimageComponentsEquiv_comp_componentMap`). Both maps keep the underlying point and the
underlying vertex or edge, so both generator cases are the vertex and edge-point formulas over `J`.
The inclusion proof is spelled `toOpens_le_iff.2 hIJ`; any other proof of the same inclusion gives
the same map by proof irrelevance, and the square also applies to the functor action of
`intervalComponents`. Inclusions may merge classes; they cannot split them.

```lean
intervalComponentsIso G h : intervalComponents (plHeight G h) ≅ cellComponentFunctor G h
```

is `NatIso.ofComponents` of the equivalences, with the square as naturality
(`intervalComponentsIso_hom_app`, `intervalComponentsIso_inv_app`, both `rfl`). Here
`intervalComponents f = OpenInterval.toOpensFunctor ⋙ componentFunctor f` is the interval
path-component precosheaf (`reeb-components.md`), and both functors land in `Type u`.

## Vertex-only corollary

```lean
EndpointCoverage G h I : Prop :=
  ∀ e : G.edgeSet, EdgeActive G h I e → ∃ v ∈ (e : Sym2 V), h v ∈ I
```

Under this hypothesis,

```lean
cellInducedEquiv G h I hcov :
    (cellGraph G h I).ConnectedComponent ≃ (G.induce (h ⁻¹' (I : Set ℝ))).ConnectedComponent
preimageInducedEquiv G h I hcov :
    ZerothHomotopy {p : Realization G // plHeight G h p ∈ I} ≃
      (G.induce (h ⁻¹' (I : Set ℝ))).ConnectedComponent
```

The map from induced-graph components to incidence components sends a vertex to its node
(`inducedToCell`); adjacent surviving vertices meet at their active edge, so it needs no coverage.
In the other direction an edge node goes to a surviving endpoint chosen by `coverEndpoint`; two
surviving endpoints of one edge are equal or adjacent in the induced graph
(`induce_mk_eq_of_mem`), so only the class is determined and no canonical endpoint is promised. The
formulas hold for surviving vertices (`cellInducedEquiv_inl`, `preimageInducedEquiv_mk_vertex`) and
send an edge node or an edge point to the class of any surviving endpoint of its edge
(`cellInducedEquiv_inr`, `preimageInducedEquiv_mk_edgePoint`). This is a component argument, not a
graph homomorphism contracting edges.

The hypothesis is necessary and is stated explicitly. For one edge of heights `0` and `2` and
`I = (0, 2)` or `(1/2, 3/2)`, no vertex survives while the preimage is one open arc, so no
equivalence with the induced-graph components exists; subdividing at the vertex heights or taking
critical interval endpoints does not remove this case. Over the full interval coverage holds
(`endpointCoverage_top`), and the comparison through the full incidence graph agrees with the
realization's `componentsEquiv` (`full_componentsEquiv`).

The corollary is stated pointwise in `I`; no naturality is stated for it. For a nonempty `I ≤ J`,
coverage at `I` implies coverage at `J`: an edge active over `J` with no endpoint height in `J` has
`J` inside its open height range, so it is active over `I` with no endpoint height in `I`. This
implication is not formalized here. It fails when `I` is empty: every graph is covered over `⊥`,
while the edge above is not covered over `(1/2, 3/2)`.

## Names, universes and finiteness

The production modules are `TDA/Reeb/GraphPLHeight.lean` and `TDA/Reeb/GraphPLComponents.lean`,
both in namespace `TDA.Reeb.GraphPL`; the fixtures are `TDA/Reeb/GraphPLHeightExamples.lean` and
`TDA/Reeb/GraphPLComponentsExamples.lean`, in namespace `TDA.Reeb.Examples.GraphPL`. No production
module imports the fixtures. The vertex type has an arbitrary universe `u`, and `Cell G h I`,
`cellComponentFunctor G h` and the preimage path components live in `Type u`.

Every comparison law holds for an arbitrary vertex type; finite graphs are a direct instance.
`[Finite V]` occurs only in `instFiniteCell` and `finite_zerothHomotopy`. No decidable adjacency,
nonempty vertex type, injectivity of heights or orientation choice is assumed, and no topology on
`V` is assumed. `cellInclusion` takes `G` and `h` explicitly, since `hIJ` does not determine them. The
private helpers are the vertex and edge parts of the label and their four equations. The reversal
`unitInterval.symm` is written with a local notation `σ`, because `open unitInterval` would make `I`
a token and clash with the interval variable.

`eq_of_walk` states that a function on the vertices of a simple graph that respects adjacency is
constant along walks; a pattern search of pinned mathlib's `Combinatorics/SimpleGraph` found no
such lemma, which is not a proof that none exists.

Fully qualified names are distinct from all other library names, but some short names are not.
`mk_eq_of_joinedIn` also occurs in `TDA.Reeb.CylinderPresentation`, and the last component `mono`
of `EdgeActive.mono` also occurs as `TDA.Reeb.Interleaving.mono` and
`TDA.Filtration.FilterFunction.mono`. The private helpers `vertexLabel` and `edgeLabel` share their
short names with `TDA.Reeb.FiniteReebData.vertexLabel` and `edgeLabel`; being private, they do not
clash. Among the fixtures, `quarter` and `coe_quarter` also occur in
`TDA.Reeb.Examples.ConstructibleSmoothing`, `d01` in `TDA.Reeb.Examples.GraphRealization`, and
`support_mono` as `TDA.Filtration.support_mono`. A file opening more than one of these namespaces
qualifies the overlapping names.

## Fixtures

The single edge is `⊤ : SimpleGraph Bool` with the dart `d₀ : false → true` from
`TDA.Reeb.Examples.GraphRealization`, with heights `h02 = (0, 2)` unless stated otherwise.

`TDA.Reeb.GraphPLHeightExamples` proves:

- **Reversal formulas.** `dartHeight h02 d₀ t = 2t` and `dartHeight h02 d₀.symm t = 2 - 2t` for
  every `t`, with the reversal equation at every `t` (`dartHeight_d₀`, `dartHeight_d₀_symm`,
  `d₀_reversal`). At `t = 1/4` the two orientations have heights `1/2` and `3/2`
  (`orientation_quarter_ne`); at `t = 1/2` they agree (`orientation_half_eq`), so a witness at the
  midpoint alone cannot discriminate orientation.
- **Support.** Over `(1/4, 3/4)` the edge is active although neither endpoint height lies in it,
  the midpoint is not a witness, and the reversed dart supports the edge at the reversed parameter
  (`support_interior_active`, `support_interior_no_endpoint`, `support_half_not_witness`,
  `support_reversed_witness`). Over `(-∞, 1/2)` one endpoint survives, the other does not, and the
  edge is active, with an interior witness obtained from the endpoint by openness
  (`support_endpoint_active`, `support_endpoint_other_out`, `support_endpoint_interior`). Over
  `(3, ∞)` the edge is inactive (`support_inactive`), and activity passes from `(1/4, 3/4)` to
  `(0, 2)` (`support_mono`).
- **Horizontal edge.** With constant height `1` the edge is active over `I` exactly when `1 ∈ I`,
  so it is active over `(0, 2)` and inactive over `(2, 3)` (`horizontal_active_iff`,
  `horizontal_inside_active`, `horizontal_outside_inactive`).

`TDA.Reeb.GraphPLComponentsExamples` proves:

- **Empty interval and empty vertex type.** For every graph, there is no node, no incidence
  component and no preimage path component over `⊥` (`cell_bot_isEmpty`,
  `cellComponents_bot_isEmpty`, and `preimage_bot_isEmpty` from `intervalComponents_obj_bot_isEmpty`).
  For every graph on an empty vertex type `[IsEmpty V]`, there is no node over any interval
  (`cell_isEmpty_of_isEmpty`), and the preimage has no path component
  (`preimage_isEmpty_of_isEmpty`). The latter is derived through the comparison to exercise it; it
  also follows from `instIsEmptyRealization` and `TDA.Reeb.componentFunctor_obj_isEmpty_of_isEmpty`.
  This fixture is about an empty vertex type, not about edgeless graphs on a nonempty type, which
  the general theorem also covers.
- **One edge of heights `0` and `2`.** For every `I` with `1 ∈ I` and `0, 2 ∉ I`: no vertex
  survives (`single_no_vertex`), exactly one unoriented edge is active (`single_activeEdge_eq`), the
  only node is its edge node (`single_cell_eq`), and both the incidence components and the preimage
  path components number exactly one (`single_card_cell`, `single_card_preimage`). Edge points of
  both darts lie in one class (`single_opposite_darts`). Endpoint coverage fails, the induced graph
  has no component, and no equivalence of the preimage path components with the induced-graph
  components exists (`single_not_endpointCoverage`, `single_induce_isEmpty`,
  `single_no_vertexOnly_equiv`). These are instantiated at `I = (0, 2)` (`zeroTwo_*`) and
  `I = (1/2, 3/2)` (`half_*`). At `t = 1/3` the two darts give two distinct points in one class
  (`opposite_points_ne`, `opposite_points_same_class`).
- **Horizontal edge.** With constant height `1`, over `(0, 2)` every node lies in the class of the
  edge node and the preimage has one path component (`horizontal_cell_class`,
  `horizontal_inside_card_cell`, `horizontal_inside_card`); over `(2, 3)` the preimage and the node
  type are empty (`horizontal_outside_preimage_isEmpty`, `horizontal_outside_cell_isEmpty`).
- **Ray.** Over `(1, ∞)` exactly the endpoint of height `2` survives, and the edge is truncated to
  the parameters above `1/2` (`ray_true`, `ray_false`, `ray_truncated`). Coverage holds, the
  preimage has one path component, and every truncated edge point lies in the class of the
  surviving vertex (`ray_endpointCoverage`, `ray_card`, `ray_edgePoint`, `ray_edge_class`).
- **4-cycle.** On `cycleGraph 4` with heights `0, 1, 2, 1` and `I = (1/2, 3/2)`, the surviving
  vertices are exactly `1` and `3` (`h4_mem_I4`). Their incidence classes are distinct, by a side
  function that every adjacency preserves (`c4Side_adj`, `c4_cell_ne`), and every class is one of
  them (`c4_cell_classification`, `c4_card_cell`). The preimage classes `x1` and `x3` of the two
  vertices are distinct and exhaustive (`c4_x1_ne_x3`, `c4_preimage_classification`,
  `c4_card_preimage`), and the edge points at parameter `3/4` of the darts `0 → 1` and `2 → 3` lie in
  the classes of `1` and `3` (`c4_d01_class`, `c4_d23_class`).
- **Proper inclusion.** For `I < J = (-1/2, 5/2)` (`I4_lt_J4`) the two classes merge through
  `ConnectedComponent.map (cellInclusion …)` (`c4_J_cell_merge`), through
  `TDA.Reeb.componentMap (preimageInclusion …)` (`c4_J_preimage_merge`), on both sides of the square
  (`c4_square_x1`, `c4_square_x3`) and through the packaged functors (`c4_functor_merge`). Since
  `x1 ≠ x3` over `I`, the merge discriminates.
- **Vertex-only corollary.** It holds on the 4-cycle, where the induced-graph classes of `1` and `3`
  are distinct (`c4_endpointCoverage`, `c4_vertexOnly_x1`, `c4_vertexOnly_x3`,
  `c4_vertexOnly_ne`), and on the ray; the single edge above is the counterexample to the
  unconditional version.

## Vertex-height perturbations of a fixed graph

Fix `G : SimpleGraph V` and two vertex-height functions `h g : V → ℝ` on the same graph. On a dart
`d` at parameter `t`,

```lean
dartHeight h d t - dartHeight g d t = (1 - t) * (h d.fst - g d.fst) + t * (h d.snd - g d.snd)
```

is a convex combination of the two endpoint displacements. Hence `|h v - g v| ≤ ε` for every
vertex gives `|dartHeight h d t - dartHeight g d t| ≤ ε` (`abs_dartHeight_sub_le`) and, by
quotient induction over vertices and edge points,

```lean
∀ x : Realization G, |plHeight G h x - plHeight G g x| ≤ ε
```

(`abs_plHeight_sub_le`). These statements hold for `V` in any universe and for every simple graph,
with `ε : ℝ` arbitrary; no finiteness, connectivity, nonemptiness or injectivity of heights is
assumed. Nothing relates the orders of the two height functions: vertex heights may cross, coincide
or separate, so the number of distinct heights and the set of horizontal edges may change.

Vertex evaluation gives the converse inequality. In mathlib's uniform extended distance on
`α →ᵤ ℝ` (`UniformFun`, `edist f g = ⨆ x, edist (f x) (g x)`),

```lean
edist (ofFun (plHeight G h)) (ofFun (plHeight G g)) = edist (ofFun h) (ofFun g)
```

for every `V` (`edist_ofFun_plHeight`). For `[Fintype V]` the right side is the product extended
distance `edist h g = Finset.univ.sup fun v => edist (h v) (g v)`, a finite maximum seeded at `0`
(`edist_ofFun_plHeight_eq_edist`); for empty `V` both sides are `0`. This equality concerns the
two piecewise-linear heights. The Reeb quotients below satisfy only an inequality.

Applying the general uniform-perturbation interleaving `perturbationInterleaving` to the
pointwise bound gives `vertexHeightInterleaving G hhg`, an `ε`-interleaving of
`intervalComponents (plHeight G h)` and `intervalComponents (plHeight G g)` for `ε : ℝ≥0`
(`vertexHeightInterleaving_eq`). Its forward map at `I` sends the path component of
`x ∈ plHeight G h ⁻¹' I` to the path component of the same point in `plHeight G g ⁻¹' T_ε I`, and
its backward map is the same construction with `h` and `g` exchanged
(`vertexHeightInterleaving_φ_app_mk`, `vertexHeightInterleaving_ψ_app_mk`). Consequently
`interleavingDistance_intervalComponents_plHeight_le` bounds the interleaving distance of the two
precosheaves by `ε`. Composing `edist_ofFun_plHeight` with the sup-distance stability theorem
`interleavingDistance_intervalComponents_le_edist` of `TDA/Reeb/Stability.lean` bounds it by the
uniform distance of the vertex heights
(`interleavingDistance_intervalComponents_plHeight_le_edist_ofFun`), and by `edist h g` for
`[Fintype V]` (`interleavingDistance_intervalComponents_plHeight_le_edist`).

For `V : Type` and `[Finite V]`, the geometric interleaving distance of `graphPLReebGraph G h` and
`graphPLReebGraph G g` is that precosheaf distance (`geometricInterleavingDistance_graphPLReebGraph`
in `TDA/Mapper/GraphPLReebQuotient.lean`). Therefore

```lean
geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤ ε
geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤
  edist (ofFun h) (ofFun g)
geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) ≤ edist h g
```

(`geometricInterleavingDistance_graphPLReebGraph_le` under the vertex budget `ε : ℝ≥0`,
`geometricInterleavingDistance_graphPLReebGraph_le_edist_ofFun`, and
`geometricInterleavingDistance_graphPLReebGraph_le_edist` for `[Fintype V]`). None of them takes
a critical-value list, an order condition on the heights, a fixed number of distinct heights or a
constructibility proof. The height range of `graphPLReebGraph G h` is the range of `plHeight G h`
(`heightRange_graphPLReebGraph`), which supplies the lower bounds in the fixtures. The universe-zero
restriction comes from the real-graph category; the pointwise and uniform statements have none.

Vertical translation is exact already for interval components: for continuous `f` on a nonempty
space with range bounded below, `intervalComponents (f + c)` is the translate
`translatePre c (intervalComponents f)` and
`interleavingDistance (intervalComponents f) (intervalComponents (f + c)) = ‖c‖₊`
(`interleavingDistance_intervalComponents_add_const` in `TDA/Reeb/IntervalTranslation.lean`;
the upper bound is `translationInterleaving`, the lower bound the obstruction at a short interval
around the infimum of the range, and the identity height of `ℝ` shows that `BddBelow` is needed). With
`plHeight_add_const` this rederives `geometricInterleavingDistance_graphPLReebGraph_add_const`.

The estimate controls the piecewise-linear extension only. A continuous function on the
realization with the same vertex values as `plHeight G h` can differ from it by any amount inside
an edge.

The production modules are `TDA/Reeb/GraphPLVertexPerturbation.lean` (namespace
`TDA.Reeb.GraphPL`) and `TDA/Mapper/GraphPLReebStability.lean` (namespace `TDA.Mapper.GraphPL`).
The fixtures are `TDA/Reeb/GraphPLVertexPerturbationExamples.lean` and
`TDA/Mapper/GraphPLReebStabilityExamples.lean`:

- **Empty vertex type and equal heights.** Any two heights on `Empty` give uniform distance `0`
  between their piecewise-linear heights and geometric distance `0` between their Reeb quotients
  (`empty_edist_ofFun_plHeight`, `empty_geometricInterleavingDistance`). On the single edge, equal
  heights give the same two zeros through the vertex-height bound
  (`tilted_self_geometricInterleavingDistance`).
- **One vertex.** At heights `a` and `b` the Reeb quotients are at distance exactly `|a - b|`; the
  lower bound is the Hausdorff distance `{a}` to `{b}` of the height ranges
  (`point_geometricInterleavingDistance`).
- **Single edge from `(0, 0)` to `(0, 1)`.** The vertex-height set `{0}` becomes `{0, 1}` and the
  horizontal edge becomes nonhorizontal. The vertex heights are at product distance `1`
  (`edist_flat_tilted`), the piecewise-linear heights are at uniform distance exactly `1`
  (`flat_tilted_edist_ofFun_plHeight`), and the Reeb quotients are at geometric distance exactly
  `1`; the lower bound compares the suprema `0` and `1` of the height ranges
  (`flat_tilted_geometricInterleavingDistance`).
- **Reversal and collision.** On the single edge, `(0, 1)` to `(1, 0)` reverses the endpoint
  order. The vertex swap `swapHomeomorph` carries one height to the other, so the Reeb quotients
  are isomorphic and at distance `0`, strictly below `edist h g = 1`
  (`reversal_geometricInterleavingDistance`). The heights `(0, 1)` to `(1/2, 1/2)` make the edge
  horizontal and give distance at most `1/2` (`collision_geometricInterleavingDistance_le`).
- **Disconnected graph.** On two disjoint edges, which do not form a connected graph, raising one
  edge by `1` gives distance at most `1` (`twoEdges_geometricInterleavingDistance_le`).
- **Interior bump.** On the single edge, the continuous function `bump` has vertex values `0` and
  value `4t(1 - t)` on either dart. Its vertex displacement from the zero height is `0`, but it
  differs from `plHeight edgeGraph 0` by `1` at the midpoint, so their uniform distance is at
  least `1` (`bump_not_controlled`).

## Height-controlled maps between graph-PL spaces

For continuous heights `f : C(X, ℝ)` and `g : C(X', ℝ)`, a `HeightMapPair f g ε` consists of
continuous maps in both directions with height error at most `ε`. Each composite must be joined
to the identity by paths whose height remains within `2ε` of its starting value. The pair induces
an `ε`-interleaving of `intervalComponents f` and `intervalComponents g`, hence bounds their
interleaving distance. Identity maps and constant paths recover `perturbationInterleaving` from a
pointwise perturbation bound.

For finite graph vertex types, applying the same criterion to the piecewise-linear heights bounds
the geometric interleaving distance of their Reeb quotients
(`geometricInterleavingDistance_graphPLReebGraph_le_of_heightMapPair`). The fixtures include a
zero-distance collapse from the zero-height interval to the zero-height point, the exact distance
`1/2` from an edge of height range `[0, 1]` to a point at height `1/2`, recovery of the fixed-graph
perturbation interleaving, and a discrete two-point-to-one-point negative control whose distance
is `⊤`.

This sufficient criterion has no converse or functional-distortion identity. No optimality claim
is made for the `2ε` path-deviation allowance. No comparison morphism in `RGraphCat`, map of Reeb
quotients, or consequence for Mapper covers or reconstructions is established; the Mapper
homology consequences of a height-map pair (`realInterleavingDistance_centredMapperPair_graphPL_le`,
`bottleneck_cappedCentredDiagram_pair_plHeight_le`) are recorded in [the Mapper digest](mapper.md). The
criterion is a library result;
its fixed-space specialization recovers the perturbation result attributed above to de Silva, Munch
and Patel.

## Source correspondence

This is a library formulation of the standard combinatorial description of path components of
interval preimages of a piecewise-linear height on a graph. No cited source states these theorems,
and none is attributed to a source.

**de Silva, Munch and Patel.** *Categorified Reeb Graphs*, Notation 2.7, presents an ℝ-graph as a
quotient of vertex points over critical values and edge intervals between consecutive critical
values, with edges monotone in height, no horizontal edges and no reversal relation. Example 3.3
takes path components of inverse images of open intervals as a pre-cosheaf, which is
`intervalComponents`. Both are context only. The comparison here covers piecewise-linear heights on
arbitrary simple graphs, with horizontal edges, no ordering of critical values, and every open
interval including `∅`, rays and `ℝ`. It is not Proposition 3.12, Theorem 3.17 or Proposition 3.18
of the paper, and none of them is cited for it.

**reeb-ordering.** `uda-lab/reeb-ordering`,
[`ReebOrdering/InterpolationBridge.lean`](https://github.com/uda-lab/reeb-ordering/blob/aa7d10f4f7dc0474b76f17ea81afcab5a230d521/ReebOrdering/InterpolationBridge.lean#L22-L38)
at commit `aa7d10f4f7dc0474b76f17ea81afcab5a230d521`, states as a hypothesis,
`IsInterpolationBridge`, that every ε-isomorphism of its semi-discrete objects extends to their
interpolations, and derives an interleaving-distance bound from it
(`interleavingDistance_le_of_isInterpolationBridge`); its module docstring says it does not
formalise the continuous Reeb graph, triangulation or piecewise-linear interpolation. Nothing from
it is used or imported. The comparison here concerns one height function; it does not prove that
hypothesis and states no distance or interleaving comparison.

**Mathlib and TauCeti.** Pinned mathlib has `SimpleGraph.incidenceSet`, the multigraph
`Graph.ofSimpleGraph` (`Mathlib/Combinatorics/Graph/Simple.lean`), the abstract simplicial complex
`Geometry.AbstractSimplicialComplex.ofSimpleGraph` and the affine simplicial complex
`Geometry.SimplicialComplex.ofSimpleGraph` in `V →₀ 𝕜`
(`Mathlib/Analysis/Convex/SimplicialComplex/AffineIndependentUnion.lean`). None provides a
piecewise-linear height, a vertex–edge incidence `SimpleGraph` or a comparison of preimage
components; the realization used here is the dart-cell quotient of `reeb-graph-realization.md`. A
keyword search of `Mathlib/Combinatorics` for incidence-graph, subdivision-graph and Levi-graph
constructions finds none. TauCeti, at revision `53179609555d7535017bfe43c77ed61c14be38ee`, has
13,128 `.lean` files. No file path names Reeb graphs, and no path naming subdivision or
piecewise-linear structure names graphs. Its only path naming incidence,
`TauCeti/AlgebraicTopology/Cellular/Incidence.lean`, concerns cellular incidence coefficients of CW
complexes; `TauCeti/AlgebraicTopology/PathComponent.lean` concerns fundamental groups of a path
component; and its `SimpleGraph` files lie under `TauCeti/Combinatorics/SimpleGraph/` and in
`TauCeti/LinearAlgebra/RootSystem/FiniteType/SimpleGraph.lean`. This is a partial check by file
path and module docstring, not a content-level inspection of every file, so it does not establish
that TauCeti has no such comparison. Nothing from TauCeti is used, and TauCeti is not a dependency.

**Vertex-height perturbations.** The general step, that a uniform bound `|f x - g x| ≤ ε` gives an
`ε`-interleaving of the interval-component precosheaves, is de Silva, Munch and Patel,
arXiv:1501.04147v1, Theorem 4.6(i), already formalised as `perturbationInterleaving`. The
vertex-to-edge estimate, the uniform-distance equality and the graph-PL Reeb-quotient bound are
library results and are not attributed to the paper.

**Extremal vertex heights.** For finite nonempty `V`, vertices attain the extremes of the
piecewise-linear height, and `plHeight_mem_Icc_of_forall` bounds every point, so
`sSup (range (plHeight G h)) = Finset.univ.sup' _ h` and `sInf (range (plHeight G h)) =
Finset.univ.inf' _ h` (`sSup_range_plHeight`, `sInf_range_plHeight`). The Hausdorff
edistance of the height ranges is at most the geometric interleaving distance, and on the real line
`ENNReal.ofReal |sInf s - sInf t| ≤ Metric.hausdorffEDist s t` for nonempty sets bounded below
(`ofReal_abs_sInf_sub_le_hausdorffEDist`, the twin of the supremum bound). Hence

```lean
ENNReal.ofReal |sup' h - sup' g| ≤ geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g)
ENNReal.ofReal |inf' h - inf' g| ≤ geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g)
```

(`ofReal_abs_sup'_sub_le_geometricInterleavingDistance_graphPLReebGraph`, the `inf'` form and the
`max` form), for arbitrary `G`, `h`, `g`. If `edist h g` equals one of the two displacements, the
distance equals `edist h g` (`geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_sup'`
and `_of_inf'`). For every `c : ℝ`, the distance between `h` and the translate
`fun v => h v + c` is `ENNReal.ofReal |c|`, because `edist h (fun v => h v + c)` is
`ENNReal.ofReal |c|` and both extremes move by `c`
(`geometricInterleavingDistance_graphPLReebGraph_add_const`); the graph may be disconnected or
contain cycles. For empty `V` the distance is `0`
(`geometricInterleavingDistance_graphPLReebGraph_of_isEmpty`). The reversal `(0, 1)` to `(1, 0)` on a
single edge has equal maxima and equal minima, distance `0` and `edist h g = 1`: the lower bounds
are attained there, and the upper bound `edist h g` is not. Minimal displacement alone is detected only by the `inf'` bound:
on a single edge, `(0, 1)` against `(-1, 1)` has equal maxima and distance exactly `1`. These
statements are library results.

**Component counts.** If no vertex height lies in `I`, the incidence graph over `I` has no edges,
and its components are the active edges (`cellComponentsEquivActiveEdges`,
`card_cellComponents_eq_card_activeEdges`). If `h w ∈ I`, `EndpointCoverage G h I` holds and every
vertex with height in `I` is `w` or adjacent to `w`, the incidence graph over `I` is connected
(`card_cellComponents_eq_one`). At `⊤` the interval components of `plHeight G h` are as many as
the connected components of `G` (`card_intervalComponents_plHeight_top`). With the cardinality
obstruction of `reeb-interleaving-distance.md`, finite graphs `G` on `V` and `G'` on `V'` with
different numbers of connected components give
`geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G' h') = ⊤` for all
heights (`geometricInterleavingDistance_graphPLReebGraph_eq_top_of_card_ne`). This is a statement
about the distance only; no map between the two graphs is involved.

**Merge-height change.** Let `mergeY` be the tree on `Fin 4` with edges `0 — 2`, `1 — 2`, `2 — 3`,
and `mergeHeights a M = (0, 0, a, M)`: two leaves at `0` merge at the apex `2` at height `a`, below
the top vertex `3` at `M`. For `0 < a < b ≤ 2a` and `b ≤ M`,

```lean
geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
  (graphPLReebGraph mergeY (mergeHeights b M)) = ENNReal.ofReal (b - a)
```

(`geometricInterleavingDistance_mergeY`). The value is `edist (mergeHeights a M)
(mergeHeights b M)` (`edist_mergeHeights`), while both extremal displacements are `0`
(`max_ofReal_abs_sub_mergeHeights_eq_zero`). The upper bound is the vertex budget `b - a`. For the lower bound fix `ε < b - a` and `I = (0, b - 2ε)`, nonempty because
`ε < b - a ≤ b/2`. Then `T_ε I = (-ε, b - ε)` and `T_ε T_ε I = (-2ε, b)`.

- With the apex at `b`, no vertex height lies in `I`, the two leaf edges are active and the top
  edge is not, so there are two components over `I` (`card_cellComponents_mergeHeights_ioo`).
  Over `(-2ε, b)` the apex and the top vertex are still absent, and the two leaf edges stay in
  different components; for `ε > 0` each leaf vertex joins the component of its edge. The
  restriction from `I` is injective (`injective_cellComponentFunctor_mergeHeights_map`).
- With the apex at `a`, `-ε < a < b - ε`, every edge contains the apex and every other vertex is
  adjacent to it, so there is one component over `(-ε, b - ε)`
  (`card_cellComponents_mergeHeights_eq_one`).

The obstruction `1 < 2` holds for every `ε < b - a`, so `ENNReal.ofReal (b - a)` is a lower bound.
For every `0 < a < b ≤ M`, the exact distance is
`ENNReal.ofReal (min (b - a) (b / 2))` (`geometricInterleavingDistance_mergeY_eq_min`). The
continuous section `mergeSection c M` selects the point at each clamped height on the path
`0 — 2 — 3`; `plHeight_mergeSection` proves height preservation on `[0, M]`. Every point joins
the section point at its height by a path whose heights stay between that height and `c`, or are
constant when the input height exceeds `c` (`exists_mergeSection_path`). If `c = M`, a point on
the horizontal edge `2 — 3` joins vertex `2` along that edge at constant height `M`.
`mergeFoldHeightMapPair` supplies a map pair with error `b / 2`; together with the identity-map
budget `b - a`, it proves the upper bound by their minimum. For `b ≤ 2a` the formula gives `b-a`,
recovering `geometricInterleavingDistance_mergeY`; for `2a < b` it gives `b/2 < b-a`. Reflection
proves the exact split-tree formula `geometricInterleavingDistance_splitY_eq_min`. The new
exactness theorem is a library result; the cited source supplies the distance and perturbation
context, not this formula. The injectivity hypothesis of the
obstruction cannot be dropped: for `(0, 0, a, M)` against `(0, 0, 0, M)` with `ε = a` and
`I = (0, a/2)`, the counts are again `2` and `1`, but the apex height `a` lies in
`T_ε T_ε I = (-2a, 5a/2)`, both leaf edges reach one component there, and the vertex budget `a`
gives an `a`-interleaving (`mergeY_injective_needed`). The production module is
`TDA/Mapper/GraphPLReebMergeHeight.lean` (namespace `TDA.Mapper.GraphPL`), with fixtures in
`TDA/Mapper/GraphPLReebMergeHeightExamples.lean`: the numeric instance `a = 2`, `b = 3`, `M = 4` at
distance `1` with extremal and height-range bounds `0` (`mergeY_numeric`), the negative control
above, and two disjoint edges against a single edge at distance `⊤`
(`twoEdges_edge_geometricInterleavingDistance`). These are library results.

## Scaling heights

For a real scalar `s`, `OpenInterval.scale s I = {x | s * x ∈ I}` is an open interval,
including when `s ≤ 0`, and `scalePre s F = scaleFunctor s ⋙ F`. The endpoint formulas
`scale_ioo_of_pos` and `scale_ioo_of_neg` divide the endpoints by `s`, reversing their order
in the negative case. At zero the interval is `⊤` if `0 ∈ I` and `⊥` otherwise (`scale_zero`).
The thickening identity

```lean
thicken ε (scale s I) = scale s (thicken (‖s‖₊ * ε) I)
```

(`thicken_scale`) transports an `ε`-interleaving to a `‖s‖₊ * ε`-interleaving
(`Interleaving.scalePre`). For precosheaves into any category and `s ≠ 0`, scaling back by
`s⁻¹` proves `interleavingDistance_scalePre`: the distance is multiplied by
`(‖s‖₊ : ℝ≥0∞)`, including infinite distances. Reflection preserves distance
(`interleavingDistance_scalePre_neg_one`). The height identity
`intervalComponents (s • f) = scalePre s (intervalComponents f)` is definitional
(`intervalComponents_smul`); `interleavingDistance_intervalComponents_smul` applies to heights
on different topological spaces in the same universe.

For vertex types in any universe, `plHeight_smul` identifies the PL height of `fun v => s * h v`
with `s • plHeight G h`. For finite `V V' : Type`, arbitrary graphs `G`, `G'` and heights `h`,
`h'`, a common nonzero scale multiplies the geometric Reeb-quotient distance by
`ENNReal.ofReal |s|` (`geometricInterleavingDistance_graphPLReebGraph_smul`). The `_neg` form is
reflection invariance; `_affine` allows a common added constant after scaling.

The split tree has heights `splitHeights a M v = -mergeHeights a M v`. Reflection gives the
exact split-tree distance `b-a` for `0 < a < b ≤ 2a` and `b ≤ M`
(`geometricInterleavingDistance_splitY`), and for all `0 < a < b ≤ M` reflection of the exact
merge formula gives `ENNReal.ofReal (min (b-a) (b/2))`
(`geometricInterleavingDistance_splitY_eq_min`).

The modules are `TDA/Reeb/IntervalScaling.lean` and `TDA/Mapper/GraphPLReebScaling.lean`, with
fixtures in `TDA/Mapper/GraphPLReebScalingExamples.lean`: a point realizes the factor `|s|`;
scaling the numeric merge tree by `1/2` agrees with the direct distance `1/2`; the reflected
numeric tree has distance `1` with both extremal displacements zero; for apex heights `1`, `3`
below top height `4` the two-sided bound gives `[3/2,2]`, and the exact value `3/2` is
`mergeY_beyond_twice_exact` in `TDA/Mapper/GraphPLReebMergeFoldExamples.lean`. Two disjoint
edges and one edge stay at distance `⊤` under
zero scaling, whereas `0 * ⊤ = 0`, so the nonzero hypothesis is necessary. The empty-interval
fixture records the limit of this obstruction family. The scaling and branch-height statements
are library results; no numbered theorem of de Silva–Munch–Patel states scaling homogeneity.
Their Definition 4.4 and Theorem 4.6(i) supply the distance and perturbation-bound context.
Scaling on `RGraphCat`, commutation with the Reeb quotient or geometric smoothing, nonlinear
height changes, scaling Mapper covers or Mapper persistence modules, maps between graph objects in `RGraphCat` or maps of Reeb quotients are outside these
scaling results.

Not claimed here: equality of the Reeb-quotient distance with `edist h g` beyond the exactness
criterion and the merge/split values above; exact distances for other
perturbations and other tree shapes; the Hausdorff
distance of height ranges for disconnected graphs beyond the extremal bounds; maps between graph
objects in `RGraphCat` or maps of Reeb quotients; Mapper cover or reconstruction
consequences of `HeightMapPair` (its Mapper homology consequences are in [the Mapper digest](mapper.md)); constructible thickening; any distance or interleaving comparison of
realizations beyond the vertex-height bounds above; Definition 4.36 of de Silva, Munch and Patel;
naturality across changes of graph or heights; general finite CW complexes; another realization;
algorithms. Trees and simple connectivity of realizations are proved in
[reeb-graph-tree-contraction.md](reeb-graph-tree-contraction.md).

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.3 Notation 2.7, §3.1 Example 3.3 and Theorem 4.6](https://arxiv.org/html/1501.04147v1);
[pinned mathlib darts](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/SimpleGraph/Dart.lean#L61-L103),
[graph components](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean#L390-L493)
and [restricted quotient maps](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Constructions.lean#L645-L650).
