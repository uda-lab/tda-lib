# Mapper foundations

Consulted manifestations, attribution and rights: [DMW16-v2](references.md#DMW16-v2), [CO16-v3](references.md#CO16-v3).

## Indexed set covers

An indexed cover family is a function `U : I → Set X`. Its index type is part of the
data: equal members at different indices remain distinct labelled members, and empty
members are retained. The support covered by a family is explicit:

`Covers U A := ∀ x ∈ A, ∃ i, x ∈ U i`.

Thus full coverage is written `Covers U Set.univ`; coverage is not built into the
family and no topology, finiteness, nonemptiness, decidability, minimality or quotient
of indices is required.

A selected refinement from `U` to `V` consists of a selector `r : I → J` and the
containments `U i ⊆ V (r i)`. Its identity selects each index, and composition selects
`s (r i)`. The identity, composition and associativity laws are proved from these
functions. A refinement records a selected map; its existence does not choose a
canonical selector.

For `f : X → Y`, pullback retains the index type and sends each member to
`f ⁻¹' U i`. Coverage of a support pulls back to coverage of its inverse image, and
coverage of `Set.range f` pulls back to full coverage of `X`. Pullback also preserves
selected refinements, their identity and their composition. Pullback along an identity
or a composite map is expressed with explicit family equalities and the corresponding
selector or refinement equalities.

Concrete fixtures establish that an empty index family covers exactly the empty
support; duplicate singleton members can be merged by a selected refinement; a cover
of a map range need not cover its whole codomain but becomes a full pullback cover; a
member disjoint from the range becomes empty without losing its index; and two valid
selectors can remain distinct as index functions.

## Path-component pullback covers

For a continuous map `f : C(X, Y)` and an indexed family `U : I → Set Y`, the
path-component pullback cover has index type

` Σ i, ZerothHomotopy {x : X // f x ∈ U i}`.

The member labelled by `(i, c)` consists of the points `x` whose class in the
inverse-image subspace over `U i` is `c`. This definition uses no chosen representative,
and the class is independent of the proof that `f x ∈ U i`. Every labelled member is
nonempty. For each fixed `i`, distinct classes give disjoint members whose union is
`f ⁻¹' U i`; the union over all labels is `f ⁻¹' (⋃ i, U i)`. Consequently,
coverage of `Set.range f` by `U` gives a full cover of `X`. An empty inverse image has no
component label, while equal target members at distinct original indices still give
distinct labelled copies.

A selected refinement `U → V` restricts to a continuous inclusion between the
corresponding inverse-image subspaces. Applying the path-component map to these
inclusions gives a selected refinement between component covers. Its selector sends the
class of a point to the class of the same point in the selected larger inverse image,
and it preserves identity and composition. The containing target component is unique
after a target member has been selected; without the original refinement selector there
is no canonical target label.

No openness is asserted for arbitrary families. If `X` is locally path connected and
every `U i` is open, each inverse image is open and every component-cover member is its
relative path component in that inverse image. The pinned
`IsOpen.pathComponentIn` theorem then makes every member open in `X`.

This is the path-component pullback cover underlying the Mapper construction of
Dey–Mémoli–Wang, *Multiscale Mapper*, §2. They state openness of the pullback cover
without a hypothesis on the domain, but path components of an open inverse image need
not be open in an arbitrary space. The library recovers the construction unconditionally
and the openness sentence under local path connectedness. It also keeps arbitrary index
types and set families.

## Support-aware ordinary nerves

For an indexed family `U : I → Set X`, the ordinary nerve `nerve U` is the
`PreAbstractSimplicialComplex I` whose faces are the nonempty finite index sets
with a common point in all corresponding members. The nonempty-face condition
is part of the definition: the empty simplex is absent, and an index is a
vertex exactly when its member is nonempty. Equal nonempty members at distinct
indices therefore give distinct vertices and their common edge.

The construction is defined for arbitrary sets and index types. It is
monotone under pointwise member inclusion, every nonempty subface of a face is
a face, and an empty ambient type gives the bottom complex. A bijective index
relabeling transports faces through `Finset.image`.

Pulling a family back along `f : X → Y` gives a face exactly when its indices
are nonempty and there is a witness in `Set.range f` belonging to every target
member. Thus the pullback nerve is a subcomplex of the target nerve, with
equality when `f` is surjective. A constant map into one of two disjoint target
members can make this inclusion proper. Pairwise intersections do not imply a
triple face, as shown by the three two-point members `{0, 1}`, `{1, 2}`, and
`{0, 2}`.

These set-theoretic conventions organize the cover maps used in Dey–Mémoli–Wang,
*Multiscale Mapper*, §2–3. They deliberately provide an arbitrary-set library
interface beyond the open-cover setting used for Mapper constructions.

## Vertex maps and refinement-induced nerve maps

For preabstract simplicial complexes `K` on `I` and `L` on `J`, a vertex map is
a total function `r : I → J` such that every finite face `s ∈ K` has image
`s.image r ∈ L`. The map may identify vertices, so an `n`-face can have an
image with fewer vertices; no order, injectivity or same-dimension assumption
is part of the interface. In the pinned mathlib API, this pointwise condition
is equivalent to `PreAbstractSimplicialComplex.map K r ≤ L`.

A selected refinement of indexed families induces a vertex map between their
ordinary nerves using its selector as the ambient function. The common point
of a source face remains a common point after applying the refinement
containments, so the simplicial property is proved by the refinement itself.
Identity and composition agree extensionally with refinement identity and
composition. A bijective index relabelling gives inverse vertex maps whose two
composites are identities, while ambient indices with empty family members
remain absent as nerve vertices.

## Ordinary Mapper and cover multiplicity

For a continuous map `f : C(X, Y)` and an indexed target family `U`, ordinary
Mapper is the support-aware nerve of the path-component pullback cover:

`mapper f U := nerve (componentCover f U)`.

Its ambient vertices are pairs consisting of a target-family index and a path
component of that member's inverse image. Every such component index is a
supported vertex because component-cover members are nonempty. A finite set of
vertices is a face exactly when one domain point lies in every represented
component member. Two vertices in one face with the same target-family index
are equal: their common witness represents both path-component classes in the
same inverse image. Consequently, projection to target-family indices is
injective on each face.

Cover multiplicity is imposed only on attained values. It is at most `m` when,
for every `y ∈ Set.range f`, every finite set of target indices whose members
all contain `y` has cardinality at most `m`. For a Mapper face, project its
vertices to target indices. Facewise injectivity preserves cardinality, and
the common domain witness maps to an attained value contained in every
projected member. Thus every Mapper face has at most `m` vertices.

At multiplicity at most two, the supported vertices carry a simple graph:
distinct vertices are adjacent exactly when their underlying pair is a Mapper
face. Every Mapper face is then either a supported singleton or an adjacent
pair. This conclusion depends on the explicit multiplicity hypothesis, not on
calling the target members intervals. The construction also covers the empty
Mapper and isolated supported vertices. Without a multiplicity bound, three
duplicate target labels containing the value of a constant map from a
one-point domain form a genuine triangle.

A selected target-family refinement acts first on path components and then by
the refinement-induced nerve map. The resulting Mapper vertex map preserves
identity and composition, evaluates on a represented component by keeping its
representative in the selected larger inverse image, and gives mutually
inverse maps under a bijective relabelling. It need not be injective: enlarging
a pullback member can merge distinct source components.

This is ordinary Mapper in the sense of Dey–Mémoli–Wang, *Multiscale Mapper*,
§2. It records the existence of common intersections. The MultiNerve Mapper of
Carrière–Oudot, *Structure and Stability of the 1-Dimensional Mapper*, retains
additional path-component data for intersections (the paper writes "connected" under
its stated path-connected convention); it is described in the next two sections. No Reeb
equivalence, convergence, stability, persistence-diagram result,
or Nerve Lemma follows from this definition.

## Multinerves of indexed families

For an indexed family `V` on a topological space and a nonempty finite index set
`σ`, write `V_σ` for the intersection of the members indexed by `σ`. A multinerve
cell is a pair of such a `σ` and a path component of the subspace `V_σ`. An empty
intersection has no path component and carries no cell; empty members and
repeated labels are retained as in the ordinary nerve. For `τ ⊆ σ`, the
inclusion `V_σ ⊆ V_τ` induces a face map on path components, and face maps
preserve identities and composition.

A cell `(τ, D)` lies below `(σ, C)` when `τ ⊆ σ` and the face map sends `C` to
`D`. This is a partial order. Below a fixed cell `(σ, C)` a cell is determined
by its index set, and every nonempty `τ ⊆ σ` occurs, so the lower set of the cell
is order-isomorphic to the nonempty subsets of `σ`. These are the simplicial-poset
axiom of Carrière–Oudot, Definition 3.1, and the cells of their Definition 3.2.

Forgetting the component gives a monotone projection onto the faces of the
ordinary support-aware nerve. A representative of a component is a common point
of the indexed members, and a common point of a nerve face represents a
component, so the image of the projection is exactly the set of nerve faces
(Carrière–Oudot, Lemma 3.4). The fibre over a face `σ` is in bijection with the
path components of `V_σ`. The projection is therefore injective exactly when every
nonempty finite intersection has at most one path component, and under this
condition it is an order isomorphism onto the nerve faces ordered by inclusion.
Path-connectedness of every nonempty such intersection is a sufficient condition.
The criterion and the sufficient condition are elementary consequences recorded
here, not results attributed to the paper. No openness, local path-connectedness,
finiteness or nonemptiness is assumed, and no geometric realization, homology or
Nerve Lemma is constructed.

## MultiNerve Mapper

The MultiNerve Mapper of a continuous map `f` and a target family `U` is the
multinerve of the path-component pullback cover, following Carrière–Oudot,
Definition 3.3; it is not the multinerve of the plain preimage family. Ordinary
Mapper is the nerve of the same cover, so the projection maps the MultiNerve Mapper
onto ordinary Mapper.

Every component member is path-connected. Each component index therefore carries
exactly one cell with one-element support, and these cells are in bijection with
the component indices. A multiplicity bound `m` on attained values bounds the
support size of every cell by `m`. At `m = 2` every cell is a vertex or an edge
cell, and one Mapper edge may carry several edge cells. Without a multiplicity
bound, three duplicate labels over a one-point domain give a cell with
three-element support over the Mapper triangle.

The projection is an order isomorphism onto ordinary Mapper when every nonempty
finite intersection of component members has at most one path component. A
target-side sufficient condition is that the preimage of every nonempty finite
intersection of target members is empty or path-connected. Such a preimage is
then contained in every component member that meets it, and so equals the
intersection of the component members over the corresponding labels. The
component-level condition is the hypothesis under which component-sensitive
statements of Munch–Wang or Carrière–Oudot type would transfer to ordinary
Mapper. Such a transfer to ordinary Mapper is not asserted. The interval-indexed
categorical assembly has a separate [resolution bound and convergence theorem](mapper-reeb-approximation.md).

On the 4-cycle with vertex heights `0, 1, 2, 1` and the intervals `(-1, 3/2)` and
`(1/2, 3)`, each interval preimage is path-connected, so ordinary Mapper has two
vertices and one edge. The intersection of the two component members is the
preimage of `(1/2, 3/2)`. It has two path components, represented by the vertices
`1` and `3`, so the MultiNerve Mapper has two edge cells over the single Mapper
edge and the projection is not injective. On one edge with endpoint heights `0`
and `2`, the same intervals satisfy the target-side condition and the two
constructions agree. The empty domain has no cells.

The component-level condition is strictly weaker than the target-side one. On two
disjoint edges with endpoint heights `0` and `2` and the same intervals, the
preimage of `(-1, 3/2)` has two path components, one on each edge, so the
target-side condition fails. Component members on different edges are disjoint,
so a nonempty intersection of component members lies on one edge. It is either one
path-connected member or the intersection of the two members of one edge, whose
points are all joined to the midpoint of that edge inside the preimage of
`(1/2, 3/2)`. Hence every nonempty finite intersection of component members has at
most one path component, and the MultiNerve Mapper is order-isomorphic to the
ordinary Mapper of two disjoint edges.

## Refinement maps of multinerves

Let `R` be a selected refinement of indexed families `U` and `V` on one space. For
a finite index set `σ`, the intersection `U_σ` lies in `V_τ` with
`τ = R.selector '' σ`, so the inclusion induces a map on path components. The
induced map of multinerves sends a cell `(σ, C)` to `(τ, C')`, where `C'` is the
path component of `V_τ` containing `C`. It is monotone for the face order, sends the
face of a cell over a subset to the face of the image cell over the image subset,
and preserves the identity and composition of selected refinements. Projected to
the ordinary nerve, it is the refinement-induced nerve map of the support. Like the
nerve map, it may lower the support size, because selectors need not be injective.
The selected refinement is supplied data in the convention of Dey–Mémoli–Wang
§2–3; the laws are elementary library results, not attributed to a source.

On the discrete space `Bool`, refining the singletons `{false}` and `{true}` to the
one-member family `Bool` collapses both nerve vertices to one, while the
multinerve map keeps two distinct cells over the one index, represented by `false`
and `true`.

A selected refinement of target families induces the selected refinement of
path-component pullback covers, and hence a map of MultiNerve Mappers. It
preserves identity and composition, sends the vertex cell of a component index to
the vertex cell of its image under the ordinary Mapper map, and lies over that
map under the projections onto ordinary Mapper. A coherent cover tower gives
MultiNerve Mapper maps with strict reflexivity and transitivity. On the merged
three-stage tower, the first transition sends the cell over two first-stage
indices to the middle-stage vertex cell, and the direct map is the composite.

For a finite set `s` of component indices, the intersection of the component
members lies in the preimage of the intersection of the target members with the
labels of `s`, and this inclusion is injective on path components. A path in the
preimage between two points of the intersection stays in the path component of
the preimage, which lies in every component member containing those points. The
target-side criterion of the previous section follows. The same lemma detects
merging: on the 4-cycle, refining the two intervals to two copies of `(-1, 3)` by
the identity selector gives an injective Mapper vertex map, but the two edge cells
represented by the vertices `1` and `3` are sent to one cell, because both
vertices lie in one path component of the preimage of `(-1/2, 5/2)`.

This refinement API does not assert a geometric realization, homology, Nerve Lemma,
contiguity or selector-independence of multinerve maps, nor an interleaving,
approximation or stability theorem for those maps.

## Graph-PL incidence labels and finite consumers

For a simple graph `G`, a vertex height `h : V → ℝ`, and a labelled family of
open real intervals, the path-component label over each interval is equivalent
to a connected component of the incidence graph `cellGraph G h I`. Combining
these equivalences over the interval labels gives a vertex equivalence from the
ordinary Mapper of `plHeight G h` to an incidence-labelled nerve. The
members of that nerve are the path-component cover members transported
along the equivalence, so a finite vertex set is a face on one side exactly when
its image is a face on the other. Coverage is inherited when the interval family
covers `Set.range (plHeight G h)`, rather than only the heights of the original
vertices.

A selected refinement of interval families acts on the incidence labels by
`ConnectedComponent.map` along `cellInclusion`. The resulting vertex map is
conjugate to the ordinary Mapper refinement map through
`preimageComponentsEquiv_componentMap`. This distinguishes merging two interval
labels from merging graph components: widening the intervals can identify two
labels on one connected graph piece without connecting distinct pieces of the
domain.

If both the graph vertex type and the interval-label type are finite, the Mapper
component-index type, its supported-vertex subtype, and the subtype of finite faces are finite. This is a noncomputable finiteness result. Finitely many
interval labels alone are insufficient: for the constant map from discrete
`ℕ` to a point and the one-member full cover, the supported Mapper vertex type
is explicitly equivalent to `ℕ`.

The concrete graph fixtures use the PL-height inverse images. An open
arc over the interval `(0, 2)` has one Mapper vertex even though neither endpoint
survives. The overlapping intervals `(-1, 3/2)` and `(1/2, 3)` give one Mapper
edge on a single graph edge and two disconnected copies on a disjoint union of
two graph edges. Refinement to `(-1, 3)` merges the two source labels within each
copy while the two domain components remain distinct.

## Contiguity and coherent Mapper towers

Two simplicial vertex maps are contiguous when, for every source face, the
union of its two finite vertex images is a target face. Contiguity is reflexive
and symmetric and is preserved by precomposition and postcomposition with
simplicial vertex maps. It is not treated as a transitive relation.

Any two selected refinements between the same indexed families induce
contiguous maps of their ordinary nerves. A common point witnessing a source
face lies in every target member selected by either refinement, so it witnesses
the union face. Applying this result to the component-cover refinements shows
that any two selected target-cover refinements induce contiguous ordinary
Mapper maps. The maps can differ on vertices; contiguity, rather than equality,
is the choice-independence statement at the vertex level. The homology-map
equality it yields on the ordered chain model is stated below.

A coherent cover tower over a preorder consists of a possibly varying index
type and indexed family at every parameter, together with a selected
refinement for every comparison. The index types may depend on the parameter
but live in one common universe. Strict identity and composition equations for
the selector functions are supplied as part of the tower data; coherence is
not inferred from unrelated selector choices. Ordinary Mapper assigns a
complex to every parameter and a simplicial vertex map to every comparison,
and the existing strict refinement laws prove identity and composition for
these maps. This direct interface makes no fixed-ambient inclusion claim and
adds no categorical, diagram or stability conclusion; the persistence module
below does not need the strict equations.

## Refinement-induced homology maps and Mapper persistence modules

Fix a continuous map `f : X → Y`, a ring `R` and a degree `n`. For families
`U : I → Set Y` and `V : J → Set Y` with `I` and `J` in one universe, and
linear orders on the component-index types of `mapper f U` and `mapper f V`,
a selected refinement `r : Refinement U V` induces the map
`mapperHomologyMap R f r n = simplicialHomologyMap R (mapperMap f r) n` on
the ordered-chain homology. The identity refinement induces the identity map
and composition of refinements induces composition. No openness, coverage,
multiplicity, finiteness, field or local path-connectedness hypothesis
enters. The linear orders are chain-model data; nothing is claimed about
replacing them by other orders.

Two selected refinements `r, s : Refinement U V` induce contiguous Mapper
maps, so the signed prism of the contiguity bridge is a chain homotopy
`mapperChainHomotopy R f r s` between their chain maps and
`mapperHomologyMap R f r n = mapperHomologyMap R f s n`. Consequently every
refinement of a family into itself induces the identity on homology, and the
composite of the maps induced by `r : Refinement U V` and `s : Refinement V W`
is the map induced by any `t : Refinement U W`. The vertex maps and the chain
maps may still differ; the equality is a statement about homology. This is a
library consequence of the contiguity statement above and of the signed prism
homotopy of the [simplicial vertex-map bridge](simplicial-vertex-maps.md); it
adds no source claim beyond those already recorded for them.

Along a preorder `P`, cover families `U p` with index types in one universe,
linear orders on their component-index types, and a selected refinement
`r h : Refinement (U p) (U q)` for every `h : p ≤ q` form the persistence
module `mapperHomologyPModule R f U r n : PModule R P`. Its value at `p` is
`simplicialHomology (mapper f (U p)) R n` and its structure map at `h` is
`mapperHomologyMap R f (r h) n`. The functor laws follow from the homology
equalities above, so no identity or composition equation on the selectors is
required, and replacing the whole family `r` by another choice of refinements
between the same families gives the same module. A `CoherentCoverTower`
supplies such a family; the homology maps of its strict Mapper maps are
exactly the structure maps of this module, and the strict tower interface is
unchanged.

Fixtures: over a one-point domain, the two selections of a duplicated target
member give different Mapper vertex maps and the same nonzero `H₀` map over
`ℚ`; a three-stage family whose direct first-to-last selector differs from
the composite of the adjacent selectors gives a persistence module equal to
the module of the strictly coherent three-stage tower; its first transition
collapses an edge, killing the edge generator in degree one over every ring
while, over `ℚ`, sending both endpoint classes in `H₀` to the nonzero
middle-vertex class; an empty domain over a nonempty index type gives an
empty Mapper, zero chain maps and equal homology maps in every degree over
every ring. As a negative
control, the two simplicial maps from a point to two isolated vertices are
not contiguous and have different `H₀` maps over `ZMod 2`; they are not the
Mapper maps of two refinements between one pair of families, and over the
zero ring `ZMod 1` their homology maps coincide, so the nontriviality of the
coefficient ring is necessary for this control.

No multinerve chain complex or multinerve selector independence, Nerve Lemma,
categorical reconstruction, barcode algorithm or q-tame theory is included. The
stability statement for interleaved cover towers is in the next section.

## Interleaved cover towers and Mapper homology stability

A real cover tower on `Y` is a family `U t : IndexU t → Set Y` for every
`t : ℝ` with a selected refinement `rU h : Refinement (U s) (U t)` for every
`h : s ≤ t`; no identity or composition equation is required. Fix
`f : C(X, Y)`, a ring `R`, a degree `n` and linear orders on the component-index
types. For `η : ℝ≥0`, two towers `U` and `V` (index types in one universe) are
related by selected cover maps `ζ t : Refinement (U t) (V (t + η))` and
`ξ t : Refinement (V t) (U (t + η))` for every `t`. This is a library form of
Definition 5 of [DMW16-v2](references.md#DMW16-v2): the families need not be
finite or cover `Y`, the tower refinements need not satisfy identity or
composition equations, and the parameter has no resolution lower bound. As in
the source, no commutation between the cover maps and the tower maps is
assumed.

`mapperHomologyInterleaving R f rU rV ζ ξ n` is a real `η`-interleaving of
`mapperHomologyPModule R f U rU n` and `mapperHomologyPModule R f V rV n`. The
component of its first map at `t` is `mapperHomologyMap R f (ζ t) n` and that of
its second map is `mapperHomologyMap R f (ξ t) n`. Naturality at `s ≤ t`
compares two refinements `U s → V (t + η)`, the composite through `U t` and the
composite through `V (s + η)`. The double-shift identity at `t` compares the
composite of `ζ t`, `ξ (t + η)` and the parameter transport with the tower
refinement `U t → U (t + 2η)`. In each case both sides are induced by
refinements between the same families, so they agree on homology by the
selector independence of the previous section. The components, and for fixed
tower refinements the whole interleaving, do not depend on which cover maps or
tower refinements were selected. Hence
`realInterleavingDistance_mapperHomologyPModule_le` bounds the real interleaving
distance of the two modules by `η`, and composing an `η₁`-pair of cover maps
with an `η₂`-pair bounds the distance between the outer modules by `η₁ + η₂`.
This is the homology-module form of DMW16-v2 Proposition 4.2 and Corollary 4.3,
with Proposition 4.1(i) at the level of modules. The source states the
conclusion for nerve towers up to contiguity (Definition 6) and for persistence
diagrams of finite towers. The nerve-tower form is not formalised; the diagram
form is obtained for step towers in
[a later section](#diagrams-of-mapper-homology-along-step-towers).

The Mapper complex of `f` along `U t` is definitionally the Mapper complex of the
identity of `X` along `pullback f (U t)`, with `pullbackRefinement f` applied to
the tower refinements and the same component orders, so
`mapperHomologyPModule_pullback` is an equality of persistence modules. This is
the module form of the source definition `MM(𝔘, f) := N(f*(𝔘))`; together with
the pulled-back cover maps it plays the role of Proposition 4.1(ii) in the
perturbation result below.

For `s t : ℝ`, `centredCover s t k` is the open interval of radius `t` about
`k * s`, indexed by `k : ℤ`; it is empty for `t ≤ 0`, increasing the radius gives
the identity-selector refinement `centredCoverRefinement s`, and for `s ≠ 0` and
`|s| / 2 < t` the family covers `ℝ`. Let `f g : C(X, ℝ)` satisfy
`|f x - g x| ≤ δ` for every `x`. Then `f x` in the member of label `k` and radius
`t` puts `g x` in the member of label `k` and radius `t + δ`, so identity
selectors are cover maps between the pulled-back centred towers on `X` in both
directions. By the pullback identification, the interleaving theorem for the
identity of `X` gives `centredMapperHomologyInterleaving`, a `δ`-interleaving
of the Mapper homology modules of `f` and `g` along the centred tower, and
`realInterleavingDistance_centredMapperHomology_le` bounds their distance by
`δ`, for every spacing, degree, ring and supplied component orders. This
specialisation is a library result; it is not the function-perturbation
statement of DMW16-v2 Proposition 4.5 and Corollary 4.6, which use
`(c, s)`-good towers, logarithmic reindexing and truncation.

No finiteness, openness, coverage, field, nonemptiness or local
path-connectedness hypothesis enters. A source tower with resolution `r` is
represented by any extension of it to all of `ℝ`, for example by empty families
below `r`; the library does not identify the two conventions.

Fixtures: interleaving a tower with itself at `η = 0`, with tower refinements as
cover maps, gives the identity isomorphism of its module. Over a one-point
domain, cover maps whose composite selector differs from the tower selector
still give an interleaving. The centred tower is interleaved with its own
`η`-shift, and its Mapper complexes have no faces at nonpositive radius, with no
inhabitedness assumption on the domain. On the unit interval, the constant map
`0` and the map `x ↦ 4x` are at pointwise distance `4`; along the centred tower
of spacing `1`, their `H₀` over `ℚ` at radius `1/2` has dimensions `1` and `5`,
so their modules are not isomorphic, while the distance between them is at
most `4`. For the identity map, the pullback form agrees with the direct form.
As a control, refinements between one family pair induce one homology map,
while the two simplicial maps from a point to two isolated vertices of the
previous section, which are not induced by refinements, have different `H₀`
maps over `ZMod 2`.

Rank obstructions give lower bounds. Let `k` be a field and `i` a real
`ε`-interleaving of persistence modules `M` and `N` over `k`. The double-shift
identity writes the structure map `M(t → t + 2ε)` as `i.φ` at `t`, followed by
`i.ψ` at `t + ε` and the parameter transport, so it factors through `N (t + ε)`.
If `N (t + ε)` is finite-dimensional, then
`finrank_range_structureMapLinear_le_of_realInterleaving` bounds the rank of
`M(t → t + 2ε)` by `dim N (t + ε)`; the primed form exchanges `M` and `N`, and
`structureMap_eq_zero_of_realInterleaving` gives `M(t → t + 2ε) = 0` when
`N (t + ε)` is zero. No other value of `M` or `N` need be finite-dimensional.
`le_realInterleavingDistance_of_finrank_lt` concludes `r ≤ d(M, N)` when every
finite `ε < r` admits some `t` with `dim N (t + ε)` finite and smaller than the
rank of `M(t → t + 2ε)`; `le_realInterleavingDistance_of_structureMap_ne_zero`
is the zero-fibre form. This is the elementary factorisation step behind
algebraic stability, not a theorem of a cited source. The statements are kept
in the Mapper module and are generic in the modules.

For a map `f` with a real tower `U` and a map `g` with a real tower `V`, the
structure maps of `mapperHomologyPModule k f U rU n` are the homology maps of
the selected refinements, so
`isEmpty_realInterleaving_mapperHomologyPModule_of_finrank_lt` excludes an
`ε`-interleaving when the homology map of `U t → U (t + 2ε)` has rank larger than
`dim Hₙ(mapper g (V (t + ε)))`. The zero-fibre form requires
`mapper g (V (t + ε))` to have no `n`-faces, which holds when it has no vertices
(`isEmpty_face_mapper`), and a nonzero homology map; both have distance forms.
With `g = f` these compare two towers of one map; with `U = V` the centred tower
they restate as `isEmpty_realInterleaving_centredMapperHomology_of_finrank_lt`
and `le_realInterleavingDistance_centredMapperHomology_of_finrank_lt`, which
combine with the perturbation bound above.

Fixtures: over the one-point domain, let the single member be the whole space
from radius `1` on in the tower `lateTower` and from radius `0` on in
`earlyTower`, with identity selectors. Cover maps shifting by `1` exist in both
directions. For `ε < 1`, the early tower's `H₀` map from `1 - ε` to `1 + ε` sends
the nonzero class of its unique vertex to the class of the unique vertex, while
the late tower's Mapper complex at radius `1` has no vertices. Hence
`realInterleavingDistance_late_early` states that the two degree-zero modules
are at distance exactly `1`, over every field. For the flat and steep maps,
the Mapper complexes along the centred tower of spacing `1` have no edges at
every radius in `(0, 1/2]`, with `H₀` of dimension `1` and `5` respectively, and
the steep refinement maps between such radii are bijective on `H₀`, so they have
rank `5`. At `t = 1/4` and `ε < 1/8` this excludes an `ε`-interleaving, and
`flat_steep_distance_bounds` places the distance in `[1/8, 4]`. For a module and
itself, the identity `0`-interleaving satisfies every rank inequality and the
hypothesis of the distance lower bound fails at `ε = 0`. As a negative control,
for the constant map from discrete `ℕ` with one full member every value of the
degree-zero module is infinite-dimensional, so the rank bound does not apply;
`Module.finrank` is `0` there by convention and no inequality is asserted.

Not included: the simplicial-tower interleaving up to contiguity as a separate
structure; `(c, s)`-good towers, reindexing or truncation (DMW16-v2 Propositions
4.4–4.5, Corollary 4.6, Theorems 4.7–4.8); persistence diagrams or bottleneck
bounds other than those for step towers; the bar-length lower bound
`(death − birth)/2` or any lower bound through decompositions, induced matchings or the
isometry theorem, except the step-tower isometry below; tightness of the rank
obstruction in general and the exact flat/steep distance; lower bounds for
graph-PL Reeb distances; independence of the component orders; multinerve
homology; any Nerve Lemma.

## Finite Mapper barcodes

Keep the setting of the previous section and fix a degree `n`. If every Mapper
complex `mapper f (U p)` has finitely many `n`-faces, then over a field `k`
every value of `mapperHomologyPModule k f U r n` is finite-dimensional, because
its chain module in degree `n` is.

Now let the preorder be the finite chain `Fin N` and let the field, the domain
`X` and the index types lie in one universe, as the
[finite interval decomposition](finite-interval-decomposition.md) requires of
its carriers. The Mapper barcode `mapperBarcode k f U r n` is the canonical rank
barcode of `mapperHomologyPModule k f U r n`: a multiset of half-open intervals
`[b, d)` with `b < d ≤ N`. A bar with `d = N` records a class that survives to
the last observed stage; it does not assert an infinite lifetime. Because the
module does not depend on the selected refinements, neither does its barcode.
The finite interval decomposition gives a natural isomorphism from the module to
the realization of its barcode; the isomorphism is chosen and not canonical. For
stages `q ≤ t`, the rank of `mapperHomologyMap k f (r h) n` is the number of
bars with `b ≤ q` and `t < d`, and a multiset is the barcode exactly when it
satisfies all of these rank equations. Two such modules, with possibly different
maps, covers and degrees, are naturally isomorphic exactly when their barcodes
agree. For a `CoherentCoverTower` on `Fin N`, the same counts are the ranks of
the homology maps of the tower's strict Mapper maps. These statements specialize
the finite interval decomposition to the Mapper module of the
[DMW16-v2](references.md#DMW16-v2) towers above and add no source claim.

For the piecewise-linear height of a finite graph and finitely many open
interval labels at a stage, the finiteness of the Mapper faces recorded above
holds in every degree, so the barcode is available without further hypotheses.
Coverage of the height range is not needed.

Fixtures: on `Fin 0` and on the empty domain every barcode is empty, without a
nonemptiness hypothesis. On the single edge with heights `0` and `1`, the
members `(-1, 1/3)` and `(2/3, 2)` refine by a constant selector to `(-1, 2)`;
over `ℚ` the degree-zero barcode is `{[0, 2), [0, 1)}` and the degree-one
barcode is empty. On `Fin 3`, the three-stage family over a point whose direct
selector differs from the composite of its adjacent selectors has the barcode
`{[0, 3)}` of the strictly coherent tower. On the 4-cycle with heights
`0, 1, 2, 1`, the members `(-1, 3/2)` and `(1/2, 3)` meet in two components, yet
ordinary Mapper is a single edge with no degree-one homology; only the
multinerve retains the second intersection component. The three members
`(-1, 3/4)`, `(1/2, 3/2)` and `(5/4, 3)` give a Mapper 4-cycle with degree-one
homology of rank one, and after a constant refinement to `(-1, 3)` the
degree-one barcode over `ℚ` is the single bar `[0, 1)`. As a negative control,
the constant map from discrete `ℕ` with one full member has infinitely many
Mapper vertices, and for every component order its degree-zero homology is not
finite-dimensional, so no degree-zero barcode is defined; the complex has no
edges, so degree one still satisfies the finiteness hypothesis.

Real diagrams and their bottleneck stability are given for step towers in the
next section; q-tame Mapper barcodes, independence of the barcode from the
supplied component orders, multinerve barcodes and executable barcode
extraction are not provided.

## Diagrams of Mapper homology along step towers

Keep the setting of the previous two sections. A grid is a strictly increasing
`c : Fin m ↪o ℝ`, and `cellIndex c t ∈ Fin (m + 1)` counts the grid values at or
below `t` ([finite-constructible modules](constructible-modules.md)): cell `0` is
the left ray below `c 0`, cell `i + 1` is `[c i, c (i + 1))`, and the last cell
is unbounded on the right. Step data on the grid are cover families
`cover i : Index i → Set Y` for `i : Fin (m + 1)` with a selected refinement for
every `i ≤ j` and supplied component orders; no identity or composition
equation is required. The step tower `stepTower c cover` is the real tower whose
family at radius `t` is `cover (cellIndex c t)`, with refinements
`stepRefinement c cover r` taken from the cells. Its Mapper homology module is
definitionally the finite-chain module `mapperHomologyPModule R f cover r n`
reindexed along `cellIndex c`, over every ring and in every degree.

A family with an empty index type, or more generally without component
indices, has the empty Mapper complex, and its homology vanishes in every
degree. If `Index 0` is empty, the step module is therefore zero on the left ray
and its structure maps within a cell are identities, so it is finite-constructible
on `c`. If moreover every stage has finitely many `n`-faces and the field, `X`
and the index types lie in one universe, the step module is finite-dimensional
at the grid values and `stepMapperDiagram k f c cover r n` is its real endpoint
diagram. Because `cellIndex c (c j) = j + 1`, the diagram is the image under
`ofIndexBars c` of the finite Mapper barcode of the stages `1, …, m`: a bar
`[b, d)` of that barcode becomes the real bar `[c b, c d)`, or the essential bar
`[c b, ∞)` when `d = m`. Equivalently, it is the image of the barcode of all
`m + 1` stages restricted along `Fin.succ`; the empty stage `0` contributes no
bar. The diagram has positive bars and does not depend on the selected
refinements.

Let `(c, cover, r)` and `(d, cover', r')` be step data, possibly on grids of
different sizes, both with an empty initial family and finitely many faces in
degree `n`. For `η : ℝ≥0`, selected cover maps between the two step towers
shifting the radius by `η` in both directions bound the bottleneck distance of
the two step diagrams by `η`. Through any intermediate real tower, cover maps
shifting by `η₁` and `η₂` bound the bottleneck distance of the outer step
diagrams by `η₁ + η₂`. The [finite-constructible isometry](constructible-isometry.md)
identifies this bottleneck distance with the real interleaving distance of the
two step modules; at every finite parameter, an interleaving exists exactly
when an occurrence matching of that cost exists; and the distance is infinite
exactly when the two diagrams have different numbers of essential bars. No
identification of the number of essential bars with the dimension of the top
stage is stated. For the piecewise-linear height of a finite graph and finitely
many open-interval labels at every stage, the face-finiteness hypothesis holds
by instance.

The empty initial family is the zero left tail of the finite-constructible
convention and not a restriction on the Mapper data: a tower that starts with a
nonempty family is placed on the grid after an empty stage. The diagram
consequence that [DMW16-v2](references.md#DMW16-v2) draws for finite towers is
obtained here only for step towers on finite grids, as a library specialisation
of the module interleaving of the previous section through the BL15-v4
isometry; no theorem of DMW16-v2 is formalised in this form.

Fixtures: with no grid values and one empty stage, the module vanishes at every
radius, the diagram is empty and its bottleneck distance to itself is `0`. The
two-stage merge of the previous section, placed after an empty stage at the
radii `0` and `1`, has the degree-zero diagram over `ℚ` with finite part
`{(0, 1)}` and essential part `{0}`. The same stages at `1/2` and `3/2` are
related to it by selected stage refinements shifting the radius by `1/2` in
both directions: identities from the first copy, whose stage at `t` is the
stage of the copy at `t + 1/2`, and the merge refinements back, whose selector
to the coarse stage is constant; the bottleneck distance is at most `1/2` and equals the interleaving
distance, while the essential bars are born at `0` and at `1/2`, so the diagrams
differ. The skew three-stage family over a point, after an empty stage, has the
same diagram `{[c 0, ∞)}` for its skew and its coherent selections. The loop on
the 4-cycle at the radii `0` and `1` has the degree-one diagram `{(0, 1)}` with
no essential bar, with all finiteness instances synthesized. As negative
controls, the constant tower of the one full member over a point has nonzero
`H₀` below every grid, so it is not finite-constructible on any grid, for every
field and component order. Along the centred tower of spacing `1`, the constant
map `0` on the unit interval has zero Mapper homology at radius `0` and nonzero
`H₀` at every positive radius; every grid has a positive radius in the cell of
`0`, so this module is not finite-constructible on any grid. Radius-indexed
towers of open members are left-open at their first nonempty radius and lie
outside the zero-left, right-continuous convention; no diagram is defined for
them.

Not included: diagrams or bottleneck bounds for towers that are not step towers,
in particular the centred tower, or for q-tame modules; a finite capped version
of the centred tower; tightness of the bound and bottleneck values beyond the
fixtures; identification of the essential multiplicity with the top-stage
homology dimension; DMW16-v2 `(c, s)`-good towers, reindexing and truncation;
independence of the component orders; multinerve diagrams; executable
extraction.

## Uniform interval covers and edge cells

For a base point `a`, an interval length `r` and an overlap length `g`, the
uniform family has the open members `U_k = (a + k(r − g), a + k(r − g) + r)`;
its first `n` members are indexed by `Fin n`, with `n` explicit and no floor or
ceiling. For `g ≤ r` consecutive members meet in
`(a + (k + 1)(r − g), a + (k + 1)(r − g) + g)`, an interval of length `g`. For
`2g ≤ r` members whose indices differ by at least two are disjoint, so every
real number lies in at most two members and the family has multiplicity at most
two for every continuous map. For `n ≥ 3` and `g < r` this bound holds exactly
when `2g ≤ r`: if `r < 2g`, the midpoint of `(a + 2(r − g), a + r)` lies in the
first three members. Carrière–Oudot (CO16-v3 §2.4) measure an interval cover by
its granularity, the largest member length, and show that no three members of
a minimal cover meet (Lemma 2.10). The uniform family need not be minimal or
generic: at `2g = r` the part of the middle member outside its neighbours is a
single point. The multiplicity bound is proved directly and is not attributed
to Lemma 2.10.

For `0 < g` and `n > 0` the window `(a, a + n(r − g) + g)` lies in the union of
the members, by induction on `n`. For `g ≤ r` the union is exactly the window;
for `r < g` and `n ≥ 2` later members reach to the left of `a`. If the vertex
heights of a graph lie in `[m, M]`, so does every value of its piecewise-linear
height, without connectedness of the graph or nonemptiness of its vertex set.
The uniform family therefore covers the attained range when `a < m` and `M` is
below the right end of the window, and for `0 < g < r` such an `n` exists.

For a continuous map `f`, a target family `U` and a nonempty finite label set
`τ`, the MultiNerve Mapper cells whose support has label set `τ` correspond to
the path components of `f⁻¹(⋂_{i∈τ} U_i)`; a cell goes to the class of any
point of its carrier. Two points joined inside this preimage lie in the same
component member over every label, so cells with the same image have the same
support, and the inclusion of the intersection of component members into the
preimage is injective on path components. For two labels `i` and `j` the cells
are the edge cells over `U_i ∩ U_j`. The ordinary Mapper faces with label set
`{i, j}` are their supports, so there are at most as many such faces as path
components of `f⁻¹(U_i ∩ U_j)` when these are finite. This makes explicit the
gluing of parallel edges that relates the two constructions after CO16-v3
Corollary 3.5; the equivalence is an elementary library result.

For a piecewise-linear height on a graph and interval labels, the edge cells
with labels `{i, j}` are the connected components of the incidence graph over
`U_i ∩ U_j`. If the overlap contains no vertex height, every incidence node is
an edge node and no two edge nodes are adjacent, so the components are the
active edges. Over a bounded overlap `(p, q)`, an edge whose endpoint heights
avoid `(p, q)` is active exactly when its smaller endpoint height is at most `p`
and its larger one at least `q`. For the uniform family with `g ≤ r`,
consecutive labels carry the components over their overlap of length `g`; for
`2g ≤ r` labels at distance at least two carry no edge cell.

On the 4-cycle with vertex heights `0, 1, 2, 1`, the members `(-5/4, 3/4)` and
`(1/4, 9/4)` have path-connected preimages. Their overlap `(1/4, 3/4)` contains
no vertex height and meets the edges `0 — 1` and `0 — 3`, so the MultiNerve
Mapper has two edge cells over the single Mapper edge and is a 2-cycle. With the
members `(-1/8, 7/8)`, `(1/2, 3/2)` and `(9/8, 17/8)`, the middle preimage has
the two components of the vertices `1` and `3`, each consecutive overlap
carries two edge cells with different supports, and both constructions are
4-cycles. On one edge with endpoint heights `0` and `2` the same families give
one edge cell and one Mapper face per consecutive pair. The one-member families
`(-1/2, 5/2)` and `(-1, 3)` give as many Mapper vertices as graph components on
the 4-cycle and on two disjoint edges. For the family `(-1/2, 1/2)`,
`(-1/4, 3/4)`, `(0, 1)`, where `2g > r`, the attained value `1/4` of the single
edge lies in all three members and ordinary Mapper has a face of size three.

## Height-separating uniform covers and cell classification

For a connected graph with vertices `lo` and `hi` of lowest and highest height,
the piecewise-linear height attains exactly `[h(lo), h(hi)]`: the realization is
path-connected, so the attained range is an interval, and it contains the two
extreme vertex heights. A finite connected graph has such vertices. Connectedness
cannot be dropped: on two isolated vertices of heights `0` and `2` every point
of the realization is a vertex, and the height `1` is not attained.

A family `U : Fin n → OpenInterval` is height-separating for the vertex heights
`h` when every member contains at most one vertex height and every overlap of
consecutive members contains none. Vertex heights are used as a witness set of
critical values, as in the `CriticalValues` interface, not as a minimal
critical set: a vertex of degree two whose neighbours lie on both sides of it
still counts as a height to be separated. For a finite vertex set with heights
in `[m, M]` and every `ρ > 0` there is a height-separating uniform family with
`0 < g`, `2g ≤ r < ρ`, `n > 0`, `m − (r − g) < a < m` and
`M < a + n(r − g) + g`; it covers the attained range of every graph on these
vertices. The step `s = r − g` is half of `min(ρ, δ)`, where `δ` is the smallest
positive difference of two vertex heights, so two heights in one member, which
differ by less than `r < δ`, are equal. The base point `a ∈ (m − s, m)` avoids
the finitely many values `h(v) − l s`, so every left overlap end `a + l s` has
positive distance from every vertex height; `g` is half the minimum of `s`
and the smallest such distance, and `r = s + g`. No minimality of `n` and no canonicity of the
parameters is claimed; later members may miss the attained range and then carry
no cells.

For every open interval `K`, the components of the incidence graph over `K`
split as the components of the graph induced on the vertices with height in
`K`, together with the uncovered edges: the active edges with no endpoint
height in `K`. A vertex node and an edge node with a surviving endpoint go to
the induced class of that endpoint, whichever surviving endpoint is used, and
an uncovered edge node is alone in its component. No coverage, finiteness or
decidability is assumed. Under endpoint coverage there is no uncovered edge
and the splitting is the earlier vertex-only comparison; without surviving
vertices it is the earlier description of components by active edges.

The MultiNerve Mapper cells with label set `{i}` are the path components of
`f⁻¹(U_i)`, for a piecewise-linear height the incidence components over `U_i`.
Over a height-separating uniform family three cases remain, under the
positivity conditions stated with each.

* A member containing the vertex height `c` contains no other vertex height, so
  its surviving vertices are those of height `c`. An active edge without a
  surviving endpoint then has endpoint heights strictly on both sides of `c`:
  it crosses the level. The vertex cells over the member are the components of
  the graph induced on the level `{h = c}` together with the edges crossing `c`.
* For `0 < r`, a member `(p, q)` containing no vertex height carries one vertex
  cell for each edge whose height interval contains `[p, q]`.
* For `0 < g ≤ r`, the overlap `(p, q) = (a + l(r − g), a + l(r − g) + g)` of
  consecutive labels `k` and `l = k + 1` contains no vertex height, so the edge
  cells over `{k, l}` are the edges whose height interval contains `[p, q]`.

For `2g ≤ r`, labels at distance at least two carry no edge cell. Height
separation alone does not give this: for the single edge of heights `0` and
`2`, the members `(-1/4, 5/4)`, `(1/4, 7/4)`, `(3/4, 9/4)` with `g = 1` are
height-separating, while the first and the third meet in `(3/4, 5/4)` and
carry an edge cell.

These are the vertex and edge data of a Reeb graph in the combinatorial form
used for finite graph-PL input: components of vertex-height levels together
with crossing edges, and edges spanning the gaps between consecutive heights.
DMP15-v1 (Notation 2.7 and 3.11) describes a Reeb graph by vertices over
critical values and edges over the gaps between them; this is context, and no
statement here is attributed to it. The crossing summand is genuine: on
the tree with edges `0 — 2`, `1 — 2`, `2 — 3` and heights `0, 1, 2, 3`, under the
family with members `(k − 1/2, k + 3/4)` the member around height `1` carries
two vertex cells, the vertex `1` and the edge `0 — 2` passing through that
level. The consecutive pairs carry `1, 2, 1` edge cells.

On the 4-cycle with heights `0, 1, 2, 1` and members `(-1/8, 7/8)`,
`(1/2, 3/2)`, `(9/8, 17/8)`, the vertex cells over the three labels number
`1, 2, 1`: the vertices `1` and `3` of the level `1` are not adjacent, and no
edge crosses height `1`. Each consecutive pair carries two edge cells, spanned
by `0 — 1`, `0 — 3` and by `1 — 2`, `2 — 3`. Read informally, there is one cell
at height `0`, two at height `1` and one at height `2`, the shape of a cycle.
This matches the Reeb graph of the 4-cycle, which is a cycle rather than one
edge with parallel edges because the level set at `1` has two components. The
identification of these cells with the Reeb graph is proved in the subsection
`The Reeb quotient of graph-PL height`: `graphPLReebQuotientIso` states that,
when the critical-value list covers the vertex heights, the realization of
`graphPLReebData G h S` is isomorphic over `ℝ` to the Reeb quotient of
`plHeight G h`. The next section constructs the finite Reeb data of graph-PL
input and identifies it with the cycle.

Crossing is strict and spanning is not. An edge with endpoint heights `0` and
`2` spans `[0, 2]` and is the one active edge over `(0, 2)`, but it crosses
neither `0` nor `2`; at a level, an endpoint at the level height survives
instead.

Each hypothesis has a failure mode. The single member `(-1/2, 5/2)` contains
both heights `0` and `2` of one edge, so the family is not height-separating;
the splitting still gives one vertex cell, one induced component and no
uncovered edge. For the members `(-1/4, 5/4)`, `(3/4, 9/4)`, `(7/4, 13/4)` on
the 4-cycle, the overlap `(3/4, 5/4)` contains the height `1`; there are two
edge cells over the first pair, the induced components `{1}` and `{3}`, while no
edge spans `[3/4, 5/4]`, so the spanning description fails without its
hypothesis. Connectedness of the graph is needed for the attained range, as
shown above.

## Finite Reeb data of graph-PL input

Fix a critical list `S` with levels `a 0 < ⋯ < a n`, the stars
`J i = (a (i − 1), a (i + 1))` with infinite extremes and the gaps
`K e = (a e, a (e + 1))`. For a finite graph with vertex heights `h`, the
finite data `graphPLReebData G h S` have

* at level `i`, the components of the graph induced on the vertices of height
  `a i`, together with the edges crossing `a i`;
* over gap `e`, the edges whose height interval contains `[a e, a (e + 1)]`;
* as endpoint maps, the level component of an endpoint at the level when the
  edge has one, and the edge itself as a crossing vertex otherwise.

A spanning edge without an endpoint at a bounding level crosses it, so the
endpoint maps are well defined. Two endpoints at the same level are adjacent in
the level graph, so the choice of endpoint does not matter. A crossing edge is a
Reeb vertex of degree two over the level: on the single edge of heights `0` and
`2` at the levels `0, 1, 2`, the level `1` carries no graph vertex, and the
edge is one Reeb vertex there, shared by the two incident gaps. A horizontal
edge spans no gap; it merges its endpoints in the level graph. The construction
needs no covering hypothesis, and a level may carry no vertex. For a nonempty
finite vertex set, the sorted distinct vertex heights form a canonical list
whose levels are exactly the vertex heights.

The data are compared with the extraction of the path-component precosheaf of
the piecewise-linear height, whose vertex values are the path components over
the stars and whose edge values are those over the gaps. Suppose every vertex
height is a level of `S`. Then the vertices with height in `J i` are those of
height `a i`, and no vertex height lies in a gap. An active edge over `J i`
without an endpoint in `J i` has endpoint heights on both sides of `a i`, so the
uncovered edges over the star are the edges crossing `a i`, for every open
interval containing a single vertex height, rays and `ℝ` included. Through the
incidence-graph comparison and the splitting of incidence components, the path
components over `J i` are the Reeb vertices at level `i`, and those over `K e`
are the Reeb edges over gap `e`. Under these bijections, the inclusions
`K e ⊆ J e` and `K e ⊆ J (e + 1)` are the endpoint maps on every element of the
gap value, so the extracted data and `graphPLReebData G h S` are isomorphic
finite data. Neither bijection needs finiteness.

The comparison above is at stars. Closed levels are treated in the subsection
`Closed level sets of graph-PL height` below.

The covering hypothesis cannot be dropped. For two isolated vertices of heights
`0` and `2` and the single level `0`, the star is `ℝ` and has two path
components, while the level carries the single Reeb vertex of height `0`; no
bijection exists. For two isolated vertices of equal height, the data have two
Reeb vertices, against one for the edge joining them.

On the 4-cycle with heights `0, 1, 2, 1` at the levels `0, 1, 2`, the data have
`1, 2, 1` vertices and two edges over each gap. The left endpoint map of the
lower gap is constant at the component of `0`, its right endpoint map is
injective onto the components of `1` and `3`, and symmetrically for the upper
gap. A map of finite data from the cycle data of the realization theory, with
bijective components, identifies the two, so the realization of the graph-PL
data is not the path with one vertex per level. On the tree with edges
`0 — 2`, `1 — 2`, `2 — 3` and heights `0, 1, 2, 3`, the counts `1, 2, 1, 1` and
`1, 2, 1` agree with the MultiNerve Mapper cell counts of the previous section.
These are elementary library results, not attributed to a source.

Constructibility of the precosheaf and its cosheaf identification with the
realized data are proved in the subsection `Constructibility and the cosheaf of
graph-PL height` below; the Reeb quotient identification is proved in the
subsection `The Reeb quotient of graph-PL height`, under a covering
critical-value list. The separate [categorical assembly](mapper-reeb-approximation.md)
is reconstructed as a real graph and compared with the Reeb quotient.
These finite-data comparisons do not identify the ordinary Mapper or MultiNerve Mapper
with that reconstruction. A refinement tower of height-separating covers is not asserted;
refinement of covering critical lists is treated in the last subsection.

### Closed level sets of graph-PL height

For the piecewise-linear height on a graph realization, the closed level
`plHeight G h ⁻¹' {c}` consists of the vertices of height `c`, the whole
segments of horizontal edges whose two endpoints have height `c`, and one
interior point on each edge whose endpoint heights strictly cross `c`. The
crossing is strict, and its crossing parameter is unique; an edge with exactly
one endpoint at `c` contributes only that endpoint.

For finite `V`, there is an equivalence
`ZerothHomotopy (ClosedLevel G h c) ≃ LevelVertex G h c`: the components of the
graph induced on vertices of height `c`, together with the crossing edges. The equivalence
`closedLevelComponentsEquiv` has the explicit inverse `closedLevelPoint`, which
represents an induced component by any of its vertices and a crossing edge by
its `crossingPoint`. A horizontal edge lies in the component of its endpoints.

A level window is an open interval containing `c` and no other vertex height
(`IsLevelWindow`), and `exists_isLevelWindow` supplies one when `V` is finite.
For every level window, inclusion of the closed level into the window is
bijective on path components, and its triangle with the window classification
`levelWindowEquiv` commutes, by
`componentMap_levelInclusion_bijective` and
`levelWindowEquiv_comp_componentMap_levelInclusion`. Consequently, the
vertices of `graphPLReebData G h S` at level `i` are the path components of
`plHeight G h ⁻¹' {S.value i}` without a covering hypothesis, via
`graphPLReebDataVEquivClosedLevel`. Under `CoversVertexHeights`, the star
bijection factors through the level inclusion by
`graphPLStarEquiv_comp_componentMap_levelInclusion`.

The 4-cycle with heights `0, 1, 2, 1` illustrates the window condition. Its
level `1` has two path components, represented by vertices `1` and `3`, and
the window `(1/2, 3/2)` gives a bijective inclusion. The larger interval
`(-1/2, 5/2)` contains the heights `0` and `2`, so it is not a level window and
the corresponding inclusion map on components is not injective. Thus the
window hypothesis cannot be dropped. At level `1/2` the same cycle has two
crossing-point components and no level vertex, while level `3` is empty.

### MultiNerve Mapper as finite Reeb data

The comparison uses a level for each member of the uniform cover, rather than
the canonical vertex-height list `vertexHeightLevels`. A critical list `T` is
`LevelsAdapted` when its level for member `k` belongs to that member and to no
other member. If `0 < g`, `2g ≤ r`, the cover is height-separating, and every
vertex height lies in some member, `exists_levelsAdapted` produces such a list
with `CoversVertexHeights T h`. Conversely, `LevelsAdapted.heightSeparating`
shows that adaptedness together with this vertex-height coverage implies height
separation.

The member-adapted choice is necessary because a regular member can contain no
vertex height and still carry a vertex cell coming from an edge crossing that
level. Thus the Mapper data can subdivide the canonical data. In
F2, `edge_mapperIso` compares the single-edge Mapper at `S012`, whose regular
middle member contributes the crossing vertex and whose two gaps each carry an
edge cell, with the graph-PL finite data; `edge_S02_counts` records the one-gap
canonical comparison at `S02`.

For a two-label cell, `labelFace` is its face over either label, and
`eq_labelFace_of_le` characterizes it as the unique single-label face below the
cell. These faces are the `left` and `right` fields of `uniformMapperData`.
The equations `uniformMapperVertexEquiv_left` and
`uniformMapperVertexEquiv_right` identify them with the endpoint maps of the
corresponding graph-PL finite Reeb data, yielding `uniformMapperIso` with
`graphPLReebData G h T`.

When `2g ≤ r`, `uniformMapperCellsEquiv` exhausts all MultiNerve cells: every
cell is either over one label or over a consecutive pair. The bound is needed:
for the boundary cover with `2g > r`, `triple_cell` supplies a cell with three
labels, so it belongs to neither summand of that equivalence.

The hypotheses also have independent negative controls. The cover governed by
`overlap_control` admits no adapted list covering the vertex heights, as shown
by `overlap_no_adapted`. The list `T1` is adapted but does not cover the vertex
heights, and `T1_no_iso` shows that it gives no isomorphism with the Mapper data.
At the positive end, `exists_uniformMapperIso` gives member-adapted levels and
an isomorphism whenever the finite graph-PL height is bounded in `[m, M]` and
`0 < ρ`, with `0 < g`, `2g ≤ r`, and `r < ρ`.

These results compare the MultiNerve Mapper with finite Reeb data at
member-adapted levels. The MultiNerve terminology is used in the sense of
CO16-v3 Definitions 3.2 and 3.3 as context; the comparison itself is a
library result. The comparison with the canonical list is in the next
subsection; the ordinary Mapper one-skeleton is compared below.

Under `2g ≤ r`, `incidenceGraphUniformMapperIso` identifies the incidence graph of
`uniformMapperData G h a r g n` with the ordinary Mapper one-skeleton
`mapperOneSkeleton`. The vertices match through `uniformMapperIncidenceVertexEquiv`, which
needs no hypothesis; the bound `2g ≤ r` excludes edges between labels at distance two or
more. Composing with `uniformMapperIso` gives `mapperOneSkeletonGraphPLIso`, with the
consequences `mapperOneSkeleton_connected_iff` and
`card_mapperOneSkeleton_edgeSet_le`. Parallel MultiNerve edge cells, that is, several
cells over the same label pair, are forgotten by the ordinary one-skeleton. Fixtures M1–M4
are in `TDA/Mapper/OneSkeletonReebDataExamples.lean`. M5 is the boundary control: for the
point graph with `2g > r`, the one-skeleton is complete on three vertices while the
incidence graph has non-adjacent vertices at levels 0 and 2, so no isomorphism exists
(`point_no_oneSkeletonIso`) and `2g ≤ r` cannot be dropped.

### Refinement of graph-PL finite Reeb data

Let `S : CriticalValues n` and `T : CriticalValues m`, and suppose that
`CoversVertexHeights S h` and
`hST : Set.range S.value ⊆ Set.range T.value`. The graph-PL finite Reeb data
over `T` are isomorphic to the fibre-based refinement of the data over `S`:
`graphPLRefineIso : graphPLReebData G h T ≅
RGraph.refineData hST (graphPLReebData G h S)`. At an old level, its vertex
component transports the level graph along the equality of heights and then
uses the inverse of `refineVEquivOld`; at an inserted level in `S.K e`, the
level graph is empty and its crossing-edge summand is exactly the set of edges
spanning the surrounding `S`-gap, followed by the inverse of `refineVEquiv`.
On a refined gap, the component is the identity on spanning edges followed by
the inverse of `refineEEquiv`. Exterior levels and gaps are empty on both
sides. These formulas are recorded by `graphPLRefineHom_v_old`,
`graphPLRefineHom_v_inserted`, and `graphPLRefineHom_e`.

For `S ⊆ T ⊆ U`, the pointwise transitivity statements
`graphPLRefineHom_trans_v` and `graphPLRefineHom_trans_e` say that the direct
comparison from `U` to the data over `S` agrees with first applying
`realizeHom` to the comparison from `U` to `T` and then `refineMap` from `T`
to `S`. The categorical form of this transitivity is not stated here.

The isomorphism `uniformMapperRefineIso` identifies member-adapted Mapper data
with the refinement of graph-PL data over any coarser covering list. In
particular, `uniformMapperCanonicalIso` identifies them with a refinement of
the graph-PL data over the canonical list `vertexHeightLevels h`, and
`exists_uniformMapperCanonicalIso` supplies such parameters and a covering
list under the bounded-height and positive-radius hypotheses of the Mapper
comparison.

At the realization level,
`graphPLRefineToOverIso` and `uniformMapperCanonicalToOverIso` give the
corresponding isomorphisms in the real slice (universe `0`), respectively
between the realizations over `T` and `S`, and between the adapted Mapper
realization over `T` and the canonical graph-PL realization.

The covering hypothesis is necessary. For `path3` with heights `0, 1, 2`,
`S02` does not cover the vertex heights, its gap carries no spanning edge, and
`path_no_refineIso` shows that there is no isomorphism over `S012`. Exterior
behaviour is controlled as well: for the single edge with heights `0, 2` over
`S0123`, the level `3` and the gap `[2, 3]` are empty on both sides. These are
elementary library results, not results attributed to a source.

### Constructibility and the cosheaf of graph-PL height

Let `V : Type` be finite, let `G : SimpleGraph V`, let `h : V → ℝ`, and let
`S : CriticalValues n` satisfy `CoversVertexHeights S h`. If `I ≤ J` are nested
open intervals, `I` is nonempty, and they meet the same levels, then the
surviving vertices and active edges in the two cell graphs are the same. Thus
`cellGraphIsoOfSameLevels` is a graph isomorphism, and the induced map on
components is bijective. Finiteness of `V`, together with the empty tails forced
by the vertex heights lying between the extreme levels, gives
`isConstructibleAt_intervalComponents_plHeight`. This is constructibility in the
sense of DMP15-v1 Definition 3.9, with the nonempty-source correction recorded
in `docs/math/references.md`.

`graphPLCosheafIsoOfIso` gives the labelled identification for finite Reeb data
isomorphic to `graphPLReebData G h S`. Its canonical case `graphPLCosheafIso`
has type `(graphPLReebData G h S).toCosheaf S ≅ intervalComponents (plHeight G h)`.
Both are obtained from the labelled lift `toCosheafLift`; the canonical lift uses
the inverse of `graphPLExtractIso`, while the arbitrary case first composes it
with the given finite-data isomorphism. This has the shape of DMP15-v1
Proposition 3.18. Their star and gap formulas use `graphPLStarEquiv` and
`graphPLGapEquiv`, and
`graphPLCosheafIso_hom_unique` records labelled uniqueness. This is not a
functorial image of `toCosheaf`, which has no action on morphisms.
`realizeExtractIso` is the corresponding case for extracted data.

The corollaries are `isConstructibleCosheaf_intervalComponents_plHeight`,
`cosheafFunctorGraphPLIso`, and `geometricInterleavingDistance_graphPL`. The
last states that the geometric interleaving distance of two graph-PL
realizations equals the interleaving distance of their path-component
precosheaves. The finite-data statements use universe `0`, forced by
`IsIntervalCosheaf.{0}`.

The fixtures include the 4-cycle comparison through `cycleIso`, with two
components over the middle star; the single edge at `0 < 2`, together with its
refinement `0 < 1 < 2` whose middle level is vertex-free; the Y-tree; and the
horizontal edge, whose level has one component. The negative control uses two
isolated vertices of heights `0` and `2` at the single level `0`: the
precosheaf has one component over `(-1, 1)` and two over `ℝ`, so it is not
constructible at this single-level list, as recorded by `missing_not_isConstructibleAt`.
Thus the covering hypothesis cannot be dropped from the critical-list comparison.

These graph-PL statements are elementary library results, not attributed to a
source. The Reeb quotient homeomorphism of the realization is proved in
`TDA.Mapper.GraphPLReebQuotient`, under a covering critical-value list; see
`The Reeb quotient of graph-PL height` below.

### The Reeb quotient of graph-PL height

Let `V : Type u` be finite, let `G : SimpleGraph V`, let `h : V → ℝ`, and let
`S : CriticalValues n` cover the vertex heights, in the sense of
`CoversVertexHeights S h`. Horizontal edges are allowed. The module
`TDA.Mapper.GraphPLReebQuotient` proves the following identification.

(A) The continuous map `graphPLReebMap` sends the graph realization to the
realization of `graphPLReebData G h S`, preserves height, and has explicit
formulas on vertices, closed levels, and regular points in a gap, through
`graphPLReebMap_vertex`, `graphPLReebMap_of_level`, and
`graphPLReebMap_edgePoint_of_mem_K`.

(B) The map descends through `RGraph.quotientLift` to a bijection and then to
the homeomorphism `graphPLReebQuotientHomeomorph` from
`ReebQuotient (plHeight G h)` to the finite realization. It preserves the
real-valued height. In the real slice, this is packaged by
`graphPLReebQuotientIso`; `graphPLReebQuotientIsoOfIso` transports the result to
isomorphic finite Reeb data. The induced map on interval components is the
inverse of `graphPLCosheafIso`, as stated by
`intervalComponentNatTrans_graphPLReebMap` and
`intervalComponentComparison_comp_graphPLReebQuotientMap`.

(C) Without choosing a list, the Reeb quotient, as an object of the real
slice, is an ℝ-graph (`RGraph.IsRGraph`, by
`isRGraph_graphPLReebQuotient`), and `graphPLReebGraph` packages it as an
object of `RGraph.RGraphCat`, with `graphPLReebGraphIso` identifying it with
`(RGraph.toRGraph S).obj (graphPLReebData G h S)` for every covering list. The
interval-component comparison is an isomorphism, and
`geometricInterleavingDistance_graphPLReebGraph` identifies the geometric
distance between two graph-PL Reeb graphs with the
interleaving distance of their interval-component precosheaves. The
homeomorphism uses `V : Type u`; the real-slice statements, the coherence
statements, and these list-free corollaries use `V : Type`, as required by the
universe-`0` categorical APIs.

The route is direct: construct a height-preserving map into the finite
realization, descend it with `RGraph.quotientLift`, and use the proved
compactness of the graph realization and the quotient together with
Hausdorffness of the finite realization. Constructibility of the graph
realization and the identification of this comparison with the general
`quotientIsoOfIso` are proved in the next subsection. The graph-PL results are
library statements. Their quotient argument
has the shape of DMP15-v1 Proposition 2.12, and the comparison corollary has
the shape of DMP15-v1 Theorem 3.17; the graph-PL statements themselves make no
external source claim.

The fixtures record the scope and boundary. R1 is given by
`c4_reebQuotientIso` and `c4_reebQuotient_not_iso_path`: the 4-cycle quotient
is the cycle realization, not the path realization. R2 is given by
`edge_reebQuotientIso_S02` and `edge_reebQuotientIso_S012`, including a level
with no vertex. R3 is `Y_reebQuotientIso` and `Y_isRGraph` for the tree `Y`
with edges `0 — 2`, `1 — 2` and `2 — 3`. R4 is
`flatEdge_reebQuotient_subsingleton` together with
`flatEdge_vertex_ne`, showing that a horizontal edge collapses in the Reeb
quotient although its realization endpoints differ. R5 is
`c4_isIso_intervalComponentComparison`. R6 is the negative control
`path3_reebQuotient_not_iso_S02`: the covering hypothesis cannot be dropped.

### The graph-PL realization as a constructible ℝ-space

Let `V : Type u`, let `G : SimpleGraph V`, and let `h : V → ℝ`. For (A),
with no hypothesis on `V`, `barycentric` is a continuous injective map from
the graph realization into `V → ℝ`; `t2Space_realization` gives Hausdorffness,
`edgePoint_eq_vertex_iff` and `edgePoint_eq_edgePoint_iff` give the two
point-identification results, `locallyPathConnectedSpace_realization` gives
local path-connectedness, and `realizationMap_injective` gives injectivity of
realized graph embeddings.

(B) Under `[Finite V]`, `LevelPiece` combines the realization of the level
graph with the finite discrete set of crossing edges. The homeomorphism
`levelPieceHomeomorph` identifies this model with `ClosedLevel G h c`, and
`compactSpace_closedLevel` and `locallyPathConnectedSpace_closedLevel` show
that every closed level is compact and locally path-connected.

(C) Without a hypothesis on `V`, `graphPLPresentation` uses closed levels as
its vertex pieces and spanning edges as discrete cylinder pieces, and
`graphPLPresentationMap` maps its realization to the graph realization over
`ℝ`. The map preserves height by `plHeight_graphPLPresentationMap` and is
injective by `graphPLPresentationMap_injective` for every critical list. When
the list covers the vertex heights, `graphPLPresentationMap_surjective` gives
surjectivity. Under `[Finite V]` and for a covering list,
`graphPLPresentationHomeomorph` gives a homeomorphism.

Closed levels are used as vertex pieces because horizontal edges are allowed:
K3 shows that the vertex piece of a horizontal edge need not be discrete,
while K4 shows that the discrete-piece finite data are not homeomorphic over
`ℝ` to `|G|`. Thus the finite-data realization is not a substitute for the
closed-level presentation.

(D) Under `[Finite V]`, `graphPLComponentDataIso` identifies the component data
of the presentation with `graphPLReebData G h S`, and
`graphPLReebMap_graphPLPresentationMap` is the pointwise comparison. For a
covering list, `graphPLPresentationIso` is the slice isomorphism and
`graphPLReebQuotientIsoOfIso_graphPLComponentDataIso` identifies the two
quotient-isomorphism constructions. The covering hypothesis is needed for the
homeomorphism and surjectivity: K5 records that the presentation map remains
injective for every list but is not surjective for an uncovered list.

(E) Under `[Finite V]` and with `V : Type`, `graphPLSpace` regards the graph
realization with its graph-PL height as a constructible `ℝ`-space.
`quotientRGraphFunctor_obj_graphPLSpace` identifies its restricted quotient
functor image with `graphPLReebGraph`, `overBaseMap_graphPLSpace` identifies
the structure map with `plHeight`, and
`isRGraph_quotient_thickening_graphPLOver` shows that the Reeb quotient of
every geometric thickening is an ℝ-graph. The constructibility theorem
`isConstructibleSpace_graphPLOver` needs only `[Finite V]`, with no covering
list chosen in its statement.

The realization, presentation, presentation map, presentation homeomorphism,
and pointwise identification above are universe-polymorphic for `V : Type u`.
The slice isomorphism, constructibility, identification of isomorphisms, and
the consequences in (E) use `V : Type`, because the relevant categorical APIs
live in universe `0`.

These are library results and make no external source claim. The presentation
follows the notion of a constructible ℝ-space in DMP15-v1 §2.2, and the
comparison `quotientIsoOfIso` packages DMP15-v1 Proposition 2.12.

The fixtures record the scope and boundary. K1 is given by
`c4_isConstructibleSpace`, `c4_componentDataIso`, and
`c4_quotientIsoOfIso_eq`. K2 is given by `Y_presentationHomeomorph` and
`Y_isRGraph_thickening`. K3 is given by `flatEdge_isConstructibleSpace` and
`flatEdge_vertexPiece_not_discrete`, while K4 is the negative control
`flatEdge_not_iso_finiteData`. K5 is the negative control
`path3_presentationMap_not_surjective`. K6 is given by `edge_mid_ne_vertex`
and `c4_t2Space`. K7 is given by `c4_quotientRGraphFunctor_obj` and
`c4_Y_geometricInterleavingDistance`.
