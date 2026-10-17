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
Mapper. No such transfer and no approximation or stability result is proved.

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

No geometric realization, homology, Nerve Lemma, contiguity or
selector-independence of multinerve maps, interleaving, approximation or stability
statement is proved.

## Graph-PL incidence labels and finite consumers

For a simple graph `G`, a vertex height `h : V → ℝ`, and a labelled family of
open real intervals, the path-component label over each interval is equivalent
to a connected component of the incidence graph `cellGraph G h I`. Combining
these equivalences over the interval labels gives a vertex equivalence from the
actual ordinary Mapper of `plHeight G h` to an incidence-labelled nerve. The
members of that nerve are the actual path-component cover members transported
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
component-index type, its supported-vertex subtype, and the subtype of actual
finite faces are finite. This is a noncomputable finiteness result. Finitely many
interval labels alone are insufficient: for the constant map from discrete
`ℕ` to a point and the one-member full cover, the supported Mapper vertex type
is explicitly equivalent to `ℕ`.

The concrete graph fixtures use the actual PL-height inverse images. An open
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
is the choice-independence statement at this level. No homology-map equality or
chain homotopy is inferred.

A coherent cover tower over a preorder consists of a possibly varying index
type and indexed family at every parameter, together with a selected
refinement for every comparison. The index types may depend on the parameter
but live in one common universe. Strict identity and composition equations for
the selector functions are supplied as part of the tower data; coherence is
not inferred from unrelated selector choices. Ordinary Mapper assigns a
complex to every parameter and a simplicial vertex map to every comparison,
and the existing strict refinement laws prove identity and composition for
these maps. This direct interface makes no fixed-ambient inclusion claim and
adds no categorical, diagram, stability, or persistence conclusion.

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
Over a height-separating uniform family three cases remain.

* A member containing the vertex height `c` contains no other vertex height, so
  its surviving vertices are those of height `c`. An active edge without a
  surviving endpoint then has endpoint heights strictly on both sides of `c`:
  it crosses the level. The vertex cells over the member are the components of
  the graph induced on the level `{h = c}` together with the edges crossing `c`.
* A member `(p, q)` containing no vertex height carries one vertex cell for each
  edge whose height interval contains `[p, q]`.
* The overlap `(p, q) = (a + l(r − g), a + l(r − g) + g)` of consecutive labels
  `k` and `l = k + 1` contains no vertex height, so the edge cells over `{k, l}`
  are the edges whose height interval contains `[p, q]`. Labels at distance at
  least two carry no edge cell.

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
identification is not proved: neither the incidence of these cells nor a Reeb
graph of graph-PL input is constructed.

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

The face maps from edge cells to vertex cells, the finite Reeb graph of
graph-PL input as `FiniteReebData` and its isomorphism with the MultiNerve
Mapper of a height-separating uniform family are not proved. No geometric
realization of either Mapper construction, no level set of the realization as
a closed subspace, no refinement tower of height-separating covers and no
approximation statement is proved.
