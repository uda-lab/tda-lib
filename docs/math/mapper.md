# Mapper foundations

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
Dey–Mémoli–Wang, *Multiscale Mapper*, §2. The library keeps arbitrary index types and
set families and separates the openness hypothesis from the general construction.

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
additional connected-component data for intersections and is not constructed
here. No Reeb equivalence, convergence, stability, persistence-diagram result,
or Nerve Lemma follows from this definition.

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
