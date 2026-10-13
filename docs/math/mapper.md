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
