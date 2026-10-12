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

These set-theoretic conventions organize the cover maps used in Dey–Mémoli–Wang,
*Multiscale Mapper*, §2–3. They deliberately provide an arbitrary-set library
interface beyond the open-cover setting used for Mapper constructions.
