# Pairwise-intersection cosheaf condition

## Diagram and cocone

Let `α` be a meet-semilattice, viewed as a thin category, and `U : ι → α` a family indexed by
`ι : Type w`. Mathlib's `Pairwise.diagram U : Pairwise ι ⥤ α` has an object `U i` for every index
and an object `U i ⊓ U j` for every ordered pair, with the two inclusions
`U i ⊓ U j ≤ U i` and `U i ⊓ U j ≤ U j`. The pair `(i, i)` is a separate object whose value is
`U i ⊓ U i`.

For an upper bound `W` of the members, `TDA.Topology.coverCocone U hU` is the cocone over this
diagram with apex `W`. It needs only `SemilatticeInf α`, so the union of the members need not
exist in `α`. When `α` is a complete lattice and `W = ⨆ i, U i`, it agrees with mathlib's
`Pairwise.cocone U` up to its legs, which are unique because `α` is thin.

## Elementary form

For `F : α ⥤ Type w₀`, `overlapRel F U` relates two local values `⟨i, e⟩` and `⟨j, e'⟩` when
some value `c` over the overlap `U i ⊓ U j` restricts to `e` along the left inclusion and to `e'`
along the right one. Agreement is on the value over the overlap object, not on labels or on
values that merely look alike in `F (U i)` and `F (U j)`.

`nonempty_isColimit_mapCocone_iff` states, for every cocone `c` over `Pairwise.diagram U`, that
`F.mapCocone c` is a colimit in `Type w₀` exactly when

1. every value over `c.pt` is the image of a value over some member, and
2. two local values with the same image over `c.pt` are related by the equivalence closure of
   `overlapRel F U`.

The converse of the second condition holds for every cocone, because both images of an overlap
value over the apex equal its image along the leg at the pair. The value over the apex is thus
the disjoint union of the local values modulo the identifications along overlaps: the
coequalizer of the two inclusion families out of the overlaps.

The proof uses mathlib's bijectivity criterion `Types.isColimit_iff_coconeTypesIsColimit`, which
describes the colimit type of a functor to `Type` as a quotient of the sigma type of its values.
Neither `IsColimit` nor this criterion needs `HasColimit`, `Small` or `UnivLE`, and none of these
is assumed.

## Raw universal property

`existsUnique_glue_of_surjective_of_eqvGen` derives the universal property from the two
conditions. If a family `a i : F (U i) → A` satisfies
`a i (F.map (U i ⊓ U j ≤ U i) c) = a j (F.map (U i ⊓ U j ≤ U j) c)` for all `i`, `j` and every
value `c` over the overlap, there is a unique `g : F c.pt → A` with `g ∘ F (U i ≤ c.pt) = a i`.
The test object `A` lies in an arbitrary `Sort`, not only in `Type w₀`. The compatibility
hypothesis includes the diagonal pairs `i = j`. `eqvGen_overlapRel_apply_eq` is the invariance
step: a compatible family takes equal values on related local values.

## Cosheaves on open sets

For a topological space `Y`, `IsPairwiseCosheaf.{w} F` states that `F : Opens Y ⥤ Type wF` sends
`Pairwise.cocone U` to a colimit for every family `U : κ → Opens Y` with `κ : Type w`. This is the
dual of mathlib's `TopCat.Presheaf.IsSheafPairwiseIntersections`, which asks a presheaf to send
`(Pairwise.cocone U).op` to a limit. The cover-index universe is the first universe parameter
and is independent of the universes of `Y` and of the values; mathlib's sheaf-side predicate
ties its index universe to the space.

The colimit form tests only cocones whose apex lies in `Type wF`, as `IsColimit` in that category
does. The raw universal property covers test objects in every `Sort`.

## Mathlib audit

Pinned mathlib has no cosheaf API. Its sites, sieves and sheaf conditions concern presheaves
`Opens Yᵒᵖ ⥤ C`; dualising them would mean sheaves with values in an opposite category, for
which mathlib has no API. The library therefore uses the pairwise-intersection diagram directly
and proves the elementary correspondence above, rather than building a separate site framework.

## Source correspondence

de Silva, Munch and Patel define a cosheaf over the real line by asking that `F(U)` be the
colimit of `∐ F(I_p ∩ I_q) ⇉ ∐ F(I_p)` for every open interval `U` and every cover of `U` by open
intervals (*Categorified Reeb Graphs*, §3.2, diagram (3.4)). Their first interpretation of this
condition, the disjoint union modulo identifications along overlaps, is the elementary form above.
Their third, the universal property (3.5)–(3.6), is the raw form. They omit pairs with empty
overlap, which is equivalent for functors with empty value at the empty set; the Lean diagram keeps
every pair, as mathlib's sheaf condition does.

The Lean packaging is stated for an arbitrary meet-semilattice and an arbitrary functor to `Type`,
and the cosheaf predicate for all opens of an arbitrary space. These are library choices, not
statements printed in the paper. They let the same packaging serve other cosheaves, such as the
smoothings that de Silva, Munch and Patel show to be cosheaves again (Proposition 4.20). The Lean
packaging covers functors to `Type` only. The module `TDA.Topology.Cosheaf` depends
on mathlib only. Its application to path components is described in
`reeb-components-gluing.md`.

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147);
[pinned mathlib pairwise diagrams](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/CategoryTheory/Category/Pairwise.lean);
[pinned mathlib colimits in `Type`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/CategoryTheory/Limits/Types/Colimits.lean);
[pinned mathlib pairwise sheaf condition](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Sheaves/SheafCondition/PairwiseIntersections.lean).
