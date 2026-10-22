# Gluing of the path-component functor

## Statement

Let `X` and `Y` be topological spaces, `f : C(X, Y)`, `W` an open set of `Y`, and `U : ι → Opens Y`
a family of opens with `U i ≤ W` for every `i` and `W ≤ ⨆ i, U i`. Write `C_f` for the open-set
path-component functor `componentFunctor f` (`reeb-components.md`). If maps
`a i : C_f(U i) → A` agree after both inclusions from every overlap,

```text
a i (C_f.map (U i ⊓ U j ≤ U i) c) = a j (C_f.map (U i ⊓ U j ≤ U j) c)
```

for all `i`, `j` and every class `c` over `U i ⊓ U j`, then there is a unique
`g : C_f(W) → A` with `g ∘ C_f(U i ≤ W) = a i` for every `i`
(`TDA.Reeb.componentFunctor_existsUnique_glue`). The test object `A` lies in an arbitrary `Sort`.
Agreement is on classes over the overlap, not on labels of components.

The empty cover is included. It forces `C_f(W)` to be empty (`Examples.emptyCover_isEmpty`), and
then the unique `g` is the map out of the empty type.

## Colimit forms

The statement is derived from the elementary form of the cosheaf condition (`cosheaf.md`):

- `componentFunctor_exists_map_eq`: every class over `W` comes from a member. A point of the class
  has its image in some `U i` (`Opens.mem_iSup`).
- `componentFunctor_map_eq_iff_eqvGen`: two local classes have the same image over `W` iff they are
  related by the equivalence closure of `overlapRel C_f U`. The forward direction takes the chain
  of `componentFunctor_reflTransGen_of_mk_eq` and turns each shared chain point into an overlap
  step with `overlapRel_mk`. The backward direction holds because both inclusions of a class over
  an overlap send it to the class of the same point over `W`.

Hence `C_f` sends every cocone over the pairwise-intersection diagram whose apex is covered by the
members to a colimit (`componentFunctor_isColimit`). The cases `coverCocone U hU` and mathlib's
`Pairwise.cocone U` give `componentFunctor_isColimit_coverCocone` and
`componentFunctor_isPairwiseCosheaf`: `C_f` satisfies `IsPairwiseCosheaf.{w}` for every
cover-index universe `w`.

## Naturality

For `Z : Type u`, `g : C(Z, Y)` and `h : C(X, Z)` with `g ∘ h = f`, gluing commutes with the induced
transformation `componentNatTrans h`: if `G` glues a family `a` for `C_g`, and `G'` glues the
family `a i ∘ (componentNatTrans h).app (U i)` for `C_f`, then
`G' = G ∘ (componentNatTrans h).app W` (`componentFunctor_glue_natTrans`). The fixture
`Examples.collapse_glue_identifies` applies this to the collapse of the discrete two-point space
over the one-point base. The glue for the collapsed map identifies two classes that are distinct
over the two-point space.

## Universes and index sorts

The carrier `X : Type u` and the base `Y : Type v` are independent, and the cover index
`ι : Type w` is independent of both. The functor lands in `Type u`, so the colimit forms test only
cocones with apex in `Type u`; the raw statement covers every `Sort`. A cover indexed by an
arbitrary `Sort` is reindexed through `PLift`, which preserves the union
(`Examples.existsUnique_glue_sort`). No smallness assumption is used.

## Acceptance cases

- Two overlapping intervals `(-∞, 2/3)` and `(1/3, ∞)` covering `ℝ`: the class of `0` over the
  first and the class of `1` over the second are related through overlap steps
  (`Examples.twoOpens_classes_related`), and the colimit form holds (`Examples.twoOpens_isColimit`).
- Disjoint cover of `ℝ \ {0}` by `(-∞, 0)` and `(0, ∞)`: an overlap step never changes the member,
  so the classes of `-1` and `1` over the union differ (`Examples.negPos_classes_ne`). Gluing makes
  no false identification.
- Empty cover (`Examples.emptyCover_isEmpty`, `Examples.emptyCover_existsUnique_glue`) and empty
  open with a nonempty cover (`Examples.bot_isColimit`).
- Duplicate indices, `⊤` twice: the two local classes of one point are related
  (`Examples.dupCover_related`), and the colimit form holds (`Examples.dupCover_isColimit`).
- Naturality at the collapse (`Examples.collapse_glue_identifies`).

## Source correspondence

de Silva, Munch and Patel prove that the path-component pre-cosheaf of an ℝ-space is a cosheaf
(*Categorified Reeb Graphs*, Proposition 3.15), in the universal-property form (3.5)–(3.6) of
§3.2. Their proof defines the glued map on the class of a point `y` through any member containing
`f(y)`, shows independence of the member by the consistency condition, and shows independence of
the point by local constancy along a path. The Lean proof follows the same argument in factored
form. Independence of the member is the overlap step, independence of the point is the chain of
the path-local cover lemma (`path-cover.md`), and the glued map is chosen through a representative.
Uniqueness holds because every class comes from a member.

Library generalizations, chosen by the library and not printed in the paper: an arbitrary base
space instead of `ℝ`, arbitrary opens and open covers instead of open intervals and interval covers,
and covers indexed by any type or, through `PLift`, any sort. The empty cover is explicit in Lean
and implicit in the source's convention that the value at the empty set is empty. Restricting to open
intervals of `ℝ` recovers the source statement. The result concerns path components of inverse
images. The source notes that it fails for connected components (Example 3.20); no constructibility
or finiteness is assumed or concluded.

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147).
