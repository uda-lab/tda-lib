# Real shift diagrams and occurrence untranslation

Positive evaluation shifts move a real persistence module's barcode to the
left. The critical restrictions prove this formula, and the resulting
occurrence bijections let a matching's shifted target return to its original
diagram. The construction retains finite endpoint pairs, essential tails and
all copies of repeated bars.

## Modules, grids and endpoint conventions

Fix a field `k : Type u`, a module `M : PModule.{u,0,u} k ℝ` and an increasing
grid `c : Fin n ↪o ℝ`. The diagram `moduleDiagram c M hfd` is obtained from the
restriction of M to its critical fibers, assumed finite dimensional by
hfd. Its intervals are `[birth,death)`: the left endpoint is included, the
finite right endpoint is excluded, and death at the finite chain's terminal
endpoint represents an essential tail with death `⊤`. An empty grid selects no
critical stage. The padded zero stage of
[reconstruction](constructible-modules.md) receives no real grade.

A finite diagram is a multiset of endpoint pairs. Its finite and essential
occurrence types retain separate labels for repeated pairs or births.
The [bottleneck matching API](../api.md) uses a partial injection
on finite occurrences and a total equivalence on essential occurrences.
Finite and essential occurrences cannot be cross-matched.

## Positive evaluation and the diagram formula

For `ε : ℝ≥0`, the shift evaluates at `t+ε`, so a bar `[b,d)` becomes
`[b−ε,d−ε)` and `[b,∞)` becomes `[b−ε,∞)`. The existing `translateDiagram D a`
adds a to both finite endpoints, or to an essential birth while preserving
`⊤`. Thus the diagram translation parameter is **−ε**:

\[
D_{c-\varepsilon}(S_\varepsilon M)
 =\operatorname{translateDiagram}(D_c(M),-\varepsilon).
\]

`shiftedCriticalIso` compares the restrictions on `shiftGrid ε c` and c.
At every critical index their real parameters agree by
`(c_i−ε)+ε=c_i`. Applying M to this index comparison gives a natural
isomorphism, not just equality of dimensions. Finiteness of each shifted
critical fiber follows from the same index equality. Rank-barcode invariance
under this natural isomorphism gives the same finite interval multiset;
`ofIndexBars_shiftGrid` then moves each real endpoint. Its finite-death and
terminal-death cases preserve the half-open and essential conventions.
`moduleDiagram_shift` is the resulting formula. It needs no constructibility
assumption on the native shifted grid.

If M is constructible on c, its shifted module is constructible on
`shiftGrid ε c`. For any refinement e of that shifted grid, the
[refinement theorem](constructible-refinement.md) derives finite dimensionality
at every added critical fiber and preserves the real diagram.
`moduleDiagram_shift_refinement` therefore proves the same formula on e.
In particular e may be the constructed common grid with another source grid;
no finiteness witness at those new observations is assumed.
Translating this shifted diagram by **+ε** recovers `D_c(M)`.

## Occurrence bijections and matchings

`finiteTranslationEquiv D a` and `essentialTranslationEquiv D a` send the
original occurrence labels bijectively to those of `translateDiagram D a`.
Their value theorems give `(b+a,d+a)` and `b+a`. Their inverse value theorems
give `(b−a,d−a)` and `b−a`. Consequently the inverse for `a=−ε` adds ε,
which is the barcode correspondence usually denoted by `rε`.

These are equivalences of labels, including all copies with equal values.
They do not deduplicate a multiset. At ε=0 the endpoint values are unchanged;
a choice of labels for repeated values need not be definitionally the identity.

`translatedMatching D a` is a complete matching made from these
bijections. Every finite target is selected, so no finite label is sent to
the diagonal. Its maximum cost is at most `|a|`: each finite pair and each
essential birth moves exactly that amount, while an empty maximum is zero.
`exists_shift_matching` and `exists_shift_refinement_matching` apply this
construction to the module diagrams above, with every finite endpoint
value, finite-target coverage, essential birth and cost bound proved. They
compare M with its own shift and require no supplied matching or endpoint
estimate.

For an existing matching from D to `translateDiagram E a`,
`OccurrenceMatching.untranslateTarget` returns the target labels to E by the
inverse equivalences. A finite source is matched to j exactly when the old
matching selected the translated occurrence of j. Unmatched sources are the
same; the selected target range is transported by that same bijection.
The essential target birth changes from b to `b−a`. This relabelling is an
operation on a matching. Translating only its target can change its
pair costs, so it supplies no cost-invariance claim.

## Boundary consumers

A finite-barcode pullback has two copies of `[1,3)` and one essential
bar `[3,∞)`. Its positive evaluation shift by 2 has two copies of `[-1,1)` and
one essential bar `[1,∞)`. The consumers check both exact finite endpoints,
the essential birth and unbounded tail, and the preserved multiplicities.
Observations before, inside and after the shifted grid retain these diagrams
using derived finiteness. The occurrence inverse has the stated endpoint
values, and untranslating the constructed matching recovers each original
label. Parameter zero and the empty grid are also checked in
`TDA.Persistence.ConstructibleShiftBarcodeExamples`.

## Source correspondence and the algebraic-stability dependency

[Bauer–Lesnick v4](https://arxiv.org/html/1311.3681v4), §§2.1–2.3, defines
interval modules and multiset barcode occurrences, including decorated
endpoints. Section 3.1 defines the positive-evaluation shift and its leftward
barcode displacement. The bijection immediately preceding Theorem 6.4 in
§6.1 adds ε back to shifted endpoints. The formula and inverse here are a
checked specialization to the library's finite, zero-left, right-continuous
half-open convention. The grid/rank proof, occurrence representation
and target-relabel operation are library constructions. Source and rights
metadata are in [BL15-v4](references.md#BL15-v4).

The [real induced matching](real-induced-matchings.md) constructs a matching
into the shifted target, with exact `2ε` endpoint and unmatched-length
bounds and a total essential equivalence. The
[isometry construction](constructible-isometry.md) applies the +ε target
inverse, proves the ε pair/diagonal cost bounds and takes the distance infimum
to obtain `d_B=d_I` for finite-constructible modules. The shift-specific
construction above establishes its own complete matching and cost bound. General infinite
decomposition and the source's omitted duality proof are outside its scope.
