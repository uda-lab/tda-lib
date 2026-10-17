# Actual diagram transport at attained grades

`dgm_common_face_endpoints_of_orderingEquivalent` transports the actual finite-face
homology diagrams of two ordering-equivalent filters on the same complex. It
produces one finite multiset of endpoint occurrences

```text
E : Multiset (TotalFace K × Option (TotalFace K)).
```

Mapping a pair `(s, Some t)` through either filter labels it by that filter's
values at the birth face `s` and finite death face `t`. A pair `(s, None)` labels
essential death by the outer `⊤` of `WithTop`. Both actual diagram point multisets
are obtained from this same `E`. Repeated occurrences remain repeated; equality
of supports or fiber dimensions would be insufficient.

`dgm_points_map_of_strictMonoOn` specializes this correspondence to a total
function `φ : α → β`, strict only on `Set.range f.value`, and a genuine supplied
filter `g` satisfying `g.value s = φ (f.value s)` for every actual face. Its exact
conclusion is

```text
(dgm k g n).points =
  (dgm k f n).points.map (fun p => (φ p.1, WithTop.map φ p.2)).
```

The vertex type and coefficient field share universe `u`, as in the actual
homology diagram API. The source and target grade types have independent
universes `v` and `w`. Both grade types and the vertex type are linearly ordered,
the coefficient type is a field, and the actual face type is finite. Neither
law assumes an inhabited grade type, a nonempty complex, positive critical
cardinality, or global injectivity or monotonicity of `φ`.

`dgm_points_map_of_monotoneOn` removes the strictness assumption and allows `φ` to identify
attained values. If `φ` is monotone on `Set.range f.value` and
`g.value s = φ (f.value s)` for every face, then

```text
(dgm k g n).points =
  ((dgm k f n).points.map (fun p => (φ p.1, WithTop.map φ p.2))).filter
    (fun p => (p.1 : WithTop β) ≠ p.2).
```

The filter deletes exactly the finite points that become diagonal under a non-injective
reparametrisation; essential deaths remain at `⊤`. The strict law
`dgm_points_map_of_strictMonoOn` is the companion for strict monotonicity on the attained
values, where no off-diagonal point collapses and the map is unfiltered. Both laws are
library extensions proved from the face-template definitions.

## Homology ranks and vanishing

`finrank_sublevelHomology_eq_countP` identifies the homology dimension at a threshold with the
number of diagram points alive there:

```text
Module.finrank k (simplicialHomology (f.sublevel t) k n) =
  (dgm k f n).points.countP (fun p => p.1 ≤ t ∧ (t : WithTop α) < p.2).
```

Consequently, `not_isZero_sublevelHomology_of_mem_dgm` says that the sublevel homology object
at a diagram point's birth is not `IsZero`. The vanishing criterion
`dgm_points_eq_zero_of_isZero` says that if
`IsZero (simplicialHomology (f.sublevel t) k n)` holds for every threshold `t`, then the
diagram point multiset is zero. These are library extensions and do not cite an external source.

## Proof from the existing library definitions

Ordering equivalence supplies an order isomorphism between the attained value
ranges that sends each face's value to its counterpart. The critical-value
subtypes are these finite attained ranges. Restricting the range isomorphism
gives their bijection and equal cardinalities without choosing a face. Pinned
mathlib's `Finset.orderEmbOfFin_unique` identifies their increasing enumerations
after the private cardinality alignment.

For each actual grade, attainment gives a face witness. The existing
`OrderingEquivalent.sublevel_eq` then identifies the two grade complexes.
Equality-induced homology maps commute with every actual inclusion: after
eliminating the two complex equalities, the square is reflexive. The ranks of
all grade structure maps consequently agree. The existing `rankBarcode_eq_iff`
gives equality of the canonical indexed barcodes. Its integer sentinel and
four-rank multiplicity proof is reused, including birth zero, death at the
terminal index and repetitions.

Each bar occurrence has an attained birth index. A death below the terminal
index also has an attained witness; terminal death supplies `None`. These
witness pairs form `E`, whose two maps are the existing `ofIndexBars` definitions
of the actual diagrams. When the critical cardinality is zero there are no
indexed bars, so `E=0`; no face or ambient default value is selected.

Strictness on attained values, together with the supplied face-value equality,
preserves and reflects every weak face comparison and hence gives ordering
equivalence. Applying the first law and composing multiset maps proves the
second. The optional-death split fixes essential top and maps each finite
attained death through `φ`. Tied source values yield tied target values, so no
canonical choice among face witnesses is required.

This is a direct construction from the repository's finite filtration,
actual homology and rank definitions. It is not attributed to a theorem in a
primary paper and introduces no interval-decomposition existence result.
The supporting definitions are `Filtration.OrderingEquivalent`,
`FilterFunction.criticalValues`, `gradeHomologyBarcode`, `rankBarcode_eq_iff`
and `IndexDiagram.ofIndexBars`; the public result modules are
`Persistence.SublevelDiagramTransport` and its private examples.

## Actual finite examples and boundaries

The private examples use genuine filters and actual homology over `ZMod 2`:

| Fixture | Actual statement |
| --- | --- |
| Empty | Common occurrence multiset zero and both diagrams empty in every degree, including an inhabited source grade type and `Empty` target grade type; the separate point-map consumer supplies an actual `Empty → ℚ` function. |
| One vertex | Birth `2` transports to birth `3`, with exactly one essential H0 point and no finite point. |
| Two vertices and an edge | Source face values `2,5,9` give `{(2,⊤),(5,9)}`; target values `3,6,10` give `{(3,⊤),(6,10)}`. Both laws are consumed. The actual first-to-second inclusion has rank `1` into dimension `2`, and its matched square and two-step composition are proved. |
| Strictness on support | On `ℚ`, `φ(2)=3`, `φ(5)=6`, `φ(9)=10`, and `φ(x)=0` elsewhere. Strictness on the exact attained set is proved, together with an off-support collision and failure of global monotonicity. |
| Tied repeated point | Two isolated vertices at birth `2` have actual H0 rank `2` and two essential occurrences, transported to two occurrences at birth `3`; point counts are natural numbers. |
| Independent universes | Both public types have generic independent-universe consumers and nonempty genuine singleton consumers with separately lifted grade types. |

The actual singleton and isolated-vertex H0 computations use public simplicial
homology APIs. The edge computation uses its actual signed boundary and
inclusions; its grade ranks determine the barcode through the existing rank
uniqueness theorem. No private predecessor declaration is imported as an API
and no supplied numerical rank array replaces an actual map computation.

Correspondence concerns attained critical grades and actual endpoints. For the
support-only function above, the source sublevel at `3` is nonbottom but the
target sublevel at `φ(3)=0` is bottom. Thus arbitrary ambient-threshold
naturality would be false. A finite greatest grade is still a finite endpoint
below the separate essential outer top. No global `Diagram.map`, general
ambient reparameterization, interval decomposition, triangle/H1 computation,
or complete real-valued acceptance suite follows from these two laws. For order
embeddings, `Diagram.map` is defined separately in
[filter and diagram reparametrization](filter-reparametrization.md).
