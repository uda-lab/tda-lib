# Finite induced matchings through the actual image

## Modules and labeled barcodes

Fix a field `k : Type u`, a finite chain `Fin s`, and pointwise finite-dimensional
modules `M N : PModule.{u,0,u} k (Fin s)`. The input is an arbitrary actual natural
transformation `f : M ⟶ N`. The field and module carriers share their universe.

The canonical barcode `rankBarcode M` is a multiset of half-open intervals
`[birth,death)` with natural endpoints `birth < death ≤ s`.
`BarcodeOccurrence s B` is the index type of `B.toList`, and `occurrence B i`
is the interval at that index. Equal interval values retain distinct labels.
Death `s` records survival through the final observed stage.

## The actual image factorization

`finiteImage f` has fiber `range (f.app i).hom` at stage `i`. Naturality sends
each such range into the next one, so restricting the structure maps of `N`
gives its functor structure. The image fibers inherit finite dimensionality
from the target fibers by the existing submodule instance.

`toFiniteImage f` corestricts each component to its range and is componentwise
surjective. `fromFiniteImage f` includes each range in the target fiber and is
componentwise injective. Both transformations are natural and their composite
is `f`, as proved by `toFiniteImage_comp_fromFiniteImage`.

Write `A = O(rankBarcode (finiteImage f))`, `B = O(rankBarcode M)` and
`C = O(rankBarcode N)` for the three occurrence types. The existing
[epi embedding](finite-epi-matching.md) and
[mono embedding](finite-mono-matching.md) give actual embeddings

```text
E : A ↪ B,    J : A ↪ C.
```

They are exposed as `imageSourceEmbedding` and `imageTargetEmbedding`.
`E` preserves birth and sends the image bar to a source bar dying no earlier.
`J` preserves death and sends it to a target bar born no later. Their canonical
orders use the original occurrence indices to distinguish tied copies.

## The partial injection

`inducedDomain f` is exactly `range E`. `imageOccurrenceEquivDomain` identifies
`A` with this domain by `Equiv.ofInjective`. Taking its inverse and then applying
`J` defines `inducedMatching f`, an embedding of the domain subtype into `C`.
Thus its inverse step is defined precisely where an intermediate occurrence exists.

`inducedMap f : B → Option C` evaluates this partial injection on every source
label. It returns `none` on unselected labels. `inducedMap_eq_some_iff_unique`
characterizes its graph:

```text
inducedMap f i = some j  ↔  ∃! a : A, E(a) = i and J(a) = j.
```

Consequently its domain is exactly `range E` and its range is exactly `range J`.
`inducedMap_injective` proves that equal selected values have equal source labels.
`imageOccurrenceEquivPairs` is an actual equivalence from `A` to the subtype of
matched pairs `(i,j)`. This retains intermediate multiplicities even when several
bars have equal endpoint values. The construction also works with empty occurrence
sets and on the empty chain: no stage or unmatched output value is chosen.

## Endpoints and specializations

For a matched source interval `I`, target interval `K` and their intermediate
image interval `H`, the epi and mono properties give

```text
birth(H) = birth(I),    death(H) = death(K),
birth(K) ≤ birth(I) < death(K) ≤ death(I).
```

The strict middle inequality is the nonempty-interval property of `H`.
`inducedMap_intermediate_endpoints` and `inducedMap_endpoints` expose these facts.
In this half-open convention, `H` therefore has the endpoints of `I ∩ K`.
Terminal target survival forces terminal source survival by the upper bound `death ≤ s`.

For componentwise injective `f`, the map to its image is an isomorphism.
For componentwise surjective `f`, the inclusion from its image is an isomorphism.
Isomorphism invariance identifies the corresponding canonical barcodes. Transport
along that equality preserves the original list indices and both group ordinals;
the mono and epi embeddings across the isomorphic factor are inverse transports.
This proves the specializations of the actual constructed map:

- `inducedMap_of_injective` is `some (monoEmbedding f hf i)` on every source label.
- `inducedMap_of_surjective_iff` is the reverse graph of `epiEmbedding f hf`.
- `inducedMap_id` matches every occurrence to itself.

Consumers include a rank-one endomorphism between modules with two repeated bars,
whose actual image supplies exactly one matched pair; a zero map selecting none;
an overlap map `[1,3) → [0,2)`; duplicate identity labels; terminal bars; and an empty chain.

## Source correspondence and limits

Manifestation, attribution and rights: [BL15-v4](references.md#BL15-v4).
The image-factorization construction specializes
[Bauer–Lesnick v4, §5](https://arxiv.org/html/1311.3681v4#S5), and the qualitative
endpoint result specializes Proposition 5.3 and its proof. The intermediate-occurrence
equivalence implements the matched-pair bijection used in Proposition 5.4's proof;
the full barcode-reconstruction statement of that proposition is not asserted here.
The range-valued functor, domain subtype, Option map and explicit list-label transports
are library representation choices.

Composition laws concern the mono and epi subcategories, as in Proposition 5.7.
The general induced matching need not preserve composition; see Example 5.6.
The distance-specific `OccurrenceMatching` has a separate total essential equivalence,
so it is not the interface for this construction on all finite-chain occurrences.
Quantitative endpoint errors, short-lived kernel/cokernel estimates, constructible
closure, real-grid/shift compatibility, distance-matching conversion and `d_B ≤ d_I`
remain separate results.
