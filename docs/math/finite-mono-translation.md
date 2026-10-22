# Quantitative finite mono matchings under monotone translations

## Modules, intervals and translations

Fix a field `k : Type u` and pointwise finite-dimensional modules
`M N : PModule.{u,0,u} k (Fin s)`. The field and module carriers share their universe.
A natural transformation `f : M ⟶ N` has injective components.
Its [canonical mono embedding](finite-mono-matching.md) pairs occurrence labels in
the two rank barcodes, preserving death and the ordinal at that death.
Repeated interval values keep their original list labels.

Intervals use `[birth,death)` with `birth < death ≤ s`.
`FiniteInterval.birthStage` packages the birth as an index in `Fin s`.
Let `theta : Fin s →o Fin s` be monotone and suppose `hTheta : ∀ i, i ≤ theta i`.
It may identify stages and need not advance a fixed number of indices.
Call a target interval `[b,d)` long when `(theta b).val < d`.
Equality belongs to the short case because the interval excludes its death.

## Shortness of the cokernel

`finiteCokernel f` is mathlib's categorical cokernel in the functor category.
`finiteCokernelFiberIso` identifies its fiber at `i` with
`N_i / range(f_i)`. The identification sends the cokernel projection to
the quotient map, and target finite dimensionality gives cokernel finite dimensionality.
The structure maps are those induced by the original natural transformation.

`TranslationTrivial theta hTheta K` says that every structure map
`K(i → theta i)` is zero. In particular, it imposes no barcode or matching condition.
`cokernel_translationTrivial_iff` proves the equivalent image criterion:

```text
TranslationTrivial theta hTheta (finiteCokernel f)
  ↔ ∀ i, range N(i → theta i) ≤ range f_(theta i).
```

The equivalence uses the natural cokernel projection, its component epimorphisms,
and the concrete range-quotient identification. Thus the image criterion is a
consequence of the shortness hypothesis.

## Shifted prefix counts

Write `D_M(b,d)` for `deathPrefixCount (rankBarcode M) b d`: the number of
occurrences born by `b` and dying exactly at `d`. Cokernel shortness gives

```text
D_N(b,d) ≤ D_M(theta b,d),    (theta b).val < d ≤ s.
```

`deathPrefixCount_le_translated_of_cokernelTrivial` proves this inequality.
For `d < s`, the counts are dimensions of the image/kernel intersections
at `d−1`. A target vector born by `b` lifts at `theta b` by the image criterion.
Transporting the lift to `d−1` produces the target vector by naturality.
Its image at `d` is zero; injectivity of `f_d` forces the source lift to die there too.
This embeds the target subspace in the image of the translated source subspace,
so dimension monotonicity gives the count comparison.

For `d=s`, the count is the final structure-map image. The same vector lift
compares these images without forming a stage `s` or a kernel there.
The inequalities justify every predecessor and finite index.

## Bounds and coverage for the canonical embedding

For a source occurrence `I` and its canonical target `J`, the result is

```text
death(I) = death(J),
birth(J) ≤ birth(I) ≤ theta(birth(J)).
```

`monoEmbedding_birth_bounds_of_cokernelTrivial` supplies both birth bounds.
For long `J`, the shifted prefix comparison and equal ordinals exclude a source
birth after the translated target birth. For short `J`, the upper bound follows
directly from `birth(I) < death(I) = death(J) ≤ theta(birth(J))`.

`monoEmbedding_covers_long_of_cokernelTrivial` gives exactly one source occurrence
for every long target occurrence. Its ordinal lies below the translated source
prefix count and hence below the source death-group cardinality.
`monoEmbedding_unmatched_short_of_cokernelTrivial` states the contrapositive:
every unmatched target is short. Short targets can also be matched.

The consumers use a nonidentity translation identifying stages, a delayed-birth
inclusion attaining the upper bound, a threshold-equality target left unmatched,
duplicate long bars, terminal coverage, the identity translation and an empty chain.
A nonzero quotient at a fixed point fails the shortness condition.

## Terminal observations and later real grids

Terminal death `s` records finite observed survival. It is always long for an
endomap of `Fin s`, so the shortness hypothesis forces terminal target coverage.
No unobserved zero stage is appended. The empty chain forms no stage at all.
The separate constant-tail [real realization](real-barcode-realization.md) is what
interprets a surviving final fiber as an essential tail.

For a later real-grid connection, the intended index at a critical value `c_i`
is the last `c_j` at or below `c_i+epsilon`. This floor convention can fix a stage
when the next critical value is far away. Testing only sample pairs separated by
at least epsilon would miss a nonzero map inside such a cell.
This real-grid transport, refinement and real endpoint estimate remain unformalized.

## Source correspondence and limits

Manifestation, attribution and rights: [BL15-v4](references.md#BL15-v4).
[Bauer–Lesnick v4, §6, Theorem 6.1(ii) and its proof](https://arxiv.org/html/1311.3681v4#S6)
give the additive-real cokernel image criterion, long-target coverage and birth bound.
The proof sandwiches a delayed image inside the image of the morphism and uses
canonical mono composition; its long/short cases motivate the corresponding split here.

The theorem for an arbitrary monotone inflationary finite `theta` is a library extension.
Its direct shifted-prefix dimension proof replaces the delayed-image barcode calculation.
The formal source theorem and the target-image condition in its proof determine the
object types; the inconsistent source symbol in the preceding delayed-image sentence
does not change the target structure map used here.
No full version comparison or general erratum claim is made.
[Kernel/epi estimates and quantitative image-factorization assembly](finite-quantitative-induced-matching.md)
provide the complementary death bounds and long-source coverage. Real-grid
compatibility, conversion to a distance matching and `d_B ≤ d_I` remain separate results.
