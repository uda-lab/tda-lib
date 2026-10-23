# Real induced occurrence matchings

A morphism between finite-constructible real persistence modules gives
an occurrence matching with exact real endpoint and long-bar bounds when its
kernel and cokernel have zero transitions at the specified parameters.
The construction retains multiplicities and essential tails. An interleaving
supplies these hypotheses for its comparison into the shifted target.

## Modules, defects and occurrences

Fix a field `k : Type u` and modules `M N : PModule.{u,0,u} k ℝ`
constructible on a common finite increasing grid `c : Fin n ↪o ℝ`.
Assume finite dimensionality only at the original critical fibers. Write
`D_M=moduleDiagram c M` and `D_N=moduleDiagram c N` for their critical
rank-barcode diagrams. The [constructible convention](constructible-modules.md)
is a zero left tail, left-closed/right-open finite strata and a constant final
tail. A terminal index death n represents real death `⊤`.

For `f : M → N` and finite `δK δC : ℝ≥0`, assume the transition
of `kernel f` across δK and of `cokernel f` across δC is zero.
The [sampling comparison](constructible-defects-sampling.md) derives shortness
of the sampled finite defects. No chosen decomposition, matching or
endpoint estimate is supplied.

A diagram is a multiset. An occurrence label contains both an endpoint value
and an index among its copies. Finite occurrence labels and essential birth
labels form a disjoint sum. An `OccurrenceMatching` consists of a partial
injection on finite labels and a total equivalence on essential labels.

## The induced map on real labels

`RealBarcode.indexOccurrenceEquiv` identifies finite rank-barcode list labels
with the finite/essential sum of the real endpoint diagram. Equality of their
value multisets proves a value-preserving equivalence; equal endpoint values
retain distinct labels. `FiniteBarcode.RealInduced.sumMap` conjugates the
[finite induced partial injection](finite-induced-matching.md) by these
equivalences. Its selected-pair theorem and injectivity refer to that same map.

Let source `[b,d)` be selected with target `[b′,d′)`. For finite deaths,
`sumMap_bounds` proves

\[
b'\le b\le b'+\delta_C,\qquad
b<d'\le d\le d'+\delta_K.
\]

The [finite quantitative bounds](finite-quantitative-induced-matching.md)
place each upper endpoint below the critical stage selected by the rounded
translation. That stage has real value at most the original value plus δ.
Monotonicity of c therefore gives the displayed real bounds directly, even
on an irregular grid. No mesh-size term is added. The argument also works
at δ=0 and when the rounded translation fixes or identifies indices.

The finite death upper bound forces the source death to be finite whenever
the selected target death is finite. The opposite classification is excluded
by the qualitative death order. Thus selected finite and essential labels
cannot cross. An unmatched essential source would have `⊤≤b+δK`, contradicting
its finite right side; the unmatched-target estimate gives the analogous
contradiction for essential targets. Partial injectivity then makes the
selected essential map a total equivalence, including every repeated birth.

`FiniteBarcode.RealInduced.matching` splits this map into the required
finite partial injection and essential equivalence. Its finite and essential
pair theorems retain the exact selected-pair relation. The theorem
`matching_bounds` derives `RealMatchingBounds δK δC`, which collects the
endpoint conclusions and the following unmatched-length bounds:

\[
d-b\le\delta_K\quad\text{for every unmatched finite source},\qquad
d'-b'\le\delta_C\quad\text{for every unmatched finite target}.
\]

Consequently every source longer than δK and every target longer than δC has
exactly one partner. Equality is the short case: a threshold-equality bar may
be matched or unmatched. Essential occurrences are always covered in both
directions.

## Constructible morphisms and interleavings

`FiniteConstructible.inducedOccurrenceMatching` constructs the matching of
`D_M` with `D_N` from the real defect hypotheses above.
`inducedOccurrenceMatching_bounds` derives every field of its bounds object.
Only critical-fiber finite dimensionality is supplied; finite sampled
shortness is obtained from constructibility and defect annihilation.

For an ε-interleaving of M on c and N on another grid d,
`interleaving_shifted_induced_matching` constructs the common grid of c and
`shiftGrid ε d`. The interleaving equations give kernel and cokernel
`2ε`-annihilation for `M → SεN`. Refinement derives finiteness at the new
observations. The [shift-diagram formula](constructible-shift-diagrams.md)
identifies the resulting target with `translateDiagram D_N (−ε)`. The output
is a matching into that shifted diagram with `RealMatchingBounds
(ε+ε) (ε+ε)`, including its essential equivalence and strict long-bar coverage.
No common-grid, new-fiber-finiteness, shortness or matching witness is an input.

The [finite-constructible isometry construction](constructible-isometry.md)
applies the +ε target inverse and proves every finite, essential and diagonal
cost contribution is at most ε. It then takes the interleaving-parameter
infimum and combines the reverse bound into equality. The shifted-target
bounds here are its derived input, with no extra matching or cost hypothesis
on the original interleaving.

## Concrete boundary cases

On the grid `[0,1,3,4]`, a genuine overlap map from `[1,4)` to `[0,3)`
has nonzero kernel and cokernel and attains both displacement-one
upper bounds. The gap of length two adds no error. A map erasing
`[0,1)` leaves its sole real source unmatched at threshold one. Identity
maps retain threshold-short bars, two distinct copies of `[0,3)` and two
essential copies born at one. They also give unique strict-long coverage,
essential coverage at every finite threshold and the parameter-zero result.
The empty grid constructs the empty matching without choosing a stage.

The zero-comparison one-interleaving on `[0,2)` derives a matching into
its shifted target with both bounds equal to two. These consumers are in
`RealInducedMatchingExamples`, `FiniteInducedTranslationExamples` and
`ConstructibleDefectExamples`.

## Source correspondence and limits

[Bauer–Lesnick v4](https://arxiv.org/html/1311.3681v4), §§2.1–2.3 and §3.1,
supplies the functor, multiset-occurrence, endpoint-decoration and shift
conventions. Formal Theorem 6.1(ii) controls births and long targets from
cokernel triviality; (iii) controls deaths and long sources from kernel
triviality. Their combined finite, half-open specialization is proved here.
The finite quantitative proof uses a direct quotient-surjection argument
rather than the source's duality route. The source omits Lemma 6.2's proof;
no verification of that omitted argument is claimed.

In the proof of Theorem 6.1(ii), both the v4 HTML and PDF define a submodule
of N using an image labelled with M, then use the transition of N in the
following cokernel argument. The formal theorem and the target maps
of N determine the specialization used here. This notation inconsistency
does not alter the library's hypotheses or endpoint inequalities.

Lemma 6.3 supplies double-shift defect annihilation. The occurrence
correspondence immediately before Theorem 6.4 adds ε back to shifted
endpoints, and its proof converts the induced bounds to an ε-matching.
The shifted-target part is established here; the linked isometry theorem
completes its return and cost argument on the finite-constructible domain.
Finite-grid sampling, real occurrence relabelling and the derived essential
equivalence are library constructions implementing the specialization.
General decorated intervals, infinite or q-tame decompositions and full
isometry are outside this result. Source and rights metadata are recorded
in [BL15-v4](references.md#BL15-v4).
