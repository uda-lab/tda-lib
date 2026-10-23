# Persistence matrix reduction primitives

Consulted manifestations, attribution and rights: [Bauer21-v2](references.md#Bauer21-v2), [ZC04](references.md#ZC04), [mathlib-0df444a](references.md#mathlib-0df444a).

## Finite column pivots and a cancellation step

For a coefficient vector `c : Fin m → k`, `columnPivot c` is the greatest index with nonzero
coefficient, represented by `some p`; the zero vector has pivot `none`. This option-valued
representation separates a genuine pivot at zero-based row `0` from the zero-vector sentinel.
`pivotHeight none = 0` and `pivotHeight (some p) = p.val + 1`, so every present pivot has positive
height.

This records the maximum-nonzero-row convention in §3.1 of Bauer's *Ripser: efficient computation
of Vietoris–Rips persistence barcodes*. Bauer's paper uses `0` as its zero-column sentinel; this
library uses `none` so that row `0` remains an ordinary pivot. The source restricts coefficients
to prime fields for its persistence algorithm. The vector cancellation lemmas here use an
arbitrary field and establish only the algebraic operation, not that algorithm.

If `a` and `b` have a common pivot `p`, then `a p ≠ 0` and both vectors vanish above `p`. The
operation

```lean
cancelColumn a b p = b - (b p / a p) • a
```

therefore vanishes at `p` and above `p`. Its `pivotHeight` is strictly less than that of `b`,
including the case where the result is zero. The proof does not claim that a nonzero result has
pivot exactly `p - 1`.

The matrix bridge uses right multiplication: `M * Matrix.transvection i j c` adds `c` times source
column `i` to target column `j` and fixes every other column. With `i < j` and a common pivot `p`,
the coefficient `-(M p j / M p i)` realizes `cancelColumn` in the target column and strictly
decreases its pivot height. This is the elementary column operation used in matrix reduction;
the result here does not construct a reduction loop, filtered chain complex, homology, or barcode.

The executable acceptance fixtures are private, so they are not part of public theorem-pin
coverage. `PivotExamples.lean` therefore runs `#print axioms` separately for all 24 private fixture
theorems and the private `F₂` prime-field instance witness. The standalone Lean run on 2026-10-09
reported only `{propext, Classical.choice, Quot.sound}` for each of those 25 declarations. Finite
pivot checks use kernel-checked `decide`; the rational and `F₂` vector cancellation equalities use
coordinate extensionality and `norm_num`. None uses `native_decide`, `Lean.ofReduceBool`, or
`sorryAx`.

Zomorodian and Carlsson's §4 describes field-based column operations for persistence, including
elimination of entries at pivot rows. Its broader graded-basis construction is not part of this
vector API. The matrix identities are supported by mathlib's pinned `Matrix.transvection` lemmas
`mul_transvection_apply_same` and `mul_transvection_apply_of_ne`.

Sources: [Bauer, *Ripser*, §3.1](https://doi.org/10.1007/s41468-021-00071-5); [Zomorodian and
Carlsson, *Computing Persistent Homology*, §4](https://geometry.stanford.edu/paper/zc-cph-04/zc-cph-04.pdf);
[pinned mathlib transvection source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Transvection.lean).

## Prefix spans under an earlier-column operation

For a square matrix `M : Matrix (Fin m) (Fin m) k`, `prefixSpan M t` is the submodule spanned by
the columns `M.col q` for which `q.val < t`. The parameter `t` is a prefix length: it may be zero,
equal to `m`, or larger than `m`. Thus every column occurs once `m ≤ t`, while the empty prefix
spans only zero. The ambient submodule is the span of the columns of `M`, not necessarily the
whole vector space.

`col_mem_prefixSpan`, `prefixSpan_zero`, `prefixSpan_mono`, and `prefixSpan_eq_full` establish the
basic prefix properties. For `i < j`, `prefixSpan_mul_transvection` proves that right
multiplication by `Matrix.transvection i j c` preserves every prefix for any scalar `c`. If the
target column lies in a prefix, its earlier source lies there too, and the generator function is
an update at the target index. The proof specializes mathlib's pinned
`Submodule.span_range_update_add_smul` to those prefix indices. If the target is outside the
prefix, all included generators are unchanged. No `[DecidableEq k]` or nonzero coefficient
hypothesis is required. `prefixSpan_cancel` specializes this preservation result to the existing
`-(M p j / M p i)` cancellation coefficient; it does not claim that an arbitrary row is a pivot.
pivot decrease remains the separate `pivotHeight_mul_transvection_lt` theorem with its
common-pivot hypotheses.

`PrefixSpanExamples.lean` checks the empty `Fin 0` matrix and zero matrices, a rational
three-column operation with coefficient `-3/2` at prefix lengths 0 through 4, a lower-pivot
rational example, and an `F₂` example. It also checks that reversing the column order can change
the first prefix span. These are finite illustrations of the universal theorem; they do not
package an elimination algorithm or a persistence computation.

## Finite earlier-column traces

`EarlierColumnOp m k` is the existing matrix transvection together with the proof that its source
index is strictly earlier than its target. A client supplies a finite list of these operations;
`replay` folds that list by right multiplication in chronological order, and `traceChange` is the
corresponding left-to-right product. The bridge theorem states `replay M ops = M * traceChange
ops`. Its append laws keep the same order, so a trace `[a, b]` acts as `M * T(a) * T(b)`.

`prefixSpan_replay` proves that every natural-number prefix span is preserved by every supplied
trace. The statement includes zero, in-range, and oversized prefix lengths and requires no
decidable equality on the coefficient field. `prefixSpan_mul_traceChange` gives the equivalent
product-form result. Applying the replay theorem to `ops.take n` preserves every prefix after any
finite initial segment. The API accepts arbitrary operation lists; it neither chooses operations
nor claims that every trace is a reduction run or that pivots decrease along it.

`TraceExamples.lean` checks the executable chronological product over `ℚ` and `ZMod 2`, including
an order-sensitive two-step example, repeated targets, a zero coefficient, empty dimensions, and
zero input. These fixtures illustrate the finite algebra only; they do not construct a reducer,
inverse certificate, grading, or barcode.

## A graded trace certificate and explicit inverse

`inverseTrace` reverses the supplied chronological operation list and negates each transvection
coefficient. Its matrix `traceChangeInv` is an explicit right-product, with both
`traceChange ops * traceChangeInv ops = 1` and the opposite product equal to one. Reversal matters:
for operations `(0,1,2)` followed by `(1,2,3)` over `ℚ`, the change matrix has rows
`[[1,2,6],[0,1,3],[0,0,1]]`, while the inverse has
`[[1,-2,0],[0,1,-3],[0,0,1]]`. Negating without reversing leaves a nonzero `(0,2)` entry.
The same distinction occurs over `ZMod 2`, where negation itself changes no coefficient.

`TraceChangeCertificate degree V W` records the two inverse laws, upper triangularity and
diagonal one for both matrices, and zero entries whenever their row and column homological
degrees differ. `traceChange_certificate` constructs it for a supplied trace whose every
operation joins columns of equal homological degree. This degree is simplex dimension, not
filtration time, pivot height, or the polynomial grading in Zomorodian–Carlsson. No ordering of
columns by degree is required. The equal-degree premise is sufficient even for zero-scalar
operations; it is not claimed necessary for every individual trace.

`LowersDegree degree M` says that each nonzero entry at row `r`, column `c` satisfies
`degree c = degree r + 1`. This entry-support property is preserved by replaying a
degree-respecting trace. If two columns of such a matrix share a nonzero `columnPivot` row,
`degree_eq_of_common_pivot` derives equality of their column degrees. It therefore supplies
the grading premise for a future pivot-chosen operation when its separate earlier-index
condition is met. The mixed-degree fixture uses degrees `[0,1,1]`, a pivot at row zero,
coefficients `2` and `3`, and cancellation coefficient `-3/2`. A valid earlier operation
across degrees `[0,1]` shows why the grading premise cannot be omitted.

Together with the existing `replay_eq_mul_traceChange` and `prefixSpan_replay`, the certificate
gives `R = D * V`, an explicit undo trace, and preservation of every natural-number prefix,
including zero and oversized prefixes. These are facts about a supplied trace and arbitrary
input matrix. They assert neither that the input is a chain differential nor that the output is
reduced, square-zero, or a barcode. In particular, `R = D * V` does not imply `R² = 0`.

The certificate follows elementary transvection identities from pinned mathlib and the
right-column convention already used here. Bauer's *Ripser* §3.1 motivates the `R = D * V`
change-of-basis goal; Zomorodian–Carlsson §4 describes field-based elimination. Neither source
is used to claim a completed persistence reduction or to identify filtration grading with
homological dimension. `TraceCertificateExamples.lean` checks empty dimensions, noncommuting
`ℚ` and `ZMod 2` traces, mixed degrees and a row-zero pivot, the omitted-degree counterexample,
zero scalars, repeated targets, and inverse-prefix integration.

## Chronological all-column reduction

`matrixReductionTrace M` visits `List.finRange m` in order. At each index it runs the existing
`columnReductionTrace` on the matrix obtained by replaying all previous blocks, then appends
that block. Thus `matrixReductionTrace_step_spec` describes an occurrence using precisely the
preceding trace: the two current columns share a present pivot, the source is the least earlier
matching column, the coefficient is the negative ratio at that row, and the operation strictly
lowers the target pivot height. The source is earlier by the `EarlierColumnOp` type. An empty
block still advances the traversal; `m = 0` yields an empty trace.

The prefix induction keeps four facts after `t` targets: emitted targets lie below `t`, future
columns equal the input columns, completed present pivots are pairwise unique, and the trace
length is bounded by the sum of the input pivot heights of the first `t` columns. Consequently
`matrixReductionTrace_pivots_distinct` proves global pivot uniqueness and
`matrixReductionTrace_length_le` bounds emitted operations by the sum of **original** column
heights. A missing pivot has height zero and a present row `p` has height `p.val + 1`. No
initially reduced prefix, square-zero, grading, or triangularity is assumed. The algorithm is
executable over any field with decidable equality and chooses no extra data.

When `LowersDegree degree M` holds, `matrixReductionTrace_respectsDegree` proves equal degrees
at every emitted source and target. `matrixReductionTrace_graded_certificate` also proves
lowering after replay and provides the established graded change certificate. The ungraded
`matrixReductionTrace_certificate` instantiates `R = M * V`, both explicit inverse laws,
upper-unitriangularity of `V` and `W`, undo replay, and preservation of every column prefix
span. These are applications of the existing trace algebra, not a second certificate type.

This formalization matches the chronological field-column elimination in Bauer, *Ripser*,
§3.1/Algorithm 1, and the field cancellation step of Zomorodian–Carlsson, §§4.1–4.2. The
paper's pivot index `0` also denotes a zero column; Lean uses `Option (Fin m)` so row zero
remains a real pivot. The Lean result is restricted to a finite square matrix and says only
that equal present pivots
cannot remain in two columns. It does not claim a canonical form, persistence pairing,
barcode, simplicial origin, or square-zero output. `MatrixReductionExamples.lean` checks
empty, zero and identity matrices; row-zero ratios; evolving sources and product order;
unreduced initial prefixes; repeated cancellation; characteristic two; nonconstant grading;
a square-zero input whose reduced output is not square-zero; and a raw triangle matrix.

## Filtered normal form of a square-zero boundary

`FilteredNormalForm.lean` starts with a finite boundary matrix `D` over a field, with `D² = 0`,
strictly upper-triangular support and entries lowering homological degree by exactly one. In
particular, a degree-zero column has zero boundary; the differential is unaugmented. The
reducer supplies `R = D * V`, the inverse graded upper-unitriangular change `W`, and distinct
pivots of nonzero `R` columns. The proof does **not** use `R` as the differential or assume
`R² = 0`. These are the right-column and filtration conventions of the reduction above,
with the graded basis interpretation of Zomorodian–Carlsson, §4.

The pivot set `I`, nonzero-column or death set `J`, and remaining zero-column or essential
set `E` partition the indices. Distinct greatest rows make the nonzero `R` columns linearly
independent. For a death column `j` with pivot `i` and coefficient `c = R i j`, put
`a = W * R.col j`. Square-zero gives `R * a = 0`, so independence forces `a` to vanish at
every death index. Upper unitriangularity of `W` preserves the highest coordinate of
`R.col j`: `a i = c ≠ 0`. Thus `i` cannot be a death index and `R.col i = 0`. This is the
step that turns a reduced-column certificate into a valid cycle/death pairing.

The fixed basis has `b_i = R.col j / c` at each pivot `i` and `b_i = V.col i` otherwise.
Its matrix `B` and inverse are graded, upper unitriangular and preserve every prefix;
`D b_j = c b_i` for a death index, while pivot and essential columns are cycles. The
normal differential is conjugate to the **original** `D`. For every prefix length
`t = 0,…,m`, the resulting original-boundary homology quotient is identified with the
coordinates still alive at that stage, and those identifications commute with inclusion
maps. A paired index `(i,j)` contributes degree `deg i` on stages `i+1,…,j`; an essential
index `i` contributes on stages `i+1,…,m`. On `Fin (m+1)` these are the half-open intervals
`[i+1,j+1)` and `[i+1,m+1)`. The endpoint `m+1` is a finite observation sentinel, not
infinity or a constant-tail extension.

For `0 ≤ s ≤ t ≤ m`, the rank of the original-homology map from prefix `s` to prefix `t`
is the number of death columns `j` with `deg i(j) = p`, `i(j) < s`, and `t ≤ j`, plus the
number of essential indices `i` with `deg i = p` and `i < s`. Indices count occurrences,
including repeated interval endpoints. `matrixReductionTrace_normalForm_input` and
`matrixReductionTrace_originalHomologyMap_rank_formula` discharge the generic premises for
the existing all-column reducer. `FilteredNormalFormExamples.lean` checks empty and
mixed-degree zero boundaries, arbitrary nonzero pair coefficients, interleaved pairs and
an essential cycle, map death, a nontrivial change of basis, and an input with
`D² = 0` but `R² ≠ 0`. The matrix theorem itself does not assume a simplicial origin.
`SimplicialAdapter` constructs the signed square boundary from faces,
and `SimplicialAdapterNaturality` identifies its prefix-homology maps with
simplicial inclusions.

Sources and conventions: [Zomorodian–Carlsson, *Computing Persistent Homology*, §4](https://geometry.stanford.edu/paper/zc-cph-04/zc-cph-04.pdf)
for graded filtered basis reduction; [Bauer, *Ripser*, §3.1](https://doi.org/10.1007/s41468-021-00071-5)
for greatest-row pivot column reduction; and the [finite interval convention](finite-interval-rank.md)
for the library's half-open finite-stage modules. The Lean statements above derive their
normal form and homology comparison directly from the matrix certificate.

## Homology and interval realization

`facePrefixHomology_rank` transports the original-boundary quotient maps
through natural linear equivalences to simplicial homology. The
commuting square identifies their ranges, so its rank is the rank of the
inclusion map, not a declared count. `facePivotBarcode_rank` proves
the same count for the interval realization. Equality of every structure-map
rank then gives `facePivotBarcode_eq_facePrefixBarcode`.

`nonempty_facePrefixHomologyIsoPivotBarcode` combines that equality with
the constructed finite interval decomposition. Its conclusion is a genuine
natural isomorphism between prefix homology and the reducer's
interval realization. The decomposition is constructed before rank
classification is used; equal dimensions alone are never used to infer
an isomorphism. This existence theorem involves classical choices and is
separate from the executable F₂/integer path.

The general occurrence API lives in `PivotBarcode`: `mem_pivotIndexPairs_iff`
requires distinct pivots and identifies row/death-column pairs,
`mem_pivotEssentialIndices_iff` identifies unpaired zero columns, and the
two `*_nodup` lemmas distinguish index occurrences. `pivotBarcode_endpoints`
records the face-index to stage-endpoint shift. Distinct index occurrences
may still evaluate to identical grade intervals, whose multiplicities are
preserved. These library lemmas have no dependency on acceptance fixtures.

[Bauer, §§2–3, Propositions 2.1 and 3.1](https://arxiv.org/pdf/1908.02518v2)
gives simplexwise grade reindexing and the filtered cycle/death basis,
including essential indices. His coefficient convention is a prime field.
The library's graded certificate and homology comparison recover
that finite specialization; their arbitrary-field scope is supported by
[Zomorodian–Carlsson, §§3–4](https://geometry.stanford.edu/paper/zc-cph-04/zc-cph-04.pdf).
The elementary finite splitting proof and its explicit natural-isomorphism
interface are library proof constructions, rather than an implementation
of the source's polynomial-module classification.
