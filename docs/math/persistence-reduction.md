# Persistence matrix reduction primitives

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
Actual pivot decrease remains the separate `pivotHeight_mul_transvection_lt` theorem with its
common-pivot hypotheses.

`PrefixSpanExamples.lean` checks the empty `Fin 0` matrix and zero matrices, a rational
three-column operation with coefficient `-3/2` at prefix lengths 0 through 4, a lower-pivot
rational example, and an `F₂` example. It also checks that reversing the column order can change
the first prefix span. These are finite illustrations of the universal theorem; they do not
package an elimination algorithm or a persistence computation.
