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

Zomorodian and Carlsson's §4 describes field-based column operations for persistence, including
elimination of entries at pivot rows. Its broader graded-basis construction is not part of this
vector API. The matrix identities are supported by mathlib's pinned `Matrix.transvection` lemmas
`mul_transvection_apply_same` and `mul_transvection_apply_of_ne`.

Sources: [Bauer, *Ripser*, §3.1](https://doi.org/10.1007/s41468-021-00071-5); [Zomorodian and
Carlsson, *Computing Persistent Homology*, §4](https://geometry.stanford.edu/paper/zc-cph-04/zc-cph-04.pdf);
[pinned mathlib transvection source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Transvection.lean).
