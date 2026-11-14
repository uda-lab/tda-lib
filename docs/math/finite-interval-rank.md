# Finite interval modules and rank recovery

Consulted manifestations, attribution and rights: [CCDS14-v1](references.md#CCDS14-v1).

The discrete interval module in Chazal, Crawley-Boevey, and de Silva, §1.1, assigns `k` to
indices in a closed interval `[p,q]` and zero elsewhere, with identity maps between active
stages. Their four-rank formula recovers the multiplicity of each interval from the ranks of
the structure maps. For this library's finite index set `Fin N`, the Lean interval `[b,d)` is
the same convention with `p = b` and `q = d - 1`; thus `d = N` means the last observed stage
`N - 1` is alive. It does not encode an infinite lifetime.

For an explicitly supplied finite multiset `B` of these intervals, the range dimension of the
map `M_B(i → j)` is the number of occurrences with `b ≤ i` and `j < d`. Extending this
table to integers with the left sentinel `r(-1,j) = 0` and right sentinel `r(i,N) = 0`, the
finite difference is

```text
multiplicity_B(b,d) = r(b,d-1) - r(b-1,d-1) - r(b,d) + r(b-1,d).
```

The predecessor is taken in `ℤ`, so `b = 0` uses `-1` without truncated natural subtraction.
The extension is auxiliary outside valid ordered index pairs; there it is not a structure-map
rank. The inversion proves uniqueness of the multiset for these constructed realizations. It
does not prove an interval decomposition for arbitrary persistence modules.

## API map

- **Intervals and realizations:** Import `TDA.Persistence.FiniteBarcode` and open namespace
  `TDA.Persistence`. `FiniteInterval N` stores natural endpoints `birth < death ≤ N`;
  `intervalModule` realizes one interval ([`Interval.lean`](../../TDA/Persistence/Interval.lean)).
  [`barcodeModule`](../../TDA/Persistence/FiniteBarcode.lean) realizes a supplied finite multiset
  `B` over field `k` with one coordinate per occurrence, so repeated intervals remain distinct.
  Supply `(k := k)` when the coefficient field cannot be inferred from `B` alone.
- **Ranks and multiplicities:** For `i j : Fin N` with `i ≤ j`, `rank_barcodeMap` gives the
  structure-map rank of `barcodeModule (k := k) B` as the count of intervals with
  `birth ≤ i.val` and `j.val < death`.
  `barcodeRankInteger (k := k) B` extends this table to integer pairs and is zero unless
  `0 ≤ i ≤ j < (N : ℤ)`; outside this range it is not a structure-map rank.
  `barcodeMultiplicity B b d` counts in `ℕ`. For natural endpoints `b < d ≤ N`,
  `multiplicity_eq_rank_difference` casts that count to `ℤ` and states the four-rank identity in
  `ℤ`, not truncated natural subtraction.
- **Inversion and module decomposition:** `barcodeRankInteger_injective` recovers equality of
  supplied multisets when their extended tables agree at every integer pair. It concerns explicit
  barcode realizations and does not construct a decomposition of an arbitrary module. For the
  separate existence theorem for finite-chain modules over a field with pointwise finite-dimensional
  fibers, see [finite interval decomposition](finite-interval-decomposition.md#using-the-existence-result).

Source: [Chazal–Crawley-Boevey–de Silva, *The observable structure of persistence modules*,
§1.1, p.1](https://arxiv.org/pdf/1405.5644v1).
