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

Source: [Chazal–Crawley-Boevey–de Silva, *The observable structure of persistence modules*,
§1.1, p.1](https://arxiv.org/pdf/1405.5644).
