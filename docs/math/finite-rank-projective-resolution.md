# Euler formula for finite rank-exact resolutions

For a persistence module `M` over a field `k` and indices `a ≤ b`, write
`r_M(a,b)` for the dimension of the image of its structure map `M(a → b)`.
Each row below is pointwise short exact, has a pointwise finite-dimensional
middle term, and satisfies rank additivity across the row for every such pair.

Suppose a finite indexed family of actual rows is supplied:

```text
0 → K_(i+1) → Q_i → K_i → 0,  for i : Fin m,
```

with every row rank exact, `K_0` isomorphic to `M`, and the last kernel
`K_m` isomorphic to zero. Then, for every `a ≤ b`,

```text
r_M(a,b) = ∑ i : Fin m, (-1)^i r_(Q_i)(a,b),
```

where the sum is in the integers. For each row, rank exactness gives
`r_(Q_i) = r_(K_(i+1)) + r_(K_i)`. Multiplying by `(-1)^i` and summing
cancels every intermediate kernel rank. The endpoint terms are `r_M` and zero.
The sum is indexed by occurrences, so equal modules at different indices are
counted separately.

The exported theorem `FiniteRankExactResolution.rank_eq_alternating_sum` proves
this row-only identity for any preorder. The projective-resolution package adds
the lifting property of each `Q_i` and exposes the same formula as
`FiniteRankProjectiveResolution.rank_eq_alternating_sum`.

When `m = 0`, the endpoint isomorphisms identify `M` with zero, and the empty
sum is zero. A one-term example uses a nonzero principal-upset hook as its
projective term. A two-term contractible resolution of zero uses the same
nonzero hook at both indices; its two ranks cancel.

The row-by-row identity is polymorphic over any preorder and needs only the
actual rank-exact rows and endpoint isomorphisms. Projectivity is recorded by
the projective-resolution package, but the telescope does not use it. The
existing `IsRankProjective` interface is defined for partial-order index types
in universe zero, so the named projective-resolution package uses that scope.

This statement concerns a supplied finite family of rows. It does not assert
that every finitely presented module has such a resolution, or that a supplied
resolution is minimal, unique, or of a bounded length. It makes no barcode
decomposition or stability claim. The source describes the rank invariant and
rank exactness in [§1.2 and §2.14 of the paper], and Theorem 2.7 gives finite
minimal rank-projective resolutions in its stated categories. The Lean identity
is the finite telescoping consequence of the row additivity equation.

Separately, `FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_of_pfd_finitePoset`
constructs a finite rank-projective resolution on a finite poset and certifies
each actual kernel-row quotient as a projective cover. Its input is a
pointwise finite-dimensional module on that finite poset; it does not certify
minimality of the real-coordinate resolution obtained from a finite
presentation by left Kan extension.

[§1.2 and §2.14 of the paper]: https://arxiv.org/html/2208.00300v3
