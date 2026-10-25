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
rank exactness in [§1.2 and §2.14 of the paper]; the finite telescoping identity
above follows directly from rank additivity in each row.

## Minimal resolutions from real-coordinate finite presentations

For a quotient `π : Q ⟶ K`, the public `IsRankProjectiveCover` certificate
says that `Q` is rank-projective, the actual categorical-kernel row
`kernel.ι π` followed by `π` is rank exact, and every endomorphism
`u : Q ⟶ Q` satisfying `u ≫ π = π` is an isomorphism. In this API, a
`MinimalFiniteRankProjectiveResolution` is a finite rank-projective resolution
for which every actual quotient row carries this certificate.

Let `k` be a field, let `n > 0`, and let
`M : PModule k (Fin n → ℝ)` be originally finitely presented in the
real-coordinate category, in the sense of `GradedFree.FinitelyPresented M`.
Then
`FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution`
proves that an actual `MinimalFiniteRankProjectiveResolution M` exists.

The proof starts from the finite presentation of `M` and reconstructs an
isomorphism from the actual left Kan extension of a pointwise
finite-dimensional module on a finite coordinate grid. The finite-poset
theorem
`FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_of_pfd_finitePoset`
supplies a resolution with the cover certificate on every grid row. The actual
grid left Kan functor preserves rank-projectivity and rank-exactness of the
actual categorical-kernel rows. It is also full and faithful on maps between
its images:
`CoordinateGrid.lanMapPreimage` gives the grid map for a real-coordinate map,
`CoordinateGrid.lan_map_preimage` proves its Lan image is the given map, and
`CoordinateGrid.lan_map_surjective` exposes existence;
`CoordinateGrid.lan_map_injective` gives uniqueness.
Consequently, a quotient-fixed endomorphism of a Lan row lifts to the grid,
where the cover certificate makes it invertible. Lan carries that inverse back
to an inverse on the real-coordinate row. Finally, the resolution and all row
certificates are transported across the reconstruction isomorphism.

This finite-grid Kan transfer is the content of [Theorem 2.7(2), proved in
Appendix A by Botnan, Oppermann, Oudot and Scoccola](https://arxiv.org/html/2208.00300v3).
The only module-specific input to the Lean theorem is the original
finite-presentation predicate; the finite grid and its pointwise
finite-dimensional module are constructed in the proof.

[§1.2 and §2.14 of the paper]: https://arxiv.org/html/2208.00300v3
