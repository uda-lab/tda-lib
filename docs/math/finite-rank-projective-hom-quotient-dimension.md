# Finite-grid Hom-module and Hom-cokernel dimensions

Let `k` be any field and `S` a finite bounded lattice. Put
`P = PairPoset S`, let `A` be its actual incidence algebra, let `I` be the diagonal ideal, and
write `C = (A/I)ᵐᵒᵖ`. The finite hook generator `L = HookSum` has opposite endomorphism algebra
`T = (End L)ᵐᵒᵖ`, which is identified with `C` by the existing hook-endomorphism algebra
equivalence. The objects of `ModuleCat T` and `ModuleCat C` are left modules, encoding the actual
right-module convention. Write `D(P) = maxComplementCard (S := P)`.

For a persistence module `M`, let `H(M) = homFunctor.obj M` be the actual natural-transformation
module from `L`, and let `K(M)` be the actual categorical cokernel of `H` applied to the
two-injective differential of `M`. If `M` is pointwise finite-dimensional, the library proves
that the canonical restricted-field dimension of `K(M)` is finite and
`HasProjectiveDimensionLE K(M) (D(P))`. The bound uses the actual quotient-module action through
the algebra equivalence and the existing diagonal-quotient projective-dimension theorem. The
scalar restriction and its comparison with the natural Hom-space action are constructed with
explicit identity-on-vectors linear equivalences; neither compatible scalar actions nor a
projective-dimension estimate is an input.

For an actual coordinate grid `G : CoordinateGrid n` with nonempty factors and `n ≥ 1`, a
pointwise finite-dimensional `M : PModule k G.Point` satisfies
`HasProjectiveDimensionLE K(M) (2*n)` and
`HasProjectiveDimensionLE (H(M)) (2*n-2)`. Every supplied certified minimal finite-rank-projective
resolution of `M` has zero `termAt j` for `j > 2*n-2`. This is a highest-nonzero-degree statement,
so adding terminal zero terms does not affect it; no bound on the stored `length` field is claimed.
The bounds hold over arbitrary fields and do not require a finite coefficient field or a
finite-dimensionality premise beyond pointwise finite-dimensionality of `M`.

These results are the ordinary ambient projective dimensions of the actual modules. They do not
establish the real-coordinate transfer or the final stability result, and they do not claim a
sharp bound for arbitrary grids. The grid count used here is the existing finite-grid
complement-cardinality bound.

The source context is the upper-bound argument of Theorem 5.16 and the upper-bound consequence of
Proposition 5.17 in [BOOS24-v3](references.md#BOOS24-v3), together with Lemma 5.11's Hom and
resolution comparison. The library reuses its actual two-injective rows and minimal-resolution
comparison, proves finite-dimensionality and quotient transport for the actual Hom cokernel, and
specializes the resulting bounds to finite coordinate grids. The real-coordinate transfer is a
separate result.
