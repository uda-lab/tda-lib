# Actual simplicial homology and persistence

`TDA.Simplicial.simplicialChainComplex` is the ordinary, unaugmented chain
complex on the actual nonempty faces of a `PreAbstractSimplicialComplex` in one
linearly ordered vertex type. Its incoming differential at degree `n` is the
signed deletion boundary `boundary K R n : C_(n+1) → C_n`; its outgoing
degree-zero differential is zero. Coefficients form an arbitrary, possibly
noncommutative ring, and chains are left modules.

`simplicialHomology K R n` is the homology of that chain complex.
`simplicialCycles` is the kernel of its degree-`n` outgoing map, and
`simplicialBoundaries` is the range of the incoming map **inside** that kernel.
Thus the concrete quotient is `Z_n / B_n`. The pre-existing
`homologyKernelQuotient` identifies this quotient with categorical homology.
An inclusion of subcomplexes in the same ambient order sends an actual face
chain to the identical face chain in the larger complex. The resulting cycle
map preserves boundaries and yields `simplicialQuotientIncl` through
`Submodule.mapQ`. The naturality theorem identifies this map with the map on
homology induced by `simplicialChainIncl`.

The short-complex source for this construction is pinned mathlib's
[`HomologicalComplex.sc` and `homologyMap`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean),
[`moduleCatToCycles` and `moduleCatHomologyIso`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean),
[`LeftHomologyMapData.homologyMap_comm`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Homology/ShortComplex/Homology.lean),
[`LeftHomologyData.ofZeros`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean),
and [`Submodule.mapQ`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Quotient/Basic.lean).
The imported [actual chain inclusion](../../TDA/Simplicial/Inclusion.lean)
provides the signed boundary square. No separate generic homology foundation
is introduced.

The bottom complex has zero actual face chains. A singleton complex has one
degree-zero face and no edges. Applying `LeftHomologyData.ofZeros` to their
actual degree-zero short complexes gives zero bottom homology and a
cross-universe linear equivalence from singleton H₀ to `R`. The equivalence
uses the coefficient of the unique vertex, so the vertex class of coefficient
`a` maps to `a`. Nonzero claims require `Nontrivial R`.

For a preorder-indexed simplicial filtration, monotonicity supplies a
same-ambient inclusion at every arrow. `simplicialHomologyPModule` uses the
resulting homology map in the forward direction. This construction makes no
barcode, rank, finite-dimensionality, reduced-homology, or arbitrary vertex-map
claim.
