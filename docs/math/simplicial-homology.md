# Simplicial homology and persistence

`TDA.Simplicial.simplicialChainComplex` is the ordinary, unaugmented chain
complex on the nonempty faces of a `PreAbstractSimplicialComplex` in one
linearly ordered vertex type. Its incoming differential at degree `n` is the
signed deletion boundary `boundary K R n : C_(n+1) → C_n`; its outgoing
degree-zero differential is zero. Coefficients form an arbitrary, possibly
noncommutative ring, and chains are left modules.

`simplicialHomology K R n` is the homology of that chain complex.
`simplicialCycles` is the kernel of its degree-`n` outgoing map, and
`simplicialBoundaries` is the range of the incoming map **inside** that kernel.
Thus the concrete quotient is `Z_n / B_n`. The pre-existing
`homologyKernelQuotient` identifies this quotient with categorical homology.
An inclusion of subcomplexes in the same ambient order sends a face
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
The imported [chain inclusion](../../TDA/Simplicial/Inclusion.lean)
provides the signed boundary square. No separate generic homology foundation
is introduced.

The bottom complex has zero face chains. A singleton complex has one
degree-zero face and no edges. Applying `LeftHomologyData.ofZeros` to their
degree-zero short complexes gives zero bottom homology and a
cross-universe linear equivalence from singleton H₀ to `R`. The equivalence
uses the coefficient of the unique vertex, so the vertex class of coefficient
`a` maps to `a`. Nonzero claims require `Nontrivial R`.

For a preorder-indexed simplicial filtration, monotonicity supplies a
same-ambient inclusion at every arrow. `simplicialHomologyPModule` uses the
resulting homology map in the forward direction. This construction makes no
barcode, rank, finite-dimensionality, reduced-homology, or arbitrary vertex-map
claim.

## Apex cones are acyclic

`IsApexCone K v` means that `{v}` is a face, inserting `v` into any face keeps
the result in `K`, and `v ≤ w` for every vertex `w` of every face. The last
condition makes the apex minimal in the fixed vertex order. It puts the apex at
enumeration position zero, so every cone face has the sign `(-1)^0` at the
apex. Without minimality the acyclicity result remains true, but the signs
depend on the apex position; that variant is not covered here.

For an apex cone, `IsApexCone.coneOperator` sends a face basis `s` to
`v ∗ s` when `v ∉ s`, and to zero when `v ∈ s`. The proved identities are
`boundary_coneOperator_add`, which gives `∂h + h∂ = id` in positive degree,
and `boundary_coneOperator_zero`, which gives
`∂h = id − ε(·)[v]` in degree zero, where `ε` is the coefficient sum and
`[v]` is the apex face. Consequently `isZero_simplicialHomology_succ` gives
zero homology in every positive degree over every ring, while
`finrank_simplicialHomology_zero` gives degree-zero rank one over a field.

The full complex `⊤` on a finite linearly ordered vertex type is covered by
`isZero_simplicialHomology_top_succ` without a nonemptiness hypothesis, and by
`finrank_simplicialHomology_top_zero` with a nonempty vertex type. This is a
library-proved result; no external source claim is made here.

`TDA.Simplicial.ConeExamples` checks triangle vanishing in degrees one and two
over `ℤ`, degree-zero rank one over `ZMod 2`, and the concrete signed boundary
calculation on the top triangle face. It also records the two non-cone controls
`not_isApexCone_top_one` and `not_isApexCone_bot_zero`.
