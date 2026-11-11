# Weak-pair rank erosion

Let $M,N$ be persistence modules on $\mathbb R^n$ over a field $k$, with
finite-dimensional fibers. The current API permits every $n\in\mathbb N$,
including $n=0$. Write $r_M(a,b)$ for the dimension of the image of the actual
structure map $M(a)\to M(b)$, where $a\le b$ coordinatewise.

## The predicate and distance

For a finite nonnegative radius $\varepsilon$, `RankErosion ε M N` means

$$r_M(a-\varepsilon\mathbf1,b+\varepsilon\mathbf1)\le r_N(a,b),
\qquad
r_N(a-\varepsilon\mathbf1,b+\varepsilon\mathbf1)\le r_M(a,b)
\quad\text{for every }a\le b.$$

These are **weak pairs**: $a=b$ is included, and $r_M(a,a)=\dim_k M(a)$.
The diagonal is significant, not an omitted endpoint convention. When $n=0$,
the grade set has one element and these diagonal tests still compare the fibers;
a convention using only strict pairs would have no tests.

`erosionLower` and `erosionUpper` implement the two shifts.
`rankOfStructureMap_four_point` proves that widening an interval decreases its
rank. This yields `RankErosion.refl` and `RankErosion.mono`; symmetry and
composition are `RankErosion.symm` and `RankErosion.trans`.

`rankErosionDistance` is the extended infimum of the admissible finite radii:

$$d_E(M,N)=\inf\{\varepsilon\ge0:\operatorname{RankErosion}(\varepsilon,M,N)\}.$$

An empty admissible set gives infinity. `rankErosionDistance_self`,
`rankErosionDistance_comm` and `rankErosionDistance_triangle` give the extended
pseudometric laws in the stated finite-dimensional scope. A supplied predicate
witness gives an upper bound through `rankErosionDistance_le_of_erosion`.
The definition uses `Module.finrank`, which is zero on infinite-dimensional
spaces; it must not be read as a cardinal-rank theory without finiteness.

## Stability from actual interleavings

An actual coordinate $\varepsilon$-interleaving factors the widened structure
map through the other module's unshifted map:

$$M(a-\varepsilon\mathbf1)\longrightarrow N(a)
\longrightarrow N(b)\longrightarrow M(b+\varepsilon\mathbf1).$$

The outside arrows are interleaving components. Naturality and the double-shift
equations identify the composite with the original structure map, rather than
assuming a rank inequality. The reverse interleaving gives the other inequality.
`CoordinateInterleaving.factor_structureMap` supplies this factorization;
`CoordinateInterleaving.rank_erosion_le` and `CoordinateInterleaving.rankErosion`
extract the rank comparisons for pointwise finite-dimensional modules.
Passing to infima proves

$$d_E(M,N)\le d_I(M,N)$$

as `rankErosionDistance_le_coordinateInterleavingDistance`. This includes zero
radius, $n=0$ and infinite distances; no minimizing interleaving is assumed.

## Using a failed rank test

Choose a weak pair $a\le b$ and prove

$$r_N(a,b)<r_M(a-\varepsilon\mathbf1,b+\varepsilon\mathbf1).$$

- `no_coordinateInterleaving_of_rank_violation` excludes an actual
  $\varepsilon$-interleaving.
- `radius_le_coordinateInterleavingDistance_of_rank_violation` gives
  $\varepsilon\le d_I(M,N)$ without attainment.
- `radius_lt_coordinateInterleavingDistance_of_rank_violation` gives
  $\varepsilon<d_I(M,N)$ when both modules have original finite graded-free
  presentations (`GradedFree.FinitelyPresented`), in addition to the
  finite-dimensional instances in its signature. This uses the existing
  **interleaving** attainment theorem, not an erosion attainment theorem.

Interchange $M,N$ for a violation in the other direction. A failed test alone
does not justify a strict lower bound for arbitrary pointwise finite-dimensional
inputs: an infimum need not be attained.

`RankErosionWitness.originHook_diagonal_rank` computes a nonzero diagonal rank
for the principal upset over $\mathbb Q$.
`originHook_no_zero_interleaving` applies it against the zero module, including
$n=0$. `originHook_positive_radius_no_interleaving` uses the genuinely
off-diagonal pair $a=1,b=2$ at radius $1$ in one coordinate. These are actual
hook-module consumers, not an executable finite-test algorithm.

## Zero radius, zero distance and future extensions

`rankErosion_zero_iff` identifies the **predicate** `RankErosion 0 M N` with
equality of all weak-pair ranks. Consequently equal rank invariants give distance
zero. This theorem does not identify the infimum equation $d_E(M,N)=0$ with
that predicate, nor does it classify modules up to natural isomorphism.
In multiple parameters, ranks do not record how images of maps from incomparable
grades meet, so rank equality cannot in general recover the module.

The [next-release extension proposal](https://github.com/uda-lab/tda-lib/issues/865)
separates the following targets: a precise comparison with strict-pair conventions;
erosion attainment and strict erosion lower certificates for original finite
presentations; image rank beyond finite-dimensional fibers; and certified finite
grid tests with actual persistent-homology consumers. Executable tests additionally
need effective grades, coefficients and a matrix-rank correctness bridge. These
are proposed extensions, not declarations supplied by this note. The proposal
also records endpoint and nonseparation counterexamples that a broader API must
respect, rather than promising to remove necessary hypotheses.

## Imports and source convention

Import `TDA.Persistence` for the public area API. Narrow imports are
`TDA.Persistence.RankErosion`, `TDA.Persistence.RankErosionInterleaving` and
`TDA.Persistence.RankErosionWitness`. Their declarations are in `TDA.Persistence`;
the concrete hook witnesses are in its `RankErosionWitness` namespace.
Coordinate notation uses `open scoped TDA.Persistence`.

[Puuska, §2.2](https://arxiv.org/html/1710.01577v1) defines the rank invariant
on strict pairs and proves its erosion stability using the interleaving
factorization (Theorem 22). The current library uses weak pairs and a
finite-dimensional specialization; it does not yet prove equivalence with that
strict-pair convention. The proposed convention comparisons and finite-presentation
erosion attainment are additional library targets, not results attributed to the
paper. See the [source record](references.md#Puuska17-v1).
