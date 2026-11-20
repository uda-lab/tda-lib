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

## Finite test grids for grid Kan extensions

Let `G` and `H` be finite coordinate grids, `M` a module on the points of `G`
and `N` a module on the points of `H`, over a field, and consider their left
Kan extensions to `Fin n → ℝ`. The fiber of the extension of `M` at a grade
`a` is the fiber of `M` at the floor of `a`, the coordinatewise greatest grid
point below `a`, and it is zero when no grid point lies below `a`. Structure
maps follow the floors. Hence the rank of the extension from `a` to `b` is the
rank of `M` between the two floors, or zero when `a` has no lower grid point
(`rankOfStructureMap_lan`, `rankOfStructureMap_lan_eq_zero`). This uses only
that ranks are preserved by the fiber isomorphisms, so no finite-dimensionality
is needed.

The two inequalities of `RankErosion ε` at a weak pair `a ≤ b` compare the
extension of `M` from `a − ε` to `b + ε` with the extension of `N` from `a` to
`b`, and conversely. By the previous paragraph they depend only on which grid
values lie below the coordinates of `a − ε`, `b + ε`, `a` and `b`. Since
`g ≤ aᵢ − ε` means `g + ε ≤ aᵢ`, and `g ≤ bᵢ + ε` means `g − ε ≤ bᵢ`, they
depend only on which **breakpoints** lie below `aᵢ` and below `bᵢ`: the values
of both grids in coordinate `i` and their shifts by `±ε`
(`erosionBreakpoints`).

Let `T` be a finite grid containing the breakpoints. If `a` has a lower point
of `T`, so has `b`; their floors in `T` are comparable points of `T`, and a
value of `T` lies below a coordinate of the floor exactly when it lies below
that coordinate of the grade. Replacing the pair by its floors therefore keeps
all four ranks. If `a` has no lower point of `T`, then `a − ε` has no lower
point of `G` or of `H`, because each `g + ε` is a value of `T`; both left-hand
ranks are zero and the inequalities hold. So `RankErosion ε` holds for the two
extensions if and only if its inequalities hold at the comparable pairs of
points of `T` (`rankErosion_lan_iff_of_subset`), including the diagonal pairs.

Testing only the original grid values is not enough. In
`RankErosionGridExamples`, the interval module `[0, 1)`, extended from the
grid `{0, 1}`, and the zero module satisfy both inequalities at radius `1/4`
for every pair of original values `0` and `1`, while the predicate fails at
the shifted breakpoint `1/4 = 0 + 1/4`, where the interval module has rank one
from `0` to `1/2` (`interval_original_values_pass`, `not_rankErosion_quarter`).
The one-parameter modules born at `0` and at `1` behave in the same way at
radius `1/2` (`original_values_pass`, `not_rankErosion_half`); at radius `1`
their predicate is obtained from the criterion by checking the four breakpoint
values (`rankErosion_one`). With no coordinates the predicate is
equality of one rank, and an empty coordinate set in both grids leaves no test
point.

The criterion is a mathematical reduction over the real numbers. It supplies
no executable test, rational arithmetic or matrix computation.

## Executable representations over the two-element field

A grid module over the field with two elements can be given by finite data: a
list of rational grid values in each coordinate, a fiber dimension at each grid
grade, and a matrix for each comparable pair of grid grades. The lists are used
as finite sets, so order and repetitions do not matter. The data define a
module on the real image of the grid when the matrices are identities on the
diagonal and compose along comparable triples of grid grades; this finite
condition is `F2GridRep.Valid`, and it can be decided by computation. (The
condition is also necessary for functoriality; that converse is not
formalised.)
For valid data, `F2GridRep.toModule` is the module with fibers
`Fin (dim a) → ZMod 2` and the stored matrices as structure maps. In Lean the
dimension and matrix functions are total on rational grades; their values off
the grid, and at non-comparable pairs, are never read.

For rational grades `x ≤ y`, the floor of each grade in the rational grid is
computable, and it is the rational grade of the floor of the corresponding
real grade in the real grid. By the rank formula of the previous section, the
rank of the Kan extension between the real grades of `x` and `y` is therefore
the rank of the stored matrix between the two rational floors, or zero when
`x` has no lower grid value. `F2GridRep.rankAt` computes this number with the
enumeration rank of [finite homology-map dimensions](finite-ph-map-dimensions.md),
and `F2GridRep.rankAt_eq` proves the identification with the actual Kan
extension. `F2GridRepExamples` executes the interval module `[0, 1)`, the same
module from an unsorted list with a repeated value, a two-parameter module
with a rank-one map out of a two-dimensional fiber, and two rejected inputs.

## A certified finite test

For two valid representations, possibly on different rational grids, and a
rational radius `e ≥ 0`, the rational breakpoint grid lists in each coordinate,
without repetitions, the values of both grids and their shifts by `±e`. Its
real image is exactly the breakpoint grid of the two real grids
(`RatGrid.grid_erosionBreakpoints`),
so the finite criterion applies with it as the test grid, and lowering or
raising a rational grade by `e` corresponds to the real operations in the
definition of erosion.

`F2GridRep.runErosion` first decides validity of both representations and
`0 ≤ e`; otherwise it returns `invalid`. It then enumerates the comparable
pairs `p ≤ q` of breakpoint grades and compares the executed rank of one module
from `p − e` to `q + e` with the executed rank of the other from `p` to `q`,
in both directions. It returns `pass` when every comparison holds, and
otherwise `fail` with one violated inequality: its direction, the pair of
grades and the two ranks.

The three outcomes are characterised for the actual Kan extensions of the two
grid modules. The outcome is `invalid` exactly for invalid input
(`runErosion_eq_invalid_iff`). It is `pass` exactly when the input is valid and
`RankErosion` holds at radius `e` (`runErosion_eq_pass_iff`). A reported
failure is a genuine violation: the recorded ranks are the ranks of the widened
structure map of one extension and of the structure map of the other at a
comparable pair of grades of the rational breakpoint grid, the first exceeds
the second, and `RankErosion` fails (`runErosion_eq_fail`). Which violation is
reported depends on the enumeration order.

In `F2GridErosionExamples`, the interval module `[0, 1)` against the zero
module fails at radius `1/4` at the shifted breakpoint `1/4`, although the
pairs of original grid values `0` and `1` show no failure; it passes at radius
`1/2`. Further fixtures cover both directions of failure, two nonzero modules
on different grids, radius zero, negative grid values, no coordinates, two
parameters, and invalid input.

A failure shows that the predicate fails at the tested radius. It is not a
strict lower bound for an erosion or interleaving distance, which needs an
attainment theorem that the library does not have; and the test neither
minimises a radius nor works over other fields. A coordinate has at most three
times as many breakpoints as the two grids have values there, and the
breakpoint grades are the product over the coordinates. The test validates
both representations, which enumerates the comparable triples of their grid
grades, and then evaluates four enumeration ranks at each comparable pair of
breakpoint grades. No polynomial bound is claimed.

## Zero radius, zero distance and future extensions

`rankErosion_zero_iff` identifies the **predicate** `RankErosion 0 M N` with
equality of all weak-pair ranks. Consequently equal rank invariants give distance
zero. This theorem does not identify the infimum equation $d_E(M,N)=0$ with
that predicate, nor does it classify modules up to natural isomorphism.
In multiple parameters, ranks do not record how images of maps from incomparable
grades meet, so rank equality cannot in general recover the module.

The [extension proposal](https://github.com/uda-lab/tda-lib/issues/865)
separates several targets. Of these, the finite criterion, the executable
representations over the two-element field and the certified finite test of
the three preceding sections are supplied. The following remain proposed
extensions, not declarations supplied by this note: a precise comparison with
strict-pair conventions; erosion attainment and strict erosion lower
certificates for original finite presentations; image rank beyond
finite-dimensional fibers; finite tests fed by actual persistent-homology
input; and execution over other fields. The proposal also records endpoint and
nonseparation counterexamples that a broader API must respect, rather than
promising to remove necessary hypotheses.

## Imports and source convention

Import `TDA.Persistence` for the public area API. Narrow imports are
`TDA.Persistence.RankErosion`, `TDA.Persistence.RankErosionInterleaving`,
`TDA.Persistence.RankErosionWitness`, `TDA.Persistence.RankErosionGrid`,
`TDA.Persistence.F2GridRep` and `TDA.Persistence.F2GridErosion`. Their
declarations are in `TDA.Persistence`; the concrete hook witnesses are in its `RankErosionWitness` namespace, the grid
criterion is in `TDA.Persistence.CoordinateGrid`, and the executable
representations are in `TDA.Persistence.RatGrid` and `TDA.Persistence.F2GridRep`.
Coordinate notation uses `open scoped TDA.Persistence`.

[Puuska, §2.2](https://arxiv.org/html/1710.01577v1) defines the rank invariant
on strict pairs and proves its erosion stability using the interleaving
factorization (Theorem 22). The current library uses weak pairs and a
finite-dimensional specialization; it does not yet prove equivalence with that
strict-pair convention. The proposed convention comparisons and finite-presentation
erosion attainment are additional library targets, not results attributed to the
paper. See the [source record](references.md#Puuska17-v1).
