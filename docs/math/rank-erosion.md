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
`rankOfStructureMap_four_point` proves that widening an interval does not
increase its rank. This yields `RankErosion.refl` and `RankErosion.mono`; symmetry and
composition are `RankErosion.symm` and `RankErosion.trans`.

`rankErosionDistance` is the extended infimum of the admissible finite radii:

$$d_E(M,N)=\inf\{\varepsilon\ge0:\operatorname{RankErosion}(\varepsilon,M,N)\}.$$

An empty admissible set gives infinity. `rankErosionDistance_self`,
`rankErosionDistance_comm` and `rankErosionDistance_triangle` give the extended
pseudometric laws; these three statements need no finiteness hypothesis. A supplied predicate
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
inputs: an infimum need not be attained. For finitely presented modules a
failed test does give a strict lower bound of the erosion distance
([below](#attainment-for-finitely-presented-modules)).

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

A failure shows that the predicate fails at the tested radius. The Kan
extensions have finite-dimensional fibers, so the tested radius is then a lower
bound of the erosion distance (`le_rankErosionDistance_of_not_rankErosion`,
[below](#strict-pairs)) and hence of the interleaving distance
(`rankErosionDistance_le_coordinateInterleavingDistance`). The Kan extensions
are also finitely presented, so the erosion distance is strictly larger than
the tested radius
([attainment](#attainment-for-finitely-presented-modules)). The test neither
minimises a radius nor works over other fields. A coordinate has at most three
times as many breakpoints as the two grids have values there, and the
breakpoint grades are the product over the coordinates. The test validates
both representations, which enumerates the comparable triples of their grid
grades, and then evaluates four enumeration ranks at each comparable pair of
breakpoint grades. No polynomial bound is claimed.

## Strict pairs

`StrictRankErosion ε M N` requires the two inequalities of `RankErosion ε M N`
only at the **strict pairs** of the product order: $a\le b$ and $a\ne b$.
`strictRankErosion_iff_lt` restates this with $a<b$. A strict pair need not be
strict in every coordinate; no predicate on coordinatewise strict pairs is
supplied. `strictRankErosionDistance` is the extended infimum of the radii
admissible for the strict predicate.

The weak predicate implies the strict one at the same radius
(`RankErosion.strict`), for every $n$ and without a finiteness hypothesis, so
the strict distance is at most the weak one
(`strictRankErosionDistance_le_rankErosionDistance`).

Conversely, let $n\ge1$ and let both modules have finite-dimensional fibers.
For a weak pair $a\le b$ and $\delta>0$, the pair
$(a-\delta\mathbf1,b+\delta\mathbf1)$ is strict. The strict test at this pair
and the fact that widening an interval does not increase its rank give

$$r_M(a-(\varepsilon+\delta)\mathbf1,b+(\varepsilon+\delta)\mathbf1)
\le r_N(a-\delta\mathbf1,b+\delta\mathbf1)\le r_N(a,b).$$

Hence strict erosion at $\varepsilon$ implies weak erosion at every larger
radius (`StrictRankErosion.rankErosion_add`,
`StrictRankErosion.rankErosion_of_lt`), and the two distances are equal,
infinite values included (`strictRankErosionDistance_eq_rankErosionDistance`).
Finite dimensionality enters through the rank comparison only.

The strict predicate is symmetric, composes with addition of radii without a
finiteness hypothesis, because widening a strict pair gives a strict pair, and
is monotone in the radius for finite-dimensional fibers
(`StrictRankErosion.symm`, `StrictRankErosion.trans`, `StrictRankErosion.mono`).
Its distance therefore has zero self-distance, symmetry and the extended
triangle inequality for every $n$. At radius zero the strict predicate is
equality of the ranks at strict pairs (`strictRankErosion_zero_iff`).

For finite-dimensional fibers, a radius at which one of the two predicates
fails is a lower bound of its distance
(`le_rankErosionDistance_of_not_rankErosion`,
`le_strictRankErosionDistance_of_not_strictRankErosion`). These bounds are not
strict.

Two boundary cases delimit these statements. The first shows that the two
predicates can differ at a fixed radius and that the weak infimum need not be
attained when the fibers are only finite-dimensional. The second shows that
the implication from strict to weak pairs and the equality of the distances
fail with no coordinates. They are proved in `StrictRankErosionExamples`.

- **A fixed radius.** Take the module with one copy of $\mathbb Q$ at each grade
  of the closed box $[0,2c]^n$ and zero elsewhere, against the zero module, for
  a radius $c\ge0$. For $a\le b$, the grades $a-c\mathbf1$ and $b+c\mathbf1$
  both lie in the box only when $a=b=c\mathbf1$. So strict erosion holds at
  radius $c$, and weak erosion fails there, on the diagonal at the centre of
  the box (`closedBox_strictRankErosion`, `closedBox_not_rankErosion`). For
  $n\ge1$, weak erosion holds at every radius above $c$ and both distances
  equal $c$ (`closedBox_rankErosion_of_lt`, `closedBox_rankErosionDistance`,
  `closedBox_strictRankErosionDistance`). The two predicates therefore differ
  at a fixed radius although their distances agree; the weak infimum is not
  attained; and for modules with finite-dimensional fibers a failed weak test
  at a radius does not show that the distance exceeds that radius. For $c=0$
  the module is supported at one grade.
- **No coordinates.** When $n=0$ there is one grade and no strict pair. The
  strict predicate holds for all modules at every radius and the strict
  distance is zero (`strictRankErosion_fin_zero`,
  `strictRankErosionDistance_fin_zero`). For two modules whose single fibers
  have dimensions three and two, weak erosion fails at every radius and the
  weak distance is infinite (`noCoordinates_not_rankErosion`,
  `noCoordinates_rankErosionDistance`).

The executed tests of the previous section are consumers. A passing test gives
strict erosion at its radius. For $n\ge1$, a failing test at a radius excludes
strict erosion at every smaller radius; and a failure reported at a strict pair
excludes strict erosion at the tested radius itself. For the interval module
`[0, 1)` against zero, the tests at radii `1/4` and `1/2` exclude strict erosion
at radius `1/8` and enclose the strict distance between `1/4` and `1/2`
(`interval_zero_not_strictRankErosion`,
`interval_zero_strictRankErosionDistance_bounds`); for the modules born at `0`
and at `1`, the failure at radius `1/2` is reported at the strict pair
`(1/2, 1)` (`rays_not_strictRankErosion`). These statements record what the
executed tests give and are not sharp: the distance of the interval module from
zero is `1/2`, and its strict predicate fails at every radius below `1/2`
(`interval_zero_strictRankErosionDistance` and
`interval_zero_not_strictRankErosion_of_lt` in `RankErosionAttainmentExamples`,
[below](#attainment-for-finitely-presented-modules)).

Nothing in this section identifies the two predicates at a fixed radius for a
restricted class of modules, or makes a lower bound strict.

## Attainment for finitely presented modules

Let $M$ and $N$ have original finite graded-free presentations
(`GradedFree.FinitelyPresented`). Their fibers are finite-dimensional. No
further hypothesis is used below, and $n=0$ is allowed.

A finitely presented module is constant under small diagonal moves to the
right: at every grade $a$ there is $\eta>0$ such that
$M(a)\to M(a+\delta\mathbf1)$ is an isomorphism for $0\le\delta\le\eta$
(`GradedFree.finitelyPresented_exists_pos_structureMap_isIso`). Hence, for a
weak pair $a\le b$ and all small $\delta\ge0$,

$$r_M(a,b+\delta\mathbf1)=r_M(a,b),
\qquad
r_M(a+\delta\mathbf1,b+\delta\mathbf1)=r_M(a,b).$$

The first equality follows a structure map by an isomorphism. The second uses
the commuting square of the four structure maps, whose two diagonal moves are
isomorphisms. This is
`GradedFree.finitelyPresented_exists_pos_rankOfStructureMap_erosionUpper`.
Nothing is claimed for moves to the left or for moves that are not diagonal,
and the bound $\eta$ depends on the pair.

Suppose an inequality of erosion fails at radius $\varepsilon$ and a pair
$a\le b$, say $r_N(a,b)<r_M(a-\varepsilon\mathbf1,b+\varepsilon\mathbf1)$.
Test the radius $\varepsilon+\delta$ at the pair
$(a+\delta\mathbf1,b+\delta\mathbf1)$. The widened structure map of $M$ runs
from $a-\varepsilon\mathbf1$ to $b+(\varepsilon+2\delta)\mathbf1$, and the
structure map of $N$ from $a+\delta\mathbf1$ to $b+\delta\mathbf1$. For small
$\delta$ both ranks are the ranks at $\delta=0$, so the inequality fails at
radius $\varepsilon+\delta$ as well
(`GradedFree.finitelyPresented_exists_pos_not_rankErosion_add`). A failure at
some radius above $\varepsilon$ is a non-strict lower bound of the distance by
the [previous section](#strict-pairs), so

$$\lnot\operatorname{RankErosion}(\varepsilon,M,N)\implies
\varepsilon<d_E(M,N)$$

(`GradedFree.finitelyPresented_lt_rankErosionDistance_of_not_rankErosion`),
also when the distance is infinite. Consequently:

- $d_E(M,N)\le\varepsilon$ if and only if `RankErosion ε M N` holds
  (`GradedFree.finitelyPresented_rankErosionDistance_le_iff_rankErosion`); a
  finite distance is itself an admissible radius
  (`GradedFree.finitelyPresented_rankErosion_at_distance`).
- The admissible radii form a closed set, which is the half-line
  $[d_E(M,N),\infty)$ when the distance is finite and is empty otherwise
  (`GradedFree.finitelyPresented_isClosed_rankErosion_parameters`,
  `GradedFree.finitelyPresented_rankErosion_parameters_eq_Ici`).
- $d_E(M,N)=0$ if and only if $r_M(a,b)=r_N(a,b)$ for every weak pair
  (`GradedFree.finitelyPresented_rankErosionDistance_eq_zero_iff`). This does
  not make the modules isomorphic.

Both presentations are needed. The closed box $[0,2c]^n$ of the previous
section has finite-dimensional fibers, and the zero module is finitely
presented (`GradedFree.finitelyPresented_zero`). For $n\ge1$ their distance is
$c$ while erosion fails at radius $c$, so the module of the closed box is not
finitely presented (`closedBox_not_finitelyPresented`); and for $c=0$ the
distance is zero while the rank invariants differ on the diagonal at the
origin (`closedBox_zero_distance_zero_and_ranks_differ`).

The Kan extension of a valid representation over the two-element field is
finitely presented (`F2GridRep.finitelyPresented_lan_toModule`), so a failing
executed test at a radius shows that the erosion distance exceeds that radius.
In `RankErosionAttainmentExamples`, the interval module `[0, 1)` and zero have
distance above `1/4` (`interval_zero_quarter_lt_rankErosionDistance`); the
modules born at `0` and at `1` have distance above `1/2` and at most `1`
(`rays_rankErosionDistance_bounds`); and two two-parameter modules whose test
fails at radius `0` have nonzero distance at most `1`
(`plane_flat_rankErosionDistance_bounds`).

For the interval module `[0, 1)` and zero the distance is computed. Below
radius `1/2` the diagonal pair at the grade `1/2` is a failed test, because the
widened structure map stays inside the interval
(`interval_zero_not_rankErosion_of_lt`), and the executed test passes at `1/2`.
So both distances equal `1/2` (`interval_zero_rankErosionDistance`,
`interval_zero_strictRankErosionDistance`), strict erosion fails at every
smaller radius (`interval_zero_not_strictRankErosion_of_lt`), and by attainment
erosion holds exactly at the radii from `1/2` on
(`interval_zero_rankErosion_iff`).

This section makes no statement about the strict predicate at a fixed radius
for finitely presented modules and none about the interleaving distance.

## Zero radius, zero distance and future extensions

`rankErosion_zero_iff` identifies the **predicate** `RankErosion 0 M N` with
equality of all weak-pair ranks. Consequently equal rank invariants give distance
zero. This theorem does not identify the infimum equation $d_E(M,N)=0$ with
that predicate, nor does it classify modules up to natural isomorphism. For
finitely presented modules distance zero is equality of the rank invariants
([above](#attainment-for-finitely-presented-modules)); the module supported at
one grade shows that this fails for finite-dimensional fibers in general.
In multiple parameters, ranks do not record how images of maps from incomparable
grades meet, so rank equality cannot in general recover the module.

The [extension proposal](https://github.com/uda-lab/tda-lib/issues/865)
separates several targets. Of these, the finite criterion, the executable
representations over the two-element field, the certified finite test, the
comparison of weak and strict pairs and the attainment theorem of the five
preceding sections are supplied. Of the proposal's first package, on
conventions and exact thresholds, the supplied items are the strict-pair
predicate, its two comparisons with the weak predicate, the equality of the
distances, the non-strict lower bounds, the closed-box and no-coordinates
boundary cases, and erosion attainment for original finitely presented
modules: admissibility of the infimum, the strict lower bound from a failed
predicate, and the identification of distance zero with equal rank invariants,
with the right-local isomorphisms taken from the presentation. Its remaining
items are proposed extensions, not declarations supplied by this note: the
equivalence of the strict and weak predicates at a fixed radius for finitely
presented modules; the certificate $\varepsilon<d_E\le d_I$ from a failed
test; and a two-parameter example of non-isomorphic modules with equal rank
invariants. The
other packages also remain proposed: image rank beyond finite-dimensional
fibers; finite tests fed by actual persistent-homology input; and execution
over other fields. The proposal records endpoint and nonseparation
counterexamples that a broader API must respect, rather than promising to
remove necessary hypotheses.

## Imports and source convention

Import `TDA.Persistence` for the public area API. Narrow imports are
`TDA.Persistence.RankErosion`, `TDA.Persistence.RankErosionInterleaving`,
`TDA.Persistence.RankErosionWitness`, `TDA.Persistence.RankErosionGrid`,
`TDA.Persistence.F2GridRep`, `TDA.Persistence.F2GridErosion`,
`TDA.Persistence.StrictRankErosion` and
`TDA.Persistence.RankErosionAttainment`. Their
declarations are in `TDA.Persistence`; the concrete hook witnesses are in its `RankErosionWitness` namespace, the grid
criterion is in `TDA.Persistence.CoordinateGrid`, and the executable
representations are in `TDA.Persistence.RatGrid` and `TDA.Persistence.F2GridRep`.
The strict-pair examples are in `TDA.Persistence.StrictRankErosionExamples`
and the attainment examples in `TDA.Persistence.RankErosionAttainmentExamples`;
the attainment theorems are in `TDA.Persistence.GradedFree`.
Coordinate notation uses `open scoped TDA.Persistence`.

[Puuska, §2.2](https://arxiv.org/html/1710.01577v1) defines the rank invariant
on strict pairs and proves its erosion stability using the interleaving
factorization (Theorem 22). The library's `RankErosion` uses weak pairs and a
finite-dimensional specialization. `StrictRankErosion` uses the strict pairs of
the product order with the same diagonal shift, and the
[comparison above](#strict-pairs) relates the two library predicates.

For the pair convention, the exact version arXiv:1710.01577v1 was consulted.
Its §1 defines the pair set Dgm_P as the pairs (a, b) of P × P with a < b, and
its footnote 2 fixes a < b to mean a ≤ b and a ≠ b. The introduction defines
Dgm_{Rⁿ} in the same way and states the erosion conditions as
f(a − ε, b + ε) ≤ g(a, b) and g(a − ε, b + ε) ≤ f(a, b) for all (a, b) in
Dgm_{Rⁿ}. Definition 5 defines d_E as the infimum of the ε with ∇Ω_ε f ≤ g and
∇Ω_ε g ≤ f, or ∞; Definition 17 takes the rank invariant to be the image of
F(a < b); Definition 23 uses Ω_ε(a) = a + ε·1. The set Dgm′_{Rⁿ} of the pairs
with aᵢ < bᵢ for each i is separate and is used only for d_T (Definition 29).
So the strict-pair relation `a ≤ b ∧ a ≠ b` and the diagonal shift of
`StrictRankErosion` match the paper's convention.

Two points were not verified. The paper does not state explicitly that ≤ on Rⁿ
is the product order; this is implied by the sublevel sets and by a
coordinatewise step after Theorem 30. And the paper works with images in a
preordered abelian category, not with `finrank`, so agreement of the predicates
beyond the pair convention is not established.

The comparison of the two library predicates, its boundary cases and the
finite-presentation erosion attainment are library derivations. No
theorem about strict pairs in this note is attributed to a numbered result of
the paper. See the [source record](references.md#Puuska17-v1).
