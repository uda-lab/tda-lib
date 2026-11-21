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
spaces; it must not be read as a cardinal-rank theory without finiteness. The
[extended image rank](#extended-image-rank) below is the rank that does not
collapse an infinite image to zero.

## Extended image rank

`eRankOfStructureMap M hab` is `Cardinal.toENat` of the cardinal rank of the
structure map at $a\le b$: the dimension of its image when that is finite, and
$\top$ when the image is infinite-dimensional. Every infinite cardinal is
collapsed to $\top$, so distinct infinite dimensions are not distinguished
(`continuumConst_collapse`: constant modules of dimensions $\aleph_0$ and
$\mathfrak c$). The choice of $\mathbb N_\infty$ over cardinals is recorded on
[the extension proposal](https://github.com/uda-lab/tda-lib/issues/865); it
follows Mathlib's `Matrix.eRank`. The definition and its laws are stated for an
arbitrary index preorder and carrier universe; extended ranks of modules in
different universes are compared without lifting (`eRank_infiniteLarge`).

For every module, with no finiteness hypothesis:

- `eRankOfStructureMap_trans_le_left`, `eRankOfStructureMap_trans_le_right`
  and `eRankOfStructureMap_four_point`: composing or widening does not increase
  the rank;
- `eRankOfStructureMap_self` (fiber dimension on the diagonal),
  `eRankOfStructureMap_zero`, `eRankOfStructureMap_eq_top_iff` and
  `eRankOfStructureMap_iso`.

`rankOfStructureMap_eq_toNat_eRankOfStructureMap` states that the `ℕ`-valued
rank is the truncation sending $\top$ to $0$.
`eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional` (finite-dimensional
image) and `eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional_source`
(finite-dimensional source fiber) identify the two ranks, and
`eRankOfStructureMap_le_eRankOfStructureMap_iff` identifies their comparisons
when both source fibers are finite-dimensional. The examples
(`TDA.Persistence.StructureMapERankExamples`) show that a
countably-infinite-dimensional constant module has the `ℕ`-valued ranks of the
zero module, so `RankErosion 0` holds between them
(`rankErosion_zero_infinite`), while its extended ranks are $\top$
(`infinite_vs_zero`). Erosion on the extended rank is in
[the next section](#erosion-on-extended-ranks).

## Erosion on extended ranks

`ERankErosion ε M N` (`TDA.Persistence.ERankErosion`) is `RankErosion ε M N`
with `rankOfStructureMap` replaced by `eRankOfStructureMap`: the same weak
pairs $a\le b$, the same widened pair from $a-\varepsilon$ to $b+\varepsilon$
and both directions. `eRankErosionDistance` is the infimum in
$[0,\infty]$ of its admissible radii. For every number of parameters, every
field and every module, with no finiteness hypothesis:

- `ERankErosion.mono` (larger radii), `ERankErosion.refl`, `ERankErosion.symm`
  and `ERankErosion.trans` (radii add); `eRankErosion_zero_iff` (radius zero is
  equality of all weak-pair extended ranks, diagonal included);
- `eRankErosionDistance_self`, `eRankErosionDistance_comm` and
  `eRankErosionDistance_triangle`, so the distance is an extended pseudometric;
  `eRankErosionDistance_le_of_erosion`,
  `le_eRankErosionDistance_of_not_eRankErosion` and
  `eRankErosionDistance_eq_top_iff`;
- `CoordinateInterleaving.eRankErosion` and
  `eRankErosionDistance_le_coordinateInterleavingDistance`: the extended
  distance is at most the coordinate interleaving distance. The proof reuses the
  factorization `CoordinateInterleaving.factor_structureMap` of the next section
  and Mathlib's `LinearMap.rank_comp_le_left/right`.

`RankErosion.refl`, `RankErosion.mono` and
`le_rankErosionDistance_of_not_rankErosion` assume finite-dimensional fibers;
their extended analogues do not. On pointwise finite-dimensional modules
`eRankErosion_iff_rankErosion` and
`eRankErosionDistance_eq_rankErosionDistance` identify the predicate and the
distance with `RankErosion` and `rankErosionDistance`.

Without finite dimensionality the predicates are incomparable. The examples
(`TDA.Persistence.ERankErosionExamples`) show both failures.
`ephemeralInfinite` has fiber `ℕ →₀ ℚ` at every grade and zero maps between
distinct grades; `RankErosion 0` holds between it and zero
(`ephemeralInfinite_rankErosion_zero`), while `ERankErosion 0` fails on the
diagonal. With at least one coordinate, `ERankErosion` holds against zero at
every positive radius, so the extended distance is $0$ and is not attained
(`ephemeralInfinite_eRankErosionDistance`). With no coordinate it fails at every
radius, and the extended distance is $\top$
(`ephemeralInfinite_eRankErosionDistance_fin_zero`). The infinite constant
module against zero has extended distance $\top$ and `ℕ`-valued distance $0$
(`infinite_vs_zero_distance`). Conversely, `split`, with fiber
$\mathbb Q\times(\mathbb N\to_0\mathbb Q)$, the identity on the diagonal and
`inl ∘ fst` between distinct grades, satisfies `ERankErosion` against the
one-dimensional constant module at every positive radius, while `RankErosion`
fails, because its `ℕ`-valued diagonal rank is $0$
(`split_line_eRankErosion_not_rankErosion`). On pointwise finite-dimensional
inputs the distances agree: `line_vs_zero_distance` (both $\top$) and
`closedBox_eRankErosionDistance` (the finite value $c$ for the closed box).

Distance $0$ does not imply erosion at radius $0$, nor an isomorphism. Since
every infinite cardinal is collapsed to $\top$, constant modules of different
infinite dimensions are at extended distance $0$ although no interleaving
exists; this is not formalized. No strict-pair extended predicate is supplied.

The predicate and distance are stated for `PModule.{u,0,u}`, as `RankErosion`
and `CoordinateInterleaving.factor_structureMap` are. This deliberately departs
from the remark in the
[rank-codomain decision](https://github.com/uda-lab/tda-lib/issues/865#issuecomment-7056569407)
that the general laws need not be universe-restricted, so that the existing
factorization is reused unchanged. Lifting it later only generalizes the
signature of `factor_structureMap`.

### One parameter: q-tame modules and real interleavings

`TDA.Persistence.ERankQTame` connects the one-parameter `PModule.QTame` and
real interleavings with the extended rank. `eRankOfStructureMap_ne_top_iff`
(in `StructureMapERank`) says that the extended rank is finite exactly when the
image is finite-dimensional. A real module is q-tame exactly when every
structure map across a strict inequality has finite extended rank
(`PModule.qTame_iff_eRankOfStructureMap_ne_top`), and exactly when its
one-coordinate module `CoordinateRealBridge.fromReal M` has finite extended
rank on every strict pair of the product order on `Fin 1 → ℝ`
(`PModule.qTame_iff_eRankOfStructureMap_fromReal_ne_top`, with the consumers
`PModule.QTame.eRankOfStructureMap_ne_top` and
`PModule.QTame.eRankOfStructureMap_fromReal_ne_top`). With one coordinate,
strictness in the product order and in every coordinate coincide.

For a real `ε`-interleaving `i` of `M` and `N`,
`RealInterleaving.eRankOfStructureMap_le_toENat_rank` bounds the extended rank
of the structure map of `M` from $a$ to $(a+\varepsilon)+\varepsilon$ by the
extended dimension of the middle fibre `N.obj (a + ε)`, with no finiteness
hypothesis, and `RealInterleaving.eRankOfStructureMap_ne_top` is the local
finite-image bound: that rank is finite when the middle fibre is
finite-dimensional. Its `finrank` sibling
`finrank_range_structureMapLinear_le_of_realInterleaving`
(`RealInterleavingRankObstruction`) states the grade inequality as
`t ≤ t + ((ε + ε : ℝ≥0) : ℝ)`, while the extended statements use
`a ≤ (a + ε) + ε`, as `RealInterleaving.finiteDimensional_range_structureMap`
does. Through `CoordinateRealBridge.toCoordinate`, a real interleaving gives
extended-rank erosion of the one-coordinate modules
(`RealInterleaving.eRankErosion`), and
`eRankErosionDistance_fromReal_le_realInterleavingDistance` bounds their
extended erosion distance by `realInterleavingDistance`. These two are stated
at `PModule.{u,0,u}`, as `ERankErosion` is, while the q-tame and local-bound
statements are at `PModule.{u,0,w}`.

The examples (`TDA.Persistence.ERankQTameExamples`) use `realEphemeral`, the
one-coordinate `ephemeralInfinite` read on the real line: fibre
`ℕ →₀ ℚ` at every grade and zero maps across strict inequalities. It is q-tame
and not pointwise finite-dimensional (`realEphemeral_qTame_not_pfd`). Its
one-coordinate module has extended rank $\top$ on the diagonal
(`eRank_fromReal_realEphemeral_self`), so the strictness hypothesis cannot be
dropped. It is interleaved with zero at every positive radius
(`nonempty_realInterleaving_realEphemeral_zero`), so the local bound applies
through the zero middle fibre although every fibre of `realEphemeral` is
infinite-dimensional.

No finite-image condition is stated for two or more parameters. There
"strict" can mean the strict product order ($a\le b$, $a\ne b$) or
strictness in every coordinate, and these differ: $(0,0)$ and $(1,0)$ form a
strict pair of the first kind but not of the second. Choosing between them is
left to a later decision.

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
([below](#attainment-for-finitely-presented-modules)), and a second strict
bound of the interleaving distance passes through the erosion distance:
`GradedFree.finitelyPresented_lt_coordinateInterleavingDistance_of_not_rankErosion`
([certificates](#fixed-radius-certificates-and-nonseparation), where the two
strict bounds are compared).

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
([attainment](#attainment-for-finitely-presented-modules)). What a passing or
a failing test implies for both predicates and for the distances is stated for
arbitrary valid input [below](#fixed-radius-certificates-and-nonseparation).
The test neither minimises a radius nor works over other fields. A coordinate has at most three
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
restricted class of modules, or makes a lower bound strict. Both are done for
finitely presented modules in the next two sections.

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

The strict predicate at a fixed radius and the interleaving distance are
treated in the next section.

## Fixed radius, certificates and nonseparation

Let $M$ and $N$ again have original finite graded-free presentations. The
statements of this section are in `TDA.Persistence.RankErosionCertificate`.

**The two predicates at a fixed radius.** Let $n\ge1$. Strict erosion at
$\varepsilon$ bounds the strict distance by $\varepsilon$; the strict distance
equals the weak one ([strict pairs](#strict-pairs)); and by
[attainment](#attainment-for-finitely-presented-modules) the weak predicate
holds at $\varepsilon$. With `RankErosion.strict` this gives

$$\operatorname{StrictRankErosion}(\varepsilon,M,N)\iff
\operatorname{RankErosion}(\varepsilon,M,N)$$

(`GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion`). For every
$n$, the strict distance is at most $\varepsilon$ exactly when strict erosion
holds at $\varepsilon$, and a radius at which strict erosion fails is strictly
below the strict distance
(`GradedFree.finitelyPresented_strictRankErosionDistance_le_iff_strictRankErosion`,
`GradedFree.finitelyPresented_lt_strictRankErosionDistance_of_not_strictRankErosion`);
with no coordinates the strict predicate always holds and the strict distance
is zero. Both hypotheses of the equivalence are needed. The closed box of the
[strict-pair section](#strict-pairs) has finite-dimensional fibers and
separates the two predicates at the radius $c$. With no coordinates, the two
modules with fibers of dimensions three and two are finitely presented,
satisfy strict erosion and violate weak erosion at every radius
(`noCoordinates_finitelyPresented_not_iff` in
`RankErosionCertificateExamples`). For the interval module `[0, 1)` and zero,
strict erosion holds exactly at the radii from `1/2` on
(`interval_zero_strictRankErosion_iff`).

**The certificate of a failed test.** If erosion fails at $\varepsilon$, then

$$\varepsilon<d_E(M,N)\le d_I(M,N)$$

(`GradedFree.finitelyPresented_rankErosion_failure_certificate`), and in
particular $\varepsilon<d_I(M,N)$
(`GradedFree.finitelyPresented_lt_coordinateInterleavingDistance_of_not_rankErosion`).
The first inequality is the strict bound of the previous section. The second
is `rankErosionDistance_le_coordinateInterleavingDistance`, with the
finite-dimensional fibers taken from the presentations; it does not depend on
the failed test.

`radius_lt_coordinateInterleavingDistance_of_rank_violation`
([above](#using-a-failed-rank-test)) also concludes $\varepsilon<d_I(M,N)$. It
starts from one violated inequality at a named weak pair, asks for
presentations whose generators and relations are indexed in the universe of
the coefficients and for finite-dimensionality instances, and uses attainment
of the interleaving distance. The certificate starts from the failure of
either inequality, asks for presentations indexed in `Type` and for no
instance, and places the erosion distance between the radius and the
interleaving distance. The two universe choices are exchanged by
`GradedFree.finitelyPresented_liftIndexUniverse` and
`GradedFree.finitelyPresented_lowerIndexUniverse`, and
`certificate_of_rank_violation` derives the certificate from the hypotheses of
the older theorem.

**Executed tests.** The Kan extensions of two valid representations over the
two-element field are finitely presented. For valid input and a rational
radius $e\ge0$:

- the test passes exactly when the erosion distance of the two Kan extensions
  is at most $e$ (`F2GridRep.runErosion_eq_pass_iff_rankErosionDistance_le`),
  and, for $n\ge1$, exactly when strict erosion holds at $e$
  (`F2GridRep.runErosion_eq_pass_iff_strictRankErosion`);
- a passing test gives both predicates at $e$ and bounds both erosion
  distances by $e$ (`F2GridRep.runErosion_eq_pass_certificate`); it gives no
  bound of the interleaving distance, as the nonseparation example below
  shows;
- a failing test gives $e<d_E\le d_I$ (`F2GridRep.runErosion_eq_fail_certificate`),
  and for $n\ge1$ it refutes strict erosion at $e$ and shows that $e$ is
  strictly below the strict distance
  (`F2GridRep.runErosion_eq_fail_strict_certificate`). With no coordinates a
  failing test says nothing about the strict predicate.

The three certificate statements take only the equation for the executed
result; validity of the input is part of their conclusion. In
`RankErosionCertificateExamples` the failing test of the interval module
`[0, 1)` against zero at radius `1/4` gives the chain and refutes strict
erosion at `1/4` itself (`interval_zero_quarter_certificate`,
`interval_zero_quarter_strict_certificate`); the failing test of the modules
born at `0` and at `1` bounds their interleaving distance strictly from below
by `1/2` (`rays_half_lt_coordinateInterleavingDistance`); the failing test of
two two-parameter modules at radius `0` shows that they are not isomorphic
(`plane_flat_not_iso`); the failing test with no coordinates still bounds the
interleaving distance (`noCoordinates_lt_coordinateInterleavingDistance`); and
the test of the interval module against zero passes exactly at the rational
radii from `1/2` on (`interval_zero_runErosion_eq_pass_iff`).

**The closed box and interleavings.** For the module of the closed box
$[0,2c]^n$ and the zero module there is no interleaving at radius $c$, for
every $n$, because an interleaving gives weak erosion at its radius
(`closedBox_not_interleaving`). For $n\ge1$ and $c'>c$, the structure map of
the closed box from a grade $a$ to $a+2c'\mathbf1$ leaves the box and is zero,
so the two zero maps form an interleaving at radius $c'$
(`closedBox_interleaving_of_lt`). Hence the interleaving distance is $c$ and is
not attained (`closedBox_coordinateInterleavingDistance`). For modules that
have only finite-dimensional fibers, neither the erosion distance nor the
interleaving distance need be attained, and erosion can fail at a radius
equal to both distances.

**Nonseparation.** Take the grid $\{0,1\}^2$ and two modules over the field
with two elements, with fiber zero at $(0,0)$, one-dimensional fibers at
$(1,0)$ and $(0,1)$, and a two-dimensional fiber at $(1,1)$. In the first
module both arm maps into the top fiber send the generator to the same basis
vector; in the second they send it to the two basis vectors
(`armsCoincident`, `armsIndependent`). Their Kan extensions are finitely
presented. The executed test passes at radius `0`, so the two extensions have
the same rank at every weak pair and erosion distance zero (`arms_zero`,
`arms_rank_eq`, `arms_rankErosionDistance`); the test passes at every
nonnegative rational radius (`arms_runErosion_eq_pass_iff`). They are not
isomorphic: the images of the two structure maps into the fiber at $(1,1)$
have a nonzero common vector in the first extension and none in the second,
and this property is preserved by isomorphisms (`ImagesMeet`,
`armsCoincident_imagesMeet`, `armsIndependent_not_imagesMeet`,
`arms_not_iso`). For finitely presented modules interleaving distance zero is
isomorphism, so their interleaving distance is not zero
(`arms_nonseparation`); its value is not computed. Thus the rank invariant
does not determine a finitely presented two-parameter module, $d_E\le d_I$
can be strict with $d_E=0$, and a passing rank test gives no bound of the
interleaving distance. The example is over the two-element field, the field
of the executable representations.

## Finite graded simplicial homology

Let $g,h$ be monotone grade assignments on one finite simplicial complex and
let $\delta\ge0$ bound every face-coordinate error $|g(s)_i-h(s)_i|$. The
statements of this section are in `TDA.Persistence.FiniteSimplicialErosion`;
they hold for every coefficient field, homology degree and number of
coordinates, including $n=0$, empty complexes and repeated grades.

The existing interleaving `finiteSimplicialHomology_interleaving` and the
finite-dimensional fibers of finite input give erosion at $\delta$
(`finiteSimplicialHomology_rankErosion`) and
$d_E(M_g,M_h)\le\delta$ (`rankErosionDistance_finiteSimplicialHomology_le`).
The `_supGradeError` forms take for $\delta$ the maximal error
`FiniteGraded.supGradeError`. The extended-rank forms
(`finiteSimplicialHomology_eRankErosion`,
`eRankErosionDistance_finiteSimplicialHomology_le` and their `_supGradeError`
forms) need no fiber finiteness, and on this input the two erosion distances
agree (`eRankErosionDistance_finiteSimplicialHomology_eq_rankErosionDistance`).

The homology modules are finitely presented
(`finiteSimplicialHomology_finitelyPresented`), so no caller-supplied
presentation is needed for the [certificate](#fixed-radius-certificates-and-nonseparation).
If erosion fails at $\varepsilon$, then

$$\varepsilon<d_E(M_g,M_h)\le d_I(M_g,M_h)\le\operatorname{supGradeError}(g,h)$$

(`finiteSimplicialHomology_rankErosion_failure_certificate`, and
`finiteSimplicialHomology_eRankErosion_failure_certificate` for the extended
rank). Hence $\varepsilon<\delta$ for every error bound $\delta$
(`lt_of_not_rankErosion_finiteSimplicialHomology`,
`lt_of_not_eRankErosion_finiteSimplicialHomology`) and
$\varepsilon<\operatorname{supGradeError}(g,h)$. These grade-error
corollaries do not need attainment: they also follow from erosion at
$\delta$ and monotonicity in the radius. The strict bound
$\varepsilon<d_E$ does use attainment.

The uniform translates of the tetrahedron-boundary grading
(`RankResolutionDegreeTwoSimplicial.translatedHomology`) have maximal grade
error exactly the translation gap $|t-s|$ (`supGradeError_translatedGrading`,
in `TDA.Persistence.FiniteSimplicialErosionTranslation`); erosion holds at that
gap, and both erosion distances are at most the exact interleaving distance
$\min(|t-s|,1/2)$ (`TDA.Persistence.FiniteSimplicialErosionExamples`). The
matching lower bound
is proved from actual structure maps in
`TDA.Persistence.FiniteSimplicialErosionTranslation`. For $s<t$,
$\varepsilon<t-s$ and $2\varepsilon<1$, test the diagonal pair at the earlier
birth plus $\varepsilon$ in every coordinate: the widened map of the earlier
translate is its birth map over the displacement $2\varepsilon<1$, which
survives, while the later translate has a zero fiber there. So erosion fails
at every radius below $\min(|t-s|,1/2)$, for both ranks
(`translatedHomology_not_rankErosion`, `translatedHomology_not_eRankErosion`),
and both erosion distances equal $\min(|t-s|,1/2)$, which is the
interleaving distance (`rankErosionDistance_translatedHomology`,
`eRankErosionDistance_translatedHomology`,
`rankErosionDistance_translatedHomology_eq_coordinateInterleavingDistance`).
The lower bound uses neither the interleaving distance nor attainment. These
hold over every field and every two real translations. The radius $1/8$
between the translates by $0$ and $1/4$ is a concrete failing radius, and the
certificate reads $1/8<1/4=1/4\le1/4$
(`translatedHomology_rankErosion_failure_certificate_eighth`); the examples
instantiate $\mathbb Q$ and the two-element field.

The same argument gives the exact erosion distance of the independent signed
coordinate translates `coordinateTranslatedHomology k u` and
`coordinateTranslatedHomology k v`
(`TDA.Persistence.FiniteSimplicialErosionCoordinateTranslation`). Their maximal
grade error is the coordinate gap $\max(|v_0-u_0|,|v_1-u_1|)$
(`supGradeError_coordinateTranslatedGrading`, valued in
`coordinateTranslationGap`). If $\varepsilon<v_i-u_i$ in one coordinate $i$
and $2\varepsilon<1$, test the diagonal pair at the $i$-th birth of the
$u$-translate plus $\varepsilon$ in every coordinate: the widened map of the
$u$-translate is its $i$-th birth map over the displacement $2\varepsilon$,
which survives, while the $v$-translate has a zero fiber there, because only
the $i$-th coordinate of the tested grade is below $v_i$. When the larger gap
is negative the roles are exchanged by symmetry. So erosion fails at every
radius below $\min(\max(|v_0-u_0|,|v_1-u_1|),1/2)$, for both ranks
(`coordinateTranslatedHomology_not_rankErosion`,
`coordinateTranslatedHomology_not_eRankErosion`), and both erosion distances
equal that value, which is the interleaving distance
(`rankErosionDistance_coordinateTranslatedHomology`,
`eRankErosionDistance_coordinateTranslatedHomology`). Again the lower bound
uses neither the interleaving distance nor attainment. Between the translates
by $0$ and by the vector with coordinates $1/8$ and $-1/4$ the gap $1/4$ is
attained in the negative second coordinate, the radius $1/8$ is a failing
radius, and the certificate reads $1/8<1/4=1/4\le1/4$
(`coordinateTranslatedHomology_rankErosion_failure_certificate_eighth`).

For one positive scale $s$ and two signed common delays $t,u$, the
scaled-translated modules `scaledTranslatedHomology k s hs t` and
`scaledTranslatedHomology k s hs u`
(`TDA.Persistence.FiniteSimplicialErosionScaledTranslation`) have maximal grade
error exactly the delay gap $|t-u|$ (`supGradeError_scaledTranslatedGrading`).
Write $T=\operatorname{scaledLifetime}(s)$, the larger of the two arm
lifetimes. If $\varepsilon<u-t$ and $2\varepsilon<T$, test the diagonal pair at
the birth of the longer arm of the $t$-delayed module plus $\varepsilon$ in
every coordinate: the widened map is that arm's map over the displacement
$2\varepsilon<T$, which survives, while the $u$-delayed module has a zero fiber
there, because the tested grade is below $u$ in the coordinate where the arm
is born at the delay. The shorter arm does not suffice in general: its widened
map can already be zero. When $u<t$ the roles are exchanged by symmetry. So
erosion fails at every radius below $\min(|t-u|,T/2)$, for both ranks
(`scaledTranslatedHomology_not_rankErosion`,
`scaledTranslatedHomology_not_eRankErosion`), and both erosion distances equal
$\min(|t-u|,T/2)$, which is the interleaving distance
(`rankErosionDistance_scaledTranslatedHomology`,
`eRankErosionDistance_scaledTranslatedHomology`). Again the lower bound uses
neither the interleaving distance nor attainment. Under the scale with
coordinates $1$ and $1/4$ the arm lifetimes are $1/4$ and $1/2$, so $T=1/2$;
between the delays $0$ and $1/2$ the radius $1/8$ is a failing radius at which
only the longer arm witnesses the failure, and the certificate reads
$1/8<1/4=1/4\le1/2$, with the maximal grade error strictly above the distance
(`scaledTranslatedHomology_rankErosion_failure_certificate_eighth`).

The scaled module `scaledHomology k s hs` itself, compared with the zero
module (`TDA.Persistence.FiniteSimplicialErosionScaling`), has interleaving
distance $T/2$ to zero (`coordinateInterleavingDistance_scaledHomology_zero`).
If $2\varepsilon<T$, test the diagonal pair at the birth of the longer arm plus
$\varepsilon$ in every coordinate: the widened map is that arm's map over the
displacement $2\varepsilon<T$, which survives, while every rank of the zero
module vanishes. So erosion against zero fails at every radius below $T/2$,
for both ranks (`scaledHomology_not_rankErosion_zero`,
`scaledHomology_not_eRankErosion_zero`), and both erosion distances to zero
equal $T/2$, which is the interleaving distance
(`rankErosionDistance_scaledHomology_zero`,
`eRankErosionDistance_scaledHomology_zero`). The lower bound uses neither the
interleaving distance nor attainment. Under the scale with coordinates $1$ and
$1/4$, $T=1/2$ and the radius $1/8$ is a failing radius at which only the longer
arm witnesses the failure. The fixture uses the general finitely presented
certificate, which needs no realization of the zero module as a finite
simplicial homology; the finite simplicial certificate would first require
exhibiting zero as such (for instance by a constant grading), which is not
attempted here. It gives $1/8<1/4=1/4$
(`scaledHomology_rankErosion_failure_certificate_zero_eighth`).

## Zero radius, zero distance and future extensions

`rankErosion_zero_iff` identifies the **predicate** `RankErosion 0 M N` with
equality of all weak-pair ranks. Consequently equal rank invariants give distance
zero. This theorem does not identify the infimum equation $d_E(M,N)=0$ with
that predicate, nor does it classify modules up to natural isomorphism. The
four assertions `RankErosion 0`, $d_E=0$, equal rank invariants and
isomorphism are related as follows.

- For all modules, `RankErosion 0` is equality of the ranks at all weak pairs
  (`rankErosion_zero_iff`), and it gives $d_E=0$
  (`rankErosionDistance_le_of_erosion`).
- For finite-dimensional fibers, isomorphic modules have $d_I=0$ and hence
  $d_E=0$ (`coordinateInterleavingDistance_eq_zero_of_iso`,
  `rankErosionDistance_le_coordinateInterleavingDistance`); the isomorphism is
  an interleaving at radius zero and gives `RankErosion 0`
  (`CoordinateInterleaving.ofIso`, `CoordinateInterleaving.rankErosion`).
- $d_E=0$ gives equal rank invariants for finitely presented modules
  (`GradedFree.finitelyPresented_rankErosionDistance_eq_zero_iff`). It does
  not for finite-dimensional fibers in general: the module supported at one
  grade has distance zero from the zero module
  (`closedBox_zero_distance_zero_and_ranks_differ`).
- Equal rank invariants do not give an isomorphism, also for finitely
  presented modules: in two parameters, ranks do not record how the images of
  maps from incomparable grades meet
  ([nonseparation](#fixed-radius-certificates-and-nonseparation)).
- For finitely presented modules, $d_I=0$ is isomorphism
  (`GradedFree.finitelyPresented_distance_eq_zero_iff_iso`).

The [extension proposal](https://github.com/uda-lab/tda-lib/issues/865)
separates several targets. Of these, the finite criterion, the executable
representations over the two-element field, the certified finite test, the
comparison of weak and strict pairs, the attainment theorem and the
certificates of the six preceding sections are supplied. The proposal's first
package, on conventions and exact thresholds, is supplied: the strict-pair
predicate, its two comparisons with the weak predicate and the equality of the
distances; erosion attainment for original finitely presented modules, with
the right-local isomorphisms taken from the presentation; the equivalence of
the two predicates at a fixed radius for finitely presented modules with at
least one coordinate; the certificate $\varepsilon<d_E\le d_I$ from a failed
test; and the boundary cases. The boundary cases are supplied in these forms:
the closed box $[0,2c]^n$ over $\mathbb Q$ against zero, for erosion and for
interleavings; with no coordinates, two modules with fibers of dimensions
three and two, not one copy of the field against zero; the two-parameter
nonseparation example over the two-element field, not over an arbitrary
field; and the record above of the implications between the zero-radius
assertions. A predicate on coordinatewise strict pairs, which the proposal
leaves optional, is not supplied. Of
the proposal's second package, the [extended image rank](#extended-image-rank)
and [erosion on it](#erosion-on-extended-ranks), with its interleaving bound,
are supplied, and so are the one-parameter q-tame consumer and
[local finite-image bound](#one-parameter-q-tame-modules-and-real-interleavings);
a multiparameter finite-image condition remains proposed, pending a choice of
strictness convention. Of the fourth package, erosion bounds and failed-test
certificates for [finite graded simplicial homology](#finite-graded-simplicial-homology)
are supplied, and so are the exact erosion distances of the uniformly,
coordinate- and scaled-translated families and of the scaled module against
zero. The other targets remain proposed:
finite tests fed by actual persistent-homology input; and execution over other
fields. The proposal
records endpoint and nonseparation counterexamples that a broader API must
respect, rather than promising to remove necessary hypotheses.

## Imports and source convention

Import `TDA.Persistence` for the public area API. Narrow imports are
`TDA.Persistence.RankErosion`, `TDA.Persistence.RankErosionInterleaving`,
`TDA.Persistence.RankErosionWitness`, `TDA.Persistence.RankErosionGrid`,
`TDA.Persistence.F2GridRep`, `TDA.Persistence.F2GridErosion`,
`TDA.Persistence.StrictRankErosion`,
`TDA.Persistence.RankErosionAttainment`,
`TDA.Persistence.RankErosionCertificate`,
`TDA.Persistence.StructureMapERank`, `TDA.Persistence.ERankErosion`,
`TDA.Persistence.ERankQTame`, `TDA.Persistence.FiniteSimplicialErosion`,
`TDA.Persistence.FiniteSimplicialErosionTranslation`,
`TDA.Persistence.FiniteSimplicialErosionCoordinateTranslation`,
`TDA.Persistence.FiniteSimplicialErosionScaledTranslation` and
`TDA.Persistence.FiniteSimplicialErosionScaling`. Their declarations are in
`TDA.Persistence`, except that the translated- and scaled-family results are in its
`RankResolutionDegreeTwoSimplicial` namespace; the concrete hook witnesses are in its
`RankErosionWitness` namespace, the grid criterion is in
`TDA.Persistence.CoordinateGrid`, and the executable representations are in
`TDA.Persistence.RatGrid` and `TDA.Persistence.F2GridRep`.
The strict-pair examples are in `TDA.Persistence.StrictRankErosionExamples`
the attainment examples in `TDA.Persistence.RankErosionAttainmentExamples` and
the certificate examples in `TDA.Persistence.RankErosionCertificateExamples`,
the extended-rank examples in `TDA.Persistence.StructureMapERankExamples`,
the extended-rank erosion examples in
`TDA.Persistence.ERankErosionExamples`, the q-tame examples in
`TDA.Persistence.ERankQTameExamples` and the simplicial examples in
`TDA.Persistence.FiniteSimplicialErosionExamples`;
the attainment and certificate theorems are in `TDA.Persistence.GradedFree`.
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

The comparison of the two library predicates, its boundary cases, the
finite-presentation erosion attainment, the fixed-radius equivalence, the
certificate, the nonseparation example and the extended image rank are
library derivations. No
theorem about strict pairs in this note is attributed to a numbered result of
the paper. See the [source record](references.md#Puuska17-v1).
