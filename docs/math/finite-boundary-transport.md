# Finite first-order boundary transport

For finite persistence diagrams with finite deaths, allowing real mass to split
between occurrence labels does not lower the first-order partial-matching
minimum. The transport problem here uses a boundary reservoir, unit input mass
per occurrence, and the birth–death maximum norm. An integral plan attains its
infimum, although fractional plans can also attain it.

## Occurrences, real plans and costs

Let `x : I → ℝ × ℝ` and `y : J → ℝ × ℝ`, with finite, possibly empty label types.
For the persistence-diagram interpretation every pair has birth < death. Births
may be negative; all coordinates are real, and essential bars are absent. Equal
point values keep their separate labels and contribute unit mass each. The
supporting real-cost algebra also holds without the positive-lifetime condition.

Write `c(i,j) = ‖x i - y j‖∞` and `δx(i) = |death(x i)-birth(x i)|/2`, with the
analogous `δy`. These are the existing `finitePairCost` and `diagonalCost`, converted
to real numbers. `diagonalCost_le_max` proves that every diagonal destination costs
at least `δx`; `diagonalCost_midpoint` proves attainment at the midpoint.

A `FiniteBoundaryPlan I J` is a real matrix `a` whose entries are nonnegative and
whose row and column sums are at most one. Its residual masses are

```text
u(i) = 1 - Σⱼ a(i,j),     v(j) = 1 - Σᵢ a(i,j).
```

`deletionMass_nonneg`, `insertionMass_nonneg`, `source_balance` and `target_balance`
verify the residual signs and the unit marginal equations. Sources may send their
residual mass to the boundary; targets may receive theirs from it. No equality of
the two input cardinalities is assumed. Every feasible real matrix is admitted,
including fractional ones.

The plan's `cost` is the unnormalized sum

```text
C(a) = Σᵢⱼ a(i,j)c(i,j) + Σᵢ u(i)δx(i) + Σⱼ v(j)δy(j).
```

The all-zero matrix is feasible, and `cost_nonneg` bounds all candidate costs below
by zero. `finiteFirstOrderBoundaryTransportCost x y` is their real infimum. Neither
the input mass nor the cost is normalized by a cardinality.

## Equality and attainment

`finiteFirstOrderBoundaryTransportCost_eq_matchingCost` proves

```text
finiteFirstOrderBoundaryTransportCost x y = finiteFirstOrderMatchingCost x y.
```

The right side is the [attained finite partial-matching minimum](finite-first-order-matching.md).
`ofMatching` embeds its partial injections as 0–1 incidence plans, and
`cost_ofMatching` preserves their paired and both unmatched costs exactly.
The converse inequality, `matchingCost_le_cost`, quantifies over every feasible
real plan. Consequently `exists_minimizing_boundaryPlan` supplies an actual
incidence-plan minimizer, and `exists_matching_cost_le` supplies a partial matching
of no greater cost than any given plan. These are noncomputable existence results;
no numerical optimization algorithm is supplied.

Exact one-empty and both-empty formulas and invariance under arbitrary label
equivalences follow from the equality. The matching distance laws and existing PI
bounds can likewise be used by rewriting; their hypotheses and constants remain
those of their original APIs.

## Boundary augmentation and the fractional inequality

Use rows `I ⊕ J` and columns `J ⊕ I`. The first summands are actual occurrences;
the second are dummies labelled by the opposite diagram. The raw cost blocks are

```text
             target J       source dummies I
source I     c(i,j)          δx(i)
target       δy(j)           0
dummies J
```

The deletion block is constant across each entire source row, and the insertion
block across each entire target column. A dummy with a different label is allowed
at exactly the same boundary cost.

`OccurrenceMatching.ofBoundaryAssignment` restricts any augmented bijection to
its actual-to-actual partial injection. `totalFiniteCost_ofBoundaryAssignment`
proves exact cost preservation by reindexing the dummy charges: an unmatched target
has precisely a dummy predecessor. `toBoundaryAssignment` completes a partial
matching using its reverse: unmatched sources use their own dummies, unmatched
target dummies go to their actual targets, and matched target dummies go to the
dummies of their matched sources. Restriction of this completion is the original
matching. This is a section, not a bijection of representations; other dummy
permutations can encode the same partial matching.

For a real plan, the augmented mass matrix is

```text
D(a) = [ a           diag(u) ]
       [ diag(v)     aᵀ      ].
```

Each row and column sums to one. `paddedMatrix` reindexes columns by `Equiv.sumComm`
so that `paddedMatrix_doublyStochastic` has one square index type. The linear cost
of this matrix is exactly `C(a)`; its lower-right block has zero cost.

The pinned mathlib theorem `exists_eq_sum_perm_of_mem_doublyStochastic` expresses
the padded matrix as a finite convex combination of permutation matrices, including
the empty-index case. Each permutation restricts to a partial matching with the
same cost, so each cost is at least the matching minimum. Applying the linear cost
to the convex combination gives that lower bound for `C(a)`. The incidence plan of
an already minimizing matching proves the reverse inequality and attainment.

## Concrete controls

The examples compile against the actual definitions:

- For `(0,2)` and `(0,4)`, sending mass `1/2` between them leaves boundary mass
  `1/2` on each side and costs `5/2`. Pairing costs `2`; deleting both costs `3`.
- For `(0,2)` and `(10,12)`, deleting both costs `2`, while pairing costs `10`.
  The raw cost after collapsing the boundary therefore fails the triangle inequality.
- An augmented permutation deletes a source through a differently labelled dummy
  and inserts a target from a differently labelled dummy. Their costs are `1` and
  `3`, with one additional actual pair of cost zero.
- Two source copies and one target copy of `(0,2)` have minimum `1`. Sending half
  of each source to the target is a fractional optimum, alongside an integral
  optimum. Removing duplicate occurrences would change this result.
- Empty inputs, both one-empty directions, empty padding, completion's section
  identity, and label reindexing are also checked.

## Primary-source correspondence and limits

[Figalli–Gigli](references.md#FG10), Problem 1.1, has priority for boundary-reservoir
transport. Its original domain is bounded and open in Euclidean space and its cost
is quadratic Euclidean distance. This library result does not attribute the later
upper-half-plane, general-p or maximum-norm setting to that manuscript.

[Divol–Lacombe corrected v4](references.md#DL20-v4), formula (1), separates the
matching exponent from the ground norm; the present choice is p=1, q=∞.
Definition 2.1 and §3 develop measure transport on the unbounded upper half-plane.
Proposition 3.2's proof invokes the finite result of
[Lacombe–Cuturi–Oudot](references.md#LCO18-v2), Proposition 1 and Supplement §7.1.
Their boundary augmentation and assignment argument is the proof pattern used
here. Their displayed norm is tied to p; its use here with ground norm ∞ is a
library adaptation justified by the explicit cost-matrix argument.

Equality of the finite reservoir optimization with all Borel/Radon couplings on the
closed upper half-plane is not proved. That bridge must aggregate and split
repeated occurrences and compare arbitrary boundary destinations with the diagonal
cost. Divol–Lacombe's formula (20) and Proposition 3.7 use a shortened quotient
metric; the raw cost blocks above do not supply an ordinary metric Wasserstein
interpretation. [Real-exponent powered costs](finite-p-boundary-transport.md) separately
reuse this assignment argument for finite p≥1 and take roots after optimization.
General-p metric laws, essential bars, noninteger input masses, infinite diagrams,
completeness and barycenters remain outside these finite-plan results. Fractional
transported mass does not change the unit input mass per occurrence.
