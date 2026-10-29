# Finite real-weight boundary transport

A finite weighted diagram assigns a nonnegative real mass to each of finitely
many points `(b,d)` with `b<d`. Its coefficients need not be integers or sum to
one. `FiniteWeightedDiagram` represents these masses by a finitely supported
function on the strict upper half-plane, so a zero coefficient creates no
support point. This object has no essential bars.

The supporting indexed construction also accepts arbitrary finite coordinate
families `x : I → ℝ × ℝ` and `y : J → ℝ × ℝ`, with masses
`w : I → ℝ≥0` and `v : J → ℝ≥0`. Repeated coordinates retain their labelled
masses. Raw coordinates need not have positive lifetime; that broader algebraic
interface is distinct from the positive weighted-diagram object.

## Plans and costs

A plan is a real matrix `a` satisfying

```text
a(i,j) ≥ 0,    Σ_j a(i,j) ≤ w(i),    Σ_i a(i,j) ≤ v(j).
```

Its deletion mass is `w(i)−Σ_j a(i,j)` and its insertion mass is
`v(j)−Σ_i a(i,j)`. Both are nonnegative. The zero matrix is feasible, including
when either label type is empty or the two total masses differ.

For real `p≥1`, let `c(i,j)` be the existing maximum-norm distance between the
two coordinates, and let `d(i)` and `e(j)` be their distances to the diagonal,
namely `|death−birth|/2`. The powered cost is

```text
C_p(a) = Σ_i Σ_j a(i,j)c(i,j)^p
       + Σ_i (w(i)−Σ_j a(i,j))d(i)^p
       + Σ_j (v(j)−Σ_i a(i,j))e(j)^p.
```

Mass coefficients remain linear. `weightedPowerBoundaryTransportCost` takes
the infimum over every feasible real matrix, and
`weightedPBoundaryTransportCost` takes its reciprocal-`p` root. At each fixed
exponent a feasible plan attains both quantities, and the rooted value
also equals the infimum of rooted plan costs. The optimizer may change with `p`.

Every feasible entry lies between zero and its source mass. The marginal
inequalities define a closed subset of the finite product of those compact
intervals. The objective is continuous affine in the matrix. This proves
attainment by the extreme value theorem, including zero masses and empty
types; it requires no supplied optimizer or compactness certificate.

## Compatibility and consumers

When every label has mass one, plan conversion in both directions proves exact
equality with `finitePowerBoundaryTransportCost` and
`finitePBoundaryTransportCost`. Arbitrary real-weight optimizers are not claimed
to be incidence matchings. Both optimized quantities are invariant under
exchanging the two inputs and under equivalently relabelling coordinates and
masses together.

If the target is empty, the powered optimum is exactly
`Σ_i w(i)d(i)^p`; the source-empty formula uses `Σ_j v(j)e(j)^p`.
Zero total mass gives zero cost even when labels and their coordinates are
present. The `FiniteWeightedDiagram.powerBoundaryTransportCost` and
`pBoundaryTransportCost` use the diagram's finite support, inherit attainment,
and give these same weighted diagonal moments against the zero diagram.

The examples include a source of mass `3/2` at `(0,2)` and a target of mass
`1/2` at `(3/2,7/2)`. Every feasible plan transports a scalar
`t∈[0,1/2]` and has cost `2+t((3/2)^p−2)`. At `p=1`, the minimum is `7/4`
at `t=1/2`; at `p=2`, the powered minimum is `2` at `t=0`. The first
optimizer has second-powered cost `17/8`, so reusing it would be incorrect.
Other examples exercise a split to two distinct targets, zero-weight
labels, empty inputs, repeated unit occurrences, and fractional masses in the
positive weighted-diagram object.

## Repeated indexed coordinates

Write `H` for the strict birth–death half-plane. Coalescing into a native
weighted diagram uses a finite indexed family `x : I → H`, with nonnegative
real masses `w : I → ℝ≥0`. Coordinates may repeat and masses may vanish.
`FiniteWeightedDiagram.ofIndexed w x` assigns the coefficient

```text
D(q) = Σ_{i : x(i)=q} w(i).
```

It preserves total mass: coincident occurrences contribute their combined
coefficient, and zero-weight labels add no support point. The coefficient-sum
identity also holds after multiplying by any real function of the coordinate.

`FiniteWeightedCoalescing` uses a proportional splitting kernel from a support
point `q` of `D` to the original labels:

```text
K(q,i) = w(i)/D(q) if x(i)=q, and 0 otherwise.
```

Every denominator is positive because `q` belongs to the native support.
For each such `q`, the sum over `i` is one; for each original label `i`,
`Σ_q D(q)K(q,i)=w(i)`. These identities include zero-weight labels and empty
input types.

Let `E` be the coalesced target diagram, with splitting kernel `L`. The plan map
`FiniteWeightedBoundaryPlan.aggregate` sums matrix entries over each pair of
coordinate fibers. The map `splitLift` assigns a coalesced matrix `b`
to the original labels by

```text
a(i,j) = Σ_q Σ_r K(q,i) b(q,r) L(r,j).
```

Here `q` and `r` range over the two finite native supports.

Both maps produce feasible matrices and preserve the full pair, deletion and
insertion cost for every real exponent. The powered infima therefore agree,
as do the values obtained by taking their reciprocal-`p` roots. The
infimum-of-rooted-cost interpretation uses the existing `p≥1` domain. Powered
and rooted optimizers transfer in both directions, and the finite attainment
theorems supply optimizing plans without a caller providing one. Splitting and
then aggregating recovers each coalesced matrix entry. Several indexed matrices
can share the same aggregate; the lift selects a proportional allocation within
each fiber.

With unit input masses, these identities recover the existing finite
unit-occurrence transport and matching values. A proportional lift can have
fractional entries even for unit masses. The existing integral-optimizer
theorem supplies a matching optimizer as a separate choice.

## Atomic measures and all boundary plans

For a native diagram `D`, `BoundaryTransport.atomicMeasure D` places mass
`D(x)` at each support point `x`. A sum of coefficients at the same point
therefore gives one atom with their combined mass. The measure has finite total
mass, with no integrality or probability normalization requirement.

`BoundaryTransportAtomic` converts every feasible native matrix into a Borel
boundary plan by combining its interior-pair atoms with nearest-diagonal
deletion and insertion atoms. Its integral powered cost is exactly the matrix
cost. In the other direction, take any Borel boundary plan between the two
atomic measures. The masses of its interior singleton pairs define a feasible
matrix. The remaining row and column masses are exactly its deletion and
insertion masses. Moving those boundary endpoints to the nearest diagonal
points can only reduce their charges for a nonnegative exponent. The argument
retains extended nonnegative integral values, so a competitor may have infinite
cost or continuously distributed, non-nearest diagonal endpoints.

Consequently `boundaryTransportPowerValue_atomic_eq_native` identifies the
infimum over all such plans with
`ENNReal.ofReal (FiniteWeightedDiagram.powerBoundaryTransportCost p D E)`
for `p≥0`. For `p≥1`, the rooted values agree as well. Applying the native finite attainment theorem
constructs a genuine minimizing Borel plan. The coalescing laws identify this
same native optimum with the indexed weighted objective, including repeated
coordinates and zero masses.

`BoundaryTransport.atomicMeasure_ofIndexed` identifies that measure with the
original indexed sum of weighted Dirac measures. Its powered and rooted
all-Borel values equal the indexed weighted values for `p≥0` and `p≥1`,
respectively. An indexed optimizer gives a minimizing Borel plan by aggregation
followed by the native atomic-plan construction. Unit masses recover the
existing finite matching quantities through their unit-transport compatibility.

## Sources and scope

Figalli–Gigli introduced boundary transport in their original bounded-domain
setting. [Divol–Lacombe, corrected v4](references.md#DL20-v4), Definition 2.1
and §3.2 Lemma 3.2, supply the persistence-measure setting and the pair,
deletion and insertion cost families used here. The library proves a finite
real-weight reservoir adaptation with maximum ground norm. Finite-product
compactness and the extreme value theorem are taken from the pinned mathlib.
The atomic bridge compares every Borel boundary plan for native finite
diagrams. Minimizing plans for general finite Borel inputs and `p ≥ 1` are proved separately
(`BoundaryTransport.exists_minimizing_boundaryPlan`, see
[the OT dependency map](boundary-transport-ot-dependency.md)); ordinary Wasserstein API
integration and infinite-diagram theory remain outside this result.

The existing unit-occurrence exponent limits remain unchanged. The weighted
extension here proves neither an exponent limit nor uniformity over arbitrary
positive weights. Such uniformity cannot follow from bounded point count and
total mass alone. Under the support-based bottleneck convention of
Divol–Lacombe §3.3, a half-lifetime-one atom of mass `w>0` has bottleneck one
against zero, while its rooted finite-exponent cost is `w^(1/p)`.
