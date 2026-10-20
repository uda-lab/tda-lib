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
exponent an actual feasible plan attains both quantities, and the rooted value
also equals the infimum of rooted plan costs. The optimizer may change with `p`.

Every feasible entry lies between zero and its source mass. The marginal
inequalities define a closed subset of the finite product of those compact
intervals. The objective is continuous affine in the matrix. This proves
attainment by the extreme value theorem, including zero masses and empty
types; it requires no supplied optimizer or compactness certificate.

## Compatibility and actual consumers

When every label has mass one, plan conversion in both directions proves exact
equality with `finitePowerBoundaryTransportCost` and
`finitePBoundaryTransportCost`. Arbitrary real-weight optimizers are not claimed
to be incidence matchings. Both optimized quantities are invariant under
exchanging the two inputs and under equivalently relabelling coordinates and
masses together.

If the target is empty, the powered optimum is exactly
`Σ_i w(i)d(i)^p`; the source-empty formula uses `Σ_j v(j)e(j)^p`.
Zero total mass gives zero cost even when labels and their coordinates are
present. The actual `FiniteWeightedDiagram.powerBoundaryTransportCost` and
`pBoundaryTransportCost` use the diagram's finite support, inherit attainment,
and give these same weighted diagonal moments against the zero diagram.

The examples include a source of mass `3/2` at `(0,2)` and a target of mass
`1/2` at `(3/2,7/2)`. Every feasible plan transports a scalar
`t∈[0,1/2]` and has cost `2+t((3/2)^p−2)`. At `p=1`, the minimum is `7/4`
at `t=1/2`; at `p=2`, the powered minimum is `2` at `t=0`. The first
optimizer has second-powered cost `17/8`, so reusing it would be incorrect.
Other examples exercise an actual split to two distinct targets, zero-weight
labels, empty inputs, repeated unit occurrences, and fractional masses in the
positive weighted-diagram object.

## Sources and scope

Figalli–Gigli introduced boundary transport in their original bounded-domain
setting. [Divol–Lacombe, corrected v4](references.md#DL20-v4), Definition 2.1
and §3.2 Lemma 3.2, supply the persistence-measure setting and the pair,
deletion and insertion cost families used here. The library proves a finite
real-weight reservoir adaptation with maximum ground norm. Finite-product
compactness and the extreme value theorem are taken from the pinned mathlib.
This does not establish a conversion to every Radon coupling, the full
collapsed-metric identification of Proposition 3.7, or infinite-diagram theory.

The existing unit-occurrence exponent limits remain unchanged. The weighted
extension here proves neither an exponent limit nor uniformity over arbitrary
positive weights. Such uniformity cannot follow from bounded point count and
total mass alone. Under the support-based bottleneck convention of
Divol–Lacombe §3.3, a half-lifetime-one atom of mass `w>0` has bottleneck one
against zero, while its rooted finite-exponent cost is `w^(1/p)`.
