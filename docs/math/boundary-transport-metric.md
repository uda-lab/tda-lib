# Metric laws for finite boundary measures

Boundary transport separates finite positive measures on the strict birth–death
half-plane and satisfies the sharp triangle inequality. Finite diagonal
`p`-persistence makes its extended distance finite. Its reservoir comparison
also has the literal coupling `L^p`-norm form, including probability scaling.

## Measures, distance and common capacity

Write `H = {(b,d) ∈ ℝ² : b < d}` and `δ(b,d) = (d−b)/2`. The collapsed space
`X = H ⊔ {*}` has metric

`ρ(x,y) = min(‖x−y‖∞, δ(x)+δ(y))`, `ρ(x,*) = δ(x)`.

The native boundary distance `BT_p(μ,ν)` is the reciprocal-`p` root of the
infimum of full ground costs over all boundary plans with interior marginals
`μ,ν`. The diagonal marginals are free. For finite original measures and
finite `R ≥ μ(H)+ν(H)`, the reservoir measures

`μ_R = μ + (R−μ(H))δ_*`, `ν_R = ν + (R−ν(H))δ_*`

have common mass `R`; interior measures are pushed into `X`. The proved
all-competitor comparison identifies the native powered infimum with the
infimum of `∫ρ^p dγ` over every measure `γ` with these reservoir marginals.
Original masses may be unequal or zero. No Euclidean moment along the
diagonal or compact-support condition is imposed.

## Literal coupling norm and normalization

For real `p > 0`, `eLpNorm_dist_eq_collapsedPowerCost` identifies mathlib's
`eLpNorm (fun z => dist z.1 z.2) (ENNReal.ofReal p) γ` with
`(∫ρ^p dγ)^(1/p)`. Positive reciprocal powers preserve arbitrary infima,
including empty competitor families and infinite values.
`eLpNorm_edist_eq_dist` identifies the extended-metric norm used in the
coupling formulas with the real-distance norm. Consequently
`reservoirDistance_eq_iInf_eLpNorm` expresses the native reservoir value as
the infimum of those actual norms over the two marginal equations.

For `p ≥ 1` and the full finite capacity above,
`boundaryTransportDistance_eq_iInf_eLpNorm` gives the same expression for
`BT_p`. If also `R > 0`,
`boundaryTransportDistance_eq_normalized_iInf_eLpNorm` proves

`BT_p(μ,ν) = R^(1/p) inf { ‖ρ‖_(L^p(γ)) : γ₁=μ_R/R, γ₂=ν_R/R }`.

The two normalized marginals are probability measures by
`normalizedReservoirPair_isProbability`. The factor uses the reservoir's
total mass, not the original mass of either input. These statements use
mathlib's existing norm and literal measure-marginal equations; they do not
install an independently maintained Wasserstein package.

## Sharp triangle and separation

For every real `p ≥ 1` and arbitrary finite original Borel measures,
`boundaryTransportDistance_triangle` proves

`BT_p(μ,κ) ≤ BT_p(μ,ν) + BT_p(ν,κ)`.

One capacity `R = μ(H)+ν(H)+κ(H)+1` is valid for all three pairs. Actual
reservoir minimizing plans exist by `BoundaryTransportAttainment`. A private
construction on this fixed collapsed space glues their common middle
marginal using mathlib's finite-measure conditional kernel and measure-kernel
composition. The resulting endpoint plan is a genuine competitor. Applying
the pointwise metric triangle and mathlib's `eLpNorm_add_le` to the glued
measure gives coefficient one. A gluing law or minimizing plan is never a
caller premise, and infinite optimal or competitor costs remain allowed.

`boundaryTransportDistance_eq_zero_iff` proves

`BT_p(μ,ν) = 0 ↔ μ = ν`.

An actual zero-cost reservoir optimizer has equal endpoints almost
everywhere, so its marginals agree. Restricting those marginals to the
interior gives equality of the original measures. Conversely an identity
boundary plan has zero cost. Neither this result nor the extended triangle
requires finite persistence moments. Finite `p`-persistence supplies
finiteness through `boundaryTransportDistance_lt_top`; together with the
existing self and symmetry laws these are the finite-distance metric laws.

## Native consumers and capacity countercontrol

Two far unit atoms, each of diagonal distance one, have native powered cost
two at `p=2`. Reservoir capacity two recovers that value. At capacity one,
every feasible plan is concentrated on the far point pair, and its powered
cost is four. Thus a capacity bound using only the maximum original mass
does not give the boundary value. The fixture computes the whole wrong
capacity infimum, rather than merely one expensive competitor.

Translated unit bars realize equality in the triangle inequality. Combining
the metric laws with same-original-mass finite atomic approximation bounds
the error in a distance by the sum of the two approximation errors. These
consumers use the existing `atomicMeasure` constructor and its proved native
finite matching compatibility.

## Correspondence boundary

This argument follows the mathematical contract in
[#505](https://github.com/uda-lab/tda-lib/issues/505), existing native
comparison and attainment, and the current pinned mathlib sources. It is a
fixed-space bridge, with no new general optimal-transport definitions.
Identification with a separately maintained ordinary Wasserstein API and the
authorized corrected-article comparison remain unresolved in the
[dependency and source-use map](boundary-transport-ot-dependency.md).
