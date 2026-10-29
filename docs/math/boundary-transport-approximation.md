# Same-mass finite weighted approximation

Let `H` be the strict birth–death half-plane, with diagonal distance
`δ(x) = (death − birth)/2`. For real `p ≥ 1`, every finite Borel measure `μ`
on `H` satisfying

`∫ δ(x)^p dμ(x) < ∞`

can be approximated arbitrarily closely in native boundary transport by
`atomicMeasure D`, for a native `FiniteWeightedDiagram D`, a finitely
supported nonnegative weight function on `H`, of exactly the same total
mass. Here `BT_p` is the reciprocal-p root of the native all-boundary-plan
powered infimum. The approximants also form a sequence converging in `BT_p`.
The input can be nonatomic or have noncompact support; no Euclidean moment
along the diagonal is required. The zero measure is included.

The public theorem `exists_atomicMeasure_approx_same_mass` gives the
arbitrary-accuracy diagram. `quantizedDiagram μ n` is an actual native
approximation sequence; `quantizedDiagram_mass` preserves mass at every
index, and `boundaryTransportPowerValue_quantizedDiagram_tendsto` and
`boundaryTransportDistance_quantizedDiagram_tendsto` prove powered and
rooted convergence. `quantizedDiagram_zero` identifies every zero-input
approximant with the zero diagram.

## Quantizers and native coefficients

A measurable finite-valued map `T : H → H` partitions the input into its
fibres. Give each value `y` the coefficient `μ(T⁻¹ {y})`. These coefficients
are finite because the original measure is finite. The existing indexed
coalescing constructor forms a native diagram from this finite family,
including zero coefficients. Its canonical atomic measure is exactly
`μ.map T`. In particular, its total mass is `μ(H)`, rather than a normalized
probability mass or the mass of an augmented reservoir.

The quantizers are chosen using the existing collapsed space `X = H ⊔ {*}`
with metric

`ρ(x,y) = min(‖x−y‖∞, δ(x)+δ(y))`, `ρ(x,*) = δ(x)`.

The interior image `H → X` is dense. Pinned mathlib's metric
`SimpleFunc.approxOn` can take all its values in that image, with one fixed
interior basepoint of depth one. Pulling those values back to `H` gives
finite-valued measurable `T_n : H → H`, with
`ρ(x,T_n(x)) → 0` pointwise. Each target is an interior point from the
outset: the finite approximants carry no boundary atom whose mass would
have to be discarded or added to the original measure.

## Cost convergence and capacity

The nearest-point bound supplied by `approxOn` gives

`ρ(x,T_n(x)) ≤ 1 + δ(x)`.

For `p ≥ 1`, the powered errors are therefore bounded by
`2^p (1 + δ(x)^p)`. This function is integrable using both finite original
mass and finite diagonal p-persistence. Dominated convergence gives

`∫ ρ(x,T_n(x))^p dμ(x) → 0`.

Let `m = μ(H)` and fix one capacity `R = 2m+1`. Since every target measure
has mass `m`, this satisfies the full sum-of-masses condition for every
pair, including `μ = 0`. Push `μ` along `x ↦ (x,T_n(x))` into `X × X`
and add `(R−m)δ_(*,*)`. This is a genuine competitor with the two required
reservoir marginals, and its powered cost is the displayed error integral.
The existing all-competitor reservoir/boundary comparison bounds the native
boundary infimum by this cost. Taking reciprocal-p roots yields convergence
in `BT_p` and hence the arbitrary-accuracy approximant with unchanged mass.
Neither an approximating measure nor an optimizer is a caller premise.

Finite original mass matters here: it controls the constant term in the
dominating function. A locally finite input of infinite original mass is
outside this theorem even when its diagonal persistence moment is finite.

## Sources and remaining scope

The construction consumes pinned mathlib's
[`SimpleFuncDense`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/SimpleFuncDense.lean)
and [dominated convergence](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/DominatedConvergence.lean),
together with the proved native coalescing, atomic-measure and reservoir
comparison APIs. It requires no additional OT package or toolchain change.
Mathematical correspondence is to the repository contract in
[#505](https://github.com/uda-lab/tda-lib/issues/505); the corrected article's
separate AI-input/reuse condition remains unresolved, and no article-body
comparison is claimed.

This is same-original-mass approximation by the canonical native atomic
constructor. Ordinary Wasserstein API identification remains the other open endpoint in the
[dependency map](boundary-transport-ot-dependency.md); the sharp native triangle inequality and
separation are proved in [the metric laws](boundary-transport-metric.md)
(`boundaryTransportDistance_triangle`, `boundaryTransportDistance_eq_zero_iff`).
