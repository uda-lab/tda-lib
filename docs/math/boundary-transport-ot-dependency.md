# Ordinary optimal transport and the finite-Radon boundary problem

The native boundary-plan infimum already equals the collapsed-space reservoir
infimum for arbitrary finite inputs. Identifying this value with an existing
ordinary Wasserstein API still needs a compatible optimal-transport package.
The library proves native finite-measure attainment, sharp triangle and
separation, and a literal mathlib coupling-norm formulation using the current
Lean/mathlib pin. The independently maintained ordinary Wasserstein interface
remains a separate dependency.

## Existing boundary-transport results

Let `H` be the strict birth–death half-plane, `δ(x) = (death − birth)/2`, and
`X = H ⊔ {*}` with collapsed metric

`ρ(x,y) = min(‖x−y‖∞, δ(x)+δ(y))`, `ρ(x,*) = δ(x)`.

For finite Borel measures `μ,ν` on `H`, choose finite `R ≥ μ(H)+ν(H)` and put
`μ_R = μ + (R−μ(H))δ_*`, with the interior measure pushed into `X`.
Both reservoir measures have total mass `R`. The topology on `X` is induced by
`ρ`; it is Polish and has the proved interior Borel identification.

For real `p ≥ 1`, the library proves equality between the infimum of full
powered boundary-plan costs and the infimum of `ρ^p` over **all** measures with
reservoir marginals `μ_R,ν_R`. This includes infinite competitor costs and
does not require atomic inputs. The capacity is independent of the chosen
admissible `R`; positive capacities admit probability normalization with the
factor `R^(1/p)`. Self, symmetry, finite-distance bounds from finite
`p`-persistence, the exact zero-target moment, and the native finite atomic
and indexed/coalesced bridges are also proved. The
[metric-law bridge](boundary-transport-metric.md) gives sharp triangle and
separation for every finite original measure, without a moment premise.
Finite moments make the extended distance finite.

The reservoir infimum has a native definition. The attainment theorem below
constructs general finite-input minimizers for that value and the boundary
value. Identification with a separately implemented ordinary Wasserstein
distance remains open. See [the exported contracts](../api.md#collapsed-boundary-geometry).

## Compatible API boundary

The library uses Lean **4.33.1** and mathlib
[`0df444a360eaa60ab8c11dca51a86af692955474`](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).
That source has no `IsCoupling`, `transportCost` or `wassersteinEDist`
declarations. It does provide the following relevant ingredients:

| Existing mathlib API | Contribution to the missing argument |
|---|---|
| `ProbabilityMeasure.continuous_map` | Prescribed marginal equations define a weakly closed set of probability plans. |
| `isTightMeasureSet_singleton` and `IsTightMeasureSet.prodMk` | All plans with fixed finite Polish marginals form a tight family. |
| `isCompact_closure_of_isTightMeasureSet` | Tight probability-plan families have compact closure. Closedness then gives compactness of the feasible set. |
| `FiniteMeasure.continuous_lintegral_boundedContinuousFunction` | The integral of each bounded continuous cost truncation is continuous under weak convergence. |
| `lintegral_iSup`, `lowerSemicontinuous_iSup` and `LowerSemicontinuousOn.exists_isMinOn` | Increasing truncations give a lower semicontinuous full cost and an attained minimum on a nonempty compact feasible set. |

Pinned sources: [probability maps](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean),
[tightness](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Tight.lean),
[Prokhorov](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Prokhorov.lean)
and [weak integral continuity](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean).
These ingredients are not a packaged coupling minimizer or a Wasserstein
triangle/separation theorem.

## TauCeti candidates

The [licensed OT source at `575dbdf`](https://github.com/TauCetiProject/TauCeti/tree/575dbdfaf4ae0df6e5bb35bb39e16458f028c91f/TauCeti/MeasureTheory/OptimalTransport)
and the [inspected main snapshot `6a7e27a`](https://github.com/TauCetiProject/TauCeti/tree/6a7e27a62b6dd48620f54667a7a9a9b3d24a2bda)
both pin Lean **4.36.0-rc1** and mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`. They are not directly compatible
with this project's pinned toolchain and mathlib. The first main-history
[`Wasserstein/Basic` snapshot](https://github.com/TauCetiProject/TauCeti/tree/1f12668e9c3a6a3af5b4fc3bbc429191cadee75a)
already pins Lean **4.34.0-rc2** and mathlib `03616a12cdf1e3f499349f69e80eee82b28745bc`.

The distinct [`releases/v4.33.0` snapshot](https://github.com/TauCetiProject/TauCeti/tree/300a11453493c8aed49d49a49409c79b8fd185c5)
pins Lean **4.33.0** and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
It contains gluing and multimarginal constructions, but no coupling/cost,
existence or Wasserstein modules. Its version name therefore does not supply
the required OT spine. No claim is made about every uninspected side branch
or independently maintained fork.

At `575dbdf`, the substantial ordinary APIs include:

| API | Exact role and relevant hypotheses |
|---|---|
| `IsCoupling` | The two raw measure marginals, expressed as `Measure.fst` and `Measure.snd`, agree with the prescribed measures. These match the native reservoir marginal equations. |
| `wassersteinEDist_rpow_eq_transportCost` and `wassersteinEDist_eq_transportCost_rpow` | Identify the `eLpNorm` infimum and the powered-integral infimum for a measurable ground extended distance and a finite nonzero ENNReal exponent. For real `p ≥ 1`, use exponent `ENNReal.ofReal p`. |
| `wassersteinEDist_smul` | Common finite nonzero measure scaling gives the factor `a^((1/p).toReal)`. Together with the native reservoir normalization, this supplies the requested probability convention. |
| `exists_isCoupling_eLpNorm_eq_wassersteinEDist` | Produces an actual optimizer on a complete second-countable Borel metric space for finite source mass, a finite nonzero exponent and existence of a coupling. Equal finite reservoir masses provide the last condition; an optimizer is not a caller premise. |
| `wassersteinEDist_triangle` and `wassersteinEDist_eq_zero_iff` | Sharp triangle uses standard-Borel gluing and finite intermediate mass. Separation uses a genuine metric, Polish/Borel hypotheses, finite source mass and finite nonzero exponent. |
| `exists_ae_mem_finset_wassersteinEDist_le` | On a separable pseudo-metric space with measurable opens and measurable singletons, approximates a probability law of finite moment at finite exponent `p ≥ 1` and nonzero ENNReal accuracy. The native same-mass theorem instead quantizes the original measure into interior values, preserving the common-reservoir mass constraint. |

Sources: [`Coupling`](https://github.com/TauCetiProject/TauCeti/blob/575dbdfaf4ae0df6e5bb35bb39e16458f028c91f/TauCeti/MeasureTheory/OptimalTransport/Coupling.lean),
[`Wasserstein/Basic`](https://github.com/TauCetiProject/TauCeti/blob/575dbdfaf4ae0df6e5bb35bb39e16458f028c91f/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean)
and [`FiniteSupport`](https://github.com/TauCetiProject/TauCeti/blob/575dbdfaf4ae0df6e5bb35bb39e16458f028c91f/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/FiniteSupport.lean).
The full spine includes general coupling and cost laws, weak compactness,
lower semicontinuity, kernel gluing and Wasserstein norm/metric arguments.
It is not a single theorem that can be imported independently of its package.

## Native finite-measure attainment

Attainment of the existing native reservoir value can be separated from that
full ordinary-OT dependency. Keep every auxiliary plan set on the already
proved space `X × X`. Normalize the two reservoirs to probability measures;
their product makes the feasible set nonempty. The pinned APIs above prove
its weak compactness. For the continuous cost `ρ^p`, the functions
`min(ρ^p,n)` are bounded continuous nonnegative functions increasing to the
full cost. Their weakly continuous integrals have the full integral as
supremum, so the full cost is lower semicontinuous, including at infinite
values. It therefore attains its minimum.

`exists_minimizing_reservoirPlan` produces an actual minimum for every
nonnegative real exponent and every finite positive full sum-capacity.
For `p ≥ 1` and arbitrary finite Borel `μ,ν`,
`exists_minimizing_boundaryPlan` then produces an admissible boundary
minimizing measure by the existing reverse construction and the proved
equality of infima. Choosing `R = μ(H)+ν(H)+1` handles zero inputs
without division by zero. Finite `p`-persistence is needed for finite cost,
not for existence of a minimizer whose value may be infinite.
`exists_finite_cost_minimizing_boundaryPlan` records this finite-cost
consequence. `exists_minimizing_boundaryPlan_rooted` gives one plan realizing
both powered and rooted values. Neither compact support nor a Euclidean
moment along the diagonal is required.

This is a fixed-space bridge to the native infimum. The boundary-transport lane adds no
generic coupling class, ordinary Wasserstein definition or gluing library. (The separate area
`TDA.Probability` defines `MeasureCoupling`, `measureTransportCost` and `measureWasserstein` on
`ProbabilityMeasure` with exact probability marginals for the sampled Rips laws; the
boundary-transport value is not identified with them.) The closed/tight-plan argument can be adapted from
[TauCeti `Compactness`](https://github.com/TauCetiProject/TauCeti/blob/575dbdfaf4ae0df6e5bb35bb39e16458f028c91f/TauCeti/MeasureTheory/OptimalTransport/Compactness.lean);
the specific continuous-cost truncation avoids importing its more general
lower-semicontinuous approximation layer. Compactness and a minimizing
coupling are proved internally, not requested as caller premises.

The consumers include a nonatomic uniform band of bars `(t,t+2)` and the
countable law with weights `2^(−n−1)` at `(2^(n+2),2^(n+2)+2)`. Both have
total mass one and diagonal moment one at every real exponent. The latter
has divergent first birth-coordinate moment and gives positive mass outside
every compact subset of `H`. Sending its mass to the fixed diagonal point
`(0,0)` is an admissible infinite-cost competitor at `p=1`, while an attained
optimum has cost one. Thus finite optimal cost is compatible with infinite
competitor costs.

The native metric laws use existing current-pin APIs directly.
`Measure.condKernel`, `Measure.disintegrate` and `Measure.fst_compProd`
glue finite minimizing plans on the fixed space; measurable kernel sections
identify the second prescribed pair marginal. `eLpNorm_add_le` gives the sharp
triangle estimate at a common full sum-capacity for all three pairs. A
zero-cost actual optimizer has equal endpoints almost everywhere, which
proves separation by equality of interior restrictions. The norm bridge
expresses both the unnormalized reservoir value and its probability scaling
as literal infima of mathlib `eLpNorm` over all marginal equations. This lane adds no generic
coupling class, Wasserstein definition or general gluing API, and no identification with
`TDA.Probability.measureWasserstein` is claimed.
Native [same-mass finite atomic approximation](boundary-transport-approximation.md)
is proved directly using the current-pin metric `SimpleFunc.approxOn` and
dominated convergence. Every target is chosen in the interior image;
quantizing only the original measure preserves its mass and leaves the
common boundary reservoir padding unchanged. No ordinary Wasserstein
finite-support theorem is needed for this native endpoint.

For identification with an independently maintained ordinary Wasserstein API,
the recommended dependency decision is a reviewed external backport of its
required closure to this exact Lean/mathlib pin, with compilation and axiom
validation. Merely selecting the older release branch is insufficient.
A project-wide toolchain/mathlib upgrade is a different dependency decision;
none is made here. The native attainment, metric laws and literal coupling-norm
forms do not depend on that choice.

## Source-use boundary

The inspected TauCeti code is [Apache-2.0 licensed](https://github.com/TauCetiProject/TauCeti/blob/575dbdfaf4ae0df6e5bb35bb39e16458f028c91f/LICENSE).
A source adaptation must retain its applicable notices and identify the
source revision and modifications. Code availability does not certify a
compiled backport or authorize a dependency change.

The corrected Divol–Lacombe article has a separate, unresolved article-text
AI-input/reuse condition in [#505](https://github.com/uda-lab/tda-lib/issues/505).
Open-access metadata does not establish that permission. The native contract
and the route above use the repository's mathematical digest and licensed
Lean sources; they do not claim a new comparison with the article body.
