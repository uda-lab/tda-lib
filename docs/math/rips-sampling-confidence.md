# Finite-sample confidence for Rips diagrams

A finite random sample can miss part of the support of its distribution. A finite
cover converts this geometric failure into a union of events with explicit iid
probabilities. Rips stability then bounds the probability that the sample's
persistence diagram is far from the diagram of the support itself.

## Objects and assumptions

Let `K` be a nonempty compact metric space and let `μ` be a Borel probability
measure with support equal to `K`. Fix a field `k` and a homological degree
`q ≥ 0`. Write `D_q(K)` for the canonical locally finite decorated diagram of
the existing Rips persistence module. Rips time is diameter: an edge enters at
its length. The diagram includes essential bars.

Draw an ordered tuple of `n ≥ 1` independent points with law `μ`. Its finite
range `S_n` is the sample metric space. Repeated draws give one vertex in this
range; the sampling law remains the product measure with replacement.

For `r > 0`, choose a finite nonempty set `C ⊆ K` whose open balls of radius
`r/2` cover `K`, and put

\[
  \beta=\min_{c\in C}\mu(B(c,r/2)).
\]

Full support and the positive radius imply `0 < β ≤ 1`. Compactness guarantees
that such a finite cover exists. The cover and its ball masses are fixed inputs,
not estimates computed from the observed tuple.

## Probability bound

The confidence estimate is

\[
 \mathbb P\!\left[d_B(D_q(S_n),D_q(K))>2r\right]
 \le |C|(1-\beta)^n.
\]

The probability is taken under `iidMeasure μ n`. The formal inequality uses
extended nonnegative reals, so all measures and finite products have their
ordinary probability interpretation without converting infinite values to zero.

An ambient formulation starts with a Borel probability measure on a separable
metric space and assumes its support is compact. The support has full measure,
and restriction to its subtype gives a probability law with the same ambient
pushforward. Almost every tuple lies in the support. The ambient separability
condition supplies the conull-support fact; compactness of the support by itself
is not used as a substitute for that fact in an arbitrary metric space.

## Proof and measurability

For each center `c`, the event that every draw misses `B(c,r/2)` has probability
`(1 − μ(B(c,r/2)))^n`. These events are measurable finite product boxes.
The finite union bound gives the sum of their probabilities, bounded by
`|C|(1 − β)^n`.

If every cover ball is hit, each point of `K` is within `r` of a sampled point:
go first to a cover center and then to a draw in its ball. Since the sample lies
in `K`, its Hausdorff distance from `K` is at most `r`. The existing q-tame Rips
Hausdorff theorem gives the factor-two diagram bound.

The actual diagram-distance event is measurable independently of this inclusion.
The locally finite bottleneck distance satisfies symmetry and the triangle
inequality, obtained by reversing and composing occurrence matchings. It defines
an extended pseudometric because endpoint decorations are ignored by the cost.
The sample-diagram map is two-Lipschitz for the tuple maximum metric, hence
continuous; distance to the fixed target diagram is consequently measurable.

## Source relationship

[Fasy et al., Lemma 4 and its proof](https://arxiv.org/html/1303.7117v3)
use finite-cover miss probabilities to control Hausdorff error, then specialize
to manifold covering and mass estimates. The result here retains the explicit
finite cover and minimum mass, and applies diameter-scale Rips stability.
The paper's distance-function/offset diagrams have factor one; the Rips estimate
here has factor two. This result supplies no manifold covering-number estimate,
density estimator, or data-dependent confidence radius.

The implementation is in `Probability/SamplingCoverage`,
`Persistence/LocallyFiniteDiagramBottleneckLaws`, and
`Persistence/RipsSamplingConfidence`. It uses the existing canonical q-tame
diagram directly and does not require a finite-constructible identification.
