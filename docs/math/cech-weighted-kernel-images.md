# Arctan persistence images and Čech kernel and image consumers

This note evaluates the [persistence-image](persistence-images.md) stability constant at the
[arctan weight](arctan-weight-rips-kernel.md) and composes the
[same-label Čech displacement bound](cech-displacement-stability.md) with the
[weighted Gaussian kernel embedding](weighted-kernel-embedding.md) and finite-part
persistence images, in the same way the Rips consumers compose the
[Rips bottleneck bound](rips-persistence-images.md).

## The image constant

The persistence-image stability constant is 2A + 3B·√(2/π)/σ, where A is the
birth–persistence Lipschitz constant of the weight, B its sup bound and √(2/π)/σ the
translation constant of the 2D Gaussian density. The arctan weight has A = C and B = π/2.
Since (π/2)·√(2/π) = √(π/2), the constant is

2C + 3·√(π/2)/σ.

Both forms agree for every σ, including σ = 0, where Lean's division by zero makes both
terms zero. The arctan image bounds against the finite first-order matching cost and, for
positive diagrams with finite bottleneck, against the occurrence count times the bottleneck
distance, are instances of the existing image theorems with this constant. The constant is
not sharp. At C = 0 the weight is zero, so every image and every embedding vanishes, while
the image constant 3·√(π/2) and the kernel constant √2·π/2 at σ = 1 are positive.

## Bandwidth hypotheses

The image theorems keep 0 < σ. It is used where the Gaussian density integrates to one,
which bounds each pixel vector by one, and where the translation constant is nonnegative.
The kernel route has no bandwidth sign hypothesis, since its kernel-function distance
bound holds for every σ. The image items below therefore carry 0 < σ, and the kernel items
do not.

## Čech consumers

Fix labelled configurations p, q : V → X in one pseudometric space on the same finite
ordered label type, a coefficient field and a degree. Let D_p, D_q be the actual Čech
diagrams, N_p, N_q their numbers of finite occurrences, and δ the same-label displacement,
the largest distance dist(p v, q v). The Čech bound gives full bottleneck at most δ, so the
bottleneck is finite and its real value is at most δ. With the count-times-bottleneck
theorems this gives

‖Φ(D_p) − Φ(D_q)‖ ≤ (2A + √2·B/|σ|)(N_p + N_q) δ

for the weighted-kernel embeddings Φ and every weight, the same bound divided by |τ| for the
second-level Gaussian features and for |K(D, D_p) − K(D, D_q)| with an arbitrary fixed
diagram D, and

‖I(D_p) − I(D_q)‖ ≤ (2A + 3B·√(2/π)/σ)(N_p + N_q) δ

for the finite-part persistence images I with 0 < σ and measurable pairwise disjoint pixels.
The arctan instances replace the constants by 2C + √2·π/(2|σ|) and 2C + 3·√(π/2)/σ. There
is no arctan instance for the second-level Gaussian features, as on the Rips side.

Essential bars stay in the bottleneck comparison but are omitted from the embedding and
the image. Occurrence multiplicities are retained throughout. The count factor N_p + N_q is
the one of the Rips consumers. Zero displacement, either from a configuration against itself
or from the empty label type, makes all three bounds zero.

No distance-compatible label metric is assumed. The Rips route needs metrics d, e on the
labels with d(v, w) = dist(p v, p w), which fail to exist when two labels sit at the same
point. For the configuration with both labels at 0 there is no such metric, so the Rips
consumers do not apply; against the points 0, 2, with displacement 2, the Čech consumers
do.

The size-uniform Čech weighted-kernel and persistence-image corollaries are summarized in
[Essential bars on the full complex](total-persistence.md#essential-bars-on-the-full-complex).

## Sup-norm consumers

In the sup-metric product ι → ℝ with a possibly empty finite ι, let d and e be
distance-compatible metrics for p, q : V → ι → ℝ, so d.dist v w = dist (p v) (p w) and
likewise for e and q. With a finite ordered label type V, a field k and degree n, write N_p
and N_q for the finite-occurrence counts of the two Čech diagrams and put

Δ = Rips.pairwiseDiscrepancy d e / 2.

`Cech.bottleneck_dgm_le_half_pairwiseDiscrepancy` gives the full bottleneck bound, and
`Cech.bottleneck_dgm_lt_top_supNorm` and
`Cech.toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy` give its finiteness and real
conversion. The embedding, second-level Gaussian feature and fixed-diagram kernel-value
consumers are `Cech.norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy`,
`Cech.norm_diagramGaussianFeature_sub_le_half_pairwiseDiscrepancy` and
`Cech.abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy`. Each has the matching
Rips constant times (N_p + N_q) times Δ; the feature and kernel-value constants also carry
the factor 1/|τ|. All consumer items assume hA : 0 ≤ A, hB : 0 ≤ B and a weight
`PersistenceImage.Weight A B`. The image consumer
`Cech.norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy` has the matching image
constant and requires 0 < σ, measurable pixels and pairwise disjoint pixels. The kernel,
embedding and feature items require only nonnegative weight bounds, with no sign hypothesis
on σ or τ. The arctan instances
`Cech.norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy_arctan`,
`Cech.abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy_arctan` and
`Cech.norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy_arctan` have constants
2C + √2·π/(2|σ|), (2C + √2·π/(2|σ|))/|τ| and
2C + 3·√(π/2)/σ; the image instance also keeps 0 < σ. There is no arctan feature instance.

The displacement route above needs no label metric. This sup-norm route needs d and e, but
`Cech.pairwiseDiscrepancy_le_two_mul_displacement` gives Δ ≤ δ, where δ is the same-label
displacement. The moved diagonal pair has Δ = 1/2 and δ = 1, so the halved constants are
strictly smaller there. On the line, only the bottleneck statement
`Cech.bottleneck_dgm_le_half_pairwiseDiscrepancy_real` is provided; no line consumer
theorems are stated.

## Rips versus Čech of one configuration

For a real diagram D and c > 0, `bottleneck_self_scale_le` bounds the bottleneck distance
from D to D scaled by c by ENNReal.ofReal (|1 − c| · M), when M bounds the absolute values
of both coordinates of every finite point and of every essential birth coordinate. The
proof matches each occurrence to its own scaled image. The bound is sharp for the single
finite bar (0, 2) at c = 1/2: the scaled point is (0, 1), and the bottleneck distance is
exactly 1.

The coordinates of actual diagrams are critical values by
`mem_criticalValues_of_mem_finitePart_dgm` and
`mem_criticalValues_of_mem_essentialPart_dgm`. For a Rips filter, every such value lies in
[0, diameter of the whole carrier] by `Rips.filter_value_le_diameter_univ`. Combining this
with the sup-norm scaling identity gives
`Cech.bottleneck_rips_cech_dgm_le_half_diameter` in ι → ℝ and
`Cech.bottleneck_rips_cech_dgm_le_half_diameter_real` on the line: the Rips and Čech
diagrams of one configuration are at bottleneck distance at most half the carrier
diameter.

In the sup-norm product, let N_d and N_p count finite occurrences of the Rips and Čech
diagrams. The consequences
`Cech.norm_diagramEmbedding_rips_sub_cech_le`,
`Cech.abs_gaussianDiagramKernel_rips_sub_cech_le` and
`Cech.norm_finiteDiagramImage_rips_sub_cech_le` bound the embedding, fixed-diagram
kernel-value and finite-part image differences by the corresponding constant times
(N_d + N_p) times `Rips.diameter d Finset.univ / 2`. The embedding and kernel-value items
require nonnegative weight bounds; the image item also requires 0 < σ, measurable pixels
and pairwise disjoint pixels. The Euclidean triangle fixture gives Čech_{6/5} ≠ Rips_{12/5},
so the halving identity and these additive bounds are not stated for EuclideanSpace or a
general ambient.

## Boundaries

The diagram-level image bound needs finite bottleneck. A diagram with the finite point
(0, 2) and one essential bar, compared with the empty diagram, has bottleneck ⊤. With one
pixel covering the plane, σ = 1 and C = 1, its arctan image difference has norm arctan 2,
but the real value of ⊤ in Lean is 0, so the count-times-bottleneck bound would read 0. The
Čech and Rips consumers discharge the hypothesis by their bottleneck bounds.

The additive Rips-versus-Čech kernel and image bounds are given in [Rips versus Čech of one
configuration](#rips-versus-čech-of-one-configuration), but only in the sup-norm product
and on the line. The log-scale consumers are described in
[Log-scale Rips versus Čech](#log-scale-rips-versus-čech).

## Log-scale Rips versus Čech

`TDA.Persistence.CechRipsLogScaleConsumers` has a generic layer for two filters on one finite
complex. If `g ≤ f ≤ c · g`, `1 ≤ c`, and `g` is `PositiveOnEdges`, then in every degree
`n ≥ 1` the log-scale bottleneck is at most `log c`. The layer gives the corresponding
count-times-`log c` bounds for the weighted Gaussian embedding, its second-level Gaussian
feature, a fixed-diagram Gaussian kernel value, and the finite-part persistence image.

For one finite configuration in a general pseudometric ambient, with a compatible label metric,
the exact log-scale Rips-versus-Čech bottleneck gives the same four consumer bounds, and the
`log 2` bottleneck bound gives versions stated with the radius-level occurrence counts through
the identity
`Fintype.card (logDgm k f n).finiteOccurrences = Fintype.card (dgm k f n).finiteOccurrences`
for `n ≥ 1` and `PositiveOnEdges f`. The arctan embedding, fixed-diagram kernel-value, and
image instances are included; there is no arctan feature instance. The restriction `n ≥ 1`
is required because the degree-zero log-scale module is not constructible on a finite positive
log grid, so no degree-zero `log 2` consumer is available.

`TDA.Persistence.CechRipsLogScaleConsumersExamples` records the two-point, triangle, filled
triangle, zero-weight, degree-zero, and repeated-label fixtures for these statements.

## Lean interfaces and sources

`TDA.Persistence.ArctanPersistenceImage` proves `PersistenceImage.stabilityConstant_arctan`,
the two arctan image bounds, `PersistenceImage.finiteDiagramImage_eq_sum` and the arctan
Rips image consumer. `TDA.Persistence.CechWeightedKernel` proves
`Cech.bottleneck_dgm_lt_top`, `Cech.toReal_bottleneck_dgm_le_displacement`, the three kernel
consumers and the arctan embedding and kernel-value instances.
`TDA.Persistence.CechPersistenceImage` proves the image consumer and its arctan instance.
`TDA.Persistence.CechSupNormWeightedKernel` proves
`Cech.bottleneck_dgm_lt_top_supNorm`,
`Cech.toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy`, the embedding, feature and
kernel-value consumers, their arctan embedding and kernel-value instances, and
`Cech.bottleneck_dgm_le_half_pairwiseDiscrepancy_real` for compatible label metrics in
ι → ℝ and on the line. `TDA.Persistence.CechSupNormPersistenceImage` proves
`Cech.norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy` and
`Cech.norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy_arctan`.
`TDA.Persistence.CechRipsAdditive` proves the additive
scaling bound, the critical-value coordinate lemmas, the carrier-diameter bound for Rips
values, and the half-diameter Rips-versus-Čech bottleneck bounds in the sup-norm product
and on the line, with the consumer consequences in the product. Its consumers use the
corresponding nonnegative weight bounds, and its image consumers additionally require
0 < σ and measurable pairwise disjoint pixels.
`TDA.Persistence.CechSupNormConsumersExamples` covers the moved diagonal pair, strict
Δ ≤ δ, zero weight, zero discrepancy, the line half-discrepancy bound, the sharp single
bar, two points, the sup-norm triangle and the Euclidean counterexample. The additive
scaling bound, critical-value description and Rips-versus-Čech comparison are elementary
library results and are not attributed to a paper.
`TDA.Persistence.CechRipsLogScaleConsumers` proves the generic log-scale layer, the exact
log-scale bottleneck consumers, the `log 2` Rips-versus-Čech consumers, and their arctan
instances in a general pseudometric ambient. `TDA.Persistence.CechRipsLogScaleConsumersExamples`
provides the corresponding fixtures.

[Kusano–Fukumizu–Hiraoka](references.md#KFH18) (CC-BY 4.0; see the source register for
attribution and license) is used for statement shapes: §3.2 p. 14 (w_arc), §3.2 p. 16
(assumption (W2), eq. (10), the p = 1 remark B₂ = π/2, L₂ = 2C, and the w_arc line of
Corollary 11) and §3.3 eq. (13). [Adams et al.](references.md#AE17) (CC-BY 4.0; see the
source register for attribution and license), §4 Definitions 1–2 and the §5 stability
route, supply the image construction. AE17 uses no arctan weight: the arctan persistence
image and its constant are a library composition of KFH18's weight with AE17's
construction and the library's nonsharp constant. The ambient Čech complex is that of
[Chazal–de Silva–Oudot](references.md#CDSO13-v3) §4.2.3, as in the displacement note. The
Čech-to-kernel and Čech-to-image compositions are library results and are not attributed
to any paper. The statements adapt both sources: the weight is truncated below the
diagonal, C = 0 is allowed, the constant is the library's nonsharp one, and the costs are
the library's finite matching cost and count-times-bottleneck rather than a 1-Wasserstein
distance. Proofs are independent.

Not covered here: assumption (W1) and total-persistence bottleneck stability
(Proposition 8, Theorem 9, Corollary 12), Propositions 6–7, the w_pers and w_one lines of
Corollary 11, p ≠ 1, line consumers of the half-discrepancy bound, a per-point sharp
additive bound, Rips-versus-Čech bounds outside the sup-norm product and the line, explicit
Čech or Rips diagram points, and Hausdorff, Gromov–Hausdorff or different-label stability.
