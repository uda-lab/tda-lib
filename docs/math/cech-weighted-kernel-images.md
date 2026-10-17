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

Essential bars and occurrence multiplicity stay in the bottleneck comparison but are
omitted from the embedding and the image. The count factor N_p + N_q is the one of the Rips
consumers. Zero displacement, either from a configuration against itself or from the empty
label type, makes all three bounds zero.

No distance-compatible label metric is assumed. The Rips route needs metrics d, e on the
labels with d(v, w) = dist(p v, p w), which fail to exist when two labels sit at the same
point. For the configuration with both labels at 0 there is no such metric, so the Rips
consumers do not apply; against the points 0, 2, with displacement 2, the Čech consumers
do.

## Boundaries

The diagram-level image bound needs finite bottleneck. A diagram with the finite point
(0, 2) and one essential bar, compared with the empty diagram, has bottleneck ⊤. With one
pixel covering the plane, σ = 1 and C = 1, its arctan image difference has norm arctan 2,
but the real value of ⊤ in Lean is 0, so the count-times-bottleneck bound would read 0. The
Čech and Rips consumers discharge the hypothesis by their bottleneck bounds.

No Rips-versus-Čech kernel or image bound for one configuration is claimed. The available
comparisons of Rips and Čech diagrams are multiplicative: a log-scale interleaving under
distance-compatible label metrics, and a scaling by 1/2 for the maximum norm on ι → ℝ.
Neither bounds the bottleneck distance additively, which the count-times-bottleneck route
would need.

## Lean interfaces and sources

`TDA.Persistence.ArctanPersistenceImage` proves `PersistenceImage.stabilityConstant_arctan`,
the two arctan image bounds, `PersistenceImage.finiteDiagramImage_eq_sum` and the arctan
Rips image consumer. `TDA.Persistence.CechWeightedKernel` proves
`Cech.bottleneck_dgm_lt_top`, `Cech.toReal_bottleneck_dgm_le_displacement`, the three kernel
consumers and the arctan embedding and kernel-value instances.
`TDA.Persistence.CechPersistenceImage` proves the image consumer and its arctan instance.
The example modules cover the constant at C = 1 and C = 0, the zero weight, the
infinite-bottleneck boundary, the arctan Rips image instance at discrepancy 1, a point
moved by 1, the three-point family with displacement 1, zero displacement, the empty
carrier and the repeated-label configuration.

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
Corollary 11, p ≠ 1, consumers of the half-discrepancy Čech bound for the maximum norm,
explicit Čech or Rips diagram points, and Hausdorff, Gromov–Hausdorff or different-label
stability.
