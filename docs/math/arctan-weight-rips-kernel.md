# The arctan weight and Rips weighted-kernel stability

This note instantiates the [weighted Gaussian kernel embedding](weighted-kernel-embedding.md)
at the arctan weight of [Kusano–Fukumizu–Hiraoka](references.md#KFH18) and composes its
stability with the [same-label Rips bound](rips-metric-stability.md), in the same way
[Rips persistence images](rips-persistence-images.md) compose the image bound.

## The weight

KFH18 §3.2 (p. 14) defines w_arc(x) = arctan(C·pers(x)^p) with C > 0 and p a positive
integer. Here p = 1. The library weight interface reads weights in birth–persistence
coordinates u = (b, pers) and requires 0 ≤ w ≤ B, a maximum-norm Lipschitz constant A, and
w(b, 0) = 0. For C ≥ 0 the library weight is

w(u) = arctan(C · max(pers, 0)).

On every point with birth ≤ death it equals KFH18's arctan(C·pers), so the two agree on all
finite diagram points. The truncation matters only below the diagonal. There KFH18's formula
is negative, while the library interface requires nonnegativity. The examples show that the
untruncated formula at C = 1 is not a library weight, since its value at (0, −1) is −π/4.
C = 0 is allowed and gives the zero weight.

arctan is 1-Lipschitz because its derivative 1/(1 + x²) lies in [0, 1]. Truncation at 0 is
1-Lipschitz and |u₂ − v₂| is at most the maximum norm of u − v, so A = C. The bound is
B = π/2. It is never attained, but no smaller bound holds when C > 0: the examples evaluate
at u = (0, tan y / C) for a y strictly between the proposed bound and π/2.

## The constant

The embedding constant of the weighted-kernel stability theorems is 2A + √2·B/|σ|. The
factor 2 converts a birth–persistence Lipschitz constant to a birth–death one (KFH18
Appendix C, Lemma 17), so A = C reproduces KFH18's L₂ = 2C for p = 1 (§3.2, p. 16). The
Gaussian kernel has B_k = 1 and L_k = √2/|σ| (Lemma 16). At A = C and B = π/2 the constant is

2C + √2·π/(2|σ|),

which is the w_arc line π·L_k/2 + 2·B_k·C of KFH18 Corollary 11. In place of the source's
1-Wasserstein distance, the library bounds the embedding difference by the finite
first-order matching cost and, for positive diagrams with finite bottleneck, by the
occurrence count times the bottleneck distance. The (k, w)-Gaussian kernel values of KFH18
eq. (13) satisfy the same bounds divided by |τ|. All of these are instances of the existing
weighted-kernel theorems. No bandwidth sign hypothesis is assumed; at σ = 0 the term
√2·π/(2|σ|) is zero, as is the corresponding kernel-function distance.

## Rips consumers

Fix metrics d, e on one finite labelled vertex set, a coefficient field and a degree. Let
D_d, D_e be the actual Rips diagrams, N_d, N_e their numbers of finite occurrences, and δ
the maximum pairwise discrepancy of d and e. The Rips bound gives full bottleneck at most δ,
so the bottleneck is finite and its real value is at most δ. With the count-times-bottleneck
theorems this gives

‖Φ(D_d) − Φ(D_e)‖ ≤ (2A + √2·B/|σ|)(N_d + N_e) δ

for the embeddings Φ and every weight, the same bound divided by |τ| for the second-level
Gaussian features, and the same bound divided by |τ| for |K(D, D_d) − K(D, D_e)| with an
arbitrary fixed diagram D. The arctan instances replace the constant by 2C + √2·π/(2|σ|).
Essential bars stay in the bottleneck comparison but are omitted from the embedding. The
count factor is the same as for Rips persistence images. Empty and singleton carriers have
δ = 0, so their embeddings and kernel values coincide. This composition is a library
result and is not attributed to any paper.

The sup-norm half-discrepancy consumers and the additive comparison of one Rips and Čech
configuration are described in [Sup-norm consumers](cech-weighted-kernel-images.md#sup-norm-consumers)
and [Rips versus Čech of one configuration](cech-weighted-kernel-images.md#rips-versus-čech-of-one-configuration).
The finite-bar count and coordinate estimates used for size-dependent Rips consumers are in
[total persistence and finite Rips–Čech bounds](total-persistence.md).

## The infinite-bottleneck boundary

The diagram-level bound needs finite bottleneck. A diagram with the finite point (0, 2)
and one essential bar, compared with the empty diagram, has bottleneck ⊤. Its arctan
embedding difference has norm arctan 2 > 0, but the real value of ⊤ in Lean is 0, so the
count-times-bottleneck bound would read 0. The Rips consumers discharge the hypothesis by
the Rips bound itself.

## Lean interfaces and sources

`TDA.Persistence.ArctanWeight` proves `lipschitzWith_arctan`, defines
`PersistenceImage.arctanWeight` and proves `WeightedKernel.stabilityConstant_arctan`
with the four arctan corollaries. `TDA.Persistence.RipsWeightedKernel` proves
`Rips.bottleneck_dgm_lt_top`, `Rips.toReal_bottleneck_dgm_le_pairwiseDiscrepancy`, the three
Rips consumers and their arctan specializations. The example modules cover the weight
values, the sign negative control, sup-bound sharpness, the constant at C = 1 and C = 0,
an explicit embedding distance and kernel value against their bounds, the empty, singleton
and two-point carriers, and the infinite-bottleneck boundary.

KFH18 (CC-BY 4.0; see the [source register](references.md#KFH18) for attribution and
license) is used for statement shapes: §3.2 p. 14 (w_arc and eq. (7)), §3.2 p. 16
(assumption (W2), eq. (10), Proposition 10, the p = 1 remark and Corollary 11), assumption
(K) with Lemma 16, and Appendix C Lemma 17. The statements here adapt the source: the
weight is truncated below the diagonal, C = 0 is allowed, and the cost is the library's
matching cost rather than a separately defined 1-Wasserstein distance. Proofs are
independent. The Rips side uses the sources of the
[Rips persistence images](rips-persistence-images.md) note.

Not covered here: (W1) and total-persistence bottleneck stability (Proposition 8,
Theorem 9, Corollary 12), p ≠ 1, injectivity and universality, the w_pers and w_one lines of
Corollary 11, explicit Rips diagram points and different-point-set stability. The arctan
persistence-image constant and the Čech consumers are in
[arctan persistence images and Čech consumers](cech-weighted-kernel-images.md).
