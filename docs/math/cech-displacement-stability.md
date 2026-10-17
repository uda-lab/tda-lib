# Same-label displacement stability of Čech values and diagrams

Fix a pseudometric space X and two labelled families p, q : V → X on the same label type.
Faces are finite label sets, as for [the ambient Čech complex](cech-rips-sandwich.md).
Repeated labels and non-injective families are allowed. Points are compared label by
label; the witness space X stays fixed.

## Pointwise and face estimates

Let s be a finite label set, x ∈ X and ε ≥ 0, and suppose dist (p v) (q v) ≤ ε for every
v ∈ s. For v ∈ s the triangle inequality gives

dist x (p v) ≤ dist x (q v) + dist (q v) (p v) ≤ radius_q(x, s) + ε.

The zero seed of the radius needs radius_q(x, s) + ε ≥ 0, which is where ε ≥ 0 enters.
Hence radius_p(x, s) ≤ radius_q(x, s) + ε, and by symmetry the radii differ by at most ε.
The sign condition matters only for s = ∅: there both radii are zero, the displacement
hypothesis holds vacuously for ε = −1, and the inequality 0 ≤ 0 − 1 fails.

For an actual face s, nonempty by definition, the hypothesis at any v₀ ∈ s forces ε ≥ 0,
and p v₀ shows that X is nonempty. For every x the Čech value of s under p is at most
radius_p(x, s) ≤ radius_q(x, s) + ε. Taking the infimum over x gives
čech_p(s) ≤ čech_q(s) + ε, and by symmetry |čech_p(s) − čech_q(s)| ≤ ε. The hypothesis
concerns only the labels of s.

## Displacement

For a finite V the displacement δ(p, q) is the largest of the distances dist (p v) (q v),
computed as a maximum with zero seed. It is zero on an empty carrier and uses no supremum.
It is nonnegative and symmetric, vanishes for p = q, bounds every label-wise distance, and
satisfies δ(p, q) ≤ ε exactly when ε ≥ 0 and every label moves by at most ε. Hence every
Čech value moves by at most δ(p, q).

## Diagrams

For a finite linearly ordered V, the largest face difference of the two Čech filters is
at most δ(p, q). The existing finite-face stability theorem then bounds the bottleneck
distance between the actual Čech diagrams by δ(p, q) in every homological degree. The
diagrams keep their occurrence multiplicities and essential bars at infinity. No
injectivity, properness or cardinality hypothesis is added. An explicit bound ε ≥ 0 on
every label-wise distance gives the same diagram bound with ε.

The finite diagram bound composes with the weighted Gaussian kernel embedding and with
finite-part persistence images, without a label metric; see
[arctan persistence images and Čech consumers](cech-weighted-kernel-images.md).

## Comparison with Rips

Let d and e be label metrics agreeing with the ambient distances of p and q. For labels
v, w the reverse triangle inequality for distances gives

|dist (p v) (p w) − dist (q v) (q w)| ≤ dist (p v) (q v) + dist (p w) (q w) ≤ 2δ(p, q).

So the Rips pairwise discrepancy is at most 2δ(p, q), every Rips diameter moves by at most
2δ(p, q), and the existing Rips stability theorem bounds the actual Rips diagrams by
2δ(p, q). Čech values are 1-Lipschitz and Rips values 2-Lipschitz in the displacement.

## Fixtures

- **Three points.** On the line take p = (0, 1, 2) and q = (−1, 1, 3), so δ = 1. The
  triangle has Čech values 1 and 2, centred at 1, and Rips diameters 2 and 4. The Čech
  change equals δ and the Rips change and the pairwise discrepancy equal 2δ, so both
  constants are attained. The diagram bounds are 1 for Čech and 2 for Rips.
- **One moved point.** For p = (0, 2) and q = (0, 3), δ = 1. The edge has Čech values 1
  and 3/2, so its change 1/2 is strictly below δ. The diagrams are within 1.
- **Zero displacement.** δ(p, p) = 0, so the diagram bound is zero. On the empty carrier
  δ = 0 and the diagrams coincide in every degree.
- **Same image.** For p = (0, 2) and q = (2, 0) the images coincide but δ = 2. The
  estimate depends on labels and is not a bound in terms of the images.
- **Empty set.** For ε = −1 on s = ∅ the radius estimate fails, so its sign condition
  cannot be dropped.

## Interfaces

`TDA.Filtration.CechDisplacement` contains the radius and value estimates,
`displacement` with its laws, the displacement-form face estimate and the Rips comparison
`pairwiseDiscrepancy_le_two_mul_displacement`. `TDA.Persistence.CechStability` contains
`faceSupDifference_filter_le`, `bottleneck_dgm_le_displacement`,
`bottleneck_dgm_le_of_dist_le` and `bottleneck_rips_dgm_le_two_mul_displacement`. The
fixtures are in `TDA.Filtration.CechDisplacementExamples` and
`TDA.Persistence.CechStabilityExamples`.

## Source correspondence and scope

[Chazal–de Silva–Oudot](references.md#CDSO13-v3) prove in Corollary 4.10 that ambient
Čech persistence modules of landmark sets L, L′ with common witnesses are ε-interleaved
for ε > d_H(L, L′), and deduce in Theorem 5.6 the bound d_H(L, L′) on the bottleneck
distance of their diagrams under total boundedness. The results here are a library
extension consistent with Theorem 5.6: for a nonempty finite label type the Hausdorff
distance between the images of p and q is at most δ(p, q). The library objects differ,
since faces are label sets and labels may repeat, and the bound is proved through the
finite-face stability theorem rather than exported from Corollary 4.10 or Theorem 5.6.
The Rips factor 2 matches the factor of Theorem 5.2 informally. No Hausdorff or
Gromov–Hausdorff statement, interleaving, change of witness space or relabelling is
formalized.
