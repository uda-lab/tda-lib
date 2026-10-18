# Gaussian persistence images

A finite collection of strictly positive birth–death pairs is indexed by an arbitrary
finite type. Equal pairs keep separate labels and contribute with their multiplicity.
All deaths are real; essential bars are outside this construction.

## Fixed data and construction

Fix a bandwidth σ > 0 and real constants A,B ≥ 0. The weight w on the
birth–persistence plane satisfies

- 0 ≤ w(u) ≤ B;
- |w(u) − w(v)| ≤ A ‖u − v‖∞;
- w(b,0) = 0 for every real b.

Use the birth–persistence transform T(b,d) = (b,d−b). For a center u, let gσ,u be
the product of the two normalized one-dimensional Gaussian densities, each with
variance σ². The measure on the real plane is product Lebesgue measure.

Fix finitely many measurable pairwise disjoint pixels Pₖ. They need not cover the
plane, have positive area, or be bounded. One occurrence p has pixel feature

F(p)ₖ = ∫_{Pₖ} w(Tp) gσ,Tp(z) dz.

The persistence image is the sum of F(p) over occurrence labels. Equivalently, each
coordinate is the integral of the finite weighted Gaussian surface over that pixel.
The target is `PiLp 1 (fun _ : K => ℝ)`: its norm is the sum of absolute pixel
coordinates, rather than the default maximum norm on a function type.

## Every-matching estimate

Write cσ = sqrt(2/π)/σ and C = 2A + 3B cσ. For any two such finite collections x,y
and any partial injection of their occurrence labels, let its total cost be the sum of

- ‖xᵢ − yⱼ‖∞ for each matched pair;
- (death − birth)/2 for every unmatched source and target occurrence.

Then

‖PI(x) − PI(y)‖₁ ≤ C · total matching cost.

The statement quantifies over every partial matching and allows empty collections,
repeated values and an empty pixel family. It requires the same bandwidth, weight and
pixel family on both sides. It does not assume an optimal matching or define a transport
distance. The constant is explicit and need not be sharp. The
[finite first-order matching cost](finite-first-order-matching.md) supplies an attained
minimum over these matchings; `norm_image_sub_le_finiteFirstOrderMatchingCost` bounds
the same image error by C times that minimum.

`finiteDiagramImage` applies the construction to a positive diagram's canonical finite
occurrences, omitting essential bars. A finite full bottleneck gives a count-dependent
bound, which controls [Rips images from distance-matrix perturbations](rips-persistence-images.md).
The finite-bar counts and coordinate bounds used for analogous size estimates are collected in
[total persistence and finite Rips–Čech bounds](total-persistence.md).

## Analytic proof

The one-dimensional density has maximum 1/(σ sqrt(2π)). If its centers are ordered,
their difference changes sign at the midpoint. Splitting there and translating the
half-line integrals reduces its L¹ norm to twice a finite interval integral. Bounding
that integral by the density maximum gives cσ times the center displacement.

Product integration proves that gσ,u is integrable with integral one. Splitting a
difference of products gives

∫ |gσ,u − gσ,v| ≤ cσ (|u₁−v₁| + |u₂−v₂|).

For any integrable surface h, disjointness gives

Σₖ |∫_{Pₖ} h| ≤ Σₖ ∫_{Pₖ} |h| ≤ ∫ |h|.

Split a weighted feature difference into a weight difference and a translated Gaussian
difference. The transform T has maximum-norm constant 2 and coordinate ℓ¹ constant 3,
so these terms are bounded by 2A and 3B cσ times the original birth–death displacement.
Vanishing at persistence zero bounds an unmatched feature by 2A times its diagonal
cost, which is at most C times that cost. The finite additive-feature matching theorem
then supplies the stated image estimate.

## Lean interfaces and sources

`TDA.Persistence.GaussianKernel` supplies the actual one- and two-dimensional densities,
normalization and L¹ translation estimates. `TDA.Persistence.PersistenceImage` defines
`Weight`, `pixelIntegral`, `feature` and `image`; `image_apply` identifies the coordinates
with integrals of the surface. `norm_image_sub_le_matching` is the matching estimate.
The ordinary `TDA.Persistence` import includes both modules. These are noncomputable
analytic definitions; numerical integration requires a separate implementation.

The construction follows [Adams et al., §4 Definitions 1–2](references.md#AE17).
Their §5 Gaussian surface and pixel bounds motivate the analytic route. The library
uses a maximum-norm Lipschitz hypothesis on the weight and derives the stated nonsharp
constant. The attained matching-minimum corollary uses this same library bound; C is
not identified with the paper's exact gradient/Euclidean coefficient.

[Kusano–Fukumizu–Hiraoka §4.1.3](references.md#KFH18) distinguishes pixel-vector and
RKHS norms and uses birth–death coordinates for its comparison. The present construction
uses Adams's birth–persistence transform and the finite pixel ℓ¹ norm. It proves no RKHS
norm estimate. The source register retains exact manifestations and attribution.
The separate RKHS construction is described in
[weighted kernel embedding](weighted-kernel-embedding.md).
