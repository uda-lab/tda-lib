# Attainment of the multiparameter interleaving distance

Let R be a ring, and let M and N be finitely presented persistence modules on
coordinatewise ordered ℝⁿ. A finite presentation means a cokernel of a
homogeneous map between free modules on finite graded generator families,
together with a natural isomorphism to the given module. The construction is
described in [graded free modules and finite presentations](multiparameter-foundations.md#graded-free-modules-and-finite-presentations).

Write 1 for the all-ones vector. For a nonnegative finite parameter ε,
write `M[ε](a) = M(a + ε·1)`. An
ε-interleaving consists of natural maps M → N[ε] and N → M[ε] whose two
composites are the structure maps to M[2ε] and N[2ε]. The extended distance
dᵢ(M,N) is the infimum of the parameters admitting such maps; an empty
parameter set has distance infinity.

## The attained threshold

For every finite ε ≥ 0,

    dᵢ(M,N) ≤ ε  if and only if  M and N admit an ε-interleaving.

Consequently, every finite distance is attained. Distance zero is equivalent
to natural isomorphism. When the distance is finite, the admissible parameter
set is the closed ray [dᵢ(M,N),∞); when it is infinite, the set is empty.
The distance is invariant under natural isomorphisms, symmetric and satisfies
the extended triangle inequality. It thus separates isomorphism classes.

`GradedFree.finitelyPresented_distance_le_iff_interleaving` is the threshold
theorem. The `FinitePresentationClosure` module gives attainment,
separation and closedness. `CoordinateInterleavingDistance` supplies the
infimum and distance laws, and `CoordinateInterleaving.zeroEquivIso` identifies
zero interleavings with natural isomorphisms.

`GradedFree.FinitePresentationIsoClasses` is the quotient of finitely presented
modules by natural isomorphism. Its `EMetricSpace` instance uses the descended
interleaving distance, and `FinitePresentationIsoClasses.edist_classOf` identifies
that distance on representatives. The separation proof uses finite-presentation
attainment at zero.

These statements include the zero ring, empty presentations and n = 0.
Finite-dimensional fibers and interval decompositions are unnecessary.
Over a field and for n ≥ 1, the result is
[Lesnick, Theorem 6.1 and Corollary 6.2](https://arxiv.org/html/1106.5305v4).
The ring and zero-coordinate cases are generalizations of that source's domain.

## Removing a small increase of the parameter

The proof uses two consequences of finite presentation. First, generator and
relation grades give a finite set S of test points: if a natural map X → Y is
bijective at every point of S, postcomposition gives a bijection
Hom(M,X) → Hom(M,Y). One lifts generator images through X → Y; injectivity at
relation grades makes the lifted relations vanish. Generator injectivity
gives uniqueness. This criterion is proved for the presented cokernel and
then transferred to M through its presentation isomorphism.

Second, the target N has finite critical coordinate sets. At any fixed point
there is a positive right-diagonal slack on which its structure maps are
isomorphisms. For a fixed ε, apply this at the finitely many translated test
points a + ε·1, a ∈ S. The minimum of their positive slacks makes

    Hom(M,N[ε]) → Hom(M,N[ε+δ])

bijective for every sufficiently small δ ≥ 0. The empty test set causes no
restriction. This argument requires no single positive slack valid at every
point of ℝⁿ.

Apply the Hom argument to the four pairs and parameters
(M,N,ε), (N,M,ε), (M,M,2ε) and (N,N,2ε). Choose δ smaller than the first two
slacks and half the last two. Given an (ε+δ)-interleaving, the first two
Hom bijections lift both natural maps to shift ε. After postcomposing their
double-shift composites to parameter 2ε+2δ, naturality identifies the results
with the original interleaving equations. Injectivity for the last two Hom
maps therefore proves both equations at 2ε.

The construction uses actual natural transformations. Its intermediate
algebraic step, `CoordinateInterleaving.of_postcomp_lifting`, accepts the two
surjections and two injections; the finite-presentation proof establishes
all four conditions. If dᵢ(M,N) ≤ ε, the infimum property gives an
interleaving below ε + η for the chosen positive slack η. Monotonicity
extends it to ε + η, and the lowering construction gives one at ε.

## Why the finite-presentation hypothesis matters

For a field k, the real interval modules k_[0,∞) and k_(0,∞) are interleaved at every
positive parameter. Their distance is zero, while their fibers at zero have
different dimensions, so they are not naturally isomorphic. The declarations
`RealRay.distance_eq_zero` and `RealRay.not_nonempty_iso` prove these facts.
Thus distance zero does not separate arbitrary real-indexed modules.
Informally, the usual generator at zero gives the closed ray a finite presentation while the open
ray cannot have one under the convention above; this ray-presentability remark is not formalized.

The one-dimensional finite-constructible theorem also obtains attainment
from barcode isometry and an optimal finite matching; see
[finite-constructible closure](constructible-isometry.md#attainment-and-separation).
The multiparameter proof uses finite presentations directly and needs no
barcode decomposition. `CoordinateRealBridge.interleavingEquiv` identifies the
real-indexed and one-coordinate witness types, and `CoordinateRealBridge.distance_eq`
identifies their distances. Thus the real examples and the coordinate theorem
use the same one-dimensional distance.
