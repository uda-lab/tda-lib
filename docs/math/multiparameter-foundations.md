# Interval modules, presentations and rank-exact lifting

The persistence-module API supports constructions on an arbitrary preorder,
including coordinatewise ordered real vector spaces. The results below provide
interval geometry, free presentations and lifting lemmas. Stability of rectangle
barcodes and of rank-exact signed barcodes requires further matching and
resolution arguments.

## Supports and rectangle transitions

Fix a ring R and an order-convex subset S of a preorder P. The module
`SupportInterval.module S hS` has fiber R on S and zero elsewhere, even when S
is empty. Its structure map from a to b preserves coefficients when both points
lie in S and is zero if either point lies outside S. For a nontrivial ring, it
is zero exactly in that case. Over a field, naturality also supplies coefficient
and support-boundary restrictions on morphisms between these modules.

For the rectangle results below, take coefficients in a field k.
A `BoundedInterval` records two real endpoints and whether each is included.
Nonempty intervals include closed singletons. A `Rectangle n` is a family of n
such intervals, with product support. For δ ≥ 0,
`Rectangle.diagonal_maps_eq_zero_iff` proves that every structure map from p to
p + δ·1 is zero exactly when some coordinate interval has length less than δ,
or has length δ and at least one endpoint excluded. At equality, a closed
interval retains its endpoint-to-endpoint map. In particular, a closed singleton
has a nonzero identity map at δ = 0. `Rectangle.hom_ext` shows
that a morphism is determined by its scalar at one point of a nonempty overlap.
Consumers use `open scoped TDA.Persistence` to select the coordinatewise preorder category on
`Fin n → ℝ`, rather than mathlib's category of families of category objects.

These are local geometry and morphism results used in
[Bjerkevik's rectangle stability proof](https://doi.org/10.1007/s00454-021-00298-0).
They do not extract a matching from an interleaving.

## Graded free modules and finite presentations

For a ring R and a graded generator family W, `GradedFree.module W` at a consists
of finite linear combinations of generators whose grades are at most a.
Structure maps retain the coefficients. Choosing an image for each generator
at its birth grade gives a unique natural transformation from this free module.
Consequently a map from a free module lifts through a componentwise surjective
natural transformation; two lifts differ by a kernel element on each generator
at its birth grade. A structure map is an isomorphism if exactly the same generators are
available at its source and target.

A presentation is the cokernel of a homogeneous map from a free relation module
to a free generator module. `GradedFree.FinitelyPresented` asserts the existence
of such a presentation with finite generator and relation sets and a natural
isomorphism to the given module. The quotient universal property, invariance
under isomorphism and redundant zero relations are supported. These constructions
implement the free-cover ingredients of
[Lesnick, §4.1](https://arxiv.org/html/1106.5305v4). The finite cross-presentation
characterization in Theorem 4.4 requires an additional generator-elimination proof.

A map from a presented module lifts through a natural transformation ρ when
ρ is surjective at every generator grade and injective at every relation grade.
The proof chooses preimages of the generators, then uses injectivity to show
that the relations vanish. If ρ is also injective at generator grades, the lift
is unique. Thus postcomposition with ρ gives a bijection on these morphisms.
These assertions hold over any ring and preorder; the presentation need not
be finite. They test only its declared grades.

For coordinatewise ordered `Fin n → ℝ`, each finite presentation determines a
finite set of critical values in every coordinate: the generator and relation
grade coordinates. If no critical value lies in any interval `(aᵢ, bᵢ]`, the
structure map from `a` to `b` is an isomorphism. Evaluation preserves the
presentation cokernel, so the generator and relation isomorphisms induce the
isomorphism of presented fibers. This property transfers through the natural
isomorphism in `FinitelyPresented`. Taking less than the least positive gap
from a fixed `a` to the finitely many grade coordinates gives a positive
right-diagonal slack valid for every smaller nonnegative shift, including
the empty-grade and zero-coordinate cases. These are the local results in
[Lesnick, §6, Lemmas 6.4 and 6.6](https://arxiv.org/html/1106.5305v4).

## Rank exactness and hook lifting

Consider a pointwise short exact sequence L → M → N. At a ≤ b, assume only that
M(a) is finite dimensional. `IsPointwiseShortExact.rank_add_iff_lift_kernel`
proves that rank additivity at this pair is equivalent to the following lifting
property: every vector of N(a) killed at b has a preimage in M(a) also killed at b.
`IsRankExact` requires pointwise finite-dimensional middle fibers. Naturally split
pointwise short exact sequences in this domain are rank exact, and reindexing
preserves rank exactness.

For i < j in a partial order, the hook has support {a | i ≤ a and j ≰ a}.
`Hook.homEquivKernel` identifies maps from this hook to N with vectors of N(i)
killed at j. `Hook.exists_lift` therefore lifts an entire hook morphism through
a rank-exact quotient with pointwise finite-dimensional middle fibers. The support may
be unbounded. This proves the finite-death hook lifting ingredient of
[Botnan–Oppermann–Oudot–Scoccola, §2.14 and Appendix A](https://arxiv.org/html/2208.00300v3).
The principal-upset module, representing a hook with infinite death, is the
graded free module on one generator. `HookInfinity.homEquivFiber` identifies
its morphisms with the target's birth fiber. Surjectivity at that single fiber
therefore suffices to lift any such morphism. This assertion holds over any
ring and preorder, without finite-dimensionality assumptions, and in particular
applies to rank-exact quotient maps over a field. An exact-category instance,
projective classification and rank-projective resolutions remain further results.

## Attainment on real finite-constructible modules

For right-continuous real modules on finite critical grids, with zero left tails
and finite-dimensional critical fibers, the barcode isometry and an
optimal finite matching give an interleaving at every finite distance bound.
The admissible parameters form a closed upper ray when the distance is finite,
and are empty when it is infinite. Distance zero is equivalent to a natural
isomorphism. See [finite-constructible closure](constructible-isometry.md#attainment-and-separation).

This assertion depends on the stated constructibility and finiteness hypotheses.
`RealRay.distance_eq_zero` and `RealRay.not_nonempty_iso` show that k_[0,∞) and
k_(0,∞) have zero distance but are not isomorphic: positive shifts interleave them,
while their fibers at zero differ. The zero distance is not attained. The
multidimensional finite-presentation closure theorem remains a further result.
