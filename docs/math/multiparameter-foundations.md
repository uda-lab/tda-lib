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
[Lesnick, §4.1](https://arxiv.org/html/1106.5305v4). The finite-presentation
characterization in Theorem 4.4 relates interleavings to simultaneous
presentations with shared shifted generator and relation families.

The free module on a disjoint union of graded families has the corresponding
sum universal property. A presentation can adjoin an arbitrary graded family
of redundant generators by adding the relations `new_v − chosenLift_v`.
`Presentation.adjoinRedundantIso` proves that the enlarged quotient is naturally
isomorphic to the original one; finite families remain finite.

For any morphism between two presented modules,
`Presentation.exists_chainMap_lift` supplies maps between their generator and
relation free modules making both presentation squares commute. The proof
derives the fiberwise kernel of the cover as the image of the relation map
from its cokernel, then chooses lifts of relation generators. These
statements work over any ring and preorder without finiteness assumptions.
For real coordinate grades, `W(σ)` has generator grades `gr(w) − σ`, so
`W(−ε)` delays every birth by ε. `GradedFree.shiftIso` identifies
`F(W(ε))` with `F(W)[ε]`, and `delayedInclusion` embeds `F(W(−ε))` in `F(W)`.

To give cross-presentations at ε ≥ 0, choose graded families W₁, W₂, Y₁, Y₂
and homogeneous maps from F(Y₁) to F(W₁ ⊔ W₂(−ε)) and from F(Y₂) to
F(W₁(−ε) ⊔ W₂). These are the fields of `GradedFree.CrossData`. Each
primitive relation also gives a relation on the opposite side born ε later:
the free cross map retains its coefficients and advances its availability
grade. The resulting quotients are

```text
M = ⟨W₁, W₂(−ε) | Y₁, Y₂(−ε)⟩,
N = ⟨W₁(−ε), W₂ | Y₁(−ε), Y₂⟩.
```

`CrossData.quotientInterleaving` constructs an actual ε-interleaving of M and N.
Both free cross maps kill both relation families in the opposite quotient,
so the cokernel universal property supplies the quotient maps. Their two
composites are the 2ε transitions: this follows from the free cross-map
identities by cancellation of the surjective free covers.
`CrossData.interleavingOfIso` transports the result to modules with these
presentations. Finite primitive families give finite presentations, and at
ε = 0 the construction gives a natural isomorphism. The proof works over any
ring, for arbitrary families and dimension zero as well.

For finitely presented M and N, the existence of an ε-interleaving is
equivalent to the existence of finite W₁, W₂, Y₁, Y₂ with the two displayed
presentations. `finitelyPresented_interleaving_iff_crossPresentation` proves
this finite-presentation version of
[Lesnick, Theorem 4.4](https://arxiv.org/html/1106.5305v4#S4.SS2), over any ring
and including dimension zero. The construction accepts arbitrary specified
presentations; finiteness of the original families ensures finiteness of all
four shared families.

To construct them from an interleaving, take W₁ and W₂ to be the original
generator families and write Z₁ and Z₂ for the original relation families.
The interleaving maps give values for W₂(−ε) in M and W₁(−ε) in N at their
delayed births. Lift these values through the free covers and add the
homogeneous graph relations `new generator − chosen free lift`. Thus
Y₁ = Z₁ ⊔ W₂(−ε) and Y₂ = Z₂ ⊔ W₁(−ε). `Presentation.crossData` builds the
primitive maps with precisely these relations.

Both interleaving equations are used to show that crossing and then mapping
to an original module agrees with its interleaving map after the collapse.
Consequently the opposite delayed relations also vanish. The quotient maps
then descend by the cokernel universal property. Redundant-generator
elimination and mutual descent of the relations prove
`Presentation.crossDataLeftIso` and `crossDataRightIso`, the natural
isomorphisms to M and N. No relation-vanishing or quotient-isomorphism
condition is included in the input data.

`Presentation.shift` shifts both original indexing families without changing
their cardinalities. Its relation map is conjugated through the free-shift
isomorphisms. `Presentation.presentedShiftIso` identifies the resulting
cokernel with the shift of the original quotient, using Mathlib's preservation
of cokernels under reindexing. Its free-cover compatibility is
`Presentation.cover_presentedShiftIso`; `finitelyPresented_shift` gives the
corresponding closure of finite presentation.

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

Over a field k, for right-continuous real modules on finite critical grids,
with zero left tails and finite-dimensional critical fibers, the barcode isometry and an
optimal finite matching give an interleaving at every finite distance bound.
The admissible parameters form a closed upper ray when the distance is finite,
and are empty when it is infinite. Distance zero is equivalent to a natural
isomorphism. See [finite-constructible closure](constructible-isometry.md#attainment-and-separation).

This assertion depends on the stated constructibility and finiteness hypotheses.
For a field k, `RealRay.distance_eq_zero` and `RealRay.not_nonempty_iso` show that k_[0,∞) and
k_(0,∞) have zero distance but are not isomorphic: positive shifts interleave them,
while their fibers at zero differ. The zero distance is not attained. For finitely presented modules on ℝⁿ,
[the multiparameter closure theorem](multiparameter-closure.md) gives attainment,
closedness and distance-zero separation directly from finite generators and relations.
