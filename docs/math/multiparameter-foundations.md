# Interval modules, presentations and rank-exact lifting

The persistence-module API supports constructions on an arbitrary preorder,
including coordinatewise ordered real vector spaces. The results below provide
interval geometry, Hall neighbor bounds, two-sided matchings and distance bounds
for finite rectangle sums, together with free presentations and lifting lemmas.
Rank-exact resolutions require further arguments.

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

## Hall bounds for finite rectangle sums

Let k be a field, n ≥ 1 and ε ≥ 0. Take two finite families Rᵢ and Sⱼ of
nonempty bounded rectangles in ℝⁿ, retaining the inclusion choice at every
endpoint. `RectangleFamily.module` is their finite biproduct of interval
modules. Indices label occurrences, so repeated rectangles remain distinct.

A rectangle is δ-significant if some p and p + δ·1 both belong to its support.
`RectangleHall.significant_iff_transition_ne_zero` identifies this condition
with nonvanishing of its actual δ transition. Put ρ = (2n−1)ε. A neighbor of
Rᵢ is an occurrence Sⱼ whose interval module is ρ-interleaved with that of Rᵢ.
For a selected set A of source indices, let μ(A) consist of all their neighbor
indices. Given an actual ε-interleaving of the two family modules,
`RectangleHall.card_le_neighbors` proves

```text
|A| ≤ |μ(A)|
```

whenever every Rᵢ selected by A is 2ρ-significant. The inequality counts
occurrences in both families. It includes empty A and ε = 0; at the latter
parameter closed singletons are significant. The radius is ε in one
coordinate and 3ε in two coordinates.

The proof orders the selected occurrences by the sum of their lower and
upper endpoints, breaking equal sums by the number of plus decorations.
A lower endpoint is plus-decorated when excluded, and an upper endpoint when
included. A nonzero shifted rectangle map has one scalar on its overlap.
For ordered significant endpoints of a two-step path, the geometric bounds
give a common source, middle and target grade; this proves that composition
multiplies their scalars, including closed-endpoint equality cases.

Expanding the interleaving equations through the finite biproduct gives sums
of these component paths. In the ordered entries, every intermediate
occurrence outside μ(A) contributes zero. The restricted scalar matrices
therefore multiply to a triangular matrix with diagonal one. Its full rank
is at most the number of intermediate occurrences, proving the inequality.
This implements the finite bounded part of
[Bjerkevik's Lemmas 4.7–4.9](https://doi.org/10.1007/s00454-021-00298-0).

## Two-sided occurrence matchings

A partial occurrence matching is an injection from selected source indices to
target indices; its unselected source and target indices are unmatched. At
radius ρ it is admissible when paired rectangle modules are actually
ρ-interleaved and every unmatched module on either side is actually
ρ-interleaved with zero. The existing `OccurrenceMatching` type records the
partial injection, while `RectangleMatching.IsMatching` states these module
conditions. Repeated rectangles retain their distinct occurrence indices.

A rectangle module is ρ-interleaved with zero exactly when its transition by
2ρ vanishes, equivalently when it is not 2ρ-significant. The zero natural maps
give the forward construction; the composite equation forces the reverse
implication. This equivalence retains closed-endpoint equality and ε = 0.

For finite bounded rectangle families over any field, n ≥ 1 and an actual
ε-interleaving, set ρ = (2n−1)ε. The Hall inequality above and Mathlib's Hall
theorem give an injection from the 2ρ-significant source occurrences to
admissible target partners. Reversing the interleaving supplies the corresponding
injection for significant target occurrences. These injections need not agree.
Relation-preserving Schröder–Bernstein combines them into one partial matching
covering both significant sets. Its auxiliary dummy labels allow deletion only
of non-significant occurrences and are discarded from the resulting matching.
`RectangleMatching.exists_matching` exports the actual pair and deletion
interleavings, with no Hall or matching premise.

This is the finite bounded matching-existence conclusion of
[Bjerkevik's Theorem 4.3](https://doi.org/10.1007/s00454-021-00298-0), using
Theorem 4.10 and the following Cantor–Bernstein argument.

## Assembly and distance bounds

Let M and N be the finite biproduct families associated with R and S.
An admissible radius-ε matching supplies actual interleavings of the paired
rectangle modules and actual interleavings with zero for all unmatched modules
on both sides. `IsMatching.interleaving` assembles these into an actual
ε-interleaving of M and N, in every coordinate dimension.

The assembled maps have a finite occurrence matrix. A matched edge contributes
the forward and reverse maps of the same chosen pair interleaving; every other
entry is zero. The partial injection gives at most one path through each row
and column of a composite. For a matched diagonal entry, the pair's composite
equation gives the summand transition by 2ε. An unmatched diagonal entry is zero,
as required by its interleaving with zero; off-diagonal entries are zero.
The public `RectangleFamily.component_ext` and reconstruction lemmas lift these
component equations to the two full family equations. The underlying realization
remains the existing finite biproduct.

Write d_I(M,N) for the extended infimum of finite parameters admitting an actual
interleaving. Define d_B(R,S) as the extended infimum of finite parameters
admitting an actual occurrence matching, including its deletion witnesses.
`RectangleMatching.bottleneckDistance` implements this second value. Both take
values in the extended nonnegative reals, with empty infima equal to infinity.
Assembly and the matching-existence theorem give, for n ≥ 1,

`d_I(M,N) ≤ d_B(R,S) ≤ (2n−1) d_I(M,N)`.

The first inequality follows by taking the infimum of all assembled witnesses.
For the second, each actual ε-interleaving yields a matching at `(2n−1)ε`.
Multiplication by this finite positive coefficient commutes with both infima,
even when the witness set is empty. Thus no optimal radius or attainment is
assumed. This is the finite bounded distance conclusion of
[Bjerkevik's Theorem 4.3](https://doi.org/10.1007/s00454-021-00298-0), using
Definition 2.9 and the following matching-to-interleaving observation.

Endpoint decorations can prevent attainment. Over ℚ, the singleton-supported
interval module and the zero module have both distances zero: they are
interleaved, and admit a deletion matching, at every positive radius. They
have neither a zero-radius interleaving nor a zero-radius matching. Zero
distance is therefore not identified with a parameter-zero witness.

For n = 1 the coefficient is one, giving equality for this decorated occurrence
family distance. The common half-open subclass connects to the existing
one-dimensional endpoint-diagram API below. In dimension two, the following
example attains the factor three.

## Sharpness in two coordinates

Fix any field k. `RectangleSharpExample.source` and `.target` are the two
Fin 3-indexed families of open rectangles in
[Bjerkevik's Example 5.2](https://d-nb.info/1242337318/34), pp. 117–118:

| Occurrence | Source Rᵢ | Target Sᵢ |
| --- | --- | --- |
| 0 | (0,10) × (1,11) | (1,11) × (0,10) |
| 1 | (0,12) × (-1,11) | (1,9) × (0,12) |
| 2 | (2,10) × (1,9) | (-1,11) × (2,10) |

Let M and N be their existing finite biproduct modules. The forward matrix F
has rows indexed by R and columns indexed by S; the reverse matrix G has
rows indexed by S and columns indexed by R:

```text
F = [1 1 1]       G = [-1  1  1]
    [1 1 0]           [ 1  0 -1]
    [1 0 1]           [ 1 -1  0].
```

Every nonzero entry is an admissible shifted rectangle map. All endpoint
sums are 22, and every rectangle is 6-significant, so the proved scalar
composition law applies to each two-step path. The identities FG = GF = I
give both family interleaving equations by component extensionality.
`RectangleSharpExample.interleaving` is this actual 1-interleaving. Its public
component laws recover F and G. The integer identities hold in every field,
including characteristic two.

For ρ < 3, the occurrences R₁ and R₂ are 2ρ-significant, hence neither can be
unmatched. Nonzero forward and reverse maps impose endpoint inequalities.
Pairing either occurrence with S₁ or S₂ would force ρ ≥ 3. Both would
therefore need S₀, contrary to the matching's injection. Thus every actual
matching has radius at least 3. Conversely all endpoint differences are at
most 3, and matching equal indices gives an actual 3-matching with no
deletions. `bottleneckDistance_eq_three` proves d_B(R,S) = 3.

The proved factor-three matching theorem sends every actual ε-interleaving
of M and N to a 3ε-matching. The obstruction then gives ε ≥ 1. Together
with the explicit witness this proves `interleavingDistance_eq_one`, namely
d_I(M,N) = 1. Both lower bounds test all witnesses before taking infima.
The two distances are attained in this example. `fails_smaller_constant`
shows that every coefficient below three fails on this same pair, and
`interleavingDistance_lt_bottleneckDistance` gives a finite rectangle example
where the two distances differ. These results concern dimension two; they
make no optimality assertion for dimensions three and above.

## One-dimensional barcode compatibility

The common objects are finite occurrence-indexed families of intervals [b,d)
with real endpoints b < d. Their one-coordinate rectangles have included lower
endpoints and excluded upper endpoints. The existing `RealBarcode.intervalModule`
uses exactly this support; its endpoint-pair constructor also permits empty
supports and essential right tails. The bridge restricts to positive length
and finite death, as required for these nonempty bounded rectangles.

`RectangleBarcodeBridge.halfOpenRectangle` constructs each rectangle.
`familyIso` identifies its finite categorical biproduct with the reindexing of
the existing real barcode coordinate product along evaluation at the unique
coordinate. `diagram` places each endpoint pair in the existing diagram
multiset, with no essential occurrences. `realizationIso` extends the comparison
to the existing diagram realization by a value-preserving occurrence bijection.
Equal endpoint values remain separate coordinates; an empty occurrence family
is allowed. These are natural isomorphisms of modules, including all structure
maps and inactive fibers.

For endpoint families x and y, let D_x and D_y be these diagrams. The original
diagram bottleneck takes the infimum of maximum endpoint-pair costs and diagonal
deletion costs, the latter equal to half the interval length. The rectangle
definition instead asks for actual pair and zero interleavings. The bridge proves

`d_B(rectangles x, rectangles y) = bottleneck(D_x,D_y)
 = realInterleavingDistance(realize D_x, realize D_y)`.

Passing from endpoint costs to actual witnesses uses the half-open endpoint
comparisons and the closed deletion threshold d−b ≤ 2ε. The reverse passage
requires care: two short intervals can be ε-interleaved even when their endpoint
pair cost exceeds ε. For example, [0,1) and [100,101) have such a radius-one
interleaving with zero maps, whereas pairing their endpoints costs 100. If either
interval has a nonzero 2ε transition, the two actual composite laws force both
pair maps nonzero, and the proved Hom endpoint bounds force pair cost at most ε.
Consequently every excessive-cost pair has both ends deletable. Removing precisely
those pairs gives a numerical matching at the same radius. Taking infima proves
the equality without selecting an optimal radius. The actual witness conversions
also yield `interleaving_iff_cost_matching` at every ε ≥ 0.

This is the finite bounded half-open common subclass of the interval and matching
conventions in [Bauer–Lesnick, §§2.1–2.3 and 3.1–3.3](https://arxiv.org/html/1311.3681v4).
It connects Bjerkevik's n=1 conclusion to the library's original endpoint diagram
and real barcode distance APIs. It does not identify all decorated interval modules
with half-open modules. In the raw half-open constructor, b ≥ d gives the zero
module; a nonempty half-open rectangle therefore requires b < d. In contrast,
the decorated rectangle [b,b] is a nonzero singleton module with zero distance
from zero and no parameter-zero interleaving. On the common positive half-open
subclass, `real_distance_zero_iff_diagram_eq` and `real_distance_zero_iff_iso`
derive separation from the existing endpoint diagram result. That conclusion
does not apply to the larger decorated domain.

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

The two collapse maps send the old generators through their free covers and
the added delayed generators to their prescribed interleaving images.
Both interleaving equations show that crossing and then using the shifted
opposite collapse agrees with collapse followed by the interleaving map.
Consequently the opposite delayed relations also vanish. The quotient maps
then descend by the cokernel universal property. Redundant-generator
elimination and the quotient universal property in both directions prove
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
applies to rank-exact quotient maps over a field.

## Individual hook endomorphisms and indecomposability

Fix a field k and a partially ordered grade set. A finite-death hook with
birth i < j has a unit vector at its birth, and every supported vector is a
scalar multiple of its transport from i. Naturality therefore forces an
endomorphism to act by the same scalar throughout the support. The same
argument applies to a principal upset through its single free generator.
`Hook.end_eq_smul_id` and `HookInfinity.end_eq_smul_id` express these actual
natural transformations, and `endRingEquiv` in each namespace identifies
the endomorphism ring with k. The comparison reads the coefficient at birth;
its inverse is scalar multiplication of the identity. The multiplication
law uses the actual categorical composition, whose order is reversed in
Mathlib's endomorphism ring.

Since the field has only zero and one as idempotents, these endomorphism
rings have only the zero map and identity as idempotents. A decomposition
into two nonzero summands would give a further idempotent by projecting
onto either summand. Thus `Hook.indecomposable` and
`HookInfinity.indecomposable` prove indecomposability in Mathlib's existing
categorical sense. Neither a finite grade set nor bounded support is needed.
Consumers include the two-coordinate hook with birth (0,0) and death (1,1),
whose support contains the whole ray {(t,0) | t ≥ 0}, and its genuinely
decomposable sum with a second identical occurrence.

An isomorphism of interval modules identifies their supports, including the
empty support: a nonzero supported unit cannot map into an inactive fiber.
`SupportInterval.support_eq_of_iso` proves this without assuming connectedness.
For individual nonzero hooks the least support point determines birth, and
the excluded principal upset determines finite death. Consequently
`Hook.nonempty_iso_iff` recovers both endpoints, while
`HookInfinity.nonempty_iso_iff` recovers birth. Finite and infinite death are
never isomorphic. In contrast, death at or before birth has empty support
and is a zero object, so the nonzero hook assertions require i < j.

These results supply the individual-hook ingredients for
[Botnan–Oppermann–Oudot–Scoccola, §2.6 and Theorem 2.7](https://arxiv.org/html/2208.00300v3).
Order convexity alone does not assert indecomposability for an arbitrary
support. The results here do not establish uniqueness of finite hook
decompositions, classification of rank-projective retracts or minimal
rank-projective resolutions.

## Enough rank projectives on finite posets

Fix a field k and a finite partially ordered set P. `IsRankProjective Q`
means that every natural map from Q lifts along every rank-exact quotient.
The hook lifting results above give this property for finite-death hooks and
principal upsets. It is preserved by finite categorical biproducts, natural
isomorphisms and retracts. This relative property is distinct from lifting
along all ordinary epimorphisms.

Let M be a pointwise finite-dimensional P-module. For each grade a, choose a
basis of M(a); for every a < b, choose a basis of the kernel of M(a→b).
`FiniteHookDeflation.Index M` labels each basis vector separately. A fiber
basis vector contributes a principal upset born at a; a kernel basis vector
contributes the hook with birth a and death b. The number of occurrences is

```text
sum over a<b of dim ker M(a→b) + sum over a of dim M(a).
```

Their existing categorical biproduct is `FiniteHookDeflation.module M`.
The corresponding generator maps assemble to the natural transformation
`FiniteHookDeflation.π M`. Fiber bases make it surjective at every grade.
For any vector killed by M(a→b), its expansion in the kernel basis gives
a lift in the hook sum also killed at b. At a = b the only such vector is
zero. Thus `lift_kernel` proves the dying-element criterion at every pair,
and `rankExact` derives rank additivity for the actual categorical kernel
sequence. Both the hook sum and its kernel have finite-dimensional fibers.
No rank equality or already existing deflation is an input.

The hook sum is rank projective. Consequently a pfd module M on P is rank
projective exactly when its constructed deflation admits a natural section:
`isRankProjective_iff_retract`. In particular every rank projective is a
retract of a finite hook sum. This supplies enough relative projectives in
the finite-poset part of
[Botnan–Oppermann–Oudot–Scoccola, Theorem 2.7(1)](https://arxiv.org/html/2208.00300v3).
The construction retains repeated occurrences and includes zero modules and
the empty poset. Consumers also give a branching-poset pfd module whose
rank-exact deflation does not split, and check the construction in
characteristic two.

The deflation can have redundant summands; it is not asserted to be a minimal
projective cover. An exact-category instance, classification of retracts as
hook sums, minimal resolutions, the real-grid transfer and signed barcode
stability remain further results.

## Pullbacks and composites of rank-exact deflations

Fix a field k and partially ordered grades. A rank-exact deflation is a
natural map π:M→N that is the quotient of an actual rank-exact short exact
sequence; `IsRankDeflation` expresses this condition. Its
`rankExact_kernel` law identifies the actual categorical kernel sequence as
rank exact. Ordinary pointwise surjectivity alone is insufficient. For
example, the principal upset born at zero on the two-grade chain surjects
onto the hook dying at grade one. The target's unit dies, but every
transition of the principal upset preserves its coefficient, so that unit
has no dying lift. `epi_not_rankDeflation` verifies this obstruction.

Given a rank-exact deflation π:M→N and any f:T→N with T pointwise finite
dimensional, form the existing categorical pullback X. At grade p, a pair
(m,t) is compatible when πₚ(m)=fₚ(t). Maps from the principal upset born at
p represent m and t. Their compatibility gives a map into X by the
pullback universal property, and its value at birth constructs the pair
in X(p). `PullbackFiber.mk` and its projection laws express this
construction. Conversely, the two projections distinguish every vector
in X(p), by the same generator property and categorical extensionality.
Thus X(p) embeds linearly into M(p)×T(p), proving it finite dimensional.

The projection X→T is surjective: lift fₚ(t) through πₚ and pair that lift
with t. If t is killed between a≤b, naturality shows that fₐ(t) is killed
as well. Rank exactness of π gives a lift m killed at b. The compatible
pair (m,t) is killed in X because both projected images vanish. The kernel
criterion therefore proves rank additivity for the actual kernel of X→T.
`IsRankDeflation.pullback_snd` establishes this closure without assuming an
exact-category instance or the desired lifting property.

Identity on any pfd module is a rank-exact deflation. For two composable
deflations, lift each dying vector through the second and then through
the first, retaining the same death at both steps. Surjectivity also
composes, so the kernel criterion proves `IsRankDeflation.comp` for the
actual composite kernel sequence. Consumers apply these laws to successive
finite hook deflations and to a nonidentity pullback, with genuinely
nonzero dying images, zero base change and characteristic two.

These prove the deflation-side closure laws in
[Botnan–Oppermann–Oudot–Scoccola, §2.12](https://arxiv.org/html/2208.00300v3),
including the pullback step used in Appendix A's Lemma A.1. They do not
establish the full exact structure or its inflation/pushout laws.

## One-step persistent Schanuel

Fix a field k and coordinatewise ordered ℝⁿ. Suppose K→P→M and L→Q→N
are rank-exact short exact sequences and P,Q are rank projective. The
rank-exactness hypothesis includes pointwise finite dimensionality; no
finite grid or finite presentation is required here. An actual
ε-interleaving i between M and N, for any finite ε≥0, induces an actual
ε-interleaving

\[
P\oplus L[\varepsilon]\quad\longleftrightarrow\quad K[\varepsilon]\oplus Q.
\]

Here A[ε](a)=A(a+ε). This is the rank-exact specialization of
[Botnan–Oppermann–Oudot–Scoccola, Appendix A Lemma A.1](https://arxiv.org/html/2208.00300v3).
`RankSchanuel.interleavingOfSequences` uses the original K and L; it does
not require chosen sections or identifications with categorical kernels.

Write α:P→M and β:Q→N for the quotient maps. Form the crossed pullbacks
X=Q[ε]×_{N[ε]}P and Y=P[ε]×_{M[ε]}Q, using α followed by i's forward
map, and β followed by its reverse map. A vector of X(a) is a compatible
pair (q,p), with q in Q(a+ε) and p in P(a). The forward map sends it to
(P(a→a+2ε)(p),q) in Y(a+ε). Naturality and the interleaving equations
prove compatibility. The symmetric map gives the reverse direction;
both composites are the corresponding double transitions. The public
projection laws expose these coordinates without unfolding the proofs.
This crossed-pullback interleaving only requires a coefficient ring.

Over the field, rank-exact pullback closure makes X→P and Y→Q
rank-exact deflations. Relative projectivity lifts identity to derive
their sections. Mathlib's splitting theorem and its pullback-kernel and
shift-kernel comparisons then identify X with P⊕(ker β)[ε] and Y with
(ker α)[ε]⊕Q. `IsPointwiseShortExact.kernelIso` identifies K with ker α
and L with ker β, preserving the original inclusions. Transporting the
constructed maps proves the stated interleaving with the same ε.

At ε=0 and a common quotient, the zero-shift comparison gives
`RankSchanuel.kernelSumIso`. Concrete consumers use two-copy and three-copy
covers of an unbounded planar hook. The first kernel inclusion is the
diagonal (1,−1), so the given-sequence theorem genuinely transports a
noncanonical kernel term. Both actual kernels are nonzero, including in
characteristic two. A principal-upset consumer detects a nonzero forward
map at positive width through its public projection law. Zero modules
and n=0 are also allowed; ℝ⁰ has one grade, rather than no grades.

This one-step theorem is an input to persistent Schanuel for resolutions.
It does not construct finite minimal resolutions, bound their length or
prove signed barcode stability.

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
