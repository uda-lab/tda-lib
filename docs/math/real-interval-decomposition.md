# Real interval decomposition for pointwise finite-dimensional modules

Let `k : Type u` be a field and let
`M : PModule.{u,0,u} k ℝ` have finite-dimensional fibers. The coefficient field
and every fiber use universe `u`, while the real parameter type is in universe
zero. `AlgebraicFamily.familyModule` forms the fiberwise algebraic direct sum:
at each parameter, its vectors are coefficient families with finite support
across occurrences. The theorem
`RealIntervalDecomposition.exists_interval_decomposition` gives an occurrence
type `J : Type`, nonempty order-convex sets `I j ⊆ ℝ`, and a natural
isomorphism

`M ≅ AlgebraicFamily.familyModule (fun j => SupportInterval.module (I j) ...)`.

Each `SupportInterval.module` has fiber `k` on its support and zero outside;
its maps preserve the scalar on the support and vanish when a transition leaves
it. Open, closed, half-open and singleton supports, either unbounded tail, and
the whole line are allowed. The theorem also proves
`∀ t, Set.Finite {j | t ∈ I j}`: only finitely many occurrences are active at
each parameter. Here `Type` is universe zero and places no countability bound
on `J`. This endpoint does not assert a decomposition interface with an
independent occurrence universe.

The construction is noncanonical and noncomputable. It needs no finite critical
grid, zero left tail, continuity condition, supplied basis, invertible
structure maps, or prior decomposition. Its proof builds compatible interval
pieces and then refines them to scalar copies.

## Cuts and interval quotients

A cut `c` partitions the real line into a downward-closed lower part and an
upward-closed upper part, with every lower point strictly below every upper
point. For a persistence module, the cut defines four subspaces in each fiber
`M(t)`. Images arriving from the lower and upper sides are

`imageMinus(c,t) = ⨆_{s ∈ c.lower, s ≤ t} im(M(s ≤ t))`,

`imagePlus(c,t) = ⨅_{s ∈ c.upper, s ≤ t} im(M(s ≤ t))`;

the kernels of maps toward the lower and upper sides are

`kernelMinus(c,t) = ⨆_{t ≤ r ∈ c.lower} ker(M(t ≤ r))`,

`kernelPlus(c,t) = ⨅_{t ≤ r ∈ c.upper} ker(M(t ≤ r))`.

The suprema are sums of subspaces and the infima are intersections. Empty
families retain their usual bottom/top meanings, which matters at unbounded
ends. For a nonempty downward-directed family of subspaces, finite-dimensionality
makes its intersection equal one of its members. Choose a member of least finite
rank; downward directedness gives a member contained in it and any other chosen
member, and rank minimality forces equality with the least-rank member. This is
stabilization by finite dimension, not by finiteness of the field or parameter
set.

For a pair of cuts `l,r`, the support is `l.upper ∩ r.lower`. On it, define

`intervalPlus(t) = imagePlus(l,t) ∩ kernelPlus(r,t)`,

`intervalMinus(t) = (imageMinus(l,t) ∩ kernelPlus(r,t))
                 + (imagePlus(l,t) ∩ kernelMinus(r,t))`.

The second is a subspace of the first. The quotient
`intervalPlus(t) / intervalMinus(t)` records the part born after the lower
cut and surviving before the upper cut. For `p ≤ q` in the support,
finite-dimensionality at `M(p)` gives surjectivity of the restricted
`intervalPlus` transition. The lower subspace pulls back exactly, so the
induced quotient transition is injective as well as surjective. Thus these
quotients are naturally identified along the interval. The interval subspaces
and quotient transport are derived from the module; they are not extra input
data.

## Compatible lifts and one interval subfunctor

A compatible section on a parameter set assigns a vector to every parameter
and commutes with every forward structure map. If the transitions within a
nonempty real subset are surjective, evaluation from its space of compatible
sections onto any chosen fiber is surjective. The construction uses a decreasing
coinitial sequence beginning at that fiber: a minimum gives an eventually
constant sequence, and otherwise rational density supplies one. The inverse
limit theorem for a sequence of surjections gives compatible values on the
sequence; extending from a sequence point below each target gives a section on
the whole subset. This lift theorem itself needs no finite-dimensionality.

Apply it to the module of `intervalPlus` spaces on a cut interval. Evaluation
onto the interval quotient is surjective, and its kernel is the same at every
point of the interval. Choose one complement to this kernel in the global
section space. The same complement evaluates bijectively onto every interval
quotient, so its images complement `intervalMinus` in all the `intervalPlus`
fibers. Compatibility makes these images commute with the interval maps.
Extending them by zero off the support is preserved by every structure map,
including one that crosses the right endpoint. This produces a genuine
interval-supported subfunctor of `M`; it does not choose unrelated complements
fiber by fiber. The section space need not be finite-dimensional, while the
chosen complement is finite-dimensional because it is isomorphic to a quotient
of a finite-dimensional fiber.

## From cut pieces to scalar intervals

The construction considers all pairs of real cuts whose interval support is
nonempty, with one anchor chosen in each support. The selected complements
span every fiber: a proper subspace determines birth and death cuts for which
the corresponding complement contains a vector outside it. They are also
independent: in any finite zero relation, choose a nonzero term `x` maximal
first in its birth cut and then, among equal birth cuts, in its death cut.
Group the earlier-birth terms into `y` and the equal-birth, earlier-death terms
into `z`. Cut order puts `y` in `imageMinus` and `z` in
`imagePlus ∩ kernelMinus` for the selected cuts. The selected term and `z` lie
in `kernelPlus` (because `x` lies in `intervalPlus` and `kernelMinus` is
contained in `kernelPlus`), so the zero relation puts `y` there too. Thus
`y + z` lies in `intervalMinus`. The selected complement is disjoint from that
subspace, forcing `x = 0`, contrary to its choice. This proves fiberwise
directness and spanning.

`CutDecomposition.sumIso` is the resulting natural isomorphism from the
algebraic sum of the interval-supported cut subfunctors to `M`. Those
subfunctors can have dimension greater than one on their supports. For each,
the finite-dimensional global complement has a finite basis; its compatible
basis sections give scalar interval copies, including zero fibers outside the
support. Regrouping these occurrences yields `RealIntervalDecomposition.scalarIso`,
also oriented from the algebraic sum to `M`. The existence theorem uses its
inverse to state `M ≅` the scalar interval sum. Both APIs concern
`PModule.{u,0,u} k ℝ`; the occurrence indices are in `Type`. This universe
convention is not a countability assertion, nor a claim for arbitrary
independent carrier and coefficient universes.

The intermediate `CutDecomposition.finite_active` counts nonzero cut
subfunctor fibers; some chosen complements have rank zero. After scalar
refinement, an occurrence is nonzero at `t` exactly when `t` lies in its
support. Finite-dimensionality of the sum therefore proves finite activity of
the scalar supports at each parameter.

## Algebraic sums, products and accumulation

An algebraic sum at a fiber contains coefficient families with finite support.
Its canonical map to the product is always injective. It is an isomorphism
when only finitely many summands are nonzero at each parameter. For the scalar
decomposition this condition is the proved finite activity above, so the
existing product-based `RealBarcode.familyModule` can represent the same
module under that condition. An unrestricted product is not the algebraic sum.

Finite activity means pointwise finite overlap, not topological local
finiteness of the support family. For example, the nonempty disjoint intervals
`(1/(n+2), 1/(n+1)]` have at most one active occurrence at any real parameter,
yet every neighborhood of zero meets infinitely many of them. Their algebraic
sum has finite-dimensional fibers and nonzero fibers at selected endpoints.
Thus an infinite family can accumulate at zero while meeting the theorem's
finite-activity condition.

## Finite observations and existing realizations

Let `c : Fin N ↪o ℝ` be a strictly increasing finite observation list. Only
finitely many scalar occurrences meet its sample points: each sample has
finitely many active occurrences, and there are finitely many samples. A
nonempty convex real support restricts to a consecutive block of sample
indices. If its first and last indices are `a` and `b`, that block is the
finite-index interval `[a,b+1)`; a support missing all samples contributes
nothing. This half-open convention concerns sample indices only and is
independent of whether the real support includes its endpoints. Restricting the
real decomposition therefore gives a finite sum of visible occurrences. The
existing finite rank-barcode uniqueness theorem shows
that the rank barcode of `reindex c M` is exactly the multiset of those sampled
intervals, retaining one contribution per occurrence and hence repeated bars.

A singleton support contributes precisely when its point is sampled. Empty
observation lists and empty visible families are allowed. These finite samples
do not determine unsampled support, behavior between samples, or whether a
finite terminal index represents an infinite real tail.

`IntervalCompatibility` identifies support modules with the existing
half-open real interval modules, whose support is `{t | birth ≤ t ∧ t < death}`
and whose death may be `⊤`. The natural isomorphisms preserve occurrences in
finite endpoint lists and diagram realizations. The `constructibleIso` result
additionally assumes the existing constructibility predicate and
finite-dimensionality at the supplied sample levels; it does not change that
API's endpoint or tail conventions.

The fixtures include the empty sum as the zero module, whole-line and open or
closed left tails, singleton supports, and nonidentity transition maps. The
compatible-lift examples prescribe sections on a left-unbounded open interval,
a closed interval, and a singleton, and include a rational sign-change map
sending `1` to `-1`. `IntervalCompatibility.ephemeralIso` is specifically for
the rational module `PModule.{0,0,0} ℚ ℝ`: it identifies the algebraic sum over
all real singleton occurrences with that module, whose strict maps are zero. It
illustrates why the occurrence type need not be countable and why singleton
summands remain in the isomorphism theorem.

This theorem is about pointwise finite-dimensional real persistence modules.
It does not prove a decomposition theorem for arbitrary linear orders, a
canonical multiplicity-uniqueness result, or an infinite or q-tame isometry.
Finite-dimensional images across strict inequalities do not imply
finite-dimensional fibers, so the q-tame theory has a different scope. No
decomposition algorithm or new homology or geometric-filtration construction
is part of this API.

## Source and review boundary

The explanation above is derived from the Lean declarations and proofs and the
mathematical contract recorded in [#506](https://github.com/uda-lab/tda-lib/issues/506).
That contract attributes the endpoint to Crawley-Boevey's Theorem 1.1 and the
selected compatible-lift route, including Lemma 4.1; this attribution has not
been checked anew against the article text. The [CB14-v3 register entry](references.md#CB14-v3)
records the metadata and evidence. Fresh primary-text comparison remains
pending in #506. This is a code/contract-based account, not a new source match
or full-proof certification.
