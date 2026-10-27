# Actual vertex representations of right incidence modules

Let `k` be a field and `S` a finite lattice. Write `WithTop S` for `S` with a newly adjoined
top element, and let

`P = { (a,b) ∈ WithTop S × WithTop S | a ≤ b }`,

ordered coordinatewise; this is the repository's `PairPoset S`. Let `A` be the actual incidence
algebra on `P` and `R = Aᵐᵒᵖ`. For an actual right `A`-module `M`, use its canonical `k`-module
structure restricted along `k → R`. The diagonal matrix unit `e(p)` defines the vertex fiber

`V(M)(p) = {m ∈ M | e(p) • m = m}`.

For `p ≤ q`, the actual opposite-incidence matrix unit `u(p,q)` gives the covariant map
`x ↦ u(p,q) • x`. Actual module maps restrict to these fibers, defining the additive functor
`vertexFunctor` to `PModule k P`. This construction uses every interval-pair vertex, including
diagonal vertices, and applies to arbitrary actual modules.

The diagonal units are orthogonal and sum to one. Their actions give the explicit `k`-linear
equivalence

`M ≃ₗ[k] (p : P) → V(M)(p)`,

with projections `m ↦ e(p) • m` and inverse the finite sum of the fiber inclusions. A natural
transformation `α : V(M) ⟶ V(N)` reconstructs the actual linear map

`m ↦ Σ p, (α.app p)(e(p) • m)`,

where each fiber value is included into `N`. Naturality makes this map commute with the actual
matrix units; the finite matrix-unit expansion and central field scalars then prove actual
`R`-linearity. The two reconstruction laws give the explicit Hom equivalence and show that
`vertexFunctor` is fully faithful.

For an actual module map, injectivity and surjectivity are equivalent to those properties on
every vertex fiber. For actual composable module maps `f : L → M` and `g : M → N` with `f ≫ g = 0`,
the range of `f` equals the kernel of `g` exactly when this holds on every vertex fiber: project
a global preimage to each fiber in one direction, and sum the fiberwise preimages in the other.
Consequently the actual row `L ⟶ M ⟶ N` is short exact if and only if its image under
`vertexFunctor` is pointwise short exact. This is ordinary categorical short-exactness, with no
finite-dimensionality or rank-exactness premise.

Each vertex fiber is a submodule of the canonically restricted `k`-module, and the finite
projector decomposition identifies that module with a finite product of its fibers. Thus the
actual module is finite-dimensional over `k` if and only if every vertex fiber is finite-dimensional.

The definitions and right-module convention follow the persistence-functor setup of
[BOOS24-v3, §2.4, Lemma 2.1 and Remark 2.2](references.md#BOOS24-v3). This is the explicit
vertex-fiber construction for the library's actual interval-pair incidence ring. The results do
not assert essential surjectivity or an equivalence with all `PModule k P`; projective-dimension
transport and numerical incidence bounds are separate. The examples use the Bool interval-pair
poset to exhibit a nonzero off-diagonal matrix-unit action, zero fibers, a nonidentity recovered
regular-module endomorphism, a split exact row, and a finite-dimensional regular module.
