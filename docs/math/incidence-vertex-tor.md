# Derived vertex tensor for the interval-pair incidence algebra

Let `k` be a field and `S` a finite lattice. Define the interval-pair poset
`P = { (a,b) ∈ (WithTop S) × (WithTop S) | a ≤ b }`, where `WithTop S` adds `∞` to `S`.
Its diagonal vertices are the pairs `(a,a)`, and a strict vertex is `v = (a,b) ∈ P` with
`a < b`. The incidence algebra `A = k[P]` has the actual two-sided diagonal ideal `I` generated
by those diagonal vertices, and `B = A/I`. Each strict vertex determines an algebra character
`χᵥ : A → k`. For a left `A`-module `M`, the character relation quotient is the `k`-module

`Fᵥ(M) = M / spanₖ { a • m − χᵥ(a) • m }`.

The `k`-action on `M` is restricted along `k → A`. Incidence-linear maps descend to the quotient,
and the balanced universal property gives `Fᵥ ⊣ Res(χᵥ)`. In particular `Fᵥ` is additive,
preserves finite colimits, and is right exact. The library uses Mathlib's left-derived functors of
this actual functor, with the derived functor taken in the left-module argument.

The resolution is the concrete projective resolution

`0 → I ↪ A ↠ B → 0`,

with `A` in degree zero, `I` in degree one and zero modules in all higher degrees. The regular
module is free on one generator; projectivity of the actual ideal is established by the diagonal
ideal splitting. Exactness is the actual quotient short exact row, so no resolution or
projectivity assumption is supplied by the consumer.

After applying `Fᵥ`, degree one vanishes by the character-coinvariant calculation for `I`, and all
later terms vanish because the additive functor sends zero objects to zero. The homology of the
mapped complex therefore vanishes in each positive degree. Mathlib's comparison from the actual
projective resolution identifies this homology with the left-derived functor, proving

`IsZero ((Fᵥ.leftDerived n).obj B)` for every `n > 0`, including `n = 1`.

In degree zero, the canonical comparison `leftDerived 0 ≅ Fᵥ` followed by the quotient
coinvariant equivalence gives `((Fᵥ.leftDerived 0).obj B) ≅ k`, and therefore `Fᵥ(B) ≅ k`.
The actual coinvariant class of `1 : B` maps to `1 : k`, so this value is nonzero. The public
scalar-transport equivalence is
`IncidenceVertexTor.diagonalQuotientVertexCoinvariantsEquiv`; its simp law
`diagonalQuotientVertexCoinvariantsEquiv_mkQ` sends each represented quotient class to the
corresponding natural quotient class. The degree-zero comparison's unit simp law
`diagonalQuotient_leftDerivedZeroIso_hom_unit` sends the quotient-unit class to `1`.

This specializes the projectivity-and-short-exact-row mechanism of
[BOOS24-v3, Lemma 5.6](references.md#BOOS24-v3) to the interval-pair incidence algebra and its
diagonal ideal. The result concerns the strict-vertex calculation at `B`; it does not classify
all simple `A`-modules or prove a global-dimension comparison between `A/I` and `A`, or bound the
global dimension of `A`. The Hom-cokernel estimate and the grid and real-coordinate `2n−2` bounds
are proved separately (see
[finite-grid Hom-module and Hom-cokernel dimensions](finite-rank-projective-hom-quotient-dimension.md)
and the API guide's real-coordinate degree bound). The Bool and
singleton strict-vertex consumers work over arbitrary fields; `rationalField_infinite` supplies a
concrete infinite-field example.
