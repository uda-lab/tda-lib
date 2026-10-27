# Right-module base change along the diagonal quotient

Let `k` be a field, `S` a finite lattice, `A` the interval-pair incidence algebra, `I` its
diagonal ideal, and `B = A/I`. Put `R = Aᵐᵒᵖ`, `C = Bᵐᵒᵖ`, and let `f : R →+* C` be the
opposite of the actual quotient projection. Modules in `ModuleCat R` and `ModuleCat C` are
right modules over `A` and `B`, respectively.

For `M : ModuleCat R`, form the `R`-submodule

`K(M) = span_R { a • m | a ∈ ker f, m ∈ M }`.

The quotient `M/K(M)` is annihilated by `ker f`. Factoring its actual `R`-action through the
surjection `f` therefore equips it with a `C`-action. This defines `extensionFunctor`; its
public class and map formulas identify the `C`-action with the original action after applying
`f`.

The functor is left adjoint to restriction along `f`. The adjunction is constructed from the
actual hom-set equivalence: an `R`-linear map into a restricted `C`-module kills `K(M)` and
factors uniquely through `M/K(M)`. Restriction preserves epimorphisms because its underlying
maps remain surjective. The adjunction criterion consequently proves that extension preserves
projectives; its left-adjoint property proves preservation of finite colimits, hence right
exactness. No preservation of arbitrary monomorphisms or short exact rows is claimed.

For every `N : ModuleCat C`, the natural counit isomorphism
`extensionFunctor (restrictScalars N) ≅ N` sends the class of `n` to `n` and has inverse
`n ↦ [n]`. The actual regular right module `R` extends to the regular right module `C` by
the quotient map. For each strict vertex `v`, restriction of the existing quotient vertex
module gives an actual `R`-module; its action is the pulled-back character, and it is simple
because `f` is surjective. Its extension is the original quotient vertex module by the
counit. The canonical comparison
`((extensionFunctor.leftDerived 0).obj (restrictScalars Vᵥ)) ≅ Vᵥ` is `C`-linear.

This is the underived quotient base-change construction used in the right-module argument of
[BOOS24-v3, §2.4 and Lemma 5.7](references.md#BOOS24-v3). Positive derived vanishing and exactness
of a base-changed projective resolution are separate results; neither follows from the
projective-preservation statement alone. The Bool and singleton examples exercise the zero and
regular modules, projectivity, the vertex and degree-zero comparisons, the counit class formula,
and naturality for a nonidentity endomorphism.
