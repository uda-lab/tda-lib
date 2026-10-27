# Right-module base change along the diagonal quotient

Let `k` be a field, `S` a finite lattice, `A` the interval-pair incidence algebra, `I` its
diagonal ideal, and `B = A/I`. Put `R = Aᵐᵒᵖ`, `C = Bᵐᵒᵖ`, and let `f : R →+* C` be the
opposite of the actual quotient projection. Modules in `ModuleCat R` and `ModuleCat C` are
right modules over `A` and `B`, respectively.
Write `Res` for restriction along `f` and `E` for the quotient-extension functor
`extensionFunctor`.

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

The kernel `J = ker f` is idempotent: `quotientKernel_mul_self` proves `J * J = J` from the
actual diagonal ideal and its idempotent generator. This identity shows that `E` carries every
short exact row with restricted quotient-module cokernel to a short exact row. The restriction on
the cokernel is essential to this argument.

For every quotient module `N` and every projective resolution `P` of `Res(N)`,
`extensionMappedResolution_exactAt_one` proves that `E(P)` is exact at degree one. Hence
`extension_leftDerived_one_isZero` gives the actual categorical vanishing
`IsZero ((E.leftDerived 1).obj (Res(N)))`. The theorem
`rightVertexExtension_leftDerived_one_isZero` specializes this result to each strict vertex. The
previous degree-zero comparison remains the canonical `C`-linear isomorphism
`((E.leftDerived 0).obj (Res(Vᵥ))) ≅ Vᵥ`.

For an interval pair `q = (a,b)` with `a,b ∈ WithTop S` and `a ≤ b` (so either endpoint may be
`⊤`), put `d(q) = (a,a)`, and write `δ_{p,r}` for the actual incidence matrix unit at a comparable
pair `p ≤ r` of interval-pair indices. For a right `A`-module `M`, define the additive group
`G(M) = ∏_q {m ∈ M | m · δ_{d(q),d(q)} = m}` and the assembly
`τ_M((m_q)) = Σ_q m_q · δ_{d(q),q}`, with both product and sum indexed by all interval pairs.
The functor `G` is exact: project a preimage onto the fixed subgroup in each coordinate. The image
of `τ_M` is the actual quotient relation submodule, and `τ_M` is injective for projective `M`, by
regular-module columns, arbitrary free modules, and the projective splitting. The higher-degree
cycle lift uses these exactness, image, and injectivity properties.

For every right-incidence module `M`, every actual projective resolution `P` of `M`, and every
`n ≥ 2`, `extensionMappedResolution_exactAt` proves that `E(P)` is exact at degree `n`.
Consequently, `extension_leftDerived_isZero_atLeastTwo` proves the actual categorical statement
`IsZero ((E.leftDerived n).obj M)` in that range. For a restricted quotient module `Res(N)`, this
higher result combines with the degree-one theorem to give exactness of every positive degree and
vanishing of every positive left-derived value. The same conclusion specializes to each strict
vertex.

The range is deliberately positive: on restricted modules the unaugmented mapped resolution has
the existing degree-zero comparison with `N`, which may be nonzero. No degree-one result for an
arbitrary right-incidence module, exactness at degree zero, numerical dimension bound, `2n−2`
bound, or stability statement is established here.

The quotient extension is the right-module base-change construction in [BOOS24-v3, §2.4,
Definition 5.4 and Notation 5.9](references.md#BOOS24-v3). Its idempotent-kernel factorization
formalizes the degree-one mechanism for the restricted-cokernel row. Separately, the actual
diagonal-column construction gives the higher-degree projective-ideal/column mechanism of
[Lemma 5.6](references.md#BOOS24-v3) for this interval-pair quotient. The underived vertex
comparison is also consistent with the right-module setup of [Lemma 5.7](references.md#BOOS24-v3).

The separate vertex-tensor vanishing in [the resolution and derived comparison](incidence-vertex-tor.md)
uses the other derived variable and is not a premise here; no derived tensor comparison is asserted.
The Bool and singleton examples exercise the zero and regular modules, projectivity, vertex and
degree-zero comparisons, the counit class formula, naturality for a nonidentity endomorphism, and
the degree-one and degree-two consumers.
