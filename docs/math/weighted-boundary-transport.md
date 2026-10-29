# Gaussian embedding stability for finite persistence measures

Weighted Gaussian embeddings vary continuously under native first-order boundary
transport. The inputs are positive finite Borel measures on the strict birth–death
half-plane, including unequal masses and measures with nonatomic or noncompact
support. Finite diagrams are recovered by their atomic measures.

## Measures, weights and distances

Write H = {(b,d) ∈ ℝ² : b < d} and δ(b,d) = (d−b)/2. The ground distance is
the maximum-coordinate distance on birth–death pairs. A boundary plan has the
specified interior marginals and free diagonal marginals; its first-order cost
is the integral of this ground distance. The native distance BT₁ is the infimum
over all such plans, with values in [0,∞]. See
[the boundary-plan construction](boundary-transport-metric.md).

Let w be nonnegative, bounded by B and A-Lipschitz in maximum-norm
birth–persistence coordinates, with w(b,0) = 0 and A,B ≥ 0. Put T(b,d) = (b,d−b).
For nonzero bandwidth σ, the full-plane Gaussian kernel and weighted feature are

\[
k_\sigma(p,q)=\exp\!\left(-\frac{\|p-q\|_2^2}{2\sigma^2}\right),
\qquad F_\sigma(p)=w(Tp)k_\sigma(\cdot,p).
\]

The norm below is the norm of this kernel's reproducing kernel Hilbert space.
Its sections have norm one, so ‖Fσ(p)‖ ≤ B. For every finite original measure μ,
the weighted feature is Bochner integrable and

\[
\Phi_\sigma(\mu)=\int_H F_\sigma(p)\,d\mu(p).
\]

This is the existing `weightedPersistenceEmbedding σ (upperWeight w) μ`.
`Interior` and `UpperPoint` are the same strict-half-plane subtype; the bridge
records their measurable equivalence and the integral identity explicitly.

## Extended and real estimates

Set C = 2A + √2 B/|σ|. For arbitrary finite original μ and ν,

\[
\operatorname{ofReal}\|\Phi_\sigma(\mu)-\Phi_\sigma(\nu)\|
\le \operatorname{ofReal}(C)\,\mathrm{BT}_1(\mu,\nu).
\]

The inequality is in `ENNReal`, so the right side may be infinite. Neither
integrability of the embedding nor this estimate needs a diagonal or ambient
first moment. If ∫δ dμ and ∫δ dν are finite, the existing transport finiteness
theorem proves BT₁ finite, and conversion to real numbers gives

\[
\|\Phi_\sigma(\mu)-\Phi_\sigma(\nu)\|
\le C\,\operatorname{toReal}(\mathrm{BT}_1(\mu,\nu)).
\]

The Lean statements also allow σ = 0 under the library's totalized division
convention: the kernel is then constant one, and the same proof retains the
weight term 2A. The usual nonzero-bandwidth theorem is a specialization.

## Direct boundary-plan proof

The existing pointwise estimates give
‖Fσ(p)−Fσ(q)‖ ≤ C‖p−q‖∞ and ‖Fσ(p)‖ ≤ Cδ(p).
The feature vanishes on the diagonal, so it extends by zero through the collapsed
boundary. For any admissible plan π, its interior marginal equations identify
the two endpoint integrals with Φσ(μ) and Φσ(ν). Free diagonal mass contributes
zero. Every admissible plan is finite, which makes both bounded endpoint features
integrable even when its transport cost is infinite.

The norm-of-integral inequality and the pointwise bound give
‖Φσ(μ)−Φσ(ν)‖ ≤ C∫‖p−q‖∞ dπ in extended nonnegative values.
Taking the infimum over the actual admissible plans gives the native estimate.
The zero-constant case uses an explicit admissible deletion/insertion plan before
passing to the infimum. The argument requires no optimizer or probability
normalization.

## Atomic inputs and approximation

For a finite indexed family with nonnegative real masses mᵢ at points pᵢ,

\[
\Phi_\sigma\!\left(\sum_i m_i\delta_{p_i}\right)
=\sum_i m_iF_\sigma(p_i).
\]

Zero masses disappear and coincident coordinates add their masses. The native
finite weighted diagram uses this same atomic measure, and its finite transport
optimum agrees with the all-plan value. Thus the stability bound applies directly
to fractional weighted diagrams and to the existing unit-occurrence embedding.

For finite original μ with finite first diagonal moment, let Dₙ be the existing
`quantizedDiagram μ n`. Each atomic measure μDₙ has exactly μ's original mass,
and BT₁(μ,μDₙ) tends to zero. The new estimate therefore proves
Φσ(μDₙ) → Φσ(μ) in the actual RKHS norm. These are the native
[same-mass quantizations](boundary-transport-approximation.md), with no new
choice of approximants.

The consumers include a nonatomic band of bars (t,t+2), t ∈ [0,1], and the
countable family (2ⁿ⁺²,2ⁿ⁺²+2) with masses 2⁻ⁿ⁻¹. The latter has mass one and
diagonal moment one, while its ambient first moment diverges. It demonstrates
why the real bound and approximation theorem use diagonal moments.

## Sources and scope

[Kusano–Fukumizu–Hiraoka](https://jmlr.org/papers/v18/17-317.html), equation (3),
Proposition 10 and Lemma 16, supplies the weighted Gaussian embedding and
finite-diagram stability context. Here Lk = √2/|σ|, Bk = 1, B₂ = B and L₂ = 2A.
The direct theorem for arbitrary finite original measures and native boundary
transport is a separately proved library extension.

Boundary transport originates with
[Figalli–Gigli](https://cvgmt.sns.it/paper/488/) in bounded Euclidean domains with
quadratic cost. [Divol–Lacombe](https://arxiv.org/abs/1901.03048) develops the
persistence-measure setting; the upper-half-plane, general-exponent and
maximum-norm formulation is distinct from Figalli–Gigli's original setting.
The independent ordinary-Wasserstein comparison and corrected-article source
comparison retain their [separate boundary](boundary-transport-ot-dependency.md).

[Adams et al.](https://www.jmlr.org/papers/v18/16-337.html) studies persistence
images and pixel norms. [Obayashi–Hiraoka](https://arxiv.org/abs/1706.10082) studies
linear prediction and inverse analysis. Neither supplies the RKHS stability
claim proved here. Fixed-pixel stability, infinite-original-mass transport,
essential bars and exponents above one lie outside this result.
