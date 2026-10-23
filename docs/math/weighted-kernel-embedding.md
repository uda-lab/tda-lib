# Weighted Gaussian kernel embedding of persistence diagrams

A finite family of birth–death points is embedded in the reproducing kernel Hilbert space
of a Gaussian kernel, each point scaled by a weight. This is the persistence weighted
Gaussian kernel of Kusano–Fukumizu–Hiraoka, restricted to finite occurrence families
and to the finite part of a diagram.

## Conventions

- **Points and occurrences.** Kernel arguments are birth–death points p = (b,d) in ℝ².
  An occurrence family is a map x : I → ℝ² from a finite label type. Equal values at
  distinct labels count separately. A diagram contributes its canonical finite
  occurrences, so multiplicity is kept and essential bars are omitted.
- **Kernel.** For every real σ,
  k_σ(p,q) = exp(−((p₁−q₁)² + (p₂−q₂)²) / (2σ²)).
  This uses the Euclidean squared distance of `WithLp 2 (ℝ × ℝ)`, not the maximum norm
  that `ℝ × ℝ` carries in the library. At σ = 0, Lean's division gives the all-ones
  kernel, which is still positive semidefinite, so no hypothesis on σ is needed.
- **Weight.** The weight is the persistence-image `Weight A B`, evaluated at the
  birth–persistence point T(b,d) = (b,d−b). The effective birth–death weight p ↦ w(Tp)
  vanishes on the diagonal. The constants A and B enter only the stability bounds.
- **Positive semidefiniteness.** This is mathlib's `Matrix.PosSemidef`. It requires a
  Hermitian matrix whose quadratic form is nonnegative at every finitely supported
  coefficient vector, so it makes sense for an arbitrary index type.

## Statements

Let H_σ be mathlib's RKHS `RKHS.OfKernel` of k_σ and let k_σ(·,p) ∈ H_σ be its kernel
function. These functions satisfy ⟨k_σ(·,p), k_σ(·,q)⟩ = k_σ(p,q) and have norm one. The
weighted embedding of an occurrence family x is

Φ(x) = Σᵢ w(T xᵢ) k_σ(·, xᵢ),

so Φ(x)(z) = Σᵢ w(T xᵢ) k_σ(z, xᵢ) (KFH18 eq. (3)). With the linear kernel

K_L(x,y) = Σᵢ Σⱼ w(T xᵢ) w(T yⱼ) k_σ(xᵢ, yⱼ),

the RKHS inner product is ⟨Φ(x), Φ(y)⟩ = K_L(x,y) (eq. (12)). The squared distance is
‖Φ(x) − Φ(y)‖² = K_L(x,x) + K_L(y,y) − 2 K_L(x,y) (§3.3). These are theorems about the
inner product and norm of `RKHS.OfKernel`; none of them defines a norm by the Gram formula.

For any family of diagrams D_a, indexed by an arbitrary type, two Gram matrices are positive
semidefinite. The first is the linear Gram matrix ⟨Φ(D_a), Φ(D_b)⟩. The second is the
(k,w)-Gaussian matrix exp(−‖Φ(D_a) − Φ(D_b)‖² / (2τ²)) (eq. (13)), for every real τ.

## Proof route

1. **Hadamard powers.** The entrywise n-th power of a positive semidefinite real matrix is
   positive semidefinite. The zeroth power is the all-ones matrix, the inner-product kernel
   of a constant family. The induction step is mathlib's Schur product theorem
   `Matrix.PosSemidef.hadamard`, which already holds for arbitrary index types.
2. **Entrywise exponential.** At a finitely supported coefficient vector c, each entry
   has the series exp(Mᵢⱼ) = Σₙ Mᵢⱼⁿ / n!. Summing over the finite support gives a series
   whose n-th term is the quadratic form of (n!)⁻¹ times the n-th Hadamard power. Each
   term is nonnegative, so the sum is too. No matrix exponential or partial-sum limit is
   used.
3. **Inner-product kernels.** For any family v in a real inner product space, the quadratic
   form at c equals ‖Σᵢ cᵢ vᵢ‖² over the support of c. Mathlib's `Matrix.posSemidef_gram`
   covers only finite index types.
4. **Diagonal rescaling.** The matrix dᵢ Mᵢⱼ dⱼ is the Hadamard product of M with the
   rank-one kernel dᵢ dⱼ, which is the inner-product kernel of d in ℝ.
5. **Gaussian factorization.** From ‖a−b‖² = ‖a‖² − 2⟨a,b⟩ + ‖b‖²,
   exp(−‖a−b‖²/(2σ²)) = exp(−‖a‖²/(2σ²)) · exp(⟨a,b⟩/σ²) · exp(−‖b‖²/(2σ²)).
   The middle factor is the entrywise exponential of a nonnegative multiple of an
   inner-product kernel, and the outer factors are a diagonal rescaling.
6. **Operator-valued kernel.** Mathlib's RKHS API takes kernels with values in ℝ →L[ℝ] ℝ.
   The scalar kernel times the identity is positive semidefinite by mathlib's
   characterization `RKHS.posSemidef_tfae`, applied to the scalar quadratic form. Moore's
   theorem `RKHS.OfKernel.kernel_ofKernel` recovers the kernel, which gives the
   reproducing identities above.
7. **Diagram Gram matrices.** The linear Gram matrix is step 3 applied to the family of
   diagram embeddings, and the Gaussian Gram matrix is step 5 applied to the same family.

## Stability

Bandwidths enter only through |σ| and |τ|; no sign hypothesis is assumed. With Lean's
division, at σ = 0 the kernel is identically one and all kernel functions coincide, so the
feature bounds of steps 1–2 read 0 ≤ 0. Weighted features w(Tp) k_σ(·,p) still differ at
σ = 0. There the term √2·B/|σ| vanishes, and the weighted bounds of steps 3–4 keep the
constant 2A from the weight. The same holds at τ = 0 for the second level. For σ, τ > 0
the constants are those of KFH18.

1. **Unit-vector lemma.** In a real inner product space, unit vectors u, v with
   ⟨u,v⟩ = exp(−r²/(2s²)) satisfy ‖u − v‖² = 2 − 2exp(−r²/(2s²)) ≤ r²/s², hence
   ‖u − v‖ ≤ |r|/|s|. The inequality is 1 − e^{−t} ≤ t. This is the argument of KFH18
   Lemma 16 up to eq. (25), stated once and instantiated twice.
2. **Feature bound.** With r the Euclidean distance of p and q, the lemma gives
   ‖k_σ(·,p) − k_σ(·,q)‖ ≤ ‖p − q‖₂/|σ| (eq. (25)). Since ‖p − q‖₂ ≤ √2‖p − q‖_∞, this
   is at most (√2/|σ|)‖p − q‖_∞ in the library's maximum norm on ℝ × ℝ (eq. (26)).
3. **Weighted feature.** Let F(p) = w(Tp) k_σ(·,p) for a `Weight A B`, where B bounds the
   weight and A is its maximum-norm Lipschitz constant in birth–persistence coordinates.
   The map T has Lipschitz constant 2 (KFH18 Lemma 17), so for all points
   ‖F(p) − F(q)‖ ≤ C‖p − q‖ and ‖F(p)‖ ≤ C · |p₂ − p₁|/2 with
   C = 2A + √2·B/|σ|. In the notation of Proposition 10 this is L_k B₂ + B_k L₂ with
   B_k = 1, L_k = √2/|σ|, B₂ = B and L₂ = 2A. Diagonal points have F = 0.
4. **Embedding stability.** These are the pointwise hypotheses of the additive-feature
   matching bound, so ‖Φ(x) − Φ(y)‖ ≤ C times the total finite cost of every finite
   partial matching of positive occurrence families, and hence C times the finite
   first-order matching cost. For positive diagrams with finite bottleneck distance, the
   diagram embeddings differ by at most C (|D| + |E|) d_B(D,E), where |D| counts finite
   occurrences. This is the shape of Proposition 10 with the library's finite first-order
   cost in place of d_{W₁}; no Wasserstein distance is defined.
5. **Second level.** The Gaussian kernel exp(−‖a − b‖²/(2τ²)) on any real inner product
   space E generates its own `RKHS.OfKernel`, with unit-norm kernel functions ψ_τ(a). At
   E = H_σ, the kernel functions of the diagram embeddings are a feature map of the
   (k,w)-Gaussian kernel K_G(D,E) = exp(−‖Φ(D) − Φ(E)‖²/(2τ²)) of eq. (13). The lemma
   gives ‖ψ_τ(Φ D) − ψ_τ(Φ E)‖ ≤ ‖Φ D − Φ E‖/|τ|. Writing K_G(D,E) − K_G(D,E') as
   ⟨ψ_τ(Φ D), ψ_τ(Φ E) − ψ_τ(Φ E')⟩ and applying Cauchy–Schwarz gives
   |K_G(D,E) − K_G(D,E')| ≤ ‖Φ E − Φ E'‖/|τ|. Composition with step 4 gives
   matching-cost and count-times-bottleneck bounds with constant C/|τ|. KFH18 does not
   state this second-level bound; it is the argument of Lemma 16 applied to the RKHS H_σ.

`TDA.Persistence.GaussianFeature` holds steps 1 and the generic Gaussian RKHS of step 5.
`TDA.Persistence.WeightedKernelStability` holds the remaining statements. The examples
check the bound against an exact feature distance and show by a negative control at
σ = 1/2 that the factor 1/|σ| cannot be dropped. They also cover the zero-bandwidth,
unmatched, empty-family and diagonal boundaries, a diagram-level bound, and the
second-level kernel.

## Norm distinction

The embedding lives in H_σ, whose norm comes from the Gaussian kernel. It is not the
`PiLp 1` pixel vector of [Gaussian persistence images](persistence-images.md), and it is
not an L² persistence surface. KFH18 §4.1.3 and footnote 15 explain that comparing
the two needs a bandwidth rescaling and works only in the Gaussian case. The library
claims no such identification.

## Injectivity on finite diagrams

For every real σ, the Gaussian kernel factors as

`k_σ(z,p) = g_σ(z) χ_{σ,p}(z) g_σ(p)`,

where `g_σ(z) = exp(−‖z‖²/(2σ²))` and `χ_{σ,p}(z) = exp(⟨z,p⟩/σ²)`. At σ = 0,
Lean's division makes every factor 1. The functions `χ_{σ,p}` are exponential characters
of the additive group of `ℝ × ℝ`, viewed as characters of its multiplicative wrapper.
When σ ≠ 0, distinct points give distinct characters, and Dedekind's independence lemma
(`linearIndependent_monoidHom`) makes them linearly independent. The positive factors in
the factorization transfer this to the Gaussian kernel functions `k_σ(·,p)` and to the
RKHS features.

Consequently, the Gaussian Gram matrix on every injective finite family of points is
strictly positive definite. This is the finite-support form of KFH18 Proposition 6:
the map sending a finitely supported signed measure `μ` to
`Σₚ μ(p) k_σ(·,p)` is injective, and the corresponding RKHS distance is zero exactly
when the two signed measures agree. For a diagram, the weighted measure is
`Σₚ count_D(p) w(Tp) δₚ`, so equality of embeddings identifies finite points with
multiplicity when the weight is pointwise positive on both finite parts. If the diagrams
are positive and the weight is positive on the open upper half-plane, that pointwise
hypothesis follows automatically. If the essential parts are also assumed equal, the
embedding then recovers the whole diagram.

The hypotheses are substantive. Repeated labels make the Gram matrix only positive
semidefinite (F2), σ = 0 makes every feature equal and destroys measure injectivity
(F3), and a vanishing weight erases finite points (F5). In particular, positivity on
all finite points is needed for the general diagram characterization, while `IsPositive`
is needed when positivity is supplied only on the open upper half-plane.

## Weighted-kernel RKHS isometry

A real function g weights a scalar kernel k by
kᵍ(x,y) = g(x) k(x,y) g(y). If k is positive semidefinite and g is nonzero at every
point of its domain X, multiplication `(Tf)(x) = g(x) f(x)` is a real linear
isometry equivalence between their RKHSs. Its inverse divides by g(x).
`KernelWeight.weightIsometry` constructs this equivalence on the completed spaces,
without continuity, boundedness or a uniform positive lower bound on g.

The construction compares the finite feature sums Σ c(x) g(x) k(·,x) and
Σ c(x) kᵍ(·,x), whose Gram kernels agree. A coefficient vector gives zero in one
sum exactly when it gives zero in the other, even for dependent features.
Nonvanishing makes the weighted base sections span a dense
subspace; the weighted-kernel sections are dense by the RKHS reproducing property.
Mathlib's `LinearEquiv.extendOfIsometry` extends their correspondence to a surjective
isometry of the completed spaces. The reproducing property gives the multiplication
formula for all functions, not only the finite sums.

`UpperPoint` is the open upper half-plane b < d. `UpperSpace σ` and
`WeightedUpperSpace σ w` use the Gaussian restricted to this same domain, with
`upperWeight w p = w (birthPersistence p)`. The vector `upperEmbedding` sums weighted
base sections, while `weightedUpperEmbedding` sums sections of the weighted kernel.
For pointwise positive weights, `upperWeightIsometry` sends the former vector to
the latter. The arctan specialization
works for C > 0 despite weights approaching zero near the diagonal. Every real σ is
allowed: the isometry survives the degenerate all-ones kernel at σ = 0.

The inner products and pair distances of `weightedUpperEmbedding` agree with
the existing full-plane `embedding`. The corresponding `weightedUpperDiagramEmbedding`
identities retain finite occurrences and multiplicity, omit essential bars, and need
neither weight positivity nor a bandwidth restriction. This finite-sum comparison
does not identify the entire full-plane RKHS with the upper-domain RKHS; such a claim
would need a separate density proof.

The multiplication map and positive-domain identification are KFH18 Proposition 7
and eq. (4). Source positivity implies the generic nonvanishing assumption; the
source's C₀-universality premise is unnecessary for this direct isometry proof, and
no C₀-universality theorem is claimed here. Positive source bandwidth is a
specialization of the all-real construction. The finite-diagram bridge to the
existing full-plane embedding is a library derivation. The examples include a
nonzero finite-domain vector erased by a vanishing weight, and the isometry for
the all-ones kernel at zero bandwidth.

## Lean interfaces and sources

`TDA.Persistence.GaussianGram` holds the matrix results, `gaussianGram` and the
birth–death `kernel`. `TDA.Persistence.WeightedKernel` defines `kernelOp`, `Space`,
`featureAt`, `embedding`, `diagramEmbedding` and `linearKernel`, and proves the
evaluation, inner-product, distance and Gram statements. The examples cover concrete
kernel values and a two-point quadratic form. A negative control shows that dropping the
minus sign destroys positive semidefiniteness. The remaining examples cover repeated
occurrences, an RKHS distance, the diagonal and essential-only boundary cases, and a
Gaussian diagram Gram entry. All definitions are noncomputable; no kernel evaluation
algorithm is provided.

`TDA.Persistence.WeightedKernelInjectivity` contains the character factorization,
linear-independence, strict-positive-definiteness and finite-support injectivity results,
as well as the weighted-measure and diagram-characterization theorems. The companion
`TDA.Persistence.WeightedKernelInjectivityExamples` module contains the F1–F7 consumers
and negative controls.

The construction follows [Kusano–Fukumizu–Hiraoka](references.md#KFH18) §2.3, §3.1
eq. (3), §3.3 eqs. (12)–(13) and the product principle in footnote 10. The RKHS and the
Schur product theorem come from the pinned [mathlib](references.md#mathlib-0df444a). The
Hadamard-power, exponential-series and factorization steps are the standard textbook
route; no further source is claimed for them.

The [arctan weight and Rips consumers](arctan-weight-rips-kernel.md) note instantiates
these bounds at KFH18's w_arc weight and composes them with the Rips bound.
The size-dependent total-persistence and finite-bar bounds used by bounded-carrier consumers
are stated in [total persistence and finite Rips–Čech bounds](total-persistence.md).

Not covered here: C₀-universality on general measures, Proposition 8/Theorem 9,
random features and essential-bar kernels.
