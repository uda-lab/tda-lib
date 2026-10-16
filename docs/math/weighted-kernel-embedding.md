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
  vanishes on the diagonal. The constants A and B play no role here.
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

## Norm distinction

The embedding lives in H_σ, whose norm comes from the Gaussian kernel. It is not the
`PiLp 1` pixel vector of [Gaussian persistence images](persistence-images.md), and it is
not an L² persistence surface. KFH18 §4.1.3 and footnote 15 explain that comparing
the two needs a bandwidth rescaling and works only in the Gaussian case. The library
claims no such identification.

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

The construction follows [Kusano–Fukumizu–Hiraoka](references.md#KFH18) §2.3, §3.1
eq. (3), §3.3 eqs. (12)–(13) and the product principle in footnote 10. The RKHS and the
Schur product theorem come from the pinned [mathlib](references.md#mathlib-0df444a). The
Hadamard-power, exponential-series and factorization steps are the standard textbook
route; no further source is claimed for them.

Not covered here: stability against matching costs or the bottleneck distance,
injectivity or universality of the embedding, the RKHS isomorphism f ↦ w f, random
features and essential bars.
