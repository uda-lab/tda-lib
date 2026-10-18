import TDA.Persistence.WeightedKernel

/-!
# Injectivity of the weighted Gaussian kernel embedding

This module records the Gaussian factorization and Dedekind independence of its
exponential characters, proves strict positive definiteness on distinct points,
and gives the finite-support form of KFH18 Proposition 6.  No C₀-universality
statement and no Proposition 7 are claimed.  The final diagram results identify
finite parts with multiplicity under the stated pointwise positivity hypothesis
on the weight.
-/

namespace TDA.Persistence.WeightedKernel

open Matrix
open scoped InnerProductSpace

/-! ## Characters and the Gaussian factorization -/

/-- The exponential character associated with a point and bandwidth. -/
noncomputable def expCharacter (σ : ℝ) (p : ℝ × ℝ) :
    Multiplicative (ℝ × ℝ) →* ℝ :=
  { toFun := fun z => Real.exp ((z.toAdd.1 * p.1 + z.toAdd.2 * p.2) / σ ^ 2)
    map_one' := by simp
    map_mul' := by
      intro z z'
      change Real.exp (((z.toAdd + z'.toAdd).1 * p.1 +
        (z.toAdd + z'.toAdd).2 * p.2) / σ ^ 2) =
        Real.exp ((z.toAdd.1 * p.1 + z.toAdd.2 * p.2) / σ ^ 2) *
          Real.exp ((z'.toAdd.1 * p.1 + z'.toAdd.2 * p.2) / σ ^ 2)
      rw [← Real.exp_add]
      congr 1
      simp only [Prod.fst_add, Prod.snd_add]
      ring }

/-- Evaluation formula for `expCharacter`. -/
theorem expCharacter_apply (σ : ℝ) (p : ℝ × ℝ)
    (z : Multiplicative (ℝ × ℝ)) :
    expCharacter σ p z =
      Real.exp ((z.toAdd.1 * p.1 + z.toAdd.2 * p.2) / σ ^ 2) := rfl

/-- Distinct points give distinct exponential characters when `σ` is nonzero. -/
theorem expCharacter_injective {σ : ℝ} (hσ : σ ≠ 0) :
    Function.Injective (expCharacter σ) := by
  intro p q hpq
  have h₁ := congrArg (fun f => f (Multiplicative.ofAdd ((1, 0) : ℝ × ℝ))) hpq
  have h₂ := congrArg (fun f => f (Multiplicative.ofAdd ((0, 1) : ℝ × ℝ))) hpq
  rw [expCharacter_apply, expCharacter_apply, toAdd_ofAdd] at h₁
  rw [expCharacter_apply, expCharacter_apply, toAdd_ofAdd] at h₂
  have hs : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  have hp₁ : p.1 = q.1 := by
    simpa using (div_left_inj' hs).mp (Real.exp_injective h₁)
  have hp₂ : p.2 = q.2 := by
    simpa using (div_left_inj' hs).mp (Real.exp_injective h₂)
  exact Prod.ext hp₁ hp₂

/-- The scalar Gaussian factor in the kernel factorization. -/
noncomputable def gaussFactor (σ : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (2 * σ ^ 2))

/-- The Gaussian factor is strictly positive. -/
theorem gaussFactor_pos (σ : ℝ) (z : ℝ × ℝ) : 0 < gaussFactor σ z :=
  Real.exp_pos _

/-- Factorization of the birth--death Gaussian kernel into exponential characters. -/
theorem kernel_eq_factor (σ : ℝ) (z p : ℝ × ℝ) :
    kernel σ z p = gaussFactor σ z * expCharacter σ p (Multiplicative.ofAdd z) *
      gaussFactor σ p := by
  by_cases hσ : σ = 0
  · simp [kernel, gaussFactor, expCharacter, hσ]
  · simp only [kernel, gaussFactor, expCharacter_apply, toAdd_ofAdd]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hσ]
    ring

/-- The kernel functions are linearly independent for nonzero bandwidth. -/
theorem linearIndependent_kernelFun {σ : ℝ} (hσ : σ ≠ 0) :
    LinearIndependent ℝ (fun p : ℝ × ℝ => fun z : ℝ × ℝ => kernel σ z p) := by
  have hchars : LinearIndependent ℝ
      (fun p : ℝ × ℝ => (expCharacter σ p : Multiplicative (ℝ × ℝ) → ℝ)) := by
    exact (linearIndependent_monoidHom (Multiplicative (ℝ × ℝ)) ℝ).comp
      (expCharacter σ) (expCharacter_injective hσ)
  rw [linearIndependent_iff']
  intro s c hsum p hp
  have hsum' :
      ∑ q ∈ s, (c q * gaussFactor σ q) •
        (expCharacter σ q : Multiplicative (ℝ × ℝ) → ℝ) = 0 := by
    funext z
    let z' : ℝ × ℝ := z.toAdd
    have hz := congrFun hsum z'
    have hz' : gaussFactor σ z' *
        (∑ q ∈ s, (c q * gaussFactor σ q) *
          expCharacter σ q (Multiplicative.ofAdd z')) = 0 := by
      calc
        gaussFactor σ z' *
            (∑ q ∈ s, (c q * gaussFactor σ q) *
              expCharacter σ q (Multiplicative.ofAdd z')) =
            ∑ q ∈ s, gaussFactor σ z' *
              ((c q * gaussFactor σ q) *
                expCharacter σ q (Multiplicative.ofAdd z')) := by
                  rw [Finset.mul_sum]
        _ = ∑ q ∈ s, c q * kernel σ z' q := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [kernel_eq_factor]
          ring
        _ = 0 := by
          simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using hz
    have hz'' := (mul_eq_zero.mp hz').resolve_left (gaussFactor_pos σ z').ne'
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul, ofAdd_toAdd, z'] using hz''
  have hcoeff := (linearIndependent_iff'.mp hchars) s
    (fun q => c q * gaussFactor σ q) hsum' p hp
  exact (mul_eq_zero.mp hcoeff).resolve_right (gaussFactor_pos σ p).ne'

/-- The RKHS kernel features are linearly independent for nonzero bandwidth. -/
theorem linearIndependent_featureAt {σ : ℝ} (hσ : σ ≠ 0) :
    LinearIndependent ℝ (featureAt σ) := by
  apply LinearIndependent.of_comp
    ((RKHS.coeCLM ℝ : Space σ →L[ℝ] (ℝ × ℝ → ℝ)).toLinearMap)
  have h : ((RKHS.coeCLM ℝ : Space σ →L[ℝ] (ℝ × ℝ → ℝ)).toLinearMap ∘
      featureAt σ) = fun p z => kernel σ z p := by
    funext p z
    exact featureAt_apply σ p z
  rw [h]
  exact linearIndependent_kernelFun hσ

/-! ## Strict positive definiteness -/

/-- A nonzero finitely supported combination of distinct kernel features is nonzero. -/
theorem featureAt_sum_ne_zero {σ : ℝ} (hσ : σ ≠ 0) {x : ℝ × ℝ →₀ ℝ} (hx : x ≠ 0) :
    (x.sum fun p a => a • featureAt σ p) ≠ 0 := by
  intro hzero
  apply hx
  exact (linearIndependent_iff_injective_finsuppLinearCombination.mp
    (linearIndependent_featureAt hσ)) (by
      simpa [Finsupp.linearCombination_apply] using hzero)

/-- The Gaussian kernel matrix is positive definite for nonzero bandwidth. -/
theorem posDef_kernel {σ : ℝ} (hσ : σ ≠ 0) :
    (Matrix.of (kernel σ) : Matrix (ℝ × ℝ) (ℝ × ℝ) ℝ).PosDef := by
  refine ⟨(posSemidef_kernel σ).isHermitian, ?_⟩
  intro x hx
  have hquad :
      x.sum (fun p a => x.sum (fun q b => star a *
        (Matrix.of (kernel σ) : Matrix (ℝ × ℝ) (ℝ × ℝ) ℝ) p q * b)) =
        ⟪x.sum (fun p a => a • featureAt σ p),
          x.sum (fun q b => b • featureAt σ q)⟫_ℝ := by
    simp only [Finsupp.sum, sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, Matrix.of_apply, star_trivial]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      simp only [inner_featureAt, kernel_symm]
      ring
  rw [hquad]
  exact real_inner_self_pos.mpr (featureAt_sum_ne_zero hσ hx)

/-- Restricting the strict Gaussian Gram matrix along an injective point family. -/
theorem posDef_kernel_family {σ : ℝ} (hσ : σ ≠ 0) {I : Type*}
    (x : I → ℝ × ℝ) (hx : Function.Injective x) :
    (Matrix.of fun i j => kernel σ (x i) (x j)).PosDef := by
  exact (posDef_kernel hσ).submatrix hx

/-! ## Finitely supported measures -/

/-- The finite-support kernel embedding from KFH18 Proposition 6, eq. (2). -/
noncomputable def measureEmbedding (σ : ℝ) :
    (ℝ × ℝ →₀ ℝ) →ₗ[ℝ] Space σ :=
  Finsupp.linearCombination ℝ (featureAt σ)

/-- Evaluation of the finite-support embedding on a point, as in KFH18 Proposition 6. -/
theorem measureEmbedding_apply (σ : ℝ) (μ : ℝ × ℝ →₀ ℝ) (z : ℝ × ℝ) :
    measureEmbedding σ μ z = μ.sum fun p c => c * kernel σ z p := by
  rw [measureEmbedding, Finsupp.linearCombination_apply,
    ← RKHS.coeCLM_apply (𝕜 := ℝ), map_finsuppSum]
  simp only [Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, RKHS.coeCLM_apply, Pi.smul_apply, featureAt_apply, smul_eq_mul]

/-- The embedding sends a single atom to its weighted kernel feature. -/
theorem measureEmbedding_single (σ : ℝ) (p : ℝ × ℝ) (c : ℝ) :
    measureEmbedding σ (Finsupp.single p c) = c • featureAt σ p := by
  simp [measureEmbedding, Finsupp.linearCombination_single]

/-- The finite-support embedding is injective for nonzero bandwidth; this is the
finite-support form of KFH18 Proposition 6. -/
theorem measureEmbedding_injective {σ : ℝ} (hσ : σ ≠ 0) :
    Function.Injective (measureEmbedding σ) := by
  change Function.Injective (Finsupp.linearCombination ℝ (featureAt σ))
  exact linearIndependent_iff_injective_finsuppLinearCombination.mp
    (linearIndependent_featureAt hσ)

/-- The KFH18 Proposition 6 distance clause for finitely supported signed measures. -/
theorem norm_measureEmbedding_sub_eq_zero_iff {σ : ℝ} (hσ : σ ≠ 0)
    {μ ν : ℝ × ℝ →₀ ℝ} :
    ‖measureEmbedding σ μ - measureEmbedding σ ν‖ = 0 ↔ μ = ν := by
  constructor
  · intro h
    exact measureEmbedding_injective hσ (norm_sub_eq_zero_iff.mp h)
  · intro h
    subst ν
    simp

/-! ## Diagram measures and finite-part characterization -/

/-- The finitely supported signed measure obtained by weighting finite diagram points. -/
noncomputable def weightedMeasure {A B : ℝ} (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) : ℝ × ℝ →₀ ℝ :=
  ((finitePart D.points).map fun p => Finsupp.single p (w (birthPersistence p))).sum

private theorem multiset_sum_single_apply {s : Multiset (ℝ × ℝ)}
    (f : ℝ × ℝ → ℝ) (q : ℝ × ℝ) :
    ((s.map fun p => Finsupp.single p (f p)).sum) q =
      (s.count q : ℝ) * f q := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply,
      Finsupp.single_apply, Multiset.count_cons]
    by_cases h : q = a
    · subst q
      simp [ih]
      ring
    · simp [h, ih]
      intro h'
      exact absurd h'.symm h

/-- Pointwise count formula for the weighted finitely supported measure. -/
theorem weightedMeasure_apply {A B : ℝ} (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) (p : ℝ × ℝ) :
    weightedMeasure w D p =
      ((finitePart D.points).count p : ℝ) * w (birthPersistence p) := by
  simpa only [weightedMeasure] using
    multiset_sum_single_apply (s := finitePart D.points)
      (fun q => w (birthPersistence q)) p

/-- The diagram embedding is the measure embedding of its weighted finite part. -/
theorem diagramEmbedding_eq_measureEmbedding {A B : ℝ} (σ : ℝ)
    (w : PersistenceImage.Weight A B) (D : Diagram ℝ) :
    diagramEmbedding σ w D = measureEmbedding σ (weightedMeasure w D) := by
  rw [diagramEmbedding_eq_sum, weightedMeasure, measureEmbedding, map_multiset_sum]
  simp only [Multiset.map_map, Function.comp_apply, Finsupp.linearCombination_single]

/-- Equality of weighted embeddings is equivalent to equality of their weighted measures. -/
theorem diagramEmbedding_eq_iff_weightedMeasure_eq {A B σ : ℝ} (hσ : σ ≠ 0)
    (w : PersistenceImage.Weight A B) (D E : Diagram ℝ) :
    diagramEmbedding σ w D = diagramEmbedding σ w E ↔
      weightedMeasure w D = weightedMeasure w E := by
  rw [diagramEmbedding_eq_measureEmbedding, diagramEmbedding_eq_measureEmbedding]
  constructor
  · exact fun h => measureEmbedding_injective hσ h
  · intro h
    exact congrArg (measureEmbedding σ) h

/-- The weighted Gaussian embedding identifies finite diagram parts with multiplicity
under pointwise positivity of the weight at all finite points. -/
theorem diagramEmbedding_eq_iff {A B σ : ℝ} (hσ : σ ≠ 0)
    (w : PersistenceImage.Weight A B) {D E : Diagram ℝ}
    (hD : ∀ p ∈ finitePart D.points, 0 < w (birthPersistence p))
    (hE : ∀ p ∈ finitePart E.points, 0 < w (birthPersistence p)) :
    diagramEmbedding σ w D = diagramEmbedding σ w E ↔
      finitePart D.points = finitePart E.points := by
  classical
  constructor
  · intro h
    have hm : weightedMeasure w D = weightedMeasure w E :=
      (diagramEmbedding_eq_iff_weightedMeasure_eq hσ w D E).mp h
    apply Multiset.ext'
    intro p
    by_cases hpD : p ∈ finitePart D.points
    · have hc := congrArg (fun μ : ℝ × ℝ →₀ ℝ => μ p) hm
      rw [weightedMeasure_apply, weightedMeasure_apply] at hc
      have hcount : (finitePart D.points).count p =
          (finitePart E.points).count p :=
        Nat.cast_injective (mul_right_cancel₀ (ne_of_gt (hD p hpD)) hc)
      exact hcount
    · by_cases hpE : p ∈ finitePart E.points
      · have hc := congrArg (fun μ : ℝ × ℝ →₀ ℝ => μ p) hm
        rw [weightedMeasure_apply, weightedMeasure_apply] at hc
        have hcount : (finitePart D.points).count p =
            (finitePart E.points).count p :=
          Nat.cast_injective (mul_right_cancel₀ (ne_of_gt (hE p hpE)) hc)
        exact hcount
      · rw [Multiset.count_eq_zero.mpr hpD, Multiset.count_eq_zero.mpr hpE]
  · intro h
    apply (diagramEmbedding_eq_iff_weightedMeasure_eq hσ w D E).2
    unfold weightedMeasure
    rw [h]

private theorem finitePart_mem_isPositive {D : Diagram ℝ} (hD : D.IsPositive)
    {p : ℝ × ℝ} (hp : p ∈ finitePart D.points) : p.1 < p.2 := by
  obtain ⟨⟨b, d⟩, hbd, he⟩ := (Multiset.mem_filterMap _ _).mp hp
  cases d with
  | top => simp at he
  | coe d =>
    have hpos := hD (b, (d : WithTop ℝ)) hbd
    simp at he
    rw [← he]
    simpa using hpos

/-- Positive diagrams satisfy the finite-point positivity hypothesis whenever the weight
is positive on the open upper half-plane. -/
theorem diagramEmbedding_eq_iff_of_isPositive {A B σ : ℝ} (hσ : σ ≠ 0)
    (w : PersistenceImage.Weight A B)
    (hw : ∀ u : ℝ × ℝ, 0 < u.2 → 0 < w u) {D E : Diagram ℝ}
    (hD : D.IsPositive) (hE : E.IsPositive) :
    diagramEmbedding σ w D = diagramEmbedding σ w E ↔
      finitePart D.points = finitePart E.points := by
  apply diagramEmbedding_eq_iff hσ w
  · intro p hp
    exact hw (birthPersistence p)
      (birthPersistence_snd_pos (finitePart_mem_isPositive hD hp))
  · intro p hp
    exact hw (birthPersistence p)
      (birthPersistence_snd_pos (finitePart_mem_isPositive hE hp))

/-- Equality of weighted embeddings, together with equality of essential parts, identifies
the whole diagrams. -/
theorem eq_of_diagramEmbedding_eq {A B σ : ℝ} (hσ : σ ≠ 0)
    (w : PersistenceImage.Weight A B) {D E : Diagram ℝ}
    (hD : ∀ p ∈ finitePart D.points, 0 < w (birthPersistence p))
    (hE : ∀ p ∈ finitePart E.points, 0 < w (birthPersistence p))
    (hess : essentialPart D.points = essentialPart E.points)
    (h : diagramEmbedding σ w D = diagramEmbedding σ w E) : D = E := by
  apply Diagram.ext
  calc
    D.points = (finitePart D.points).map (fun p => (p.1, (p.2 : WithTop ℝ))) +
        (essentialPart D.points).map (fun b => (b, (⊤ : WithTop ℝ))) :=
      (parts_reconstruct D.points).symm
    _ = (finitePart E.points).map (fun p => (p.1, (p.2 : WithTop ℝ))) +
        (essentialPart E.points).map (fun b => (b, (⊤ : WithTop ℝ))) := by
      rw [(diagramEmbedding_eq_iff hσ w hD hE).mp h, hess]
    _ = E.points := parts_reconstruct E.points

/-- The RKHS distance vanishes exactly when the weighted finite parts agree. -/
theorem dist_diagramEmbedding_eq_zero_iff {A B σ : ℝ} (hσ : σ ≠ 0)
    (w : PersistenceImage.Weight A B) {D E : Diagram ℝ}
    (hD : ∀ p ∈ finitePart D.points, 0 < w (birthPersistence p))
    (hE : ∀ p ∈ finitePart E.points, 0 < w (birthPersistence p)) :
    ‖diagramEmbedding σ w D - diagramEmbedding σ w E‖ = 0 ↔
      finitePart D.points = finitePart E.points := by
  constructor
  · intro h
    exact (diagramEmbedding_eq_iff hσ w hD hE).mp
      (norm_sub_eq_zero_iff.mp h)
  · intro h
    rw [norm_sub_eq_zero_iff]
    exact (diagramEmbedding_eq_iff hσ w hD hE).mpr h

end TDA.Persistence.WeightedKernel
