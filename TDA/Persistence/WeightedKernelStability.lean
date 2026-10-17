import TDA.Persistence.GaussianFeature
import TDA.Persistence.WeightedKernel
import TDA.Persistence.PersistenceImageDiagram

/-!
# Matching-cost stability of the weighted Gaussian kernel embedding

The birth–death kernel functions satisfy KFH18 Lemma 16: `‖k_σ(·,p) - k_σ(·,q)‖` is at most
the Euclidean distance over `|σ|`, hence at most `√2 / |σ|` times the maximum-norm
distance. Together with a `Weight A B` read in birth–persistence coordinates, this gives the
two pointwise hypotheses of `OccurrenceMatching.norm_featureSum_sub_le` with the constant
`2A + √2·B/|σ|`. The embedding difference is then bounded by every finite partial matching,
by the finite first-order matching cost, and for positive diagrams with finite bottleneck by
the occurrence count times the bottleneck distance (the KFH18 Proposition 10 shape, with
`B₂ = B`, `L₂ = 2A`, `B_k = 1`, `L_k = √2/|σ|`).

The `(k, w)`-Gaussian diagram kernel of KFH18 eq. (13) is the Gaussian kernel of the RKHS
`Space σ`; its feature map is the Gaussian RKHS of `Space σ`. Its kernel functions and
kernel values are Lipschitz in the embedding with constant `1/|τ|`, and composition gives
count-times-bottleneck bounds. No bandwidth sign hypothesis is assumed. Norms are the actual
`RKHS.OfKernel` norms; the pixel norm of `PersistenceImage` is not involved.
-/

namespace TDA.Persistence.WeightedKernel

open scoped InnerProductSpace

/-! ## Euclidean and maximum norms on the plane -/

/-- The Euclidean norm on the plane is at most `√2` times the maximum norm. -/
theorem norm_toLp_sub_le_sqrt_two_mul (p q : ℝ × ℝ) :
    ‖WithLp.toLp 2 p - WithLp.toLp 2 q‖ ≤ √2 * ‖p - q‖ := by
  have h1 : ‖WithLp.toLp 2 p - WithLp.toLp 2 q‖ ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [Real.norm_eq_abs, sq_abs]
  have hn : ‖p - q‖ = max |p.1 - q.1| |p.2 - q.2| := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  have ha : (p.1 - q.1) ^ 2 ≤ ‖p - q‖ ^ 2 := by
    rw [← sq_abs, hn]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
  have hb : (p.2 - q.2) ^ 2 ≤ ‖p - q‖ ^ 2 := by
    rw [← sq_abs, hn]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
  have hle : ‖WithLp.toLp 2 p - WithLp.toLp 2 q‖ ^ 2 ≤ (√2 * ‖p - q‖) ^ 2 := by
    rw [h1, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle

/-! ## First-level feature bound, KFH18 Lemma 16 -/

/-- KFH18 Lemma 16, eq. (25): Euclidean form. -/
theorem norm_featureAt_sub_le_euclidean (σ : ℝ) (p q : ℝ × ℝ) :
    ‖featureAt σ p - featureAt σ q‖ ≤ ‖WithLp.toLp 2 p - WithLp.toLp 2 q‖ / |σ| := by
  have h := norm_sub_le_of_inner_eq_gaussian (norm_featureAt σ p) (norm_featureAt σ q)
    ((inner_featureAt σ p q).trans (kernel_eq_gaussian σ p q))
  rwa [abs_of_nonneg (norm_nonneg _)] at h

/-- KFH18 Lemma 16, eq. (26): maximum-norm form with constant `√2 / |σ|`. -/
theorem norm_featureAt_sub_le (σ : ℝ) (p q : ℝ × ℝ) :
    ‖featureAt σ p - featureAt σ q‖ ≤ √2 / |σ| * ‖p - q‖ := by
  calc
    _ ≤ ‖WithLp.toLp 2 p - WithLp.toLp 2 q‖ / |σ| := norm_featureAt_sub_le_euclidean σ p q
    _ ≤ (√2 * ‖p - q‖) / |σ| :=
      div_le_div_of_nonneg_right (norm_toLp_sub_le_sqrt_two_mul p q) (abs_nonneg σ)
    _ = _ := by ring

/-! ## The weighted feature -/

variable {A B : ℝ}

/-- The embedding constant `2A + √2·B/|σ|`, KFH18's `L_k B₂ + B_k L₂`. -/
noncomputable def stabilityConstant (σ A B : ℝ) : ℝ := 2 * A + √2 * B / |σ|

theorem stabilityConstant_nonneg (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ stabilityConstant σ A B :=
  add_nonneg (mul_nonneg zero_le_two hA)
    (div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hB) (abs_nonneg σ))

/-- The Lipschitz constant of a weight is nonnegative. -/
private theorem weight_lipschitz_nonneg (w : PersistenceImage.Weight A B) : 0 ≤ A := by
  have h := w.lipschitz (0, 0) (0, 1)
  have hn : ‖((0 : ℝ), (0 : ℝ)) - (0, 1)‖ = 1 := by
    norm_num [Prod.norm_def]
  rw [hn, mul_one] at h
  exact (abs_nonneg _).trans h

/-- One weighted kernel function `w (T p) • k_σ(·, p)`. -/
noncomputable def weightedFeature (σ : ℝ) (w : PersistenceImage.Weight A B) (p : ℝ × ℝ) :
    Space σ :=
  w (birthPersistence p) • featureAt σ p

theorem embedding_eq_finiteFeatureSum {I : Type*} [Fintype I] (σ : ℝ)
    (w : PersistenceImage.Weight A B) (x : I → ℝ × ℝ) :
    embedding σ w x = finiteFeatureSum (weightedFeature σ w) x := rfl

/-- The pair hypothesis of `norm_featureSum_sub_le`, for all points. -/
theorem norm_weightedFeature_sub_le (σ : ℝ) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (p q : ℝ × ℝ) :
    ‖weightedFeature σ w p - weightedFeature σ w q‖ ≤ stabilityConstant σ A B * ‖p - q‖ := by
  have hA := weight_lipschitz_nonneg w
  have hw : |w (birthPersistence p) - w (birthPersistence q)| ≤ 2 * A * ‖p - q‖ := by
    calc
      _ ≤ A * ‖birthPersistence p - birthPersistence q‖ := w.lipschitz _ _
      _ ≤ A * (2 * ‖p - q‖) :=
        mul_le_mul_of_nonneg_left (norm_birthPersistence_sub_le p q) hA
      _ = _ := by ring
  have hwb : |w (birthPersistence p)| ≤ B := by
    rw [abs_of_nonneg (w.nonneg _)]
    exact w.bounded _
  have he : weightedFeature σ w p - weightedFeature σ w q =
      (w (birthPersistence p) - w (birthPersistence q)) • featureAt σ q +
        w (birthPersistence p) • (featureAt σ p - featureAt σ q) := by
    simp only [weightedFeature]
    module
  rw [he]
  calc
    _ ≤ ‖(w (birthPersistence p) - w (birthPersistence q)) • featureAt σ q‖ +
        ‖w (birthPersistence p) • (featureAt σ p - featureAt σ q)‖ := norm_add_le _ _
    _ = |w (birthPersistence p) - w (birthPersistence q)| * 1 +
        |w (birthPersistence p)| * ‖featureAt σ p - featureAt σ q‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_featureAt]
    _ ≤ (2 * A * ‖p - q‖) * 1 + B * (√2 / |σ| * ‖p - q‖) :=
      add_le_add (mul_le_mul_of_nonneg_right hw zero_le_one)
        (mul_le_mul hwb (norm_featureAt_sub_le σ p q) (norm_nonneg _) hB)
    _ = _ := by unfold stabilityConstant; ring

/-- The diagonal hypothesis of `norm_featureSum_sub_le`, for all points. -/
theorem norm_weightedFeature_le_diagonalCost (σ : ℝ) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (p : ℝ × ℝ) :
    ‖weightedFeature σ w p‖ ≤ stabilityConstant σ A B * (diagonalCost p).toReal := by
  have hw := w.lipschitz (birthPersistence p) (p.1, 0)
  have ht : ‖birthPersistence p - (p.1, 0)‖ = |p.2 - p.1| := by
    simp [birthPersistence, Prod.norm_def, Real.norm_eq_abs]
  rw [w.zero_persistence, sub_zero, abs_of_nonneg (w.nonneg _), ht] at hw
  have hC : 2 * A ≤ stabilityConstant σ A B := by
    unfold stabilityConstant
    have : 0 ≤ √2 * B / |σ| :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hB) (abs_nonneg σ)
    linarith
  rw [weightedFeature, norm_smul, norm_featureAt, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (w.nonneg _)]
  calc
    _ ≤ A * |p.2 - p.1| := hw
    _ = (2 * A) * (diagonalCost p).toReal := by rw [diagonalCost_toReal]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC ENNReal.toReal_nonneg

/-- Diagonal points have zero weighted feature. -/
theorem weightedFeature_diagonal (σ : ℝ) (w : PersistenceImage.Weight A B) (b : ℝ) :
    weightedFeature σ w (b, b) = 0 := by
  rw [weightedFeature, show birthPersistence (b, b) = (b, 0) by simp [birthPersistence],
    w.zero_persistence, zero_smul]

/-! ## Embedding stability -/

/-- Embedding stability for every finite partial matching, KFH18 Proposition 10 shape. -/
theorem norm_embedding_sub_le_matching {I J : Type*} [Fintype I] [Fintype J] (σ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    ‖embedding σ w x - embedding σ w y‖ ≤ stabilityConstant σ A B * M.totalFiniteCost x y :=
  M.norm_featureSum_sub_le (weightedFeature σ w) (stabilityConstant σ A B)
    (stabilityConstant_nonneg σ hA hB)
    (fun p q _ _ => norm_weightedFeature_sub_le σ hB w p q)
    (fun p _ => norm_weightedFeature_le_diagonalCost σ hB w p) x y hx hy

/-- Embedding stability against the attained finite first-order matching cost. -/
theorem norm_embedding_sub_le_finiteFirstOrderMatchingCost {I J : Type*} [Fintype I]
    [Fintype J] (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    ‖embedding σ w x - embedding σ w y‖ ≤
      stabilityConstant σ A B * finiteFirstOrderMatchingCost x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  simpa only [hM] using norm_embedding_sub_le_matching σ hA hB w M x y hx hy

/-- Count-times-bottleneck stability of diagram embeddings. Essential bars are omitted
from the embedding; the finite bottleneck hypothesis is explicit. -/
theorem norm_diagramEmbedding_sub_le_card_mul_bottleneck (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (D E : Diagram ℝ) (hD : D.IsPositive)
    (hE : E.IsPositive) (hfinite : bottleneck D E < ⊤) :
    ‖diagramEmbedding σ w D - diagramEmbedding σ w E‖ ≤
      stabilityConstant σ A B *
        ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck D E).toReal := by
  calc
    _ ≤ stabilityConstant σ A B * finiteFirstOrderMatchingCost
        (fun p : D.finiteOccurrences => p.1) (fun p : E.finiteOccurrences => p.1) :=
      norm_embedding_sub_le_finiteFirstOrderMatchingCost σ hA hB w _ _
        hD.finiteOccurrence hE.finiteOccurrence
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (finiteFirstOrderMatchingCost_le_card_mul_bottleneck D E hfinite)
        (stabilityConstant_nonneg σ hA hB)

/-! ## The `(k, w)`-Gaussian diagram kernel, KFH18 eq. (13) -/

/-- `K_G(D, E) = exp (-‖Φ D - Φ E‖² / (2τ²))`, KFH18 eq. (13). -/
noncomputable def gaussianDiagramKernel (σ τ : ℝ) (w : PersistenceImage.Weight A B)
    (D E : Diagram ℝ) : ℝ :=
  Real.exp (-‖diagramEmbedding σ w D - diagramEmbedding σ w E‖ ^ 2 / (2 * τ ^ 2))

/-- The entries of the Gaussian diagram Gram matrix of `posSemidef_gaussianDiagramGram`. -/
theorem gaussianGram_diagramEmbedding_apply {κ : Type*} (σ τ : ℝ)
    (w : PersistenceImage.Weight A B) (D : κ → Diagram ℝ) (a b : κ) :
    gaussianGram τ (fun a => diagramEmbedding σ w (D a)) a b =
      gaussianDiagramKernel σ τ w (D a) (D b) := rfl

/-- The feature map of the `(k, w)`-Gaussian kernel in the Gaussian RKHS of `Space σ`. -/
noncomputable def diagramGaussianFeature (σ τ : ℝ) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) : GaussianSpace τ (Space σ) :=
  gaussianFeature τ (diagramEmbedding σ w D)

theorem inner_diagramGaussianFeature (σ τ : ℝ) (w : PersistenceImage.Weight A B)
    (D E : Diagram ℝ) :
    ⟪diagramGaussianFeature σ τ w D, diagramGaussianFeature σ τ w E⟫_ℝ =
      gaussianDiagramKernel σ τ w D E :=
  inner_gaussianFeature τ _ _

/-- Second-level feature bound. -/
theorem norm_diagramGaussianFeature_sub_le (σ τ : ℝ) (w : PersistenceImage.Weight A B)
    (D E : Diagram ℝ) :
    ‖diagramGaussianFeature σ τ w D - diagramGaussianFeature σ τ w E‖ ≤
      ‖diagramEmbedding σ w D - diagramEmbedding σ w E‖ / |τ| :=
  norm_gaussianFeature_sub_le τ _ _

/-- Kernel-value bound by Cauchy–Schwarz. -/
theorem abs_gaussianDiagramKernel_sub_le (σ τ : ℝ) (w : PersistenceImage.Weight A B)
    (D E E' : Diagram ℝ) :
    |gaussianDiagramKernel σ τ w D E - gaussianDiagramKernel σ τ w D E'| ≤
      ‖diagramEmbedding σ w E - diagramEmbedding σ w E'‖ / |τ| := by
  have h : gaussianDiagramKernel σ τ w D E - gaussianDiagramKernel σ τ w D E' =
      ⟪diagramGaussianFeature σ τ w D,
        diagramGaussianFeature σ τ w E - diagramGaussianFeature σ τ w E'⟫_ℝ := by
    rw [inner_sub_right, inner_diagramGaussianFeature, inner_diagramGaussianFeature]
  have hn : ‖diagramGaussianFeature σ τ w D‖ = 1 := norm_gaussianFeature τ _
  rw [h]
  calc
    _ ≤ ‖diagramGaussianFeature σ τ w D‖ *
        ‖diagramGaussianFeature σ τ w E - diagramGaussianFeature σ τ w E'‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖diagramGaussianFeature σ τ w E - diagramGaussianFeature σ τ w E'‖ := by
      rw [hn, one_mul]
    _ ≤ _ := norm_diagramGaussianFeature_sub_le σ τ w E E'

/-- Count-times-bottleneck stability of the second-level feature map. -/
theorem norm_diagramGaussianFeature_sub_le_card_mul_bottleneck (σ τ : ℝ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) (D E : Diagram ℝ) (hD : D.IsPositive)
    (hE : E.IsPositive) (hfinite : bottleneck D E < ⊤) :
    ‖diagramGaussianFeature σ τ w D - diagramGaussianFeature σ τ w E‖ ≤
      stabilityConstant σ A B / |τ| *
        ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck D E).toReal := by
  calc
    _ ≤ ‖diagramEmbedding σ w D - diagramEmbedding σ w E‖ / |τ| :=
      norm_diagramGaussianFeature_sub_le σ τ w D E
    _ ≤ (stabilityConstant σ A B *
        ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck D E).toReal) / |τ| :=
      div_le_div_of_nonneg_right
        (norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w D E hD hE hfinite)
        (abs_nonneg τ)
    _ = _ := by ring

/-- Count-times-bottleneck stability of `(k, w)`-Gaussian kernel values. -/
theorem abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck (σ τ : ℝ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) (D E E' : Diagram ℝ) (hE : E.IsPositive)
    (hE' : E'.IsPositive) (hfinite : bottleneck E E' < ⊤) :
    |gaussianDiagramKernel σ τ w D E - gaussianDiagramKernel σ τ w D E'| ≤
      stabilityConstant σ A B / |τ| *
        ((Fintype.card E.finiteOccurrences + Fintype.card E'.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck E E').toReal := by
  calc
    _ ≤ ‖diagramEmbedding σ w E - diagramEmbedding σ w E'‖ / |τ| :=
      abs_gaussianDiagramKernel_sub_le σ τ w D E E'
    _ ≤ (stabilityConstant σ A B *
        ((Fintype.card E.finiteOccurrences + Fintype.card E'.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck E E').toReal) / |τ| :=
      div_le_div_of_nonneg_right
        (norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w E E' hE hE' hfinite)
        (abs_nonneg τ)
    _ = _ := by ring

end TDA.Persistence.WeightedKernel
