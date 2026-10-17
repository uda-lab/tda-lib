import TDA.Persistence.CechSupNormDiagram
import TDA.Persistence.RipsWeightedKernel

set_option autoImplicit false

/-!
# Sup-norm Čech weighted-kernel consumers

In the sup-metric product `ι → ℝ`, distance-compatible label metrics give the
half-discrepancy bound for Čech diagrams. It composes with the count-times-bottleneck
stability of the weighted Gaussian kernel embedding, its second-level Gaussian feature
and the `(k, w)`-Gaussian kernel values. The constants are the corresponding Rips
constants times half the pairwise discrepancy; essential bars remain in the bottleneck
comparison but are omitted from the embedding. The line has the corresponding
half-discrepancy bottleneck bound. These are library compositions with no external theorem.
-/

universe u w

namespace TDA.Persistence.Cech

open TDA.Filtration Real

section SupNorm

variable {V : Type u} [LinearOrder V] [Fintype V] {ι : Type w} [Fintype ι]
  (k : Type u) [Field k] {A B : ℝ}

/-- The full bottleneck distance of two same-label sup-norm Čech diagrams is finite. -/
theorem bottleneck_dgm_lt_top_supNorm (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) < ⊤ :=
  (bottleneck_dgm_le_half_pairwiseDiscrepancy k d e p q hd he n).trans_lt ENNReal.ofReal_lt_top

/-- The real conversion of the sup-norm Čech bottleneck distance is at most half the
pairwise discrepancy of the label metrics. -/
theorem toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy (d e : MetricSpace V)
    (p q : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ) :
    (bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n)).toReal ≤
      Rips.pairwiseDiscrepancy d e / 2 := by
  simpa only [ENNReal.toReal_ofReal
      (div_nonneg (Rips.pairwiseDiscrepancy_nonneg d e) zero_le_two)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (bottleneck_dgm_le_half_pairwiseDiscrepancy k d e p q hd he n)

/-- Same-label distance perturbations bound sup-norm Čech weighted-kernel embeddings in every
degree. -/
theorem norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy (d e : MetricSpace V)
    (p q : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ)
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm k (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ w (dgm k (Cech.filter q) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.pairwiseDiscrepancy d e / 2) :=
  (WeightedKernel.norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n)
    (bottleneck_dgm_lt_top_supNorm k d e p q hd he n)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy k d e p q hd he n)
        (mul_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB) (Nat.cast_nonneg _)))

/-- Same-label distance perturbations bound the second-level Gaussian features of sup-norm
Čech diagrams. -/
theorem norm_diagramGaussianFeature_sub_le_half_pairwiseDiscrepancy (d e : MetricSpace V)
    (p q : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramGaussianFeature σ τ w (dgm k (Cech.filter p) n) -
        WeightedKernel.diagramGaussianFeature σ τ w (dgm k (Cech.filter q) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.pairwiseDiscrepancy d e / 2) :=
  (WeightedKernel.norm_diagramGaussianFeature_sub_le_card_mul_bottleneck σ τ hA hB w _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n)
    (bottleneck_dgm_lt_top_supNorm k d e p q hd he n)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy k d e p q hd he n)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

/-- Same-label distance perturbations bound `(k, w)`-Gaussian kernel values against an
arbitrary fixed diagram. -/
theorem abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy (d e : MetricSpace V)
    (p q : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Cech.filter p) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Cech.filter q) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.pairwiseDiscrepancy d e / 2) :=
  (WeightedKernel.abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck σ τ hA hB w D _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n)
    (bottleneck_dgm_lt_top_supNorm k d e p q hd he n)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy k d e p q hd he n)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

variable {C : ℝ}

/-- The arctan instance of `norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy`. -/
theorem norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy_arctan
    (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ) (σ : ℝ) (hC : 0 ≤ C) :
    ‖WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm k (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm k (Cech.filter q) n)‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.pairwiseDiscrepancy d e / 2) := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy k d e p q hd he n σ hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC)

/-- The arctan instance of `abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy`. -/
theorem abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy_arctan
    (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ)
    (σ τ : ℝ) (hC : 0 ≤ C) (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (dgm k (Cech.filter p) n) -
        WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (dgm k (Cech.filter q) n)| ≤
      (2 * C + √2 * π / (2 * |σ|)) / |τ| *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.pairwiseDiscrepancy d e / 2) := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy k d e p q hd he n σ τ hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC) D

end SupNorm

section Real

variable {V : Type u} [LinearOrder V] [Fintype V] (k : Type u) [Field k]

/-- On the line, the Čech bottleneck distance is at most half the pairwise discrepancy
of the distance-compatible label metrics. -/
theorem bottleneck_dgm_le_half_pairwiseDiscrepancy_real (d e : MetricSpace V)
    (q q' : V → ℝ) (hd : ∀ v w, d.dist v w = dist (q v) (q w))
    (he : ∀ v w, e.dist v w = dist (q' v) (q' w)) (n : ℕ) :
    bottleneck (dgm k (Cech.filter q) n) (dgm k (Cech.filter q') n) ≤
      ENNReal.ofReal (Rips.pairwiseDiscrepancy d e / 2) := by
  rw [filter_eq_scale_rips_real d q hd, filter_eq_scale_rips_real e q' he,
    bottleneck_dgm_scale k (Rips.filter d) (Rips.filter e) n _]
  calc
    ENNReal.ofReal 2⁻¹ *
          bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n) ≤
        ENNReal.ofReal 2⁻¹ * ENNReal.ofReal (Rips.pairwiseDiscrepancy d e) :=
      mul_le_mul_right (Rips.bottleneck_dgm_le_pairwiseDiscrepancy k d e n) _
    _ = ENNReal.ofReal (Rips.pairwiseDiscrepancy d e / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num), inv_mul_eq_div]

end Real

end TDA.Persistence.Cech
