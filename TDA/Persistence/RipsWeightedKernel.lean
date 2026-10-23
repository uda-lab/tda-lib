import TDA.Persistence.RipsStability
import TDA.Persistence.ArctanWeight

/-!
# Distance-matrix perturbations of Rips weighted-kernel embeddings

The same-label sublevel-diagram Rips bound composes with the count-times-bottleneck
stability of the weighted Gaussian kernel embedding, its second-level Gaussian feature and
the `(k, w)`-Gaussian kernel values. The full bottleneck bound is finite and its real
conversion is at most the pairwise discrepancy; essential bars remain in that comparison but
are omitted from the embedding. No bandwidth sign hypothesis is assumed, and the fixed
kernel argument is arbitrary. The composition is a library result.
-/

universe u

namespace TDA.Persistence.Rips

open TDA.Filtration Real

variable {V : Type u} [LinearOrder V] [Fintype V] (k : Type u) [Field k] {A B : ℝ}

/-- The full bottleneck distance of two same-label Rips diagrams is finite. -/
theorem bottleneck_dgm_lt_top (d e : MetricSpace V) (n : ℕ) :
    bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n) < ⊤ :=
  (bottleneck_dgm_le_pairwiseDiscrepancy k d e n).trans_lt ENNReal.ofReal_lt_top

/-- The real conversion of the Rips bottleneck distance is at most the pairwise
discrepancy. -/
theorem toReal_bottleneck_dgm_le_pairwiseDiscrepancy (d e : MetricSpace V) (n : ℕ) :
    (bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n)).toReal ≤
      Rips.pairwiseDiscrepancy d e := by
  simpa only [ENNReal.toReal_ofReal (Rips.pairwiseDiscrepancy_nonneg d e)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (bottleneck_dgm_le_pairwiseDiscrepancy k d e n)

/-- Same-label metric perturbations bound Rips weighted-kernel embeddings in every degree. -/
theorem norm_diagramEmbedding_sub_le_pairwiseDiscrepancy (d e : MetricSpace V) (n : ℕ)
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm k (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ w (dgm k (Rips.filter e) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) *
            Rips.pairwiseDiscrepancy d e :=
  (WeightedKernel.norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) (bottleneck_dgm_lt_top k d e n)).trans
      (mul_le_mul_of_nonneg_left (toReal_bottleneck_dgm_le_pairwiseDiscrepancy k d e n)
        (mul_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB) (Nat.cast_nonneg _)))

/-- Same-label metric perturbations bound the second-level Gaussian features. -/
theorem norm_diagramGaussianFeature_sub_le_pairwiseDiscrepancy (d e : MetricSpace V)
    (n : ℕ) (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramGaussianFeature σ τ w (dgm k (Rips.filter d) n) -
        WeightedKernel.diagramGaussianFeature σ τ w (dgm k (Rips.filter e) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) *
            Rips.pairwiseDiscrepancy d e :=
  (WeightedKernel.norm_diagramGaussianFeature_sub_le_card_mul_bottleneck σ τ hA hB w _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) (bottleneck_dgm_lt_top k d e n)).trans
      (mul_le_mul_of_nonneg_left (toReal_bottleneck_dgm_le_pairwiseDiscrepancy k d e n)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

/-- Same-label metric perturbations bound `(k, w)`-Gaussian kernel values against an
arbitrary fixed diagram. -/
theorem abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy (d e : MetricSpace V)
    (n : ℕ) (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Rips.filter d) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Rips.filter e) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) *
            Rips.pairwiseDiscrepancy d e :=
  (WeightedKernel.abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck σ τ hA hB w D _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) (bottleneck_dgm_lt_top k d e n)).trans
      (mul_le_mul_of_nonneg_left (toReal_bottleneck_dgm_le_pairwiseDiscrepancy k d e n)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

variable {C : ℝ}

/-- The arctan instance of `norm_diagramEmbedding_sub_le_pairwiseDiscrepancy`. -/
theorem norm_diagramEmbedding_sub_le_pairwiseDiscrepancy_arctan (d e : MetricSpace V)
    (n : ℕ) (σ : ℝ) (hC : 0 ≤ C) :
    ‖WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm k (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm k (Rips.filter e) n)‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) *
            Rips.pairwiseDiscrepancy d e := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    norm_diagramEmbedding_sub_le_pairwiseDiscrepancy k d e n σ hC Real.pi_div_two_pos.le
      (PersistenceImage.arctanWeight C hC)

/-- The arctan instance of `abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy`. -/
theorem abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy_arctan (d e : MetricSpace V)
    (n : ℕ) (σ τ : ℝ) (hC : 0 ≤ C) (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (dgm k (Rips.filter d) n) -
        WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (dgm k (Rips.filter e) n)| ≤
      (2 * C + √2 * π / (2 * |σ|)) / |τ| *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) *
            Rips.pairwiseDiscrepancy d e := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    abs_gaussianDiagramKernel_sub_le_pairwiseDiscrepancy k d e n σ τ hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC) D

end TDA.Persistence.Rips
