import TDA.Persistence.CechStability
import TDA.Persistence.ArctanWeight

/-!
# Same-label displacements of Čech weighted-kernel embeddings

The same-label sublevel-diagram Čech bound composes with the count-times-bottleneck stability
of the weighted Gaussian kernel embedding, its second-level Gaussian feature and the
`(k, w)`-Gaussian kernel values. The full bottleneck bound is finite and its real conversion
is at most the displacement; essential bars remain in that comparison but are omitted from
the embedding. No label metric, distance compatibility, injectivity or bandwidth sign
hypothesis is assumed, and the fixed kernel argument is arbitrary. The composition is a
library result.
-/

universe w u

namespace TDA.Persistence.Cech

open TDA.Filtration Real

variable {X : Type w} [PseudoMetricSpace X] {V : Type u} [LinearOrder V] [Fintype V]
  (k : Type u) [Field k] {A B : ℝ}

/-- The full bottleneck distance of two same-label Čech diagrams is finite. -/
theorem bottleneck_dgm_lt_top (p q : V → X) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) < ⊤ :=
  (bottleneck_dgm_le_displacement k p q n).trans_lt ENNReal.ofReal_lt_top

/-- The real conversion of the Čech bottleneck distance is at most the displacement. -/
theorem toReal_bottleneck_dgm_le_displacement (p q : V → X) (n : ℕ) :
    (bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n)).toReal ≤
      Cech.displacement p q := by
  simpa only [ENNReal.toReal_ofReal (Cech.displacement_nonneg p q)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (bottleneck_dgm_le_displacement k p q n)

/-- Same-label displacements bound Čech weighted-kernel embeddings in every degree. -/
theorem norm_diagramEmbedding_sub_le_displacement (p q : V → X) (n : ℕ)
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm k (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ w (dgm k (Cech.filter q) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            Cech.displacement p q :=
  (WeightedKernel.norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) (bottleneck_dgm_lt_top k p q n)).trans
      (mul_le_mul_of_nonneg_left (toReal_bottleneck_dgm_le_displacement k p q n)
        (mul_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB) (Nat.cast_nonneg _)))

/-- Same-label displacements bound the second-level Gaussian features of Čech diagrams. -/
theorem norm_diagramGaussianFeature_sub_le_displacement (p q : V → X) (n : ℕ)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramGaussianFeature σ τ w (dgm k (Cech.filter p) n) -
        WeightedKernel.diagramGaussianFeature σ τ w (dgm k (Cech.filter q) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            Cech.displacement p q :=
  (WeightedKernel.norm_diagramGaussianFeature_sub_le_card_mul_bottleneck σ τ hA hB w _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) (bottleneck_dgm_lt_top k p q n)).trans
      (mul_le_mul_of_nonneg_left (toReal_bottleneck_dgm_le_displacement k p q n)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

/-- Same-label displacements bound `(k, w)`-Gaussian kernel values of Čech diagrams against
an arbitrary fixed diagram. -/
theorem abs_gaussianDiagramKernel_sub_le_displacement (p q : V → X) (n : ℕ)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Cech.filter p) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm k (Cech.filter q) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            Cech.displacement p q :=
  (WeightedKernel.abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck σ τ hA hB w D _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) (bottleneck_dgm_lt_top k p q n)).trans
      (mul_le_mul_of_nonneg_left (toReal_bottleneck_dgm_le_displacement k p q n)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

variable {C : ℝ}

/-- The arctan instance of `norm_diagramEmbedding_sub_le_displacement`. -/
theorem norm_diagramEmbedding_sub_le_displacement_arctan (p q : V → X) (n : ℕ) (σ : ℝ)
    (hC : 0 ≤ C) :
    ‖WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm k (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (dgm k (Cech.filter q) n)‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            Cech.displacement p q := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    norm_diagramEmbedding_sub_le_displacement k p q n σ hC Real.pi_div_two_pos.le
      (PersistenceImage.arctanWeight C hC)

/-- The arctan instance of `abs_gaussianDiagramKernel_sub_le_displacement`. -/
theorem abs_gaussianDiagramKernel_sub_le_displacement_arctan (p q : V → X) (n : ℕ)
    (σ τ : ℝ) (hC : 0 ≤ C) (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (dgm k (Cech.filter p) n) -
        WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (dgm k (Cech.filter q) n)| ≤
      (2 * C + √2 * π / (2 * |σ|)) / |τ| *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            Cech.displacement p q := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    abs_gaussianDiagramKernel_sub_le_displacement k p q n σ τ hC Real.pi_div_two_pos.le
      (PersistenceImage.arctanWeight C hC) D

end TDA.Persistence.Cech
