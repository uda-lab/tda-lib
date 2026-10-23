import TDA.Persistence.CechSupNormWeightedKernel
import TDA.Persistence.ArctanPersistenceImage

set_option autoImplicit false

/-!
# Sup-norm Čech persistence-image consumers

In the sup-metric product `ι → ℝ`, the half-discrepancy bottleneck bound for
distance-compatible label metrics composes with the finite-part persistence-image
stability theorem. The constants are the corresponding Rips constants times half the
pairwise discrepancy; essential bars remain in the bottleneck comparison but are omitted
from the image. These are library compositions with no external theorem.
-/

universe u w

namespace TDA.Persistence.Cech

open TDA.Filtration Real MeasureTheory Set PersistenceImage

section SupNorm

variable {V : Type u} [LinearOrder V] [Fintype V] {ι : Type w} [Fintype ι]
  (k : Type u) [Field k] {A B : ℝ}

/-- Same-label distance perturbations bound finite-part sup-norm Čech persistence images in
every degree. -/
theorem norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy
    (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ)
    {K : Type*} [Fintype K] {σ : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (dgm k (Cech.filter p) n) -
        PersistenceImage.finiteDiagramImage σ w P (dgm k (Cech.filter q) n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.pairwiseDiscrepancy d e / 2) :=
  (PersistenceImage.norm_finiteDiagramImage_sub_le_card_mul_bottleneck hσ hA hB w P hm hdisj
    _ _ (dgm_isPositive k _ n) (dgm_isPositive k _ n)
    (bottleneck_dgm_lt_top_supNorm k d e p q hd he n)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy k d e p q hd he n)
        (mul_nonneg (PersistenceImage.stabilityConstant_nonneg hσ hA hB)
          (Nat.cast_nonneg _)))

variable {C : ℝ}

/-- The arctan instance of `norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy`. -/
theorem norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy_arctan
    (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ)
    {K : Type*} [Fintype K] {σ : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (dgm k (Cech.filter p) n) -
        PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (dgm k (Cech.filter q) n)‖ ≤
      (2 * C + 3 * √(π / 2) / σ) *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            (Rips.pairwiseDiscrepancy d e / 2) := by
  simpa only [PersistenceImage.stabilityConstant_arctan] using
    norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy k d e p q hd he n hσ hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC) P hm hdisj

end SupNorm

end TDA.Persistence.Cech
