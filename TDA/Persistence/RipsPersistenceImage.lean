import TDA.Persistence.RipsStability
import TDA.Persistence.PersistenceImageDiagram

/-!
# Distance-matrix perturbations of Rips persistence images

The existing same-label sublevel-diagram bound and Gaussian pixel ℓ¹ estimate compose
through a finite occurrence-count bound. The constant is an independently derived,
nonsharp library estimate. Rips time is simplex diameter; essential bars remain in
the bottleneck comparison but are deliberately omitted from the image.
-/

universe u

namespace TDA.Persistence.Rips

open TDA.Filtration MeasureTheory Set PersistenceImage

variable {V : Type u} [LinearOrder V] [Fintype V]

/-- Same-label metric perturbations bound finite-bar Rips images in every degree.
Empty carriers/maxima are allowed; essential-cardinality equality follows from
the existing finite bottleneck bound rather than being an additional hypothesis. -/
theorem norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy
    (k : Type u) [Field k] (d e : MetricSpace V) (n : ℕ)
    {K : Type*} [Fintype K] {σ A B : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖finiteDiagramImage σ w P (dgm k (Rips.filter d) n) -
        finiteDiagramImage σ w P (dgm k (Rips.filter e) n)‖ ≤
      stabilityConstant σ A B *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) *
            Rips.pairwiseDiscrepancy d e := by
  have hbound := bottleneck_dgm_le_pairwiseDiscrepancy k d e n
  have hfinite : bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n) < ⊤ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  have hreal : (bottleneck (dgm k (Rips.filter d) n)
      (dgm k (Rips.filter e) n)).toReal ≤ Rips.pairwiseDiscrepancy d e := by
    simpa only [ENNReal.toReal_ofReal (Rips.pairwiseDiscrepancy_nonneg d e)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  exact (norm_finiteDiagramImage_sub_le_card_mul_bottleneck hσ hA hB w P hm hd _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) hfinite).trans
      (mul_le_mul_of_nonneg_left hreal (by
        exact mul_nonneg (stabilityConstant_nonneg hσ hA hB) (Nat.cast_nonneg _)))

end TDA.Persistence.Rips
