import TDA.Persistence.CechWeightedKernel
import TDA.Persistence.ArctanPersistenceImage

/-!
# Same-label displacements of Čech persistence images

The same-label actual-diagram Čech bound and the Gaussian pixel ℓ¹ estimate compose through
the finite occurrence-count bound. Essential bars remain in the bottleneck comparison but are
omitted from the image. The bandwidth hypothesis `0 < σ` is that of the persistence-image
theorem; no label metric or distance compatibility is assumed. The composition is a library
result.
-/

universe w u

namespace TDA.Persistence.Cech

open TDA.Filtration Real

variable {X : Type w} [PseudoMetricSpace X] {V : Type u} [LinearOrder V] [Fintype V]
  (k : Type u) [Field k]

/-- Same-label displacements bound finite-part Čech persistence images in every degree. -/
theorem norm_finiteDiagramImage_sub_le_displacement (p q : V → X) (n : ℕ)
    {K : Type*} [Fintype K] {σ A B : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (dgm k (Cech.filter p) n) -
        PersistenceImage.finiteDiagramImage σ w P (dgm k (Cech.filter q) n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            Cech.displacement p q :=
  (PersistenceImage.norm_finiteDiagramImage_sub_le_card_mul_bottleneck hσ hA hB w P hm hd _ _
    (dgm_isPositive k _ n) (dgm_isPositive k _ n) (bottleneck_dgm_lt_top k p q n)).trans
      (mul_le_mul_of_nonneg_left (toReal_bottleneck_dgm_le_displacement k p q n)
        (mul_nonneg (PersistenceImage.stabilityConstant_nonneg hσ hA hB) (Nat.cast_nonneg _)))

/-- The arctan instance of `norm_finiteDiagramImage_sub_le_displacement`. -/
theorem norm_finiteDiagramImage_sub_le_displacement_arctan (p q : V → X) (n : ℕ)
    {K : Type*} [Fintype K] {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (dgm k (Cech.filter p) n) -
        PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (dgm k (Cech.filter q) n)‖ ≤
      (2 * C + 3 * √(π / 2) / σ) *
        ((Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) *
            Cech.displacement p q := by
  simpa only [PersistenceImage.stabilityConstant_arctan] using
    norm_finiteDiagramImage_sub_le_displacement k p q n hσ hC Real.pi_div_two_pos.le
      (PersistenceImage.arctanWeight C hC) P hm hd

end TDA.Persistence.Cech
