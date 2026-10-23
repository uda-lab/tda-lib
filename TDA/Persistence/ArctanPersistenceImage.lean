import TDA.Persistence.ArctanWeight
import TDA.Persistence.RipsPersistenceImage

/-!
# Persistence images of the arctan weight

With `A = C` and `B = π / 2` the image constant `2A + 3B·√(2/π)/σ` reads
`2C + 3·√(π/2)/σ`, using `π/2 · √(2/π) = √(π/2)`. The arctan weight of Kusano–Fukumizu–Hiraoka,
JMLR 18(189), 2018, §3.2, placed in the persistence-image construction of Adams et al.,
JMLR 18(8), 2017, §4, with this nonsharp constant, is a library composition. The corollaries
below are instances of the merged persistence-image stability theorems and of the Rips image
consumer; the bandwidth hypothesis `0 < σ` is inherited from them.
-/

universe u

namespace TDA.Persistence.PersistenceImage

open Real

/-- The persistence-image constant of the arctan weight, `2C + 3·√(π/2)/σ`. -/
theorem stabilityConstant_arctan (σ C : ℝ) :
    stabilityConstant σ C (π / 2) = 2 * C + 3 * √(π / 2) / σ := by
  have key : π / 2 * √(2 / π) = √(π / 2) := by
    rw [show (2 : ℝ) / π = (π / 2)⁻¹ from (inv_div π 2).symm, Real.sqrt_inv,
      ← div_eq_mul_inv, Real.div_sqrt]
  unfold stabilityConstant GaussianKernel.translationConstant
  rw [show 3 * (π / 2) * (√(2 / π) / σ) = 3 * (π / 2 * √(2 / π)) / σ by ring, key]

/-- Finite first-order matching-cost stability of arctan persistence images. -/
theorem norm_image_sub_le_arctan {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (P : K → Set (ℝ × ℝ))
    (hm : ∀ k, MeasurableSet (P k)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    ‖image σ (arctanWeight C hC) P x - image σ (arctanWeight C hC) P y‖ ≤
      (2 * C + 3 * √(π / 2) / σ) * finiteFirstOrderMatchingCost x y := by
  simpa only [stabilityConstant_arctan] using
    norm_image_sub_le_finiteFirstOrderMatchingCost hσ hC Real.pi_div_two_pos.le
      (arctanWeight C hC) P hm hd x y hx hy

/-- Count-times-bottleneck stability of arctan finite-part persistence images. -/
theorem norm_finiteDiagramImage_sub_le_arctan {K : Type*} [Fintype K] {σ C : ℝ}
    (hσ : 0 < σ) (hC : 0 ≤ C) (P : K → Set (ℝ × ℝ)) (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (D E : Diagram ℝ) (hD : D.IsPositive) (hE : E.IsPositive)
    (hfinite : bottleneck D E < ⊤) :
    ‖finiteDiagramImage σ (arctanWeight C hC) P D -
        finiteDiagramImage σ (arctanWeight C hC) P E‖ ≤
      (2 * C + 3 * √(π / 2) / σ) *
        ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
          (bottleneck D E).toReal := by
  simpa only [stabilityConstant_arctan] using
    norm_finiteDiagramImage_sub_le_card_mul_bottleneck hσ hC Real.pi_div_two_pos.le
      (arctanWeight C hC) P hm hd D E hD hE hfinite

/-- The finite-part image is the sum of the features over the multiset of finite points. -/
theorem finiteDiagramImage_eq_sum {K : Type*} [Fintype K] {A B : ℝ} (σ : ℝ) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (D : Diagram ℝ) :
    finiteDiagramImage σ w P D = ((finitePart D.points).map (feature σ w P)).sum := by
  rw [finiteDiagramImage, image, finiteFeatureSum, Finset.sum_eq_multiset_sum]
  exact congrArg Multiset.sum (Multiset.map_univ (finitePart D.points) (feature σ w P))

end TDA.Persistence.PersistenceImage

namespace TDA.Persistence.Rips

open TDA.Filtration Real PersistenceImage

variable {V : Type u} [LinearOrder V] [Fintype V]

/-- The arctan instance of `norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy`. -/
theorem norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy_arctan
    (k : Type u) [Field k] (d e : MetricSpace V) (n : ℕ)
    {K : Type*} [Fintype K] {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖finiteDiagramImage σ (arctanWeight C hC) P (dgm k (Rips.filter d) n) -
        finiteDiagramImage σ (arctanWeight C hC) P (dgm k (Rips.filter e) n)‖ ≤
      (2 * C + 3 * √(π / 2) / σ) *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Rips.filter e) n).finiteOccurrences : ℕ) : ℝ) *
            Rips.pairwiseDiscrepancy d e := by
  simpa only [PersistenceImage.stabilityConstant_arctan] using
    norm_finiteDiagramImage_sub_le_pairwiseDiscrepancy k d e n hσ hC Real.pi_div_two_pos.le
      (arctanWeight C hC) P hm hd

end TDA.Persistence.Rips
