import TDA.Persistence.FiniteMatchingCost
import TDA.Persistence.PersistenceImage

/-!
# Gaussian PI stability against the attained finite matching cost

An actual minimizing partial occurrence matching turns the existing every-matching
Gaussian pixel ℓ¹ estimate into a bound by the finite first-order matching minimum.
The bandwidth, weight, pixels, positivity and explicit coefficient are unchanged.
-/

namespace TDA.Persistence.PersistenceImage

open MeasureTheory Set

/-- Apply Gaussian PI stability to an attained minimizing finite matching.
No essential part or measure-transport identification is used. -/
theorem norm_image_sub_le_finiteFirstOrderMatchingCost
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : Weight A B)
    (P : K → Set (ℝ × ℝ)) (hm : ∀ k, MeasurableSet (P k))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    ‖image σ w P x - image σ w P y‖ ≤
      stabilityConstant σ A B * finiteFirstOrderMatchingCost x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  simpa only [hM] using norm_image_sub_le_matching hσ hA hB w P hm hd M x y hx hy

end TDA.Persistence.PersistenceImage
