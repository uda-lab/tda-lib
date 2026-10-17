import TDA.Persistence.FinitePBoundaryTransport
import TDA.Persistence.FinitePMatchingCostLaws

/-!
# Distance laws of finite real boundary transport

The rooted optimum over all feasible real reservoir matrices equals the finite
matching optimum. Its self, symmetry, triangle and positive-lifetime separation
laws therefore follow from the matching laws, without assuming an integral plan
or identifying all Borel/Radon couplings. Zero cost identifies occurrence values
with multiplicity, allowing arbitrary changes of labels.
-/

namespace TDA.Persistence

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

@[simp] theorem finitePBoundaryTransportCost_self {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) : finitePBoundaryTransportCost p x x = 0 := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_self hp x

/-- Symmetry holds for the supporting algebra at every real exponent. -/
theorem finitePBoundaryTransportCost_comm (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePBoundaryTransportCost p x y = finitePBoundaryTransportCost p y x := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost, finitePMatchingCost_comm p x y]

/-- The sharp rooted triangle law transfers through the proved finite-plan equality. -/
theorem finitePBoundaryTransportCost_triangle {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (z : K → ℝ × ℝ) :
    finitePBoundaryTransportCost p x z ≤
      finitePBoundaryTransportCost p x y + finitePBoundaryTransportCost p y z := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_triangle hp x y z

theorem finitePBoundaryTransportCost_eq_zero_of_equiv {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (e : I ≃ J) (he : ∀ i, x i = y (e i)) :
    finitePBoundaryTransportCost p x y = 0 := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_eq_zero_of_equiv hp x y e he

/-- Positive lifetimes exclude free deletion of diagonal occurrences. -/
theorem finitePBoundaryTransportCost_eq_zero_iff {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    finitePBoundaryTransportCost p x y = 0 ↔ ∃ e : I ≃ J, ∀ i, x i = y (e i) := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_eq_zero_iff hp x y hx hy

end TDA.Persistence
