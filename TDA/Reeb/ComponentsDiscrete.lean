import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Path components of discrete spaces

In a discrete space every path is constant, so joined points are equal
(`joined_eq_of_discrete`) and the space is its own set of path components
(`zerothHomotopyEquivOfDiscrete`, whose inverse is `ZerothHomotopy.mk`).
-/

namespace TDA.Reeb

noncomputable section

section discrete

variable {A : Type*} [TopologicalSpace A]

/-- In a discrete space, joined points are equal. -/
theorem joined_eq_of_discrete [DiscreteTopology A] {x y : A} (h : Joined x y) : x = y := by
  obtain ⟨γ⟩ := h
  simpa using PreconnectedSpace.constant (inferInstance : PreconnectedSpace unitInterval)
    γ.continuous (x := 0) (y := 1)

/-- A discrete space is its own set of path components. -/
def zerothHomotopyEquivOfDiscrete (A : Type*) [TopologicalSpace A] [DiscreteTopology A] :
    ZerothHomotopy A ≃ A :=
  (Equiv.ofBijective ZerothHomotopy.mk
    ⟨fun _ _ h => joined_eq_of_discrete (Quotient.exact h), ZerothHomotopy.mk_surjective⟩).symm

end discrete

end

end TDA.Reeb
