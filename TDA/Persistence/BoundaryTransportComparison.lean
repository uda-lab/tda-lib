import TDA.Persistence.BoundaryPlanLaws
import TDA.Persistence.BoundaryTransportForward
import TDA.Persistence.BoundaryTransportReverse

/-!
# Equality of boundary and reservoir transport infima

The two measurable competitor transformations identify the all-boundary-plan
powered value with the all-reservoir-competitor powered value. Capacities dominate
the sum of the original masses. This fixed-space comparison supplies no ordinary
transport minimizer or metric law.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.BoundaryTransport

open Set MeasureTheory
open scoped ENNReal

/-- Powered transport infimum over all measures with the two reservoir marginals. -/
def reservoirPowerValue (p : ℝ) (μ ν : Measure Interior) (R : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ γ : Measure (Space × Space),
    ⨅ (_ : γ.map Prod.fst = reservoirMeasure μ R ∧
      γ.map Prod.snd = reservoirMeasure ν R),
      ∫⁻ z, collapsedPowerCost p z ∂γ

theorem reservoirPowerValue_le_plan (p : ℝ) (μ ν : Measure Interior)
    (R : ℝ≥0∞) (γ : Measure (Space × Space))
    (hfirst : γ.map Prod.fst = reservoirMeasure μ R)
    (hsecond : γ.map Prod.snd = reservoirMeasure ν R) :
    reservoirPowerValue p μ ν R ≤ ∫⁻ z, collapsedPowerCost p z ∂γ := by
  exact (iInf_le (fun τ : Measure (Space × Space) =>
    ⨅ (_ : τ.map Prod.fst = reservoirMeasure μ R ∧
      τ.map Prod.snd = reservoirMeasure ν R),
      ∫⁻ z, collapsedPowerCost p z ∂τ) γ).trans
        (iInf_le (fun _ : γ.map Prod.fst = reservoirMeasure μ R ∧
          γ.map Prod.snd = reservoirMeasure ν R =>
          ∫⁻ z, collapsedPowerCost p z ∂γ) ⟨hfirst, hsecond⟩)

/-- Both directions compare every competitor, with extended values retained. -/
theorem boundaryTransportPowerValue_eq_reservoirPowerValue
    (p : ℝ) (hp : 1 ≤ p) (μ ν : Measure Interior)
    (R : ℝ≥0∞) (hR : R < ∞) (htotal : μ Set.univ + ν Set.univ ≤ R) :
    boundaryTransportPowerValue p μ ν = reservoirPowerValue p μ ν R := by
  apply le_antisymm
  · unfold reservoirPowerValue
    apply le_iInf
    intro γ
    apply le_iInf
    intro hγ
    obtain ⟨π, hπ, hcost⟩ :=
      Reverse.exists_boundaryPlan_cost_le p hp γ μ ν R hγ.1 hγ.2
    exact (boundaryTransportPowerValue_le_plan p hπ).trans hcost
  · unfold boundaryTransportPowerValue
    apply le_iInf
    intro π
    apply le_iInf
    intro hπ
    obtain ⟨hfirst, hsecond, hcost⟩ :=
      collapsedAugmentation_forward hπ R hR htotal p hp
    exact (reservoirPowerValue_le_plan p μ ν R (collapsedAugmentation π R)
      hfirst hsecond).trans hcost

/-- The powered reservoir value is independent of the admissible finite capacity. -/
theorem reservoirPowerValue_independent
    (p : ℝ) (hp : 1 ≤ p) (μ ν : Measure Interior)
    (R S : ℝ≥0∞) (hR : R < ∞) (hS : S < ∞)
    (hμνR : μ Set.univ + ν Set.univ ≤ R)
    (hμνS : μ Set.univ + ν Set.univ ≤ S) :
    reservoirPowerValue p μ ν R = reservoirPowerValue p μ ν S :=
  (boundaryTransportPowerValue_eq_reservoirPowerValue p hp μ ν R hR hμνR).symm.trans
    (boundaryTransportPowerValue_eq_reservoirPowerValue p hp μ ν S hS hμνS)

/-- Reciprocal-p root of the all-reservoir-competitor value. -/
def reservoirDistance (p : ℝ) (μ ν : Measure Interior) (R : ℝ≥0∞) : ℝ≥0∞ :=
  (reservoirPowerValue p μ ν R) ^ (1 / p)

theorem boundaryTransportDistance_eq_reservoirDistance
    (p : ℝ) (hp : 1 ≤ p) (μ ν : Measure Interior)
    (R : ℝ≥0∞) (hR : R < ∞) (htotal : μ Set.univ + ν Set.univ ≤ R) :
    boundaryTransportDistance p μ ν = reservoirDistance p μ ν R := by
  exact congrArg (fun z : ℝ≥0∞ => z ^ (1 / p))
    (boundaryTransportPowerValue_eq_reservoirPowerValue p hp μ ν R hR htotal)

end TDA.Persistence.BoundaryTransport
