import TDA.Persistence.BoundaryPlans

/-!
# Boundary-plan self and symmetry laws

The identity pushforward has zero cost. Transposition is a measurable involution
on every admissible plan and preserves its cost, including infinite values.
These constructions give self, symmetry, and finiteness for the rooted value.
-/
set_option autoImplicit false
noncomputable section
namespace TDA.Persistence.BoundaryTransport
open Set MeasureTheory
open scoped ENNReal

/-- Send every bar to itself as an interior–interior boundary-plan pair. -/
def identityLeg (x : Interior) : PlanSpace :=
  ⟨(interiorIncl x, interiorIncl x), Or.inl x.2⟩

theorem measurable_identityLeg : Measurable identityLeg := by
  apply Continuous.measurable
  unfold identityLeg
  exact (continuous_interiorIncl.prodMk continuous_interiorIncl).subtype_mk _

/-- A zero-cost self-plan is the pushforward of the input through the diagonal of
interior pairs. -/
def identityBoundaryPlan (μ : Measure Interior) : Measure PlanSpace :=
  μ.map identityLeg

theorem identityBoundaryPlan_admissible (μ : Measure Interior) :
    IsBoundaryPlan (identityBoundaryPlan μ) μ μ := by
  have hfirst (s : Set Interior) : identityLeg ⁻¹' firstFiber s = s := by
    ext x
    change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (interiorIncl_injective hxy).symm ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  have hsecond (s : Set Interior) : identityLeg ⁻¹' secondFiber s = s := by
    ext x
    change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (interiorIncl_injective hxy).symm ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  constructor
  · intro s hs
    rw [identityBoundaryPlan, Measure.map_apply measurable_identityLeg
      (measurableSet_firstFiber hs), hfirst]
  · intro s hs
    rw [identityBoundaryPlan, Measure.map_apply measurable_identityLeg
      (measurableSet_secondFiber hs), hsecond]

theorem identityBoundaryPlan_cost (p : ℝ) (hp : 0 < p) (μ : Measure Interior) :
    ∫⁻ z, planPowerCost p z ∂identityBoundaryPlan μ = 0 := by
  rw [identityBoundaryPlan,
    lintegral_map (measurable_planPowerCost p) measurable_identityLeg]
  simp [planPowerCost, identityLeg, Real.zero_rpow hp.ne']

/-- Every admissible plan bounds the all-plan infimum from above. -/
theorem boundaryTransportPowerValue_le_plan (p : ℝ) {μ ν : Measure Interior}
    {π : Measure PlanSpace} (hπ : IsBoundaryPlan π μ ν) :
    boundaryTransportPowerValue p μ ν ≤ ∫⁻ z, planPowerCost p z ∂π := by
  exact (iInf_le (fun τ : Measure PlanSpace =>
    ⨅ (_ : IsBoundaryPlan τ μ ν), ∫⁻ z, planPowerCost p z ∂τ) π).trans
      (iInf_le (fun _ : IsBoundaryPlan π μ ν =>
        ∫⁻ z, planPowerCost p z ∂π) hπ)

/-- The powered infimum vanishes at every input, independently of its mass. -/
theorem boundaryTransportPowerValue_self (p : ℝ) (hp : 0 < p) (μ : Measure Interior) :
    boundaryTransportPowerValue p μ μ = 0 := by
  apply le_antisymm
  · exact (boundaryTransportPowerValue_le_plan p
      (identityBoundaryPlan_admissible μ)).trans_eq (identityBoundaryPlan_cost p hp μ)
  · exact bot_le

/-- Transpose the endpoints of a genuine boundary-plan pair. -/
def transposePlan (z : PlanSpace) : PlanSpace :=
  ⟨(z.1.2, z.1.1), z.2.symm⟩

@[simp] theorem transposePlan_involutive (z : PlanSpace) :
    transposePlan (transposePlan z) = z := by
  apply Subtype.ext
  rfl

theorem measurable_transposePlan : Measurable transposePlan := by
  apply Continuous.measurable
  unfold transposePlan
  exact (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _

/-- Transposition is an involution on the whole space of Borel measures. -/
theorem transposePlan_map_map (π : Measure PlanSpace) :
    (π.map transposePlan).map transposePlan = π := by
  rw [Measure.map_map measurable_transposePlan measurable_transposePlan]
  have h : transposePlan ∘ transposePlan = id := by
    funext z
    exact transposePlan_involutive z
  rw [h]
  simp

@[simp] theorem transposePlan_preimage_firstFiber (s : Set Interior) :
    transposePlan ⁻¹' firstFiber s = secondFiber s := by
  rfl

@[simp] theorem transposePlan_preimage_secondFiber (s : Set Interior) :
    transposePlan ⁻¹' secondFiber s = firstFiber s := by
  rfl

/-- Transposing all plan mass swaps the two prescribed interior marginals. -/
theorem transposePlan_admissible {π : Measure PlanSpace} {μ ν : Measure Interior}
    (hπ : IsBoundaryPlan π μ ν) :
    IsBoundaryPlan (π.map transposePlan) ν μ := by
  constructor
  · intro s hs
    rw [Measure.map_apply measurable_transposePlan (measurableSet_firstFiber hs),
      transposePlan_preimage_firstFiber]
    exact hπ.second s hs
  · intro s hs
    rw [Measure.map_apply measurable_transposePlan (measurableSet_secondFiber hs),
      transposePlan_preimage_secondFiber]
    exact hπ.first s hs

@[simp] theorem planPowerCost_transpose (p : ℝ) (z : PlanSpace) :
    planPowerCost p (transposePlan z) = planPowerCost p z := by
  simp [planPowerCost, transposePlan, dist_comm]

theorem transposePlan_cost (p : ℝ) (π : Measure PlanSpace) :
    (∫⁻ z, planPowerCost p z ∂π.map transposePlan) =
      ∫⁻ z, planPowerCost p z ∂π := by
  rw [lintegral_map (measurable_planPowerCost p) measurable_transposePlan]
  simp

/-- The all-plan powered infimum is symmetric, including at infinite cost. -/
theorem boundaryTransportPowerValue_symm (p : ℝ) (μ ν : Measure Interior) :
    boundaryTransportPowerValue p μ ν = boundaryTransportPowerValue p ν μ := by
  apply le_antisymm
  · apply le_iInf
    intro π
    apply le_iInf
    intro hπ
    exact (boundaryTransportPowerValue_le_plan p (transposePlan_admissible hπ)).trans_eq
      (transposePlan_cost p π)
  · apply le_iInf
    intro π
    apply le_iInf
    intro hπ
    exact (boundaryTransportPowerValue_le_plan p (transposePlan_admissible hπ)).trans_eq
      (transposePlan_cost p π)

/-- Reciprocal-p root of the powered all-plan value. -/
def boundaryTransportDistance (p : ℝ) (μ ν : Measure Interior) : ℝ≥0∞ :=
  (boundaryTransportPowerValue p μ ν) ^ (1 / p)

theorem boundaryTransportDistance_self (p : ℝ) (hp : 0 < p)
    (μ : Measure Interior) : boundaryTransportDistance p μ μ = 0 := by
  rw [boundaryTransportDistance, boundaryTransportPowerValue_self p
    hp]
  exact ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp)

theorem boundaryTransportDistance_symm (p : ℝ) (μ ν : Measure Interior) :
    boundaryTransportDistance p μ ν = boundaryTransportDistance p ν μ := by
  rw [boundaryTransportDistance, boundaryTransportDistance,
    boundaryTransportPowerValue_symm]

theorem boundaryTransportDistance_lt_top (p : ℝ) (hp : 0 < p)
    (μ ν : Measure Interior)
    (hμ : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (hν : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂ν) < ∞) :
    boundaryTransportDistance p μ ν < ∞ := by
  exact ENNReal.rpow_lt_top_of_nonneg
    (le_of_lt (one_div_pos.mpr hp))
    (boundaryTransportPowerValue_lt_top p μ ν hμ hν).ne

end TDA.Persistence.BoundaryTransport
