import TDA.Persistence.FinitePCostContinuity
import TDA.Persistence.FinitePBoundaryTransportExamples

/-! Continuity of finite optima and the boundary at exponent zero. -/

noncomputable section
namespace TDA.Persistence.FinitePCostContinuityExamples

open Filter
open scoped Topology

/-- Exact values of both matching optima and both real-plan optima. -/
private def costsAt {I J : Type*} [Fintype I] [Fintype J] (p : ℝ)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (powered rooted : ℝ) : Prop :=
  finitePowerMatchingCost p x y = powered ∧ finitePMatchingCost p x y = rooted ∧
  finitePowerBoundaryTransportCost p x y = powered ∧
  finitePBoundaryTransportCost p x y = rooted

private theorem costsAt_of_matching {I J : Type*} [Fintype I] [Fintype J] {p a b : ℝ}
    {x : I → ℝ × ℝ} {y : J → ℝ × ℝ}
    (hpower : finitePowerMatchingCost p x y = a) (hroot : finitePMatchingCost p x y = b) :
    costsAt p x y a b :=
  ⟨hpower, hroot, by simpa only [finitePowerBoundaryTransportCost_eq_matchingCost] using hpower,
    by simpa only [finitePBoundaryTransportCost_eq_matchingCost] using hroot⟩

private def fourCostsContinuous {I J : Type*} [Fintype I] [Fintype J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : Prop :=
  ContinuousOn (fun p : ℝ => finitePowerMatchingCost p x y) (Set.Ici 1) ∧
  ContinuousOn (fun p : ℝ => finitePMatchingCost p x y) (Set.Ici 1) ∧
  ContinuousOn (fun p : ℝ => finitePowerBoundaryTransportCost p x y) (Set.Ici 1) ∧
  ContinuousOn (fun p : ℝ => finitePBoundaryTransportCost p x y) (Set.Ici 1)

private theorem four_costs_continuous {I J : Type*} [Fintype I] [Fintype J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : fourCostsContinuous x y :=
  ⟨finitePowerMatchingCost_continuousOn x y, finitePMatchingCost_continuousOn x y,
    finitePowerBoundaryTransportCost_continuousOn x y,
    finitePBoundaryTransportCost_continuousOn x y⟩

private def fourCostsContinuousWithinAt {I J : Type*} [Fintype I] [Fintype J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (p : ℝ) : Prop :=
  ContinuousWithinAt (fun q : ℝ => finitePowerMatchingCost q x y) (Set.Ici 1) p ∧
  ContinuousWithinAt (fun q : ℝ => finitePMatchingCost q x y) (Set.Ici 1) p ∧
  ContinuousWithinAt (fun q : ℝ => finitePowerBoundaryTransportCost q x y) (Set.Ici 1) p ∧
  ContinuousWithinAt (fun q : ℝ => finitePBoundaryTransportCost q x y) (Set.Ici 1) p

private theorem four_costs_continuousWithinAt {I J : Type*} [Fintype I] [Fintype J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) {p : ℝ} (hp : 1 ≤ p) :
    fourCostsContinuousWithinAt x y p :=
  ⟨finitePowerMatchingCost_continuousOn x y p hp,
    finitePMatchingCost_continuousOn x y p hp,
    finitePowerBoundaryTransportCost_continuousOn x y p hp,
    finitePBoundaryTransportCost_continuousOn x y p hp⟩

private def emptyFamily : Fin 0 → ℝ × ℝ := Fin.elim0

/-- Both empty optima vanish at every positive exponent, hence also on `[1,∞)`. -/
private theorem empty_values {p : ℝ} (hp : 0 < p) :
    costsAt p emptyFamily emptyFamily 0 0 := by
  apply costsAt_of_matching (finitePowerMatchingCost_empty _ _ _)
  rw [finitePMatchingCost, finitePowerMatchingCost_empty,
    Real.zero_rpow (inv_ne_zero hp.ne')]

private theorem empty_continuity :
    fourCostsContinuous emptyFamily emptyFamily ∧
    fourCostsContinuousWithinAt emptyFamily emptyFamily 1 ∧
    fourCostsContinuousWithinAt emptyFamily emptyFamily (3 / 2) :=
  ⟨four_costs_continuous _ _, four_costs_continuousWithinAt _ _ le_rfl,
    four_costs_continuousWithinAt _ _ (by norm_num)⟩

private def oneBar : Fin 1 → ℝ × ℝ := fun _ => (0, 2)

private theorem oneBar_positive (i : Fin 1) : (oneBar i).1 < (oneBar i).2 := by
  norm_num [oneBar]

/-- Nonempty identical positive bars test continuity at a zero powered minimum. -/
private theorem identical_values {p : ℝ} (hp : 0 < p) :
    costsAt p oneBar oneBar 0 0 := by
  have hpower : finitePowerMatchingCost p oneBar oneBar = 0 := by
    unfold oneBar
    rw [finitePowerMatchingCost_singleton]
    norm_num [finitePairCost, diagonalCost, Real.zero_rpow hp.ne']
  apply costsAt_of_matching hpower
  rw [finitePMatchingCost, hpower, Real.zero_rpow (inv_ne_zero hp.ne')]

private theorem identical_continuity : fourCostsContinuous oneBar oneBar :=
  four_costs_continuous _ _

private def repeated : Fin 2 → ℝ × ℝ := fun _ => (0, 2)

private theorem repeated_positive (i : Fin 2) : (repeated i).1 < (repeated i).2 := by
  norm_num [repeated]

/-- Two labels retain two unit charges, in deletion and insertion orientations. -/
private theorem repeated_values (p : ℝ) :
    costsAt p repeated emptyFamily 2 ((2 : ℝ) ^ p⁻¹) ∧
    costsAt p emptyFamily repeated 2 ((2 : ℝ) ^ p⁻¹) := by
  constructor
  · apply costsAt_of_matching
    · rw [finitePowerMatchingCost_of_isEmpty_right]
      norm_num [repeated, diagonalCost, Fin.sum_univ_two]
    · rw [finitePMatchingCost_of_isEmpty_right]
      norm_num [repeated, diagonalCost, Fin.sum_univ_two]
  · apply costsAt_of_matching
    · rw [finitePowerMatchingCost_of_isEmpty_left]
      norm_num [repeated, diagonalCost, Fin.sum_univ_two]
    · rw [finitePMatchingCost_of_isEmpty_left]
      norm_num [repeated, diagonalCost, Fin.sum_univ_two]

private theorem repeated_continuity :
    fourCostsContinuous repeated emptyFamily ∧ fourCostsContinuous emptyFamily repeated ∧
    fourCostsContinuousWithinAt repeated emptyFamily (3 / 2) ∧
    fourCostsContinuousWithinAt emptyFamily repeated (3 / 2) :=
  ⟨four_costs_continuous _ _, four_costs_continuous _ _,
    four_costs_continuousWithinAt _ _ (by norm_num),
    four_costs_continuousWithinAt _ _ (by norm_num)⟩

private def switchTarget : Fin 1 → ℝ × ℝ := fun _ => (3 / 2, 7 / 2)

private theorem switchTarget_positive (j : Fin 1) :
    (switchTarget j).1 < (switchTarget j).2 := by norm_num [switchTarget]

/-- The curve minimizes powered candidates before taking the reciprocal power. -/
private theorem switch_values (p : ℝ) :
    costsAt p oneBar switchTarget (min ((3 / 2 : ℝ) ^ p) 2)
      ((min ((3 / 2 : ℝ) ^ p) 2) ^ p⁻¹) := by
  have hpower : finitePowerMatchingCost p oneBar switchTarget = min ((3 / 2 : ℝ) ^ p) 2 := by
    unfold oneBar switchTarget
    rw [finitePowerMatchingCost_singleton]
    norm_num [finitePairCost, diagonalCost]
  exact costsAt_of_matching hpower (by rw [finitePMatchingCost, hpower])

/-- Continuity holds through the exponent-dependent optimizer change. -/
private theorem switch_continuity_and_optimizers :
    fourCostsContinuous oneBar switchTarget ∧
    finitePowerBoundaryTransportCost 1 oneBar switchTarget = 3 / 2 ∧
    finitePowerBoundaryTransportCost 2 oneBar switchTarget = 2 ∧
    FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost 1 oneBar switchTarget =
      finitePowerBoundaryTransportCost 1 oneBar switchTarget ∧
    finitePowerBoundaryTransportCost 2 oneBar switchTarget <
      FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost 2 oneBar switchTarget ∧
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan (Fin 1) (Fin 1)).powerCost 2 oneBar switchTarget =
      finitePowerBoundaryTransportCost 2 oneBar switchTarget :=
  ⟨four_costs_continuous _ _, FinitePBoundaryTransportExamples.switch_power_one,
    FinitePBoundaryTransportExamples.switch_power_two,
    FinitePBoundaryTransportExamples.optimizer_changes_with_exponent.1,
    FinitePBoundaryTransportExamples.optimizer_changes_with_exponent.2,
    FinitePBoundaryTransportExamples.deleting_both_optimal_at_two⟩

/-- The existing `0^0` convention is visible in empty rooted costs. -/
private theorem empty_zero_exponent : costsAt 0 emptyFamily emptyFamily 0 1 := by
  apply costsAt_of_matching (finitePowerMatchingCost_empty _ _ _)
  simp [finitePMatchingCost]

/-- At exponent zero, even the identical singleton's powered optimum equals one. -/
private theorem identical_zero_exponent : costsAt 0 oneBar oneBar 1 1 := by
  have hpower : finitePowerMatchingCost 0 oneBar oneBar = 1 := by
    unfold oneBar
    rw [finitePowerMatchingCost_singleton]
    norm_num [finitePairCost, diagonalCost]
  exact costsAt_of_matching hpower (by simp [finitePMatchingCost])

private theorem tendsto_zero_of_positive_values {f : ℝ → ℝ}
    (hf : ∀ p, 0 < p → f p = 0) : Tendsto f (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (hf p hp).symm

/-- Positive-side limits disagree with the value one at exponent zero. -/
private theorem zero_boundary_limits :
    Tendsto (fun p : ℝ => finitePMatchingCost p emptyFamily emptyFamily)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    Tendsto (fun p : ℝ => finitePBoundaryTransportCost p emptyFamily emptyFamily)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    Tendsto (fun p : ℝ => finitePowerMatchingCost p oneBar oneBar)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    Tendsto (fun p : ℝ => finitePowerBoundaryTransportCost p oneBar oneBar)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  exact ⟨tendsto_zero_of_positive_values (fun _ hp => (empty_values hp).2.1),
    tendsto_zero_of_positive_values (fun _ hp => (empty_values hp).2.2.2),
    tendsto_zero_of_positive_values (fun _ hp => (identical_values hp).1),
    tendsto_zero_of_positive_values (fun _ hp => (identical_values hp).2.2.1)⟩

private theorem zero_boundary_values_differ_from_limits :
    finitePMatchingCost 0 emptyFamily emptyFamily ≠ 0 ∧
    finitePBoundaryTransportCost 0 emptyFamily emptyFamily ≠ 0 ∧
    finitePowerMatchingCost 0 oneBar oneBar ≠ 0 ∧
    finitePowerBoundaryTransportCost 0 oneBar oneBar ≠ 0 := by
  rw [empty_zero_exponent.2.1, empty_zero_exponent.2.2.2,
    identical_zero_exponent.1, identical_zero_exponent.2.2.1]
  norm_num

end TDA.Persistence.FinitePCostContinuityExamples
