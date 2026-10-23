import TDA.Persistence.FinitePCostJointContinuity
import TDA.Persistence.FinitePBoundaryTransportExamples

/-! Moving labelled families, optimizer changes, diagonal crossings and the exponent-zero boundary. -/

noncomputable section
namespace TDA.Persistence.FinitePCostJointContinuityExamples
open Filter
open scoped Topology

private def exponent (t : ℝ) : ℝ := 1 + t ^ 2

private theorem exponent_ge_one (t : ℝ) : 1 ≤ exponent t := by
  dsimp [exponent]
  linarith [sq_nonneg t]

private theorem exponent_pos (t : ℝ) : 0 < exponent t :=
  zero_lt_one.trans_le (exponent_ge_one t)

private theorem exponent_continuous : Continuous exponent :=
  continuous_const.add (continuous_id.pow 2)

/-- Values refer to the matching and all-real-plan optima. -/
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

private def fourPathCostsContinuous {I J : Type*} [Fintype I] [Fintype J]
    (x : ℝ → I → ℝ × ℝ) (y : ℝ → J → ℝ × ℝ) : Prop :=
  Continuous (fun t => finitePowerMatchingCost (exponent t) (x t) (y t)) ∧
  Continuous (fun t => finitePMatchingCost (exponent t) (x t) (y t)) ∧
  Continuous (fun t => finitePowerBoundaryTransportCost (exponent t) (x t) (y t)) ∧
  Continuous (fun t => finitePBoundaryTransportCost (exponent t) (x t) (y t))

/-- Each path claim is a composition of its corresponding joint capstone. -/
private theorem four_path_costs_continuous {I J : Type*} [Fintype I] [Fintype J]
    (x : ℝ → I → ℝ × ℝ) (y : ℝ → J → ℝ × ℝ)
    (hx : Continuous x) (hy : Continuous y) : fourPathCostsContinuous x y := by
  have htuple : Continuous (fun t => (exponent t, (x t, y t))) :=
    exponent_continuous.prodMk (hx.prodMk hy)
  have hpower := (finitePowerMatchingCost_joint_continuousOn (I := I) (J := J)).comp_continuous
    htuple exponent_ge_one
  have hroot := (finitePMatchingCost_joint_continuousOn (I := I) (J := J)).comp_continuous
    htuple exponent_ge_one
  have hplanPower :=
    (finitePowerBoundaryTransportCost_joint_continuousOn (I := I) (J := J)).comp_continuous
      htuple exponent_ge_one
  have hplanRoot :=
    (finitePBoundaryTransportCost_joint_continuousOn (I := I) (J := J)).comp_continuous
      htuple exponent_ge_one
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def] using hpower
  · simpa only [Function.comp_def] using hroot
  · simpa only [Function.comp_def] using hplanPower
  · simpa only [Function.comp_def] using hplanRoot

private def fourJointContinuousWithinAt {I J : Type*} [Fintype I] [Fintype J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : Prop :=
  ContinuousWithinAt (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
    finitePowerMatchingCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} (p, (x, y)) ∧
  ContinuousWithinAt (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
    finitePMatchingCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} (p, (x, y)) ∧
  ContinuousWithinAt (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
    finitePowerBoundaryTransportCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} (p, (x, y)) ∧
  ContinuousWithinAt (fun z : ℝ × ((I → ℝ × ℝ) × (J → ℝ × ℝ)) =>
    finitePBoundaryTransportCost z.1 z.2.1 z.2.2) {z | 1 ≤ z.1} (p, (x, y))

private theorem four_joint_continuousWithinAt {I J : Type*} [Fintype I] [Fintype J]
    {p : ℝ} (hp : 1 ≤ p) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    fourJointContinuousWithinAt p x y :=
  ⟨finitePowerMatchingCost_joint_continuousOn _ hp,
    finitePMatchingCost_joint_continuousOn _ hp,
    finitePowerBoundaryTransportCost_joint_continuousOn _ hp,
    finitePBoundaryTransportCost_joint_continuousOn _ hp⟩

private def emptyFamily : Fin 0 → ℝ × ℝ := Fin.elim0

private theorem empty_values {p : ℝ} (hp : 0 < p) :
    costsAt p emptyFamily emptyFamily 0 0 := by
  apply costsAt_of_matching (finitePowerMatchingCost_empty _ _ _)
  rw [finitePMatchingCost, finitePowerMatchingCost_empty,
    Real.zero_rpow (inv_ne_zero hp.ne')]

private theorem empty_joint_and_path_continuity :
    fourJointContinuousWithinAt 1 emptyFamily emptyFamily ∧
    fourJointContinuousWithinAt (3 / 2) emptyFamily emptyFamily ∧
    fourPathCostsContinuous (fun _ => emptyFamily) (fun _ => emptyFamily) ∧
    ∀ t, costsAt (exponent t) emptyFamily emptyFamily 0 0 :=
  ⟨four_joint_continuousWithinAt le_rfl _ _,
    four_joint_continuousWithinAt (by norm_num) _ _,
    four_path_costs_continuous _ _ continuous_const continuous_const,
    fun t => empty_values (exponent_pos t)⟩

private def movingSource (t : ℝ) : Fin 1 → ℝ × ℝ := fun _ => (t, t + 2)
private def movingTarget (t : ℝ) : Fin 1 → ℝ × ℝ := fun _ => (-t, 2 - t)

private theorem moving_positive (t : ℝ) :
    (∀ i, (movingSource t i).1 < (movingSource t i).2) ∧
    (∀ j, (movingTarget t j).1 < (movingTarget t j).2) := by
  constructor <;> intro i <;> dsimp [movingSource, movingTarget] <;> linarith

private theorem moving_lifetimes_and_nonconstant :
    (∀ t i, (movingSource t i).2 - (movingSource t i).1 = 2) ∧
    (∀ t j, (movingTarget t j).2 - (movingTarget t j).1 = 2) ∧
    exponent 0 ≠ exponent 1 ∧ movingSource 0 ≠ movingSource 1 ∧ movingTarget 0 ≠ movingTarget 1 := by
  refine ⟨?_, ?_, by norm_num [exponent], ?_, ?_⟩
  · intro t i
    dsimp [movingSource]
    ring
  · intro t j
    dsimp [movingTarget]
    ring
  · intro h
    have he := congrArg (fun f : Fin 1 → ℝ × ℝ => (f 0).1) h
    norm_num [movingSource] at he
  · intro h
    have he := congrArg (fun f : Fin 1 → ℝ × ℝ => (f 0).1) h
    norm_num [movingTarget] at he

private theorem moving_charges (t : ℝ) :
    (finitePairCost (movingSource t 0) (movingTarget t 0)).toReal = 2 * |t| ∧
    (diagonalCost (movingSource t 0)).toReal = 1 ∧
    (diagonalCost (movingTarget t 0)).toReal = 1 := by
  have hb : t - -t = 2 * t := by ring
  have hd : (t + 2) - (2 - t) = 2 * t := by ring
  have hs : (t + 2) - t = 2 := by ring
  have ht : (2 - t) - -t = 2 := by ring
  norm_num [movingSource, movingTarget, finitePairCost, diagonalCost, hb, hd, hs, ht,
    abs_mul, ENNReal.toReal_ofReal, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg t)]

/-- Both coordinate families and the exponent vary in this minimum curve. -/
private theorem moving_values (t : ℝ) :
    costsAt (exponent t) (movingSource t) (movingTarget t)
      (min ((2 * |t|) ^ exponent t) 2)
      ((min ((2 * |t|) ^ exponent t) 2) ^ (exponent t)⁻¹) := by
  have hc := moving_charges t
  have hpower : finitePowerMatchingCost (exponent t) (movingSource t) (movingTarget t) =
      min ((2 * |t|) ^ exponent t) 2 := by
    unfold movingSource movingTarget at hc ⊢
    rw [finitePowerMatchingCost_singleton, hc.1, hc.2.1, hc.2.2]
    norm_num
  exact costsAt_of_matching hpower (by rw [finitePMatchingCost, hpower])

private theorem moving_path_continuity : fourPathCostsContinuous movingSource movingTarget := by
  apply four_path_costs_continuous
  · exact continuous_pi (fun _ => continuous_id.prodMk (continuous_id.add continuous_const))
  · exact continuous_pi (fun _ => continuous_id.neg.prodMk (continuous_const.sub continuous_id))

private theorem moving_zero_values :
    costsAt (exponent 0) (movingSource 0) (movingTarget 0) 0 0 := by
  simpa [exponent] using moving_values 0

private def pairingPower (t : ℝ) : ℝ :=
  FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost
    (exponent t) (movingSource t) (movingTarget t)

private def deletingPower (t : ℝ) : ℝ :=
  (FiniteBoundaryPlan.zero : FiniteBoundaryPlan (Fin 1) (Fin 1)).powerCost
    (exponent t) (movingSource t) (movingTarget t)

private theorem moving_half_candidates :
    exponent (1 / 2) = 5 / 4 ∧ pairingPower (1 / 2) = 1 ∧ deletingPower (1 / 2) = 2 ∧
    costsAt (exponent (1 / 2)) (movingSource (1 / 2)) (movingTarget (1 / 2)) 1 1 := by
  refine ⟨by norm_num [exponent], ?_, ?_, ?_⟩
  · norm_num [pairingPower, exponent, movingSource, movingTarget,
      FinitePBoundaryTransportExamples.pairSingletons, OccurrenceMatching.totalFinitePowerCost,
      OccurrenceMatching.totalBoundaryCost, finitePairCost, diagonalCost]
  · norm_num [deletingPower, exponent, movingSource, movingTarget,
      FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost, FiniteBoundaryPlan.zero,
      FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass, finitePairCost, diagonalCost]
  · simpa [exponent] using moving_values (1 / 2)

private theorem moving_one_candidates :
    exponent 1 = 2 ∧ pairingPower 1 = 4 ∧ deletingPower 1 = 2 ∧
    costsAt (exponent 1) (movingSource 1) (movingTarget 1) 2 ((2 : ℝ) ^ (1 / 2 : ℝ)) := by
  refine ⟨by norm_num [exponent], ?_, ?_, ?_⟩
  · norm_num [pairingPower, exponent, movingSource, movingTarget,
      FinitePBoundaryTransportExamples.pairSingletons, OccurrenceMatching.totalFinitePowerCost,
      OccurrenceMatching.totalBoundaryCost, finitePairCost, diagonalCost, Real.rpow_two]
  · norm_num [deletingPower, exponent, movingSource, movingTarget,
      FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost, FiniteBoundaryPlan.zero,
      FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
      finitePairCost, diagonalCost, Real.rpow_two]
  · have h := moving_values 1
    norm_num [exponent, Real.rpow_two] at h
    simpa only [show exponent 1 = 2 by norm_num [exponent]] using h

/-- Pairing attains the first optimum, while deleting both attains the second. -/
private theorem moving_optimizer_switch :
    pairingPower (1 / 2) = finitePowerMatchingCost (exponent (1 / 2))
      (movingSource (1 / 2)) (movingTarget (1 / 2)) ∧
    pairingPower (1 / 2) < deletingPower (1 / 2) ∧
    deletingPower 1 = finitePowerBoundaryTransportCost (exponent 1) (movingSource 1) (movingTarget 1) ∧
    deletingPower 1 < pairingPower 1 := by
  rw [moving_half_candidates.2.1, moving_half_candidates.2.2.1,
    moving_half_candidates.2.2.2.1, moving_one_candidates.2.1,
    moving_one_candidates.2.2.1, moving_one_candidates.2.2.2.2.2.1]
  norm_num

private def repeated (t : ℝ) : Fin 2 → ℝ × ℝ := fun _ => (t, t + 2 * exponent t)

private theorem repeated_positive_and_labels (t : ℝ) :
    (∀ i, (repeated t i).1 < (repeated t i).2) ∧
    repeated t 0 = repeated t 1 ∧ (0 : Fin 2) ≠ 1 := by
  refine ⟨?_, rfl, by decide⟩
  intro i
  dsimp [repeated]
  linarith [exponent_pos t]

private theorem repeated_charge (t : ℝ) (i : Fin 2) :
    (diagonalCost (repeated t i)).toReal = exponent t := by
  have h : (t + 2 * exponent t) - t = 2 * exponent t := by ring
  have hp := exponent_pos t
  simp [repeated, diagonalCost, h, abs_of_pos (by positivity : 0 < 2 * exponent t),
    ENNReal.toReal_ofReal hp.le]

private theorem repeated_values (t : ℝ) :
    costsAt (exponent t) (repeated t) emptyFamily
      (2 * exponent t ^ exponent t) ((2 * exponent t ^ exponent t) ^ (exponent t)⁻¹) ∧
    costsAt (exponent t) emptyFamily (repeated t)
      (2 * exponent t ^ exponent t) ((2 * exponent t ^ exponent t) ^ (exponent t)⁻¹) := by
  have hr : finitePowerMatchingCost (exponent t) (repeated t) emptyFamily =
      2 * exponent t ^ exponent t := by
    rw [finitePowerMatchingCost_of_isEmpty_right]
    simp only [Fin.sum_univ_two, repeated_charge]
    ring
  have hl : finitePowerMatchingCost (exponent t) emptyFamily (repeated t) =
      2 * exponent t ^ exponent t := by
    rw [finitePowerMatchingCost_of_isEmpty_left]
    simp only [Fin.sum_univ_two, repeated_charge]
    ring
  exact ⟨costsAt_of_matching hr (by rw [finitePMatchingCost, hr]),
    costsAt_of_matching hl (by rw [finitePMatchingCost, hl])⟩

private theorem repeated_path_continuity :
    fourPathCostsContinuous repeated (fun _ => emptyFamily) ∧
    fourPathCostsContinuous (fun _ => emptyFamily) repeated := by
  have hr : Continuous repeated := continuous_pi (fun _ => continuous_id.prodMk
    (continuous_id.add (continuous_const.mul exponent_continuous)))
  exact ⟨four_path_costs_continuous _ _ hr continuous_const,
    four_path_costs_continuous _ _ continuous_const hr⟩

private def crossing (t : ℝ) : Fin 1 → ℝ × ℝ := fun _ => (t, -t)

private theorem crossing_charge (t : ℝ) :
    (diagonalCost (crossing t 0)).toReal = |t| := by
  have h : -t - t = (-2 : ℝ) * t := by ring
  rw [diagonalCost, ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) (by norm_num))]
  dsimp [crossing]
  rw [h, abs_mul]
  norm_num

private theorem crossing_values (t : ℝ) :
    costsAt (exponent t) (crossing t) emptyFamily (|t| ^ exponent t) |t| := by
  have hp : finitePowerMatchingCost (exponent t) (crossing t) emptyFamily = |t| ^ exponent t := by
    rw [finitePowerMatchingCost_of_isEmpty_right]
    simpa using congrArg (fun a : ℝ => a ^ exponent t) (crossing_charge t)
  apply costsAt_of_matching hp
  rw [finitePMatchingCost, hp]
  exact Real.rpow_rpow_inv (abs_nonneg t) (exponent_pos t).ne'

private theorem crossing_classification :
    (∀ t, t < 0 → ∀ i, (crossing t i).1 < (crossing t i).2) ∧
    (∀ i, (crossing 0 i).1 = (crossing 0 i).2) ∧
    (∀ t, 0 < t → ∀ i, (crossing t i).2 < (crossing t i).1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht i
    dsimp [crossing]
    linarith
  · intro i
    simp [crossing]
  · intro t ht i
    dsimp [crossing]
    linarith

private theorem crossing_path_continuity :
    fourPathCostsContinuous crossing (fun _ => emptyFamily) :=
  four_path_costs_continuous _ _
    (continuous_pi (fun _ => continuous_id.prodMk continuous_id.neg)) continuous_const

private theorem empty_zero_exponent : costsAt 0 emptyFamily emptyFamily 0 1 := by
  apply costsAt_of_matching (finitePowerMatchingCost_empty _ _ _)
  simp [finitePMatchingCost]

/-- Here exponent `q` and both identical positive families move, outside the public domain near zero. -/
private theorem moving_identical_powered {q : ℝ} (hq : 0 < q) :
    finitePowerMatchingCost q (movingSource q) (movingSource q) = 0 ∧
    finitePowerBoundaryTransportCost q (movingSource q) (movingSource q) = 0 := by
  have h : finitePowerMatchingCost q (movingSource q) (movingSource q) = 0 := by
    unfold movingSource
    rw [finitePowerMatchingCost_singleton]
    have hd : q + 2 - q = 2 := by ring
    norm_num [finitePairCost, diagonalCost, hd, Real.zero_rpow hq.ne']
  exact ⟨h, by simpa only [finitePowerBoundaryTransportCost_eq_matchingCost] using h⟩

private theorem moving_identical_zero_exponent :
    finitePowerMatchingCost 0 (movingSource 0) (movingSource 0) = 1 ∧
    finitePowerBoundaryTransportCost 0 (movingSource 0) (movingSource 0) = 1 := by
  have h : finitePowerMatchingCost 0 (movingSource 0) (movingSource 0) = 1 := by
    unfold movingSource
    rw [finitePowerMatchingCost_singleton]
    norm_num [finitePairCost, diagonalCost]
  exact ⟨h, by simpa only [finitePowerBoundaryTransportCost_eq_matchingCost] using h⟩

private theorem tendsto_zero_of_positive_values {f : ℝ → ℝ}
    (hf : ∀ q, 0 < q → f q = 0) : Tendsto f (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (hf q hq).symm

private theorem zero_boundary_limits :
    Tendsto (fun q : ℝ => finitePMatchingCost q emptyFamily emptyFamily)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    Tendsto (fun q : ℝ => finitePBoundaryTransportCost q emptyFamily emptyFamily)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    Tendsto (fun q : ℝ => finitePowerMatchingCost q (movingSource q) (movingSource q))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) ∧
    Tendsto (fun q : ℝ => finitePowerBoundaryTransportCost q (movingSource q) (movingSource q))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) :=
  ⟨tendsto_zero_of_positive_values (fun _ hq => (empty_values hq).2.1),
    tendsto_zero_of_positive_values (fun _ hq => (empty_values hq).2.2.2),
    tendsto_zero_of_positive_values (fun _ hq => (moving_identical_powered hq).1),
    tendsto_zero_of_positive_values (fun _ hq => (moving_identical_powered hq).2)⟩

private theorem zero_boundary_values_differ_from_limits :
    finitePMatchingCost 0 emptyFamily emptyFamily ≠ 0 ∧
    finitePBoundaryTransportCost 0 emptyFamily emptyFamily ≠ 0 ∧
    finitePowerMatchingCost 0 (movingSource 0) (movingSource 0) ≠ 0 ∧
    finitePowerBoundaryTransportCost 0 (movingSource 0) (movingSource 0) ≠ 0 := by
  rw [empty_zero_exponent.2.1, empty_zero_exponent.2.2.2,
    moving_identical_zero_exponent.1, moving_identical_zero_exponent.2]
  norm_num

end TDA.Persistence.FinitePCostJointContinuityExamples
