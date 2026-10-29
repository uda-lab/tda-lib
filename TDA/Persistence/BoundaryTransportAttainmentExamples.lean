import TDA.Persistence.BoundaryTransportAttainment
import TDA.Persistence.BoundaryTransportZero
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite-measure attainment beyond finite diagrams

A nonatomic band and a countable unbounded family have finite diagonal moments.
The latter has infinite first birth-coordinate moment. The exported attainment
theorem applies to both without a finite-support or Euclidean-moment premise.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TDA.Persistence.BoundaryTransport.AttainmentExamples

private def bandPoint (t : ℝ) : Interior := ⟨(t, t + 2), by linarith⟩

private theorem continuous_bandPoint : Continuous bandPoint := by
  exact (continuous_id.prodMk (continuous_id.add continuous_const)).subtype_mk _

private def bandLaw : Measure Interior := (volume.restrict (Icc (0 : ℝ) 1)).map bandPoint

private instance : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr (by simp)

private instance : IsFiniteMeasure bandLaw := Measure.isFiniteMeasure_map _ _

private theorem bandLaw_noAtoms : NullSingletonClass bandLaw := by
  constructor
  intro x
  rw [bandLaw, Measure.map_apply continuous_bandPoint.measurable (measurableSet_singleton x)]
  apply le_antisymm _ bot_le
  calc
    (volume.restrict (Icc (0 : ℝ) 1)) (bandPoint ⁻¹' {x}) ≤
        (volume.restrict (Icc (0 : ℝ) 1)) {x.1.1} := by
      apply measure_mono
      intro t ht
      have h : bandPoint t = x := ht
      exact congrArg (fun z : Interior => z.1.1) h
    _ = 0 := measure_singleton _

private theorem bandLaw_moment (p : ℝ) :
    (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂bandLaw) = 1 := by
  rw [bandLaw, lintegral_map (by simp_rw [depth_eq]; fun_prop) continuous_bandPoint.measurable]
  have hdepth (t : ℝ) : depth (bandPoint t) = 1 := by
    simp [depth_eq, bandPoint]
  simp only [hdepth, Real.one_rpow, ENNReal.ofReal_one, lintegral_one]
  simp

private theorem nonatomic_minimizer :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π bandLaw 0 ∧
      (∫⁻ z, planPowerCost 2 z ∂π) = 1 := by
  obtain ⟨π, hπ, hcost⟩ := exists_minimizing_boundaryPlan 2 (by norm_num) bandLaw 0
  refine ⟨π, hπ, hcost.trans ?_⟩
  rw [boundaryTransportPowerValue_zero_target 2 (by norm_num) bandLaw (measure_lt_top _ _),
    bandLaw_moment]

private def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

private theorem half_ne_zero : half ≠ 0 := by
  intro h
  have := congrArg (fun t : unitInterval => (t : ℝ)) h
  norm_num [half] at this

private def rayPoint (n : ℕ) : Interior :=
  ⟨((2 : ℝ) ^ (n + 2), (2 : ℝ) ^ (n + 2) + 2), by linarith⟩

private def rayLaw : Measure Interior := (ProbabilityTheory.geometricMeasure half).map rayPoint

private instance : IsProbabilityMeasure rayLaw :=
  Measure.isProbabilityMeasure_map ((measurable_of_countable rayPoint)).aemeasurable

private theorem rayLaw_moment (p : ℝ) :
    (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂rayLaw) = 1 := by
  rw [rayLaw, lintegral_map (by simp_rw [depth_eq]; fun_prop) ((measurable_of_countable rayPoint))]
  have hdepth (n : ℕ) : depth (rayPoint n) = 1 := by simp [depth_eq, rayPoint]
  simp only [hdepth, Real.one_rpow, ENNReal.ofReal_one, lintegral_one]
  simp

private theorem rayLaw_first_moment_diverges :
    ¬ Integrable (fun x : Interior => x.1.1) rayLaw := by
  intro h
  have hn := (integrable_map_measure (by fun_prop : AEStronglyMeasurable
    (fun x : Interior => x.1.1) rayLaw)
    ((measurable_of_countable rayPoint)).aemeasurable).1 h
  have hs := (ProbabilityTheory.integrable_geometricMeasure_iff half_ne_zero).1 hn
  have hweight (n : ℕ) : (1 - (half : ℝ)) ^ n * (half : ℝ) *
      ‖(rayPoint n).1.1‖ = 2 := by
    simp only [half, rayPoint, Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (n + 2))]
    rw [pow_add]
    norm_num
    calc
      (1 / 2 : ℝ) ^ n * (1 / 2) * (2 ^ n * 4) =
          ((1 / 2 : ℝ) * 2) ^ n * 2 := by rw [mul_pow]; ring
      _ = 2 := by norm_num
  have hlim : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, hweight] using hs.tendsto_atTop_zero
  have hbad : (2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at hbad

private theorem rayLaw_no_compact_full_measure (K : Set Interior) (hK : IsCompact K) :
    rayLaw Kᶜ ≠ 0 := by
  intro hzero
  apply rayLaw_first_moment_diverges
  have h : IntegrableOn (fun x : Interior => x.1.1) K rayLaw :=
    (continuous_fst.comp continuous_subtype_val).continuousOn.integrableOn_compact hK
  have heq : rayLaw.restrict K = rayLaw :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hzero)
  simpa only [IntegrableOn, heq] using h

private theorem rayLaw_ambient_first_moment_diverges :
    ¬ Integrable (fun x : Interior => ‖x.1‖) rayLaw := by
  intro h
  apply rayLaw_first_moment_diverges
  refine h.mono (by fun_prop) (.of_forall fun x => ?_)
  change ‖x.1.1‖ ≤ ‖‖x.1‖‖
  rw [norm_norm, Prod.norm_def]
  exact le_max_left _ _

private theorem unbounded_minimizer :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π rayLaw bandLaw ∧
      (∫⁻ z, planPowerCost 2 z ∂π) = boundaryTransportPowerValue 2 rayLaw bandLaw ∧
      (∫⁻ z, planPowerCost 2 z ∂π) < ∞ := by
  exact exists_finite_cost_minimizing_boundaryPlan 2 (by norm_num) rayLaw bandLaw
    (by rw [rayLaw_moment]; simp) (by rw [bandLaw_moment]; simp)

private theorem unbounded_rooted_minimizer :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π rayLaw 0 ∧
      (∫⁻ z, planPowerCost 2 z ∂π) ^ (1 / (2 : ℝ)) = 1 := by
  obtain ⟨π, hπ, _, hroot⟩ := exists_minimizing_boundaryPlan_rooted 2 (by norm_num) rayLaw 0
  refine ⟨π, hπ, hroot.trans ?_⟩
  rw [boundaryTransportDistance_zero_target 2 (by norm_num) rayLaw (measure_lt_top _ _),
    rayLaw_moment]
  simp

private theorem zero_minimizer :
    ∃ π : Measure PlanSpace, IsBoundaryPlan π 0 0 ∧
      (∫⁻ z, planPowerCost 2 z ∂π) = 0 := by
  obtain ⟨π, hπ, hcost⟩ := exists_minimizing_boundaryPlan 2 (by norm_num) 0 0
  exact ⟨π, hπ, hcost.trans (boundaryTransportPowerValue_self 2 (by norm_num) 0)⟩

private def distantDeleteLeg (x : Interior) : PlanSpace :=
  ⟨(interiorIncl x, ⟨(0, 0), le_rfl⟩), Or.inl x.2⟩

private theorem measurable_distantDeleteLeg : Measurable distantDeleteLeg := by
  apply Continuous.measurable
  exact (continuous_interiorIncl.prodMk continuous_const).subtype_mk _

private def infiniteCostPlan : Measure PlanSpace := rayLaw.map distantDeleteLeg

private theorem infiniteCostPlan_admissible : IsBoundaryPlan infiniteCostPlan rayLaw 0 := by
  constructor
  · intro s hs
    rw [infiniteCostPlan, Measure.map_apply measurable_distantDeleteLeg
      (measurableSet_firstFiber hs)]
    congr 1
    ext x
    change interiorIncl x ∈ interiorIncl '' s ↔ x ∈ s
    exact interiorIncl_injective.mem_set_image
  · intro s hs
    rw [infiniteCostPlan, Measure.map_apply measurable_distantDeleteLeg
      (measurableSet_secondFiber hs)]
    have hempty : distantDeleteLeg ⁻¹' secondFiber s = ∅ := by
      ext x
      constructor
      · rintro ⟨y, _, hy⟩
        have h : y.1 = (0, 0) := congrArg Subtype.val hy
        have := y.2
        simp [h] at this
      · simp
    simp [hempty]

private theorem infiniteCostPlan_cost : (∫⁻ z, planPowerCost 1 z ∂infiniteCostPlan) = ∞ := by
  by_contra hne
  have hfin : (∫⁻ z, planPowerCost 1 z ∂infiniteCostPlan) < ∞ := lt_top_iff_ne_top.mpr hne
  rw [infiniteCostPlan, lintegral_map (measurable_planPowerCost 1)
    measurable_distantDeleteLeg] at hfin
  have hbound (x : Interior) :
      ENNReal.ofReal ‖x.1.1‖ ≤ planPowerCost 1 (distantDeleteLeg x) := by
    apply ENNReal.ofReal_le_ofReal
    change ‖x.1.1‖ ≤ dist x.1 (0, 0) ^ (1 : ℝ)
    simp only [Real.rpow_one, Prod.dist_eq, Real.dist_eq, sub_zero, Real.norm_eq_abs]
    exact le_max_left _ _
  apply rayLaw_first_moment_diverges
  exact ⟨by fun_prop,
    (hasFiniteIntegral_iff_norm _).2 ((lintegral_mono hbound).trans_lt hfin)⟩

private theorem finite_optimum_with_infinite_competitor :
    (∫⁻ z, planPowerCost 1 z ∂infiniteCostPlan) = ∞ ∧
      ∃ π : Measure PlanSpace, IsBoundaryPlan π rayLaw 0 ∧
        (∫⁻ z, planPowerCost 1 z ∂π) = 1 := by
  refine ⟨infiniteCostPlan_cost, ?_⟩
  obtain ⟨π, hπ, hcost⟩ := exists_minimizing_boundaryPlan 1 (by norm_num) rayLaw 0
  refine ⟨π, hπ, hcost.trans ?_⟩
  rw [boundaryTransportPowerValue_zero_target 1 (by norm_num) rayLaw (measure_lt_top _ _),
    rayLaw_moment]

end TDA.Persistence.BoundaryTransport.AttainmentExamples
