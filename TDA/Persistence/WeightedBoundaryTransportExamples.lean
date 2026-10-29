import TDA.Persistence.WeightedBoundaryTransportApproximation
import TDA.Persistence.WeightedKernelExamples
import TDA.Persistence.BoundaryTransportZero
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Native transport stability beyond finite unit diagrams

A nonatomic band and a countable noncompact law exercise the actual measure
bound and the native quantization convergence theorem. The latter has finite
diagonal moment and divergent ambient first moment. Fractional repeated atoms,
zero weights and unequal masses exercise the finite atomic bridge.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.WeightedKernel.BoundaryTransportExamples

open MeasureTheory Set Filter Topology BoundaryTransport
open scoped ENNReal NNReal

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


private def scaledBandLaw : Measure Interior := (3 / 2 : ℝ≥0∞) • bandLaw

private theorem scaledBandLaw_mass : scaledBandLaw univ = 3 / 2 := by
  rw [scaledBandLaw, Measure.smul_apply]
  have hm : bandLaw univ = 1 := by
    rw [bandLaw, Measure.map_apply continuous_bandPoint.measurable MeasurableSet.univ]
    simp
  simp [hm]

private instance : IsFiniteMeasure scaledBandLaw := ⟨by rw [scaledBandLaw_mass]; finiteness⟩

private theorem unequal_masses : scaledBandLaw univ ≠ rayLaw univ := by
  rw [scaledBandLaw_mass, measure_univ]
  intro h
  have hreal := congrArg ENNReal.toReal h
  norm_num at hreal

private theorem scaledBandLaw_moment :
    (∫⁻ x, ENNReal.ofReal (depth x) ∂scaledBandLaw) = 3 / 2 := by
  have h := bandLaw_moment 1
  simp only [Real.rpow_one] at h
  rw [scaledBandLaw, lintegral_smul_measure, h]
  simp

private theorem unequal_mass_nonatomic_stability {A B : ℝ} (σ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖weightedPersistenceEmbedding σ (upperWeight w) scaledBandLaw -
      weightedPersistenceEmbedding σ (upperWeight w) rayLaw‖ ≤
        stabilityConstant σ A B * (boundaryTransportDistance 1 scaledBandLaw rayLaw).toReal := by
  exact norm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance
    σ hA hB w scaledBandLaw rayLaw
    (by rw [scaledBandLaw_moment]; finiteness)
    (by simpa only [Real.rpow_one] using (rayLaw_moment 1).trans_lt (by simp))

private theorem noncompact_quantized_embedding {A B : ℝ} (σ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    (¬ Integrable (fun x : Interior => ‖x.1‖) rayLaw) ∧
      (∀ n, atomicMeasure (quantizedDiagram rayLaw n) univ = 1) ∧
      Tendsto (fun n => weightedPersistenceEmbedding σ (upperWeight w)
        (atomicMeasure (quantizedDiagram rayLaw n))) atTop
          (𝓝 (weightedPersistenceEmbedding σ (upperWeight w) rayLaw)) := by
  refine ⟨rayLaw_ambient_first_moment_diverges, ?_, ?_⟩
  · intro n
    simpa using quantizedDiagram_mass rayLaw n
  · apply weightedPersistenceEmbedding_quantizedDiagram_tendsto σ hA hB w
    simpa only [Real.rpow_one] using (rayLaw_moment 1).trans_lt (by simp)

private theorem nonatomic_quantized_embedding {A B : ℝ} (σ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    NullSingletonClass bandLaw ∧
      Tendsto (fun n => weightedPersistenceEmbedding σ (upperWeight w)
        (atomicMeasure (quantizedDiagram bandLaw n))) atTop
          (𝓝 (weightedPersistenceEmbedding σ (upperWeight w) bandLaw)) := by
  refine ⟨bandLaw_noAtoms, ?_⟩
  apply weightedPersistenceEmbedding_quantizedDiagram_tendsto σ hA hB w
  simpa only [Real.rpow_one] using (bandLaw_moment 1).trans_lt (by simp)

private theorem zero_target_bound {A B : ℝ} (σ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖weightedPersistenceEmbedding σ (upperWeight w) rayLaw‖ ≤
      stabilityConstant σ A B := by
  have h := norm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance
    σ hA hB w rayLaw 0
    (by simpa only [Real.rpow_one] using (rayLaw_moment 1).trans_lt (by simp)) (by simp)
  have hzero : weightedPersistenceEmbedding σ (upperWeight w) 0 = 0 := by
    rw [weightedPersistenceEmbedding_eq_integral_native σ hA w]
    simp
  rw [hzero, sub_zero, boundaryTransportDistance_zero_target 1 le_rfl rayLaw
    (measure_lt_top _ _), rayLaw_moment] at h
  simpa using h

private def repeatedPoint : Interior := ⟨(0, 2), by norm_num⟩
private def unusedPoint : Interior := ⟨(5, 7), by norm_num⟩
private def atomPoints : Fin 3 → Interior := ![repeatedPoint, repeatedPoint, unusedPoint]
private def atomMasses : Fin 3 → ℝ≥0 := ![1 / 2, 1 / 2, 0]

private theorem fractional_coincident_embedding :
    weightedPersistenceEmbedding 1 (upperWeight WeightedKernelExamples.clippedWeight)
      (atomicMeasure (FiniteWeightedDiagram.ofIndexed atomMasses atomPoints)) =
        featureAt 1 (0, 2) := by
  rw [weightedPersistenceEmbedding_ofIndexed]
  simp [atomMasses, atomPoints, Fin.sum_univ_succ, repeatedPoint, unusedPoint,
    weightedFeature, WeightedKernelExamples.clippedWeight, birthPersistence, ← add_smul]
  norm_num

private theorem fractional_zero_stability :
    ‖weightedPersistenceEmbedding 1 (upperWeight WeightedKernelExamples.clippedWeight)
        (atomicMeasure (FiniteWeightedDiagram.ofIndexed atomMasses atomPoints)) -
      weightedPersistenceEmbedding 1 (upperWeight WeightedKernelExamples.clippedWeight)
        (atomicMeasure 0)‖ ≤
      stabilityConstant 1 1 1 * FiniteWeightedDiagram.pBoundaryTransportCost 1
        (FiniteWeightedDiagram.ofIndexed atomMasses atomPoints) 0 :=
  norm_weightedPersistenceEmbedding_atomicMeasure_sub_le 1 (by norm_num) (by norm_num)
    WeightedKernelExamples.clippedWeight _ _

private def zeroWeight : PersistenceImage.Weight 0 0 where
  toFun _ := 0
  nonneg _ := le_rfl
  bounded _ := le_rfl
  lipschitz _ _ := by simp
  zero_persistence _ := rfl

private theorem zero_constant_without_moments (μ ν : Measure Interior)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    weightedPersistenceEmbedding 1 (upperWeight zeroWeight) μ =
      weightedPersistenceEmbedding 1 (upperWeight zeroWeight) ν := by
  have h := enorm_weightedPersistenceEmbedding_sub_le_boundaryTransportDistance
    1 le_rfl le_rfl zeroWeight μ ν
  have hn : ENNReal.ofReal
      ‖weightedPersistenceEmbedding 1 (upperWeight zeroWeight) μ -
        weightedPersistenceEmbedding 1 (upperWeight zeroWeight) ν‖ = 0 := by
    apply le_antisymm _ bot_le
    simpa [stabilityConstant] using h
  exact sub_eq_zero.mp (norm_eq_zero.mp (ENNReal.ofReal_eq_zero.mp hn |>.antisymm (norm_nonneg _)))

end TDA.Persistence.WeightedKernel.BoundaryTransportExamples
