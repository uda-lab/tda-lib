import TDA.Persistence.RipsSamplingEmpirical
import TDA.Persistence.RipsSamplingExamples

/-!
# Finite empirical sampled-law fixtures

The two-point training tuple repeats one observation, giving weights `2/3`
and `1/3`. Its total variation from the uniform population is `1/6`, and the
one-Wasserstein distance between the two-draw full H₀ laws is at most `1/3`.
-/

noncomputable section
namespace TDA.Persistence.RipsSamplingEmpiricalExamples

open TDA.Probability TDA.Persistence.Rips
open scoped ENNReal NNReal

local instance : MetricSpace Bool := RipsSamplingExamples.epsilonTwoPointMetric

/-- The uniform probability mass function on `Bool`. -/
private noncomputable def uniformBoolPMF : PMF Bool :=
  PMF.ofFintype (fun _ : Bool => (Fintype.card Bool : ℝ≥0∞)⁻¹)
    (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- A training tuple with a repeated observation. -/
def repeatedTraining : Fin 3 → Bool := ![false, false, true]

/-- Its empirical law counts both copies of the repeated observation. -/
theorem repeatedTraining_masses :
    empiricalPMF repeatedTraining (by omega) false = (2 : ℝ≥0∞) / 3 ∧
    empiricalPMF repeatedTraining (by omega) true = (1 : ℝ≥0∞) / 3 := by
  refine ⟨?_, ?_⟩
  · rw [empiricalPMF_apply]
    congr 1
    norm_cast
    rw [Finset.filter_congr_decidable]
    decide
  · rw [empiricalPMF_apply]
    congr 1
    norm_cast
    rw [Finset.filter_congr_decidable]
    decide

/-- The deterministic training error is exactly one sixth. -/
theorem repeatedTraining_totalVariation :
    finiteTotalVariation uniformBoolPMF
      (empiricalPMF repeatedTraining (by omega)) = (6 : ℝ≥0∞)⁻¹ := by
  rw [finiteTotalVariation_eq_sum_sub, Fintype.sum_bool]
  simp only [uniformBoolPMF, PMF.ofFintype_apply, Fintype.card_bool,
    repeatedTraining_masses.1, repeatedTraining_masses.2]
  norm_num only [Nat.cast_ofNat]
  have h : (2 : ℝ≥0)⁻¹ - 1 / 3 + ((2 : ℝ≥0)⁻¹ - 2 / 3) = (6 : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    norm_num [NNReal.coe_sub_def]
  have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) h
  simpa only [ENNReal.coe_add, ENNReal.coe_sub, ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
    ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_one,
    ENNReal.coe_ofNat] using hc

private theorem twoPoint_diameter : ∀ x y : Bool, dist x y ≤ (1 : ℝ) := by
  intro x y
  change dist (if x then (1 : ℝ) else 0) (if y then (1 : ℝ) else 0) ≤ 1
  cases x <;> cases y <;> norm_num [Real.dist_eq]

/-- The empirical law gives an explicit full-H₀ resampling error bound at
`p = 1` and resampling size two. The training tuple has three entries. -/
theorem repeatedTraining_fullH0_bound (k : Type*) [Field k] :
    wasserstein 1 bottleneck
      (sampleLaw k uniformBoolPMF 2 0)
      (sampleLaw k (empiricalPMF repeatedTraining (by omega)) 2 0) ≤
        (3 : ℝ≥0∞)⁻¹ := by
  have h := wasserstein_sampleLaw_empiricalPMF_le k uniformBoolPMF
    repeatedTraining (by omega) 1 twoPoint_diameter (p := 1) le_rfl 2 0 (by omega)
  have harith : (2 : ℝ≥0∞) * (6 : ℝ≥0∞)⁻¹ = (3 : ℝ≥0∞)⁻¹ := by
    have h : (2 : ℝ≥0) * (6 : ℝ≥0)⁻¹ = (3 : ℝ≥0)⁻¹ := by norm_num
    have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) h
    simpa only [ENNReal.coe_mul, ENNReal.coe_inv (by norm_num : (6 : ℝ≥0) ≠ 0),
      ENNReal.coe_inv (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using hc
  simpa only [inv_one, ENNReal.rpow_one, Nat.choose_self, Nat.cast_one,
    ENNReal.coe_one, one_mul, mul_one, repeatedTraining_totalVariation, harith] using h

/-- A population atom may have zero weight: observing only the other atom
reconstructs the point-mass population exactly. -/
theorem zeroWeight_repeatedTraining_bound (k : Type*) [Field k] (q : ℕ) :
    wasserstein 1 bottleneck
      (sampleLaw k (PMF.pure false) 2 q)
      (sampleLaw k (empiricalPMF (fun _ : Fin 3 => false) (by omega)) 2 q) = 0 := by
  apply le_antisymm _ bot_le
  have h := wasserstein_sampleLaw_empiricalPMF_le k (PMF.pure false)
    (fun _ : Fin 3 => false) (by omega) 1 twoPoint_diameter (p := 1) le_rfl 2 q (by omega)
  simpa using h

/-- A singleton carrier permits diameter zero and a one-entry training tuple. -/
theorem singleton_zeroDiameter_bound (k : Type*) [Field k] (q : ℕ) :
    wasserstein 1 bottleneck
      (sampleLaw k (PMF.pure (() : Unit)) 2 q)
      (sampleLaw k (empiricalPMF (fun _ : Fin 1 => ()) (by omega)) 2 q) = 0 := by
  apply le_antisymm _ bot_le
  have h := wasserstein_sampleLaw_empiricalPMF_le k (PMF.pure (() : Unit))
    (fun _ : Fin 1 => ()) (by omega) 0 (by intro x y; simp) (p := 1) le_rfl 2 q (by omega)
  simpa using h

end TDA.Persistence.RipsSamplingEmpiricalExamples
