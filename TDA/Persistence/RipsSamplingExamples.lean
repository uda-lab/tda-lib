import TDA.Persistence.RipsSampling
import Mathlib.Data.ZMod.Basic

/-! Concrete atomic examples of sampled Rips laws and the vanishing-mass input. -/

noncomputable section
namespace TDA.Persistence.RipsSamplingExamples

open TDA.Probability TDA.Persistence.Rips
open scoped ENNReal NNReal

/-- The two nonnegative masses are allowed to reach zero at either endpoint. -/
def twoPointWeights (ε : ℝ≥0) (hε : ε ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ((if b then ε else 1 - ε : ℝ≥0) : ℝ≥0∞)) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le hε]
    rfl)

/-- Points at distance one, with masses `1-ε` and `ε`. -/
def twoPointLaw (ε : ℝ≥0) (hε : ε ≤ 1) : PMF ℝ :=
  (twoPointWeights ε hε).map (fun b => if b then (1 : ℝ) else 0)

/-- The two-draw moment is `2ε(1-ε)` for every positive exponent. Thus the
whole-support diagram cannot replace the sampled diagram law in a GW estimate. -/
theorem twoPoint_gromovWasserstein_singleton (ε : ℝ≥0) (hε : ε ≤ 1)
    {p : ℝ} (hp : 0 < p) :
    gromovWasserstein p (twoPointLaw ε hε) (PMF.pure (() : Unit)) =
      (2 : ℝ≥0∞)⁻¹ * (2 * (ε : ℝ≥0∞) * ((1 - ε : ℝ≥0) : ℝ≥0∞)) ^ p⁻¹ := by
  rw [gromovWasserstein_of_subsingleton]
  simp only [twoPointLaw, expectation_map]
  congr 2
  simp [expectation, tsum_fintype, Fintype.sum_bool, twoPointWeights, PMF.ofFintype_apply,
    Real.dist_eq, ENNReal.zero_rpow_of_pos hp, mul_comm, mul_left_comm, mul_assoc]
  ring

/-- The sharp law theorem applies to this weighted nonuniform input, with a
one-point target, in positive degree and with iid replacement. -/
theorem weighted_twoPoint_sampleLaw_bound (ε : ℝ≥0) (hε : ε ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) (n degree : ℕ) (hn : 2 ≤ n) :
    wasserstein p bottleneck
      (sampleLaw (ZMod 2) (twoPointLaw ε hε) n (degree + 1))
      (sampleLaw (ZMod 2) (PMF.pure (() : Unit)) n (degree + 1)) ≤
      (n.choose 2 : ℝ≥0∞) ^ p⁻¹ *
        (2 * gromovWasserstein p (twoPointLaw ε hε)
          (PMF.pure (() : Unit))) :=
  wasserstein_sampleLaw_le_gromovWasserstein (ZMod 2)
    (twoPointLaw ε hε) (PMF.pure (() : Unit)) hp n degree hn

end TDA.Persistence.RipsSamplingExamples
