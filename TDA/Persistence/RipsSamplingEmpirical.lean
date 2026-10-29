import TDA.Persistence.RipsSampling
import TDA.Probability.FiniteGromovWassersteinTV
import TDA.Probability.FiniteEmpiricalPMF

/-!
# Deterministic empirical approximation of sampled Rips diagram laws

A training tuple defines a probability law by choosing one of its indices
uniformly, so repeated observations retain their occurrence weights. The
resampling size is independent of the training size. The resulting bound
compares probability laws of whole diagrams, including full ordinary H₀.
-/

noncomputable section

universe u w

namespace TDA.Persistence.Rips

open TDA.Probability
open scoped ENNReal NNReal

variable {X : Type u} [Fintype X] [MetricSpace X]

/-- Deterministic total variation control of finite sampled Rips diagram laws,
for every degree, including full ordinary H₀ and essential bars. -/
theorem wasserstein_sampleLaw_le_finiteTotalVariation (k : Type w) [Field k]
    (μ ν : PMF X) (D : ℝ≥0) (hD : ∀ x y : X, dist x y ≤ (D : ℝ))
    {p : ℝ} (hp : 1 ≤ p) (s q : ℕ) (hs : 2 ≤ s) :
    wasserstein p bottleneck (sampleLaw k μ s q) (sampleLaw k ν s q) ≤
      (D : ℝ≥0∞) * (s.choose 2 : ℝ≥0∞) ^ p⁻¹ *
        (2 * finiteTotalVariation μ ν) ^ p⁻¹ := by
  calc
    _ ≤ (s.choose 2 : ℝ≥0∞) ^ p⁻¹ * (2 * gromovWasserstein p μ ν) :=
      wasserstein_sampleLaw_le_gromovWasserstein_allDegrees k μ ν hp s q hs
    _ ≤ (s.choose 2 : ℝ≥0∞) ^ p⁻¹ *
        ((D : ℝ≥0∞) * (2 * finiteTotalVariation μ ν) ^ p⁻¹) := by
      exact mul_le_mul_right (two_mul_gromovWasserstein_le_finiteTotalVariation μ ν D hD
        (lt_of_lt_of_le zero_lt_one hp)) _
    _ = _ := by ring

/-- A training tuple controls the law obtained by iid resampling its empirical
PMF. This is deterministic and makes no concentration assertion about the
training tuple. -/
theorem wasserstein_sampleLaw_empiricalPMF_le (k : Type w) [Field k]
    (μ : PMF X) {m : ℕ} (u : Fin m → X) (hm : 1 ≤ m)
    (D : ℝ≥0) (hD : ∀ x y : X, dist x y ≤ (D : ℝ))
    {p : ℝ} (hp : 1 ≤ p) (s q : ℕ) (hs : 2 ≤ s) :
    wasserstein p bottleneck (sampleLaw k μ s q) (sampleLaw k (empiricalPMF u hm) s q) ≤
      (D : ℝ≥0∞) * (s.choose 2 : ℝ≥0∞) ^ p⁻¹ *
        (2 * finiteTotalVariation μ (empiricalPMF u hm)) ^ p⁻¹ :=
  wasserstein_sampleLaw_le_finiteTotalVariation k μ (empiricalPMF u hm) D hD hp s q hs

end TDA.Persistence.Rips
