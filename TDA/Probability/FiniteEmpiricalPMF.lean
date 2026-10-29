import TDA.Probability.FiniteSampling
import Mathlib.Probability.Distributions.Uniform

/-!
# Empirical probability mass functions of finite training tuples

Uniform choice of an observation index retains occurrence counts, including
repeated observations. No measurable-space choice or metric is needed.
-/

noncomputable section

universe u

namespace TDA.Probability

open scoped ENNReal Classical

variable {X : Type u} {m : ℕ}

/-- The empirical law of a nonempty training tuple, retaining observation
multiplicities through uniform sampling of its indices. -/
def empiricalPMF (u : Fin m → X) (hm : 1 ≤ m) : PMF X := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  exact (PMF.uniformOfFintype (Fin m)).map u

/-- Every atom has its occurrence count divided by the training size. -/
theorem empiricalPMF_apply (u : Fin m → X) (hm : 1 ≤ m) (x : X) :
    empiricalPMF u hm x =
      ((Finset.univ.filter fun i => u i = x).card : ℝ≥0∞) / m := by
  classical
  simp only [empiricalPMF, PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply,
    Fintype.card_fin, eq_comm]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- A constant training tuple gives a point mass, regardless of repetition count. -/
@[simp] theorem empiricalPMF_const (x : X) (hm : 1 ≤ m) :
    empiricalPMF (fun _ : Fin m => x) hm = PMF.pure x := by
  unfold empiricalPMF
  exact PMF.map_const _ x

end TDA.Probability
