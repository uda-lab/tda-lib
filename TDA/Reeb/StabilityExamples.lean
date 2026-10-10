import TDA.Reeb.Stability
import TDA.Reeb.PerturbationExamples

/-!
# Supremum-distance stability fixtures

Regression fixtures for `TDA.Reeb.interleavingDistance_intervalComponents_le_edist`:

* an empty domain, where both sides are `0`, derived through the stability theorem;
* the unbounded difference of `id` and `2 · id` on `ℝ`, where the supremum distance is `⊤`, the
  theorem is the trivial bound, and no finite pointwise bound exists;
* a constant height translation by `c`, bounded by `|c|` on every domain, at supremum distance
  exactly `|c|` on a nonempty domain, with equality of both sides on a one-point domain; no
  optimality on other domains is claimed;
* equal heights, where both sides are `0`.

The translation `heightShift` and the sharpness fixture `isEmpty_interleaving_const` are reused
from the uniform perturbation fixtures.
-/

open Set CategoryTheory
open scoped NNReal ENNReal UniformConvergence

namespace TDA.Reeb.Examples

open TDA.Reeb

/-- Empty domain: both sides are `0`. -/
theorem stability_of_isEmpty {X : Type*} [TopologicalSpace X] [IsEmpty X] (f g : C(X, ℝ)) :
    interleavingDistance (intervalComponents f) (intervalComponents g) = 0 ∧
      edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) = 0 := by
  have he : edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g) = 0 := by
    rw [edist_uniformFun_ofFun_eq_iSup, iSup_of_empty, bot_eq_zero]
  exact ⟨le_antisymm ((interleavingDistance_intervalComponents_le_edist f g).trans_eq he)
    zero_le, he⟩

/-- `x ↦ 2 x` on `ℝ`. -/
def twiceId : C(ℝ, ℝ) := ⟨fun x => 2 * x, by fun_prop⟩

/-- Unbounded difference: for `f = id` and `g = 2 · id` on `ℝ` the right side is `⊤`, so no
finite pointwise bound exists and the literal theorem is the trivial bound. -/
theorem edist_id_twiceId_eq_top :
    edist (UniformFun.ofFun ⇑(ContinuousMap.id ℝ)) (UniformFun.ofFun ⇑twiceId) = ⊤ := by
  rw [edist_uniformFun_ofFun_eq_iSup]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => le_iSup_of_le (r : ℝ) ?_
  have h : |(ContinuousMap.id ℝ) (r : ℝ) - twiceId (r : ℝ)| = r := by
    change |(r : ℝ) - 2 * r| = r
    rw [show (r : ℝ) - 2 * r = -r by ring, abs_neg, abs_of_nonneg r.coe_nonneg]
  rw [h, ENNReal.ofReal_coe_nnreal]

example : interleavingDistance (intervalComponents (ContinuousMap.id ℝ))
    (intervalComponents twiceId) ≤ ⊤ :=
  (interleavingDistance_intervalComponents_le_edist _ _).trans_eq edist_id_twiceId_eq_top

example (ε : ℝ≥0) : ¬ ∀ x, |(ContinuousMap.id ℝ) x - twiceId x| ≤ ε := fun h => by
  have := edist_uniformFun_ofFun_le_coe_iff.2 h
  rw [edist_id_twiceId_eq_top] at this
  exact ENNReal.coe_ne_top (top_le_iff.1 this)

/-- Constant translation: the literal bound gives `d(C_f, C_{f+c}) ≤ |c|` on every `X`. No
optimality is claimed; on an empty `X` the left side is `0`. -/
theorem interleavingDistance_heightShift_le {X : Type*} [TopologicalSpace X] (f : C(X, ℝ))
    (c : ℝ) :
    interleavingDistance (intervalComponents f) (intervalComponents (heightShift f c)) ≤
      Real.nnabs c :=
  (interleavingDistance_intervalComponents_le_edist f (heightShift f c)).trans
    (edist_uniformFun_ofFun_le_coe_iff.2 (abs_sub_heightShift_le f c))

/-- On a nonempty domain the translation distance is exactly `|c|`. -/
theorem edist_heightShift {X : Type*} [TopologicalSpace X] [Nonempty X] (f : C(X, ℝ))
    (c : ℝ) :
    edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑(heightShift f c)) = Real.nnabs c := by
  have h : ∀ x, ENNReal.ofReal |f x - heightShift f c x| = Real.nnabs c := fun x => by
    change ENNReal.ofReal |f x - (f x + c)| = Real.nnabs c
    rw [sub_add_cancel_left, abs_neg, ← Real.coe_nnabs, ENNReal.ofReal_coe_nnreal]
  rw [edist_uniformFun_ofFun_eq_iSup]
  simp only [h, ciSup_const]

/-- Attainment on a point: for the one-point space the literal bound is an equality, with both
sides `|c|`, by the existing sharpness fixture `isEmpty_interleaving_const`. -/
theorem stability_const_eq (c : ℝ) :
    interleavingDistance (intervalComponents (ContinuousMap.const Unit (0 : ℝ)))
        (intervalComponents (ContinuousMap.const Unit c)) =
      edist (UniformFun.ofFun ⇑(ContinuousMap.const Unit (0 : ℝ)))
        (UniformFun.ofFun ⇑(ContinuousMap.const Unit c)) ∧
      edist (UniformFun.ofFun ⇑(ContinuousMap.const Unit (0 : ℝ)))
        (UniformFun.ofFun ⇑(ContinuousMap.const Unit c)) = Real.nnabs c := by
  have he : edist (UniformFun.ofFun ⇑(ContinuousMap.const Unit (0 : ℝ)))
      (UniformFun.ofFun ⇑(ContinuousMap.const Unit c)) = Real.nnabs c := by
    rw [edist_uniformFun_ofFun_eq_iSup, ciSup_unique]
    change ENNReal.ofReal |0 - c| = Real.nnabs c
    rw [zero_sub, abs_neg, ← Real.coe_nnabs, ENNReal.ofReal_coe_nnreal]
  refine ⟨le_antisymm (interleavingDistance_intervalComponents_le_edist _ _) ?_, he⟩
  rw [he]
  refine le_interleavingDistance_iff.2 fun ε ⟨i⟩ => ?_
  by_contra hlt
  have hε : (ε : ℝ) < |c| := by
    rw [← Real.coe_nnabs]
    exact_mod_cast not_le.1 hlt
  exact (isEmpty_interleaving_const hε).false i

/-- Equal heights: both sides are `0`. -/
theorem stability_self {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) :
    interleavingDistance (intervalComponents f) (intervalComponents f) = 0 ∧
      edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑f) = 0 :=
  ⟨le_antisymm ((interleavingDistance_intervalComponents_le_edist f f).trans_eq (edist_self _))
    zero_le, edist_self _⟩

end TDA.Reeb.Examples
