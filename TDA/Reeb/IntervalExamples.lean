import TDA.Reeb.Interval
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic.NormNum

/-!
# Real open interval and thickening fixtures

Regression fixtures for `TDA.Reeb.OpenInterval`:

* the bounded endpoint formula needs `a < b`: the encoded empty interval `(1, 0)` thickens to
  `∅`, while moving its endpoints by `1` would give the nonempty `(0, 1)`;
* two disjoint intervals whose `1`-thickenings overlap;
* the thin category, the meet and an overlap map `I ⊓ J ⟶ I`;
* the composition order of `thickenCompIso`: precomposing a functor `F` with `thickenFunctor δ`
  and then with `thickenFunctor ε` is definitionally precomposition with
  `thickenFunctor ε ⋙ thickenFunctor δ`.
-/

open Set CategoryTheory
open scoped NNReal Pointwise

namespace TDA.Reeb.Examples

open OpenInterval

/-- Regression: the endpoint formula needs `a < b`. The encoded empty interval `(1, 0)`
thickens to `∅`, while blindly moving its endpoints by `1` would give `(0, 1) ≠ ∅`. -/
example : thicken 1 (ioo 1 0) = ⊥ ∧ ioo (1 - 1) (0 + 1) ≠ ⊥ := by
  refine ⟨?_, ?_⟩
  · have h : ioo 1 0 = ⊥ := by
      ext x
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, coe_ioo, coe_bot]
      simp only [mem_Ioo, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h; linarith
    rw [h, thicken_bot]
  · intro h
    have h' : (1 / 2 : ℝ) ∈ (ioo (1 - 1) (0 + 1) : Set ℝ) := by
      rw [coe_ioo]; constructor <;> norm_num
    rw [h, coe_bot] at h'
    exact h'

/-- Regression: disjoint intervals can have overlapping thickenings. -/
example : Disjoint (Ioo (0 : ℝ) 1) (Ioo 2 3) ∧
    ((thicken 1 (ioo 0 1) : Set ℝ) ∩ thicken 1 (ioo 2 3)).Nonempty := by
  refine ⟨Set.disjoint_left.2 fun x h₁ h₂ => by linarith [h₁.2, h₂.1], ?_⟩
  rw [thicken_ioo (by norm_num : (0 : ℝ) < 1), thicken_ioo (by norm_num : (2 : ℝ) < 3)]
  refine ⟨3 / 2, ?_, ?_⟩ <;> simp only [coe_ioo, mem_Ioo, NNReal.coe_one] <;> norm_num

example : SmallCategory OpenInterval := inferInstance
example : SemilatticeInf OpenInterval := inferInstance
example (I J : OpenInterval) : I ⊓ J ⟶ I := homOfLE inf_le_left

/-- `S_ε (S_δ F) = (T_ε ⋙ T_δ) ⋙ F` definitionally, matching `thickenCompIso ε δ`. -/
example (F : OpenInterval ⥤ Type) (ε δ : ℝ≥0) :
    thickenFunctor ε ⋙ (thickenFunctor δ ⋙ F) = (thickenFunctor ε ⋙ thickenFunctor δ) ⋙ F :=
  rfl

end TDA.Reeb.Examples
