import TDA.Reeb.IntervalTranslation

/-!
# Translation of interval precosheaves: fixtures

Z1. Translation by `0`: every precosheaf is at distance `0` from its translate by `0`, and for a
height bounded below on a nonempty space the exact translation distance at `c = 0` is `0`.

U1. The identity height of `ℝ` is not bounded below. Its interval components and those of
`id + 1` are isomorphic, through the homeomorphism `x ↦ x + 1` of `ℝ`, so they are at distance
`0` although `‖1‖₊ = 1`: the lower bound of the exact translation distance needs `BddBelow`.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb.Examples.IntervalTranslation

open TDA.Reeb TDA.Reeb.OpenInterval

/-! ## Z1. Translation by zero -/

/-- Translation by `0` gives distance `0`, for a general precosheaf and in the exact
height-translation formula. -/
theorem zero_translation {C : Type*} [Category C] (F : OpenInterval ⥤ C) {X : Type*}
    [TopologicalSpace X] [Nonempty X] (f : C(X, ℝ)) (hf : BddBelow (range f)) :
    interleavingDistance F (translatePre 0 F) = 0 ∧
      interleavingDistance (intervalComponents f)
        (intervalComponents (f + ContinuousMap.const X 0)) = 0 := by
  refine ⟨interleavingDistance_eq_zero_of_iso (translatePreZeroIso F).symm, ?_⟩
  rw [interleavingDistance_intervalComponents_add_const f hf 0, nnnorm_zero, ENNReal.coe_zero]

/-! ## U1. A height that is not bounded below -/

/-- Translation by `1` of the identity height of `ℝ` is undone by the homeomorphism `x ↦ x + 1`. -/
def idAddOneIso :
    componentFunctor (ContinuousMap.id ℝ + ContinuousMap.const ℝ 1) ≅
      componentFunctor (ContinuousMap.id ℝ) where
  hom := componentNatTrans ⟨(· + 1), by fun_prop⟩ fun _ => rfl
  inv := componentNatTrans ⟨(· - 1), by fun_prop⟩ fun x => sub_add_cancel x 1
  hom_inv_id := by
    ext U p
    induction p using ZerothHomotopy.rec with
    | mk x => exact congrArg ZerothHomotopy.mk (Subtype.ext (add_sub_cancel_right x.1 1))
  inv_hom_id := by
    ext U p
    induction p using ZerothHomotopy.rec with
    | mk x => exact congrArg ZerothHomotopy.mk (Subtype.ext (sub_add_cancel x.1 1))

/-- The identity height of `ℝ` is not bounded below, and its translate by `1` is at
interleaving distance `0` from it although `‖1‖₊ = 1`. -/
theorem id_translation_distance :
    ¬ BddBelow (range (ContinuousMap.id ℝ)) ∧ ‖(1 : ℝ)‖₊ = 1 ∧
      interleavingDistance (intervalComponents (ContinuousMap.id ℝ))
        (intervalComponents (ContinuousMap.id ℝ + ContinuousMap.const ℝ 1)) = 0 := by
  refine ⟨?_, NNReal.eq (by simp [Real.norm_eq_abs]), interleavingDistance_eq_zero_of_iso
    (Functor.isoWhiskerLeft toOpensFunctor idAddOneIso).symm⟩
  rw [ContinuousMap.coe_id, range_id]
  exact not_bddBelow_univ

end TDA.Reeb.Examples.IntervalTranslation
