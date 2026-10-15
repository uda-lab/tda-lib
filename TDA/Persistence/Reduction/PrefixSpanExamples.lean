import TDA.Persistence.Reduction.PrefixSpan
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Prefix-span examples

These private fixtures check the general prefix-preservation theorem over empty, rational, and
characteristic-two examples. Matrix and vector evaluations are paired with kernel-checked
theorems. Prefix spans are never evaluated as Booleans.
-/

namespace TDA.Persistence.Reduction.Examples

/-! ### Empty index sets, zero matrices, and dimension one -/

private theorem emptyMatrix_prefixSpan (M : Matrix (Fin 0) (Fin 0) ℚ) (t : ℕ) :
    prefixSpan M t = ⊥ := by
  have h : (Set.range (fun q : {q : Fin 0 // q.val < t} => M.col q.1)) = ∅ := by
    ext v
    constructor
    · rintro ⟨q, _⟩
      exact Fin.elim0 q.1
    · simp
  simp [prefixSpan, h]

private theorem zeroMatrix_prefixSpan {m : ℕ} {k : Type*} [Field k]
    (t : ℕ) : prefixSpan (0 : Matrix (Fin m) (Fin m) k) t = ⊥ := by
  apply le_antisymm
  · unfold prefixSpan
    apply Submodule.span_le.mpr
    rintro x ⟨q, rfl⟩
    change ((0 : Fin m → k) ∈ (⊥ : Submodule k (Fin m → k)))
    exact zero_mem _
  · exact bot_le

private theorem dimensionOne_empty_prefix (M : Matrix (Fin 1) (Fin 1) ℚ) :
    prefixSpan M 0 = ⊥ :=
  prefixSpan_zero M

private theorem dimensionOne_full_prefix (M : Matrix (Fin 1) (Fin 1) ℚ) :
    prefixSpan M 1 = Submodule.span ℚ (Set.range M.col) := by
  exact prefixSpan_eq_full M 1 (by decide)

/-! ### Rational three-column transvection -/

private def rationalMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  fun r c => if r = 0 ∧ c = 0 then 2 else
    if r = 0 ∧ c = 1 then 3 else if r = 1 ∧ c = 2 then 1 else 0

private def rationalCoefficient : ℚ :=
  -(rationalMatrix 0 1 / rationalMatrix 0 0)

private def rationalStep : Matrix (Fin 3) (Fin 3) ℚ :=
  rationalMatrix * Matrix.transvection 0 1 rationalCoefficient

private theorem rationalCoefficient_value : rationalCoefficient = -(3 / 2 : ℚ) := by
  norm_num [rationalCoefficient, rationalMatrix, Fin.ext_iff]

private theorem rational_source_column : rationalStep.col 0 = ![2, 0, 0] := by
  rw [show rationalStep.col 0 = rationalMatrix.col 0 from
    col_mul_transvection_of_ne rationalMatrix 0 1 0 rationalCoefficient (by decide)]
  ext r
  fin_cases r <;> norm_num [rationalMatrix, Fin.ext_iff]

private theorem rational_target_column : rationalStep.col 1 = ![0, 0, 0] := by
  rw [show rationalStep.col 1 =
      rationalMatrix.col 1 + rationalCoefficient • rationalMatrix.col 0 from
    col_mul_transvection rationalMatrix 0 1 rationalCoefficient]
  rw [rationalCoefficient_value]
  ext r
  fin_cases r <;> norm_num [rationalMatrix, Fin.ext_iff, smul_eq_mul]

private theorem rational_unrelated_column : rationalStep.col 2 = ![0, 1, 0] := by
  rw [show rationalStep.col 2 = rationalMatrix.col 2 from
    col_mul_transvection_of_ne rationalMatrix 0 1 2 rationalCoefficient (by decide)]
  ext r
  fin_cases r <;> norm_num [rationalMatrix, Fin.ext_iff]

private theorem rational_prefix_zero :
    prefixSpan rationalStep 0 = prefixSpan rationalMatrix 0 := by
  exact prefixSpan_mul_transvection rationalMatrix 0 1 rationalCoefficient (by decide) 0

private theorem rational_prefix_one :
    prefixSpan rationalStep 1 = prefixSpan rationalMatrix 1 := by
  exact prefixSpan_mul_transvection rationalMatrix 0 1 rationalCoefficient (by decide) 1

private theorem rational_prefix_two :
    prefixSpan rationalStep 2 = prefixSpan rationalMatrix 2 := by
  exact prefixSpan_mul_transvection rationalMatrix 0 1 rationalCoefficient (by decide) 2

private theorem rational_prefix_three :
    prefixSpan rationalStep 3 = prefixSpan rationalMatrix 3 := by
  exact prefixSpan_mul_transvection rationalMatrix 0 1 rationalCoefficient (by decide) 3

private theorem rational_prefix_four :
    prefixSpan rationalStep 4 = prefixSpan rationalMatrix 4 := by
  exact prefixSpan_mul_transvection rationalMatrix 0 1 rationalCoefficient (by decide) 4

#eval rationalCoefficient
#eval List.ofFn (rationalStep.col 0)
#eval List.ofFn (rationalStep.col 1)
#eval List.ofFn (rationalStep.col 2)

/-! ### Rational cancellation with a surviving lower pivot -/

private def lowerPivotMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  fun r c => if r = 0 ∧ c = 0 then 1 else
    if r = 0 ∧ c = 1 then 4 else
    if r = 1 ∧ c = 0 then 2 else
    if r = 1 ∧ c = 1 then 6 else
    if r = 2 ∧ c = 2 then 1 else 0

private def lowerPivotCoefficient : ℚ :=
  -(lowerPivotMatrix 1 1 / lowerPivotMatrix 1 0)

private def lowerPivotStep : Matrix (Fin 3) (Fin 3) ℚ :=
  lowerPivotMatrix * Matrix.transvection 0 1 lowerPivotCoefficient

private theorem lowerPivotCoefficient_value : lowerPivotCoefficient = -3 := by
  norm_num [lowerPivotCoefficient, lowerPivotMatrix, Fin.ext_iff]

private theorem lowerPivot_source_column : lowerPivotStep.col 0 = ![1, 2, 0] := by
  rw [show lowerPivotStep.col 0 = lowerPivotMatrix.col 0 from
    col_mul_transvection_of_ne lowerPivotMatrix 0 1 0 lowerPivotCoefficient (by decide)]
  ext r
  fin_cases r <;> norm_num [lowerPivotMatrix, Fin.ext_iff]

private theorem lowerPivot_target_column : lowerPivotStep.col 1 = ![1, 0, 0] := by
  rw [show lowerPivotStep.col 1 =
      lowerPivotMatrix.col 1 + lowerPivotCoefficient • lowerPivotMatrix.col 0 from
    col_mul_transvection lowerPivotMatrix 0 1 lowerPivotCoefficient]
  rw [lowerPivotCoefficient_value]
  ext r
  fin_cases r <;> norm_num [lowerPivotMatrix, Fin.ext_iff, smul_eq_mul]

private theorem lowerPivot_unrelated_column : lowerPivotStep.col 2 = ![0, 0, 1] := by
  rw [show lowerPivotStep.col 2 = lowerPivotMatrix.col 2 from
    col_mul_transvection_of_ne lowerPivotMatrix 0 1 2 lowerPivotCoefficient (by decide)]
  ext r
  fin_cases r <;> norm_num [lowerPivotMatrix, Fin.ext_iff]

private theorem lowerPivot_source_pivot :
    columnPivot (lowerPivotMatrix.col 0) = some (1 : Fin 3) := by
  decide

private theorem lowerPivot_target_pivot :
    columnPivot (lowerPivotMatrix.col 1) = some (1 : Fin 3) := by
  decide

private theorem lowerPivot_height_decreases :
    pivotHeight (columnPivot (lowerPivotStep.col 1)) <
      pivotHeight (columnPivot (lowerPivotMatrix.col 1)) := by
  simpa [lowerPivotStep, lowerPivotCoefficient] using
    (pivotHeight_mul_transvection_lt lowerPivotMatrix 0 1 1 (by decide)
      lowerPivot_source_pivot lowerPivot_target_pivot)

private theorem lowerPivot_prefix_all (t : ℕ) :
    prefixSpan lowerPivotStep t = prefixSpan lowerPivotMatrix t := by
  unfold lowerPivotStep
  rw [lowerPivotCoefficient_value]
  exact prefixSpan_mul_transvection lowerPivotMatrix 0 1 (-3) (by decide) t

#eval lowerPivotCoefficient
#eval List.ofFn (lowerPivotStep.col 0)
#eval List.ofFn (lowerPivotStep.col 1)
#eval List.ofFn (lowerPivotStep.col 2)

/-! ### Characteristic-two example -/

private instance f2PrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def f2Matrix : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun r c =>
  if r = 0 ∧ (c = 0 ∨ c = 1) then 1 else if r = 1 ∧ c = 2 then 1 else 0

private def f2Coefficient : ZMod 2 := -(f2Matrix 0 1 / f2Matrix 0 0)

private def f2Step : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  f2Matrix * Matrix.transvection 0 1 f2Coefficient

private theorem f2Coefficient_value : f2Coefficient = 1 := by
  norm_num [f2Coefficient, f2Matrix, Fin.ext_iff]

private theorem f2_source_column : f2Step.col 0 = ![1, 0, 0] := by
  rw [show f2Step.col 0 = f2Matrix.col 0 from
    col_mul_transvection_of_ne f2Matrix 0 1 0 f2Coefficient (by decide)]
  ext r
  fin_cases r <;> norm_num [f2Matrix, Fin.ext_iff]

private theorem f2_target_column : f2Step.col 1 = ![0, 0, 0] := by
  rw [show f2Step.col 1 = f2Matrix.col 1 + f2Coefficient • f2Matrix.col 0 from
    col_mul_transvection f2Matrix 0 1 f2Coefficient]
  rw [f2Coefficient_value]
  ext r
  fin_cases r
  · norm_num [f2Matrix, Fin.ext_iff]
    exact ZMod.natCast_self 2
  · simp [f2Matrix, Fin.ext_iff]
  · simp [f2Matrix, Fin.ext_iff]

private theorem f2_unrelated_column : f2Step.col 2 = ![0, 1, 0] := by
  rw [show f2Step.col 2 = f2Matrix.col 2 from
    col_mul_transvection_of_ne f2Matrix 0 1 2 f2Coefficient (by decide)]
  ext r
  fin_cases r <;> norm_num [f2Matrix, Fin.ext_iff]

private theorem f2_prefix_all (t : ℕ) : prefixSpan f2Step t = prefixSpan f2Matrix t := by
  exact prefixSpan_mul_transvection f2Matrix 0 1 f2Coefficient (by decide) t

#eval f2Coefficient
#eval List.ofFn (f2Step.col 0)
#eval List.ofFn (f2Step.col 1)
#eval List.ofFn (f2Step.col 2)

/-! ### Zero coefficient, order sensitivity, and explicit trust records -/

private theorem zeroCoefficient_preserves_prefix {m : ℕ} {k : Type*} [Field k]
    (M : Matrix (Fin m) (Fin m) k) (i j : Fin m) (hij : i < j) (t : ℕ) :
    prefixSpan (M * Matrix.transvection i j (0 : k)) t = prefixSpan M t := by
  exact prefixSpan_mul_transvection M i j 0 hij t

private def reversedMatrix : Matrix (Fin 2) (Fin 2) ℚ := 1

private def reversedStep : Matrix (Fin 2) (Fin 2) ℚ :=
  reversedMatrix * Matrix.transvection 1 0 (1 : ℚ)

private def coordOne : (Fin 2 → ℚ) →ₗ[ℚ] ℚ where
  toFun v := v 1
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private theorem reversed_old_prefix_in_ker :
    prefixSpan reversedMatrix 1 ≤ LinearMap.ker coordOne := by
  unfold prefixSpan
  apply Submodule.span_le.mpr
  rintro v ⟨q, rfl⟩
  have hq : q.1 = 0 := Fin.ext (by omega)
  simp [coordOne, reversedMatrix, hq]

private theorem reversed_new_column_coordinate : coordOne (reversedStep.col 0) = 1 := by
  unfold reversedStep
  rw [col_mul_transvection]
  simp [coordOne, reversedMatrix]

private theorem reversed_order_negative_control :
    reversedStep.col 0 ∉ prefixSpan reversedMatrix 1 := by
  intro hmem
  have hzero := LinearMap.mem_ker.mp (reversed_old_prefix_in_ker hmem)
  rw [reversed_new_column_coordinate] at hzero
  norm_num at hzero

#eval List.ofFn (reversedStep.col 0)

/-! Every private fixture theorem and the auxiliary instance witness is audited here. -/
#print axioms emptyMatrix_prefixSpan
#print axioms zeroMatrix_prefixSpan
#print axioms dimensionOne_empty_prefix
#print axioms dimensionOne_full_prefix
#print axioms rationalMatrix
#print axioms rationalCoefficient
#print axioms rationalStep
#print axioms rationalCoefficient_value
#print axioms rational_source_column
#print axioms rational_target_column
#print axioms rational_unrelated_column
#print axioms rational_prefix_zero
#print axioms rational_prefix_one
#print axioms rational_prefix_two
#print axioms rational_prefix_three
#print axioms rational_prefix_four
#print axioms lowerPivotMatrix
#print axioms lowerPivotCoefficient
#print axioms lowerPivotStep
#print axioms lowerPivotCoefficient_value
#print axioms lowerPivot_source_column
#print axioms lowerPivot_target_column
#print axioms lowerPivot_unrelated_column
#print axioms lowerPivot_source_pivot
#print axioms lowerPivot_target_pivot
#print axioms lowerPivot_height_decreases
#print axioms lowerPivot_prefix_all
#print axioms f2PrimeFact
#print axioms f2Matrix
#print axioms f2Coefficient
#print axioms f2Step
#print axioms f2Coefficient_value
#print axioms f2_source_column
#print axioms f2_target_column
#print axioms f2_unrelated_column
#print axioms f2_prefix_all
#print axioms zeroCoefficient_preserves_prefix
#print axioms reversedMatrix
#print axioms reversedStep
#print axioms coordOne
#print axioms reversed_old_prefix_in_ker
#print axioms reversed_new_column_coordinate
#print axioms reversed_order_negative_control

end TDA.Persistence.Reduction.Examples
