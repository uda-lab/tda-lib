import TDA.Persistence.Reduction.Pivot
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Executable pivot and cancellation fixtures

These are small executable regression examples for the generic results in `Pivot.lean`.
Each evaluation is paired with a separately elaborated proposition proving the corresponding
result; the printed output is not used as proof evidence. Finite fixtures use kernel-checked
`decide`, and every private fixture theorem has a separate `#print axioms` record below.
-/

namespace TDA.Persistence.Reduction.Examples

/-! ### Empty and zero vectors -/

private theorem emptyVector_pivot :
    columnPivot (fun _ : Fin 0 => (0 : ℚ)) = none := by
  exact columnPivot_zero

private theorem emptyVector_height :
    pivotHeight (columnPivot (fun _ : Fin 0 => (0 : ℚ))) = 0 := by
  rw [emptyVector_pivot]
  rfl

#eval columnPivot (fun _ : Fin 0 => (0 : ℚ))
#eval pivotHeight (columnPivot (fun _ : Fin 0 => (0 : ℚ)))
#eval columnPivot (fun _ : Fin 3 => (0 : ℚ))

/-! ### A genuine pivot at row zero -/

private def rowZeroVector : Fin 1 → ℚ := ![7]

private theorem rowZeroVector_pivot : columnPivot rowZeroVector = some 0 := by
  decide

private theorem rowZeroVector_height :
    pivotHeight (columnPivot rowZeroVector) = 1 := by
  rw [rowZeroVector_pivot]
  rfl

#eval columnPivot rowZeroVector
#eval pivotHeight (columnPivot rowZeroVector)

/-! ### Rational cancellation to zero -/

private def qSourceZero : Fin 2 → ℚ := ![2, 0]
private def qTargetZero : Fin 2 → ℚ := ![3, 0]

private theorem qSourceZero_pivot : columnPivot qSourceZero = some 0 := by
  decide

private theorem qTargetZero_pivot : columnPivot qTargetZero = some 0 := by
  decide

private theorem qZero_cancel : cancelColumn qSourceZero qTargetZero 0 = 0 := by
  ext r
  fin_cases r <;> norm_num [cancelColumn, qSourceZero, qTargetZero]

private theorem qZero_height_decrease :
    pivotHeight (columnPivot (cancelColumn qSourceZero qTargetZero 0)) <
      pivotHeight (columnPivot qTargetZero) := by
  exact pivotHeight_cancelColumn_lt qSourceZero qTargetZero 0
    qSourceZero_pivot qTargetZero_pivot

private theorem qZero_coefficient : qTargetZero 0 / qSourceZero 0 = (3 / 2 : ℚ) := by
  norm_num [qSourceZero, qTargetZero]

private theorem qZero_transvection_coefficient :
    -(qTargetZero 0 / qSourceZero 0) = -(3 / 2 : ℚ) := by
  rw [qZero_coefficient]

#eval qTargetZero 0 / qSourceZero 0
#eval -(qTargetZero 0 / qSourceZero 0)
#eval List.ofFn (cancelColumn qSourceZero qTargetZero 0)
#eval pivotHeight (columnPivot qTargetZero)
#eval pivotHeight (columnPivot (cancelColumn qSourceZero qTargetZero 0))

/-! ### Rational cancellation with a surviving lower pivot -/

private def qSourceLower : Fin 2 → ℚ := ![1, 2]
private def qTargetLower : Fin 2 → ℚ := ![4, 6]

private theorem qSourceLower_pivot : columnPivot qSourceLower = some 1 := by
  decide

private theorem qTargetLower_pivot : columnPivot qTargetLower = some 1 := by
  decide

private theorem qLower_result :
    cancelColumn qSourceLower qTargetLower 1 = ![1, 0] := by
  ext r
  fin_cases r <;> norm_num [cancelColumn, qSourceLower, qTargetLower]

private theorem qLower_height_decrease :
    pivotHeight (columnPivot (cancelColumn qSourceLower qTargetLower 1)) = 1 ∧
      pivotHeight (columnPivot qTargetLower) = 2 := by
  constructor
  · rw [qLower_result]
    decide
  · rw [qTargetLower_pivot]
    rfl

#eval qTargetLower 1 / qSourceLower 1
#eval List.ofFn (cancelColumn qSourceLower qTargetLower 1)
#eval pivotHeight (columnPivot qTargetLower)
#eval pivotHeight (columnPivot (cancelColumn qSourceLower qTargetLower 1))

/-! ### `F₂` cancellation and right-transvection column behavior -/

private instance f2PrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def f2Source : Fin 2 → ZMod 2 := ![1, 0]
private def f2Target : Fin 2 → ZMod 2 := ![1, 0]

private theorem f2Source_pivot : columnPivot f2Source = some 0 := by
  decide

private theorem f2Target_pivot : columnPivot f2Target = some 0 := by
  decide

private theorem f2_cancel : cancelColumn f2Source f2Target 0 = 0 := by
  ext r
  fin_cases r <;> norm_num [cancelColumn, f2Source, f2Target]

private def f2Matrix : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun r c =>
  if r = 0 ∧ (c = 0 ∨ c = 1) then 1 else if r = 1 ∧ c = 2 then 1 else 0

private def f2TransvectionCoefficient : ZMod 2 :=
  -(f2Matrix 0 1 / f2Matrix 0 0)

private def f2TransvectionMatrix : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  f2Matrix * Matrix.transvection 0 1 f2TransvectionCoefficient

private theorem f2Matrix_source_pivot : columnPivot (f2Matrix.col 0) = some 0 := by
  decide

private theorem f2Matrix_target_pivot : columnPivot (f2Matrix.col 1) = some 0 := by
  decide

private theorem f2TransvectionCoefficient_eq_one :
    f2TransvectionCoefficient = 1 := by
  norm_num [f2TransvectionCoefficient, f2Matrix]

private theorem f2_transvection_source_unchanged :
    f2TransvectionMatrix.col 0 = f2Matrix.col 0 := by
  exact col_mul_transvection_of_ne f2Matrix 0 1 0 f2TransvectionCoefficient (by decide)

private theorem f2_transvection_unrelated_column_unchanged :
    f2TransvectionMatrix.col 2 = f2Matrix.col 2 := by
  exact col_mul_transvection_of_ne f2Matrix 0 1 2 f2TransvectionCoefficient (by decide)

private theorem f2_transvection_target_zero : f2TransvectionMatrix.col 1 = 0 := by
  calc
    f2TransvectionMatrix.col 1 =
        f2Matrix.col 1 + f2TransvectionCoefficient • f2Matrix.col 0 :=
      col_mul_transvection f2Matrix 0 1 f2TransvectionCoefficient
    _ = 0 := by
      rw [f2TransvectionCoefficient_eq_one]
      ext r
      fin_cases r
      · norm_num [f2Matrix]
        exact ZMod.natCast_self 2
      · simp [f2Matrix]
      · simp [f2Matrix]

private theorem f2_transvection_height_decrease :
    pivotHeight (columnPivot (f2TransvectionMatrix.col 1)) = 0 ∧
      pivotHeight (columnPivot (f2Matrix.col 1)) = 1 := by
  constructor
  · rw [f2_transvection_target_zero]
    rw [columnPivot_zero]
    rfl
  · rw [f2Matrix_target_pivot]
    rfl

#eval List.ofFn f2Source
#eval List.ofFn (cancelColumn f2Source f2Target 0)
#eval f2TransvectionCoefficient
#eval List.ofFn (f2TransvectionMatrix.col 0)
#eval List.ofFn (f2TransvectionMatrix.col 1)
#eval List.ofFn (f2TransvectionMatrix.col 2)

/-! ### Private fixture trust audit

These records keep the fixture proof footprint visible even though the examples are private and
therefore intentionally absent from the public theorem-pin coverage list.
-/
#print axioms emptyVector_pivot
#print axioms emptyVector_height
#print axioms rowZeroVector_pivot
#print axioms rowZeroVector_height
#print axioms qSourceZero_pivot
#print axioms qTargetZero_pivot
#print axioms qZero_cancel
#print axioms qZero_height_decrease
#print axioms qZero_coefficient
#print axioms qZero_transvection_coefficient
#print axioms qSourceLower_pivot
#print axioms qTargetLower_pivot
#print axioms qLower_result
#print axioms qLower_height_decrease
#print axioms f2PrimeFact
#print axioms f2Source_pivot
#print axioms f2Target_pivot
#print axioms f2_cancel
#print axioms f2Matrix_source_pivot
#print axioms f2Matrix_target_pivot
#print axioms f2TransvectionCoefficient_eq_one
#print axioms f2_transvection_source_unchanged
#print axioms f2_transvection_unrelated_column_unchanged
#print axioms f2_transvection_target_zero
#print axioms f2_transvection_height_decrease

end TDA.Persistence.Reduction.Examples
