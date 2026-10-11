import TDA.Persistence.Reduction.TraceCertificate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-! Concrete checks for the explicit inverse and its graded certificate. -/

namespace TDA.Persistence.Reduction.TraceCertificateExamples

private def rows {m : ℕ} {k : Type*} [Field k]
    (A : Matrix (Fin m) (Fin m) k) : List (List k) :=
  List.ofFn fun i => List.ofFn fun j => A i j

private def op {m : ℕ} {k : Type*} (i j : Fin m) (c : k) (h : i < j) :
    EarlierColumnOp m k := ⟨⟨i, j, ne_of_lt h, c⟩, h⟩

private theorem empty_zero_forward :
    traceChange ([] : List (EarlierColumnOp 0 ℚ)) = 1 := traceChange_nil
private theorem empty_zero_inverse :
    traceChangeInv ([] : List (EarlierColumnOp 0 ℚ)) = 1 := traceChangeInv_nil
private theorem empty_zero_certificate (degree : Fin 0 → ℕ) :
    TraceChangeCertificate degree
      (traceChange ([] : List (EarlierColumnOp 0 ℚ)))
      (traceChangeInv ([] : List (EarlierColumnOp 0 ℚ))) :=
  traceChange_certificate degree [] (by intro a ha; cases ha)
private theorem empty_one_forward :
    traceChange ([] : List (EarlierColumnOp 1 ℚ)) = 1 := traceChange_nil
private theorem empty_one_inverse :
    traceChangeInv ([] : List (EarlierColumnOp 1 ℚ)) = 1 := traceChangeInv_nil
private theorem empty_one_certificate (degree : Fin 1 → ℕ) :
    TraceChangeCertificate degree
      (traceChange ([] : List (EarlierColumnOp 1 ℚ)))
      (traceChangeInv ([] : List (EarlierColumnOp 1 ℚ))) :=
  traceChange_certificate degree [] (by intro a ha; cases ha)
private theorem empty_zero_rows :
    rows (traceChangeInv ([] : List (EarlierColumnOp 0 ℚ))) = [] := by
  simp [rows]
private theorem empty_one_rows :
    rows (traceChangeInv ([] : List (EarlierColumnOp 1 ℚ))) = [[1]] := by
  simp [rows, traceChangeInv_nil, Matrix.one_apply]

private def ratA : EarlierColumnOp 3 ℚ := op 0 1 2 (by decide)
private def ratB : EarlierColumnOp 3 ℚ := op 1 2 3 (by decide)
private def ratOps : List (EarlierColumnOp 3 ℚ) := [ratA, ratB]
private def ratWrong : List (EarlierColumnOp 3 ℚ) :=
  [inverseEarlierColumnOp ratA, inverseEarlierColumnOp ratB]

private theorem rat_forward_rows :
    rows (traceChange ratOps) = [[1, 2, 6], [0, 1, 3], [0, 0, 1]] := by
  simp [rows, ratOps, ratA, ratB, op, traceChange, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
    Matrix.single_apply, Matrix.one_apply]; norm_num
private theorem rat_inverse_rows :
    rows (traceChangeInv ratOps) = [[1, -2, 0], [0, 1, -3], [0, 0, 1]] := by
  simp [rows, ratOps, ratA, ratB, op, traceChangeInv, inverseTrace,
    inverseEarlierColumnOp, traceChange, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
    Matrix.single_apply, Matrix.one_apply]
private theorem rat_inverse_left :
    traceChange ratOps * traceChangeInv ratOps = 1 :=
  traceChange_mul_traceChangeInv ratOps
private theorem rat_inverse_right :
    traceChangeInv ratOps * traceChange ratOps = 1 :=
  traceChangeInv_mul_traceChange ratOps
private theorem rat_replay_undo (M : Matrix (Fin 3) (Fin 3) ℚ) :
    replay (replay M ratOps) (inverseTrace ratOps) = M :=
  replay_inverseTrace M ratOps
private theorem rat_certificate :
    TraceChangeCertificate (fun _ : Fin 3 => 1)
      (traceChange ratOps) (traceChangeInv ratOps) :=
  traceChange_certificate _ _ (by intro a ha; rfl)
private theorem rat_wrong_order_entry : traceChange ratWrong 0 2 = 6 := by
  simp [ratWrong, ratA, ratB, op, inverseEarlierColumnOp, traceChange,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection, Matrix.single_apply, Matrix.one_apply]; norm_num
private theorem rat_inverse_entry : traceChangeInv ratOps 0 2 = 0 := by
  simp [ratOps, ratA, ratB, op, traceChangeInv, inverseTrace,
    inverseEarlierColumnOp, traceChange, Matrix.mul_apply,
    Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
    Matrix.one_apply]
private theorem rat_order_matters : traceChange ratWrong ≠ traceChangeInv ratOps := by
  intro h
  have he := congrFun (congrFun h (0 : Fin 3)) (2 : Fin 3)
  rw [rat_wrong_order_entry, rat_inverse_entry] at he
  norm_num at he

private def mixedDegree : Fin 3 → ℕ := ![0, 1, 1]
private def mixedD : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 2, 3; 0, 0, 0; 0, 0, 0]
private def mixedOp : EarlierColumnOp 3 ℚ := op 1 2 (-(3 / 2)) (by decide)
private def mixedOps : List (EarlierColumnOp 3 ℚ) := [mixedOp]
private theorem mixed_lowers : LowersDegree mixedDegree mixedD := by
  intro r c h
  fin_cases r <;> fin_cases c <;>
    norm_num [mixedD, mixedDegree, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] at *
private theorem mixed_source_pivot : columnPivot (mixedD.col 1) = some 0 := by
  apply (columnPivot_some_iff _ _).2
  constructor
  · norm_num [mixedD, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  · intro r hr
    fin_cases r <;> norm_num [mixedD, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] at *
private theorem mixed_target_pivot : columnPivot (mixedD.col 2) = some 0 := by
  apply (columnPivot_some_iff _ _).2
  constructor
  · norm_num [mixedD, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  · intro r hr
    fin_cases r <;> norm_num [mixedD, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] at *
private theorem mixed_equal_degrees : mixedDegree 1 = mixedDegree 2 :=
  degree_eq_of_common_pivot mixedDegree mixedD mixed_lowers 1 2 0
    mixed_source_pivot mixed_target_pivot
private theorem mixed_respects : TraceRespectsDegree mixedDegree mixedOps := by
  intro a ha
  simp only [mixedOps, List.mem_singleton] at ha
  subst a
  exact mixed_equal_degrees
private theorem mixed_certificate :
    TraceChangeCertificate mixedDegree (traceChange mixedOps)
      (traceChangeInv mixedOps) :=
  traceChange_certificate mixedDegree mixedOps mixed_respects
private theorem mixed_replay_lowers :
    LowersDegree mixedDegree (replay mixedD mixedOps) :=
  replay_lowersDegree mixedDegree mixedD mixedOps mixed_lowers mixed_respects
private theorem mixed_replay_undo :
    replay (replay mixedD mixedOps) (inverseTrace mixedOps) = mixedD :=
  replay_inverseTrace mixedD mixedOps
private theorem mixed_change_entry : traceChange mixedOps 1 2 = -(3 / 2) := by
  simp [mixedOps, mixedOp, op, traceChange,
    Matrix.TransvectionStruct.toMatrix, Matrix.transvection]
private theorem mixed_inverse_entry : traceChangeInv mixedOps 1 2 = 3 / 2 := by
  simp [mixedOps, mixedOp, op, traceChangeInv, inverseTrace,
    inverseEarlierColumnOp, traceChange, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection]
private theorem mixed_cancelled_entry : (replay mixedD mixedOps) 0 2 = 0 := by
  change (mixedD * Matrix.transvection (1 : Fin 3) (2 : Fin 3) (-(3 / 2) : ℚ)) 0 2 = 0
  rw [Matrix.mul_transvection_apply_same]
  norm_num [mixedD, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
private theorem mixed_replay_row0 :
    (replay mixedD mixedOps) 0 0 = 0 ∧
    (replay mixedD mixedOps) 0 1 = 2 ∧
    (replay mixedD mixedOps) 0 2 = 0 := by
  constructor
  · change (mixedD * Matrix.transvection (1 : Fin 3) (2 : Fin 3) (-(3 / 2) : ℚ)) 0 0 = 0
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, mixedD, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail,
      show (2 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide]
  constructor
  · change (mixedD * Matrix.transvection (1 : Fin 3) (2 : Fin 3) (-(3 / 2) : ℚ)) 0 1 = 2
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, mixedD, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail,
      show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 3) ≠ 2 by decide]
  · exact mixed_cancelled_entry

private def badDegree : Fin 2 → ℕ := ![0, 1]
private def badOp : EarlierColumnOp 2 ℚ := op 0 1 1 (by decide)
private def badOps : List (EarlierColumnOp 2 ℚ) := [badOp]
private theorem bad_entry : traceChange badOps 0 1 = 1 := by
  simp [badOps, badOp, op, traceChange, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection]
private theorem bad_upper : (traceChange badOps).IsUpperTriangular :=
  traceChange_isUpperTriangular badOps
private theorem bad_diag (i : Fin 2) : traceChange badOps i i = 1 :=
  traceChange_apply_diag badOps i
private theorem bad_inverse : traceChange badOps * traceChangeInv badOps = 1 :=
  traceChange_mul_traceChangeInv badOps
private theorem bad_not_respects : ¬ TraceRespectsDegree badDegree badOps := by
  intro h
  have h' := h badOp (by simp [badOps])
  norm_num [badDegree, badOp, op] at h'
private theorem bad_no_degree_support :
    ¬ TraceChangeCertificate badDegree (traceChange badOps) (traceChangeInv badOps) := by
  intro h
  have hz := h.degree_support 0 1 (by decide)
  rw [bad_entry] at hz
  norm_num at hz

private instance f2PrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private def f2A : EarlierColumnOp 3 (ZMod 2) := op 0 1 1 (by decide)
private def f2B : EarlierColumnOp 3 (ZMod 2) := op 1 2 1 (by decide)
private def f2Ops : List (EarlierColumnOp 3 (ZMod 2)) := [f2A, f2B]
private def f2Wrong : List (EarlierColumnOp 3 (ZMod 2)) :=
  [inverseEarlierColumnOp f2A, inverseEarlierColumnOp f2B]
private theorem f2_forward_rows :
    rows (traceChange f2Ops) = [[1, 1, 1], [0, 1, 1], [0, 0, 1]] := by decide
private theorem f2_inverse_rows :
    rows (traceChangeInv f2Ops) = [[1, 1, 0], [0, 1, 1], [0, 0, 1]] := by decide
private theorem f2_inverse_left : traceChange f2Ops * traceChangeInv f2Ops = 1 :=
  traceChange_mul_traceChangeInv f2Ops
private theorem f2_inverse_right : traceChangeInv f2Ops * traceChange f2Ops = 1 :=
  traceChangeInv_mul_traceChange f2Ops
private theorem f2_wrong_entry : traceChange f2Wrong 0 2 = 1 := by decide
private theorem f2_inverse_entry : traceChangeInv f2Ops 0 2 = 0 := by decide
private theorem f2_order_matters : traceChange f2Wrong ≠ traceChangeInv f2Ops := by
  intro h
  have he := congrFun (congrFun h (0 : Fin 3)) (2 : Fin 3)
  rw [f2_wrong_entry, f2_inverse_entry] at he
  norm_num at he

private def zeroOp : EarlierColumnOp 3 ℚ := op 0 2 0 (by decide)
private theorem zero_change : traceChange [zeroOp] = 1 := by
  simp [zeroOp, op, traceChange, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection]
private theorem zero_inverse : traceChangeInv [zeroOp] = 1 := by
  simp [zeroOp, op, traceChangeInv, inverseTrace, inverseEarlierColumnOp,
    traceChange, Matrix.TransvectionStruct.toMatrix, Matrix.transvection]
private def repeatedA : EarlierColumnOp 3 ℚ := op 0 2 2 (by decide)
private def repeatedB : EarlierColumnOp 3 ℚ := op 1 2 3 (by decide)
private def repeatedOps : List (EarlierColumnOp 3 ℚ) := [repeatedA, repeatedB]
private theorem repeated_forward_rows :
    rows (traceChange repeatedOps) = [[1, 0, 2], [0, 1, 3], [0, 0, 1]] := by
  simp [rows, repeatedOps, repeatedA, repeatedB, op, traceChange,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection, Matrix.single_apply, Matrix.one_apply]
private theorem repeated_inverse_rows :
    rows (traceChangeInv repeatedOps) = [[1, 0, -2], [0, 1, -3], [0, 0, 1]] := by
  simp [rows, repeatedOps, repeatedA, repeatedB, op, traceChangeInv, inverseTrace,
    inverseEarlierColumnOp, traceChange, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
    Matrix.single_apply, Matrix.one_apply]
private theorem repeated_append :
    traceChangeInv ([repeatedA] ++ [repeatedB]) =
      traceChangeInv [repeatedB] * traceChangeInv [repeatedA] :=
  traceChangeInv_append [repeatedA] [repeatedB]
private theorem repeated_inverse_left :
    traceChange repeatedOps * traceChangeInv repeatedOps = 1 :=
  traceChange_mul_traceChangeInv repeatedOps
private theorem repeated_inverse_right :
    traceChangeInv repeatedOps * traceChange repeatedOps = 1 :=
  traceChangeInv_mul_traceChange repeatedOps

private theorem inverse_prefix_zero :
    prefixSpan (replay mixedD (inverseTrace mixedOps)) 0 = prefixSpan mixedD 0 :=
  prefixSpan_replay mixedD (inverseTrace mixedOps) 0
private theorem inverse_prefix_interior :
    prefixSpan (replay mixedD (inverseTrace mixedOps)) 1 = prefixSpan mixedD 1 :=
  prefixSpan_replay mixedD (inverseTrace mixedOps) 1
private theorem inverse_prefix_full :
    prefixSpan (replay mixedD (inverseTrace mixedOps)) 3 = prefixSpan mixedD 3 :=
  prefixSpan_replay mixedD (inverseTrace mixedOps) 3
private theorem inverse_prefix_oversized :
    prefixSpan (replay mixedD (inverseTrace mixedOps)) 4 = prefixSpan mixedD 4 :=
  prefixSpan_replay mixedD (inverseTrace mixedOps) 4
private theorem arbitrary_input_bridge (M : Matrix (Fin 3) (Fin 3) ℚ) :
    TraceChangeCertificate (fun _ : Fin 3 => 1) (traceChange ratOps)
        (traceChangeInv ratOps) ∧ replay M ratOps = M * traceChange ratOps :=
  ⟨rat_certificate, replay_eq_mul_traceChange M ratOps⟩

#eval rows (traceChange ([] : List (EarlierColumnOp 0 ℚ)))
#eval rows (traceChangeInv ([] : List (EarlierColumnOp 0 ℚ)))
#eval rows (traceChange ([] : List (EarlierColumnOp 1 ℚ)))
#eval rows (traceChangeInv ([] : List (EarlierColumnOp 1 ℚ)))
#eval rows (traceChange ratOps)
#eval rows (traceChangeInv ratOps)
#eval rows (traceChange mixedOps)
#eval rows (traceChangeInv mixedOps)
#eval rows (traceChange f2Ops)
#eval rows (traceChangeInv f2Ops)
#eval rows (traceChange repeatedOps)
#eval rows (traceChangeInv repeatedOps)

/-! Complete local trust inventory, including private fixture data and its field witness. -/
#print axioms rows
#print axioms op
#print axioms empty_zero_forward
#print axioms empty_zero_inverse
#print axioms empty_zero_certificate
#print axioms empty_one_forward
#print axioms empty_one_inverse
#print axioms empty_one_certificate
#print axioms empty_zero_rows
#print axioms empty_one_rows
#print axioms ratA
#print axioms ratB
#print axioms ratOps
#print axioms ratWrong
#print axioms rat_forward_rows
#print axioms rat_inverse_rows
#print axioms rat_inverse_left
#print axioms rat_inverse_right
#print axioms rat_replay_undo
#print axioms rat_certificate
#print axioms rat_wrong_order_entry
#print axioms rat_inverse_entry
#print axioms rat_order_matters
#print axioms mixedDegree
#print axioms mixedD
#print axioms mixedOp
#print axioms mixedOps
#print axioms mixed_lowers
#print axioms mixed_source_pivot
#print axioms mixed_target_pivot
#print axioms mixed_equal_degrees
#print axioms mixed_respects
#print axioms mixed_certificate
#print axioms mixed_replay_lowers
#print axioms mixed_replay_undo
#print axioms mixed_change_entry
#print axioms mixed_inverse_entry
#print axioms mixed_cancelled_entry
#print axioms mixed_replay_row0
#print axioms badDegree
#print axioms badOp
#print axioms badOps
#print axioms bad_entry
#print axioms bad_upper
#print axioms bad_diag
#print axioms bad_inverse
#print axioms bad_not_respects
#print axioms bad_no_degree_support
#print axioms f2PrimeFact
#print axioms f2A
#print axioms f2B
#print axioms f2Ops
#print axioms f2Wrong
#print axioms f2_forward_rows
#print axioms f2_inverse_rows
#print axioms f2_inverse_left
#print axioms f2_inverse_right
#print axioms f2_wrong_entry
#print axioms f2_inverse_entry
#print axioms f2_order_matters
#print axioms zeroOp
#print axioms zero_change
#print axioms zero_inverse
#print axioms repeatedA
#print axioms repeatedB
#print axioms repeatedOps
#print axioms repeated_forward_rows
#print axioms repeated_inverse_rows
#print axioms repeated_append
#print axioms repeated_inverse_left
#print axioms repeated_inverse_right
#print axioms inverse_prefix_zero
#print axioms inverse_prefix_interior
#print axioms inverse_prefix_full
#print axioms inverse_prefix_oversized
#print axioms arbitrary_input_bridge

end TDA.Persistence.Reduction.TraceCertificateExamples
