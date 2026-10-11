import TDA.Persistence.Reduction.ColumnReduction
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-! Executable rational and F₂ regressions for deterministic single-column cancellation. -/

namespace TDA.Persistence.Reduction.ColumnReductionExamples
open TDA.Persistence.Reduction

private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩

private def zeroQ : Matrix (Fin 3) (Fin 3) ℚ := 0
private def firstQ : Matrix (Fin 1) (Fin 1) ℚ := !![7]
private def rowZeroQ : Matrix (Fin 2) (Fin 2) ℚ := !![2, 3; 0, 0]
private def nonzeroStopQ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 0, 4; 2, 0, 6; 0, 0, 0]
private def multiQ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0; 2, 2, 0, 7; 0, 2, 0, 6; 0, 0, 0, 0]
private def tieQ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![2, 3, 5; 0, 0, 0; 0, 0, 0]
private def laterQ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 3, 2; 0, 0, 0; 0, 0, 0]
private def multiF2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 0, 1, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]
private def limitQ : Matrix (Fin 3) (Fin 3) ℚ :=
  !![0, 1, 1; 1, 1, 0; 0, 0, 0]
private def gradedQ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![0, 0, 2, 2, 7, 0;
     0, 0, 0, 2, 6, 0;
     0, 0, 0, 0, 0, 11;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]
private def degree6 : Fin 6 → ℕ := ![0, 0, 1, 1, 1, 2]

private def dataQ {m : ℕ} (ops : List (EarlierColumnOp m ℚ)) :
    List (ℕ × ℕ × ℚ) := ops.map (fun op => (op.1.i.val, op.1.j.val, op.1.c))
private def dataF2 {m : ℕ} (ops : List (EarlierColumnOp m (ZMod 2))) :
    List (ℕ × ℕ × ZMod 2) := ops.map (fun op => (op.1.i.val, op.1.j.val, op.1.c))

#eval (List.finRange 0).map (fun j => (columnReductionTrace (0 : Matrix (Fin 0) (Fin 0) ℚ) j).length)
#eval dataQ (columnReductionTrace zeroQ 2)
#eval List.ofFn ((replay zeroQ (columnReductionTrace zeroQ 2)).col 2)
#eval dataQ (columnReductionTrace firstQ 0)
#eval List.ofFn ((replay firstQ (columnReductionTrace firstQ 0)).col 0)
#eval dataQ (columnReductionTrace rowZeroQ 1)
#eval List.ofFn ((replay rowZeroQ (columnReductionTrace rowZeroQ 1)).col 1)
#eval dataQ (columnReductionTrace nonzeroStopQ 2)
#eval List.ofFn ((replay nonzeroStopQ (columnReductionTrace nonzeroStopQ 2)).col 2)
#eval dataQ (columnReductionTrace multiQ 3)
#eval List.ofFn ((replay multiQ (columnReductionTrace multiQ 3)).col 3)
#eval dataQ (columnReductionTrace tieQ 2)
#eval List.ofFn ((replay tieQ (columnReductionTrace tieQ 2)).col 2)
#eval dataQ (columnReductionTrace laterQ 1)
#eval List.ofFn ((replay laterQ (columnReductionTrace laterQ 1)).col 1)
#eval dataF2 (columnReductionTrace multiF2 3)
#eval List.ofFn ((replay multiF2 (columnReductionTrace multiF2 3)).col 3)
#eval dataQ (columnReductionTrace limitQ 2)
#eval List.ofFn ((replay limitQ (columnReductionTrace limitQ 2)).col 2)
#eval dataQ (columnReductionTrace gradedQ 4)
#eval List.ofFn ((replay gradedQ (columnReductionTrace gradedQ 4)).col 4)
#eval List.ofFn ((replay gradedQ (columnReductionTrace gradedQ 4)).col 5)


private theorem empty_index (j : Fin 0) :
    (columnReductionTrace (0 : Matrix (Fin 0) (Fin 0) ℚ) j).length = 0 :=
  Fin.elim0 j

private theorem zeroQ_trace : dataQ (columnReductionTrace zeroQ 2) = [] := by decide +kernel
private theorem zeroQ_target :
    (replay zeroQ (columnReductionTrace zeroQ 2)).col 2 = 0 := by
  funext r
  fin_cases r <;> decide +kernel
private theorem zeroQ_others (q : Fin 3) (hq : q ≠ 2) :
    (replay zeroQ (columnReductionTrace zeroQ 2)).col q = zeroQ.col q :=
  columnReductionTrace_col_of_ne zeroQ 2 q hq
private theorem firstQ_trace : dataQ (columnReductionTrace firstQ 0) = [] := by decide +kernel
private theorem firstQ_target :
    (replay firstQ (columnReductionTrace firstQ 0)).col 0 = firstQ.col 0 := by
  funext r
  fin_cases r
  decide +kernel
private theorem firstQ_pivot :
    columnPivot ((replay firstQ (columnReductionTrace firstQ 0)).col 0) = some 0 := by
  decide
private theorem rowZeroQ_trace :
    dataQ (columnReductionTrace rowZeroQ 1) = [(0, 1, -3/2)] := by decide +kernel
private theorem rowZeroQ_target :
    (replay rowZeroQ (columnReductionTrace rowZeroQ 1)).col 1 = 0 := by
  funext r
  fin_cases r <;> decide +kernel
private theorem rowZeroQ_source :
    (replay rowZeroQ (columnReductionTrace rowZeroQ 1)).col 0 = rowZeroQ.col 0 :=
  columnReductionTrace_col_of_ne rowZeroQ 1 0 (by decide +kernel)
private theorem nonzeroStopQ_trace :
    dataQ (columnReductionTrace nonzeroStopQ 2) = [(0, 2, -3)] := by decide +kernel
private theorem nonzeroStopQ_target :
    (replay nonzeroStopQ (columnReductionTrace nonzeroStopQ 2)).col 2 = ![1, 0, 0] := by
  funext r
  fin_cases r <;> decide +kernel
private theorem nonzeroStopQ_others (q : Fin 3) (hq : q ≠ 2) :
    (replay nonzeroStopQ (columnReductionTrace nonzeroStopQ 2)).col q = nonzeroStopQ.col q :=
  columnReductionTrace_col_of_ne nonzeroStopQ 2 q hq
private theorem multiQ_trace :
    dataQ (columnReductionTrace multiQ 3) = [(1, 3, -3), (0, 3, -1/2)] := by decide +kernel
private theorem multiQ_target :
    (replay multiQ (columnReductionTrace multiQ 3)).col 3 = 0 := by
  funext r
  fin_cases r <;> decide +kernel
private theorem multiQ_others (q : Fin 4) (hq : q ≠ 3) :
    (replay multiQ (columnReductionTrace multiQ 3)).col q = multiQ.col q :=
  columnReductionTrace_col_of_ne multiQ 3 q hq
private theorem tieQ_trace :
    dataQ (columnReductionTrace tieQ 2) = [(0, 2, -5/2)] := by decide +kernel
private theorem tieQ_target :
    (replay tieQ (columnReductionTrace tieQ 2)).col 2 = 0 := by
  funext r
  fin_cases r <;> decide +kernel
private theorem laterQ_trace : dataQ (columnReductionTrace laterQ 1) = [] := by decide +kernel
private theorem laterQ_target :
    (replay laterQ (columnReductionTrace laterQ 1)).col 1 = laterQ.col 1 := by
  decide +kernel
private theorem laterQ_pivot :
    columnPivot ((replay laterQ (columnReductionTrace laterQ 1)).col 1) = some 0 := by
  decide
private theorem multiF2_trace :
    dataF2 (columnReductionTrace multiF2 3) = [(1, 3, 1), (0, 3, 1)] := by decide +kernel
private theorem multiF2_target :
    (replay multiF2 (columnReductionTrace multiF2 3)).col 3 = 0 := by
  funext r
  fin_cases r <;> decide +kernel
private theorem multiF2_product :
    replay multiF2 (columnReductionTrace multiF2 3) =
      multiF2 * traceChange (columnReductionTrace multiF2 3) :=
  replay_eq_mul_traceChange _ _
private theorem multiF2_prefix (t : ℕ) :
    prefixSpan (replay multiF2 (columnReductionTrace multiF2 3)) t =
      prefixSpan multiF2 t := prefixSpan_replay _ _ _
private theorem limitQ_trace : dataQ (columnReductionTrace limitQ 2) = [] := by decide +kernel
private theorem limitQ_target :
    (replay limitQ (columnReductionTrace limitQ 2)).col 2 = limitQ.col 2 := by
  decide +kernel
private theorem limitQ_span_witness :
    limitQ.col 2 - (limitQ.col 1 - limitQ.col 0) = 0 := by
  funext r
  fin_cases r <;> decide +kernel
private theorem gradedQ_lowers : LowersDegree degree6 gradedQ := by
  intro r c h
  fin_cases r <;> fin_cases c <;> norm_num [gradedQ, degree6] at *
private theorem gradedQ_trace :
    dataQ (columnReductionTrace gradedQ 4) = [(3, 4, -3), (2, 4, -1/2)] := by decide +kernel
private theorem gradedQ_target :
    (replay gradedQ (columnReductionTrace gradedQ 4)).col 4 = 0 := by
  funext r
  fin_cases r <;> decide +kernel
private theorem gradedQ_later :
    (replay gradedQ (columnReductionTrace gradedQ 4)).col 5 = gradedQ.col 5 :=
  columnReductionTrace_col_of_ne gradedQ 4 5 (by decide +kernel)
private theorem gradedQ_degree :
    TraceRespectsDegree degree6 (columnReductionTrace gradedQ 4) :=
  columnReductionTrace_respectsDegree degree6 gradedQ 4 gradedQ_lowers
private theorem gradedQ_certificate :
    TraceChangeCertificate degree6 (traceChange (columnReductionTrace gradedQ 4))
      (traceChangeInv (columnReductionTrace gradedQ 4)) :=
  traceChange_certificate degree6 _ gradedQ_degree
private theorem gradedQ_replay_lowers :
    LowersDegree degree6 (replay gradedQ (columnReductionTrace gradedQ 4)) :=
  replay_lowersDegree degree6 gradedQ _ gradedQ_lowers gradedQ_degree
private theorem gradedQ_product :
    replay gradedQ (columnReductionTrace gradedQ 4) =
      gradedQ * traceChange (columnReductionTrace gradedQ 4) :=
  replay_eq_mul_traceChange _ _
private theorem gradedQ_prefix (t : ℕ) :
    prefixSpan (replay gradedQ (columnReductionTrace gradedQ 4)) t =
      prefixSpan gradedQ t := prefixSpan_replay _ _ _


private def heights {m : ℕ} {k : Type*} [Field k] [DecidableEq k]
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) : List ℕ :=
  ((columnReductionTrace M j).scanl (fun A op => A * op.1.toMatrix) M).map
    (fun A => pivotHeight (columnPivot (A.col j)))

#eval heights zeroQ 2
#eval heights firstQ 0
#eval heights rowZeroQ 1
#eval heights nonzeroStopQ 2
#eval heights multiQ 3
#eval heights tieQ 2
#eval heights laterQ 1
#eval heights multiF2 3
#eval heights limitQ 2
#eval heights gradedQ 4

private theorem zeroQ_pivot : columnPivot ((replay zeroQ (columnReductionTrace zeroQ 2)).col 2) = none := by
  decide +kernel
private theorem zeroQ_height : heights zeroQ 2 = [0] := by decide +kernel
private theorem firstQ_height : heights firstQ 0 = [1] := by decide +kernel
private theorem rowZeroQ_heights : heights rowZeroQ 1 = [1, 0] := by decide +kernel
private theorem nonzeroStopQ_heights : heights nonzeroStopQ 2 = [2, 1] := by decide +kernel
private theorem nonzeroStopQ_pivot :
    columnPivot ((replay nonzeroStopQ (columnReductionTrace nonzeroStopQ 2)).col 2) = some 0 := by
  decide +kernel
private theorem multiQ_heights : heights multiQ 3 = [3, 2, 0] := by decide +kernel
private theorem tieQ_heights : heights tieQ 2 = [1, 0] := by decide +kernel
private theorem tieQ_others (q : Fin 3) (hq : q ≠ 2) :
    (replay tieQ (columnReductionTrace tieQ 2)).col q = tieQ.col q :=
  columnReductionTrace_col_of_ne tieQ 2 q hq
private theorem laterQ_heights : heights laterQ 1 = [1] := by decide +kernel
private theorem multiF2_heights : heights multiF2 3 = [2, 1, 0] := by decide +kernel
private theorem limitQ_heights : heights limitQ 2 = [1] := by decide +kernel
private theorem limitQ_pivots :
    columnPivot (limitQ.col 0) = some 1 ∧
    columnPivot (limitQ.col 1) = some 1 ∧
    columnPivot (limitQ.col 2) = some 0 := by decide +kernel
private theorem gradedQ_heights : heights gradedQ 4 = [2, 1, 0] := by decide +kernel
private theorem gradedQ_not_square_zero : (gradedQ * gradedQ) 0 5 = 22 := by
  decide +kernel


/-! Explicit trust inventory: every named fixture declaration. -/
#print axioms prime2
#print axioms zeroQ
#print axioms firstQ
#print axioms rowZeroQ
#print axioms nonzeroStopQ
#print axioms multiQ
#print axioms tieQ
#print axioms laterQ
#print axioms multiF2
#print axioms limitQ
#print axioms gradedQ
#print axioms degree6
#print axioms dataQ
#print axioms dataF2
#print axioms empty_index
#print axioms zeroQ_trace
#print axioms zeroQ_target
#print axioms firstQ_trace
#print axioms firstQ_pivot
#print axioms rowZeroQ_trace
#print axioms rowZeroQ_target
#print axioms rowZeroQ_source
#print axioms nonzeroStopQ_trace
#print axioms nonzeroStopQ_target
#print axioms multiQ_trace
#print axioms multiQ_target
#print axioms multiQ_others
#print axioms tieQ_trace
#print axioms tieQ_target
#print axioms laterQ_trace
#print axioms laterQ_pivot
#print axioms multiF2_trace
#print axioms multiF2_target
#print axioms multiF2_product
#print axioms multiF2_prefix
#print axioms limitQ_trace
#print axioms limitQ_span_witness
#print axioms gradedQ_lowers
#print axioms gradedQ_trace
#print axioms gradedQ_target
#print axioms gradedQ_later
#print axioms gradedQ_degree
#print axioms gradedQ_certificate
#print axioms gradedQ_replay_lowers
#print axioms gradedQ_product
#print axioms gradedQ_prefix
#print axioms heights
#print axioms zeroQ_pivot
#print axioms firstQ_height
#print axioms rowZeroQ_heights
#print axioms nonzeroStopQ_heights
#print axioms nonzeroStopQ_pivot
#print axioms multiQ_heights
#print axioms tieQ_heights
#print axioms tieQ_others
#print axioms laterQ_heights
#print axioms multiF2_heights
#print axioms limitQ_heights
#print axioms limitQ_pivots
#print axioms gradedQ_heights
#print axioms gradedQ_not_square_zero
#print axioms zeroQ_others
#print axioms firstQ_target
#print axioms nonzeroStopQ_others
#print axioms laterQ_target
#print axioms limitQ_target
#print axioms zeroQ_height
end TDA.Persistence.Reduction.ColumnReductionExamples
