import TDA.Persistence.Reduction.MatrixReduction
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-! Concrete full-traversal regression examples for Issue #128. -/

namespace TDA.Persistence.Reduction

private instance prime2 : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩

private def rows {n : ℕ} {α : Type*} (A : Matrix (Fin n) (Fin n) α) :
    List (List α) :=
  List.ofFn (fun r : Fin n => List.ofFn (fun c : Fin n => A r c))

private def pivots {n : ℕ} {α : Type*} [Field α] [DecidableEq α]
    (A : Matrix (Fin n) (Fin n) α) : List (Option (Fin n)) :=
  List.ofFn (fun j : Fin n => columnPivot (A.col j))

private def triples {n : ℕ} {α : Type*}
    (ops : List (EarlierColumnOp n α)) : List (ℕ × ℕ × α) :=
  ops.map (fun op => (op.1.i.val, op.1.j.val, op.1.c))

private def emptyQ : Matrix (Fin 0) (Fin 0) ℚ := 0
private def zero3Q : Matrix (Fin 3) (Fin 3) ℚ := 0
private def ident3Q : Matrix (Fin 3) (Fin 3) ℚ := 1

private def rowZeroQ : Matrix (Fin 2) (Fin 2) ℚ :=
  fun r c => if r.val = 0 then if c.val = 0 then 2 else 3 else 0

private def evolvedQ : Matrix (Fin 3) (Fin 3) ℚ :=
  fun r c =>
    if c.val = 0 then (if r.val = 1 then 2 else 0)
    else if c.val = 1 then (if r.val = 1 then 3 else if r.val = 0 then 1 else 0)
    else (if r.val = 1 then 6 else if r.val = 0 then 5 else 0)

private def unreducedQ : Matrix (Fin 3) (Fin 3) ℚ :=
  fun r c =>
    if c.val = 0 then (if r.val = 1 then 1 else 0)
    else if c.val = 1 then (if r.val = 1 ∨ r.val = 0 then 1 else 0)
    else (if r.val = 0 then 1 else 0)

private def localQ : Matrix (Fin 4) (Fin 4) ℚ :=
  fun r c =>
    if c.val = 0 then (if r.val = 0 then 2 else 0)
    else if c.val = 1 then (if r.val = 0 ∨ r.val = 1 then 2 else 0)
    else if c.val = 2 then (if r.val = 0 then 7 else if r.val = 1 then 6 else 0)
    else (if r.val = 2 then 5 else 0)

private def f2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun r c =>
    if c.val = 0 then (if r.val = 0 then 1 else 0)
    else if c.val = 1 then (if r.val = 0 ∨ r.val = 1 then 1 else 0)
    else if c.val = 2 then (if r.val = 1 then 1 else 0)
    else (if r.val = 2 then 1 else 0)

private def gradedQ : Matrix (Fin 6) (Fin 6) ℚ :=
  fun r c =>
    if c.val = 2 then (if r.val = 0 then 2 else 0)
    else if c.val = 3 then (if r.val = 0 ∨ r.val = 1 then 2 else 0)
    else if c.val = 4 then (if r.val = 0 then 7 else if r.val = 1 then 6 else 0)
    else if c.val = 5 then (if r.val = 2 then 11 else 0)
    else 0

private def degree6 : Fin 6 → ℕ :=
  fun i => if i.val < 2 then 0 else if i.val < 5 then 1 else 2

private def differentialQ : Matrix (Fin 4) (Fin 4) ℚ :=
  fun r c =>
    if c.val = 1 ∨ c.val = 2 then (if r.val = 0 then 1 else 0)
    else if c.val = 3 then (if r.val = 2 then 1 else if r.val = 1 then -1 else 0)
    else 0

private def degree4 : Fin 4 → ℕ :=
  fun i => if i.val = 0 then 0 else if i.val = 3 then 2 else 1

private def triangle {α : Type*} [Field α] : Matrix (Fin 7) (Fin 7) α :=
  fun r c =>
    if c.val = 3 then (if r.val = 0 then -1 else if r.val = 1 then 1 else 0)
    else if c.val = 4 then (if r.val = 1 then -1 else if r.val = 2 then 1 else 0)
    else if c.val = 5 then (if r.val = 0 then -1 else if r.val = 2 then 1 else 0)
    else if c.val = 6 then (if r.val = 3 ∨ r.val = 4 then 1 else if r.val = 5 then -1 else 0)
    else 0

private def degree7 : Fin 7 → ℕ :=
  fun i => if i.val < 3 then 0 else if i.val < 6 then 1 else 2

private theorem empty_trace : triples (matrixReductionTrace emptyQ) = [] := by decide +kernel
private theorem empty_matrix : replay emptyQ (matrixReductionTrace emptyQ) = emptyQ := by
  funext r
  exact Fin.elim0 r
private theorem empty_pivots : pivots (replay emptyQ (matrixReductionTrace emptyQ)) = [] :=
  by decide +kernel
private theorem empty_length : (matrixReductionTrace emptyQ).length = 0 := by decide +kernel
private theorem empty_change : traceChange (matrixReductionTrace emptyQ) = 1 := by
  funext r
  exact Fin.elim0 r
private theorem empty_inverse : traceChangeInv (matrixReductionTrace emptyQ) = 1 := by
  funext r
  exact Fin.elim0 r
private theorem empty_lowers (degree : Fin 0 → ℕ) : LowersDegree degree emptyQ := by
  intro r
  exact Fin.elim0 r
private theorem empty_certificate (degree : Fin 0 → ℕ) :
    TraceChangeCertificate degree
      (traceChange (matrixReductionTrace emptyQ))
      (traceChangeInv (matrixReductionTrace emptyQ)) :=
  traceChange_certificate degree _
    (matrixReductionTrace_respectsDegree degree emptyQ (empty_lowers degree))

private theorem rowZero_trace :
    triples (matrixReductionTrace rowZeroQ) = [(0, 1, -3/2)] := by decide +kernel
private theorem rowZero_matrix :
    replay rowZeroQ (matrixReductionTrace rowZeroQ) =
      (!![2, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem rowZero_pivots :
    pivots (replay rowZeroQ (matrixReductionTrace rowZeroQ)) =
      [some (0 : Fin 2), none] := by decide +kernel

private theorem evolved_trace :
    triples (matrixReductionTrace evolvedQ) =
      [(0, 1, -3/2), (0, 2, -3), (1, 2, -5)] := by decide +kernel
private theorem evolved_matrix :
    replay evolvedQ (matrixReductionTrace evolvedQ) =
      (!![0, 1, 0; 2, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem evolved_pivots :
    pivots (replay evolvedQ (matrixReductionTrace evolvedQ)) =
      [some (1 : Fin 3), some 0, none] := by decide +kernel
private theorem evolved_change :
    traceChange (matrixReductionTrace evolvedQ) =
      (!![1, -3/2, 9/2; 0, 1, -5; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem evolved_inverse :
    traceChangeInv (matrixReductionTrace evolvedQ) =
      (!![1, 3/2, 3; 0, 1, 5; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem f2_trace :
    triples (matrixReductionTrace f2) =
      [(1, 2, 1), (0, 2, 1)] := by decide +kernel
private theorem f2_matrix :
    replay f2 (matrixReductionTrace f2) =
      (!![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem f2_pivots :
    pivots (replay f2 (matrixReductionTrace f2)) =
      [some (0 : Fin 4), some 1, none, some 2] := by decide +kernel

private theorem differential_trace :
    triples (matrixReductionTrace differentialQ) = [(1, 2, -1)] := by decide +kernel
private theorem differential_matrix :
    replay differentialQ (matrixReductionTrace differentialQ) =
      (!![0, 1, 0, 0; 0, 0, 0, -1; 0, 0, 0, 1; 0, 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem differential_pivots :
    pivots (replay differentialQ (matrixReductionTrace differentialQ)) =
      [none, some (0 : Fin 4), none, some 2] := by decide +kernel
private theorem differential_square_zero : differentialQ * differentialQ = 0 := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem reduced_square_nonzero :
    ((replay differentialQ (matrixReductionTrace differentialQ)) *
      (replay differentialQ (matrixReductionTrace differentialQ))) 0 3 = -1 := by
  decide +kernel
private theorem reduced_square_not_zero :
    (replay differentialQ (matrixReductionTrace differentialQ)) *
      (replay differentialQ (matrixReductionTrace differentialQ)) ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h 0) 3
  rw [reduced_square_nonzero] at hentry
  norm_num at hentry

private theorem evolved_two_targets :
    triples (columnReductionTrace evolvedQ ⟨1, by decide⟩) =
      [(0, 1, -3/2)] := by decide +kernel
private theorem evolved_future_column :
    (replay evolvedQ (columnReductionTrace evolvedQ ⟨1, by decide⟩)).col 2 =
      evolvedQ.col 2 := by
  apply columnReductionTrace_col_of_ne
  decide +kernel
private theorem evolved_prefix_matrix :
    replay evolvedQ (columnReductionTrace evolvedQ ⟨1, by decide⟩) =
      (!![0, 1, 5; 2, 0, 6; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem gradedQ_lowers : LowersDegree degree6 gradedQ := by
  intro r c h
  fin_cases r <;> fin_cases c <;> norm_num [gradedQ, degree6] at *
private theorem gradedQ_square : (gradedQ * gradedQ) 0 5 = 22 := by decide +kernel
private theorem differentialQ_lowers : LowersDegree degree4 differentialQ := by
  intro r c h
  fin_cases r <;> fin_cases c <;> norm_num [differentialQ, degree4] at *
private theorem triangleQ_lowers : LowersDegree degree7 (triangle (α := ℚ)) := by
  intro r c h
  fin_cases r <;> fin_cases c <;> norm_num [triangle, degree7] at *
private theorem triangleF2_lowers : LowersDegree degree7 (triangle (α := ZMod 2)) := by
  intro r c h
  fin_cases r <;> fin_cases c <;> norm_num [triangle, degree7] at *

private theorem gradedQ_certificate :
    TraceChangeCertificate degree6
      (traceChange (matrixReductionTrace gradedQ))
      (traceChangeInv (matrixReductionTrace gradedQ)) :=
  traceChange_certificate degree6 _
    (matrixReductionTrace_respectsDegree degree6 gradedQ gradedQ_lowers)
private theorem differentialQ_certificate :
    TraceChangeCertificate degree4
      (traceChange (matrixReductionTrace differentialQ))
      (traceChangeInv (matrixReductionTrace differentialQ)) :=
  traceChange_certificate degree4 _
    (matrixReductionTrace_respectsDegree degree4 differentialQ differentialQ_lowers)
private theorem triangleQ_certificate :
    TraceChangeCertificate degree7
      (traceChange (matrixReductionTrace (triangle (α := ℚ))))
      (traceChangeInv (matrixReductionTrace (triangle (α := ℚ)))) :=
  traceChange_certificate degree7 _
    (matrixReductionTrace_respectsDegree degree7 (triangle (α := ℚ)) triangleQ_lowers)
private theorem triangleF2_certificate :
    TraceChangeCertificate degree7
      (traceChange (matrixReductionTrace (triangle (α := ZMod 2))))
      (traceChangeInv (matrixReductionTrace (triangle (α := ZMod 2)))) :=
  traceChange_certificate degree7 _
    (matrixReductionTrace_respectsDegree degree7 (triangle (α := ZMod 2)) triangleF2_lowers)


private theorem zero3_matrix :
    replay zero3Q (matrixReductionTrace zero3Q) = zero3Q := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem ident3_matrix :
    replay ident3Q (matrixReductionTrace ident3Q) = ident3Q := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem zero3_trace : triples (matrixReductionTrace zero3Q) = [] := by decide +kernel
private theorem zero3_pivots :
    pivots (replay zero3Q (matrixReductionTrace zero3Q)) = [none, none, none] :=
  by decide +kernel
private theorem ident3_trace : triples (matrixReductionTrace ident3Q) = [] := by decide +kernel
private theorem ident3_pivots :
    pivots (replay ident3Q (matrixReductionTrace ident3Q)) =
      [some (0 : Fin 3), some 1, some 2] := by decide +kernel
private theorem ident3_square_nonzero : (ident3Q * ident3Q) 0 0 = 1 := by decide +kernel

private theorem rowZero_change :
    traceChange (matrixReductionTrace rowZeroQ) =
      (!![1, -3/2; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem rowZero_inverse :
    traceChangeInv (matrixReductionTrace rowZeroQ) =
      (!![1, 3/2; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem unreduced_single_trace :
    triples (columnReductionTrace unreducedQ ⟨2, by decide⟩) = [] :=
  by decide +kernel
private theorem unreduced_trace :
    triples (matrixReductionTrace unreducedQ) = [(0, 1, -1), (1, 2, -1)] :=
  by decide +kernel
private theorem unreduced_matrix :
    replay unreducedQ (matrixReductionTrace unreducedQ) =
      (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem unreduced_pivots :
    pivots (replay unreducedQ (matrixReductionTrace unreducedQ)) =
      [some (1 : Fin 3), some 0, none] := by decide +kernel

private theorem local_trace :
    triples (matrixReductionTrace localQ) = [(1, 2, -3), (0, 2, -1/2)] :=
  by decide +kernel
private theorem local_matrix :
    replay localQ (matrixReductionTrace localQ) =
      (!![2, 2, 0, 0; 0, 2, 0, 0; 0, 0, 0, 5; 0, 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem local_pivots :
    pivots (replay localQ (matrixReductionTrace localQ)) =
      [some (0 : Fin 4), some 1, none, some 2] := by decide +kernel

private theorem gradedQ_trace :
    triples (matrixReductionTrace gradedQ) = [(3, 4, -3), (2, 4, -1/2)] :=
  by decide +kernel
private theorem gradedQ_matrix :
    replay gradedQ (matrixReductionTrace gradedQ) =
      (!![0, 0, 2, 2, 0, 0;
          0, 0, 0, 2, 0, 0;
          0, 0, 0, 0, 0, 11;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0;
          0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℚ) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem gradedQ_pivots :
    pivots (replay gradedQ (matrixReductionTrace gradedQ)) =
      [none, none, some (0 : Fin 6), some 1, none, some 2] :=
  by decide +kernel

private theorem triangleQ_trace :
    triples (matrixReductionTrace (triangle (α := ℚ))) =
      [(4, 5, -1), (3, 5, -1)] := by decide +kernel
private theorem triangleF2_trace :
    triples (matrixReductionTrace (triangle (α := ZMod 2))) =
      [(4, 5, 1), (3, 5, 1)] := by decide +kernel
private theorem triangleQ_matrix :
    replay (triangle (α := ℚ)) (matrixReductionTrace (triangle (α := ℚ))) =
      (fun r c => if c.val = 5 then 0 else triangle (α := ℚ) r c) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel
private theorem triangleF2_matrix :
    replay (triangle (α := ZMod 2)) (matrixReductionTrace (triangle (α := ZMod 2))) =
      (fun r c => if c.val = 5 then 0 else triangle (α := ZMod 2) r c) := by
  funext r c
  fin_cases r <;> fin_cases c <;> decide +kernel

private theorem triangleQ_pivots :
    pivots (replay (triangle (α := ℚ)) (matrixReductionTrace (triangle (α := ℚ)))) =
      [none, none, none, some (1 : Fin 7), some 2, none, some 5] :=
  by decide +kernel
private theorem triangleF2_pivots :
    pivots (replay (triangle (α := ZMod 2))
      (matrixReductionTrace (triangle (α := ZMod 2)))) =
      [none, none, none, some (1 : Fin 7), some 2, none, some 5] :=
  by decide +kernel

private theorem evolved_inverse_laws :
    traceChange (matrixReductionTrace evolvedQ) *
        traceChangeInv (matrixReductionTrace evolvedQ) = 1 ∧
      traceChangeInv (matrixReductionTrace evolvedQ) *
        traceChange (matrixReductionTrace evolvedQ) = 1 :=
  ⟨traceChange_mul_traceChangeInv _, traceChangeInv_mul_traceChange _⟩
private theorem f2_certificate :
    replay f2 (matrixReductionTrace f2) = f2 * traceChange (matrixReductionTrace f2) ∧
      traceChange (matrixReductionTrace f2) *
        traceChangeInv (matrixReductionTrace f2) = 1 ∧
      traceChangeInv (matrixReductionTrace f2) *
        traceChange (matrixReductionTrace f2) = 1 ∧
      (∀ s : ℕ, prefixSpan (replay f2 (matrixReductionTrace f2)) s = prefixSpan f2 s) :=
  ⟨replay_eq_mul_traceChange _ _, traceChange_mul_traceChangeInv _,
    traceChangeInv_mul_traceChange _, fun s => prefixSpan_replay _ _ s⟩

end TDA.Persistence.Reduction
