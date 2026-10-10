import TDA.Persistence.Reduction.Trace
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-!
# Finite earlier-column trace examples

These private fixtures check chronological replay and its right-product over the rationals and
`ZMod 2`, including empty dimensions, repeated targets, zero operations, and arbitrary finite
prefixes. Evaluated matrix columns are paired with kernel-checked column theorems. Prefix spans
are checked only through the general theorem and are never evaluated as Booleans.
-/

namespace TDA.Persistence.Reduction.TraceExamples

private def orderedOp {m : ℕ} {k : Type*} (i j : Fin m) (c : k) (hij : i < j) :
    EarlierColumnOp m k :=
  ⟨⟨i, j, ne_of_lt hij, c⟩, hij⟩

private def matrixRows {m : ℕ} {k : Type*} [Field k]
    (M : Matrix (Fin m) (Fin m) k) : List (List k) :=
  (List.finRange m).map fun i => (List.finRange m).map fun j => M i j

/-! ### Empty and one-dimensional indices -/

private def emptyMatrix : Matrix (Fin 0) (Fin 0) ℚ := 0

private theorem noEarlierColumnOp_zero {k : Type*} (op : EarlierColumnOp 0 k) : False :=
  Fin.elim0 op.1.i

private theorem noEarlierColumnOp_one {k : Type*} (op : EarlierColumnOp 1 k) : False := by
  rcases op with ⟨⟨i, j, hne, c⟩, hij⟩
  fin_cases i
  fin_cases j
  exact (lt_irrefl (0 : Fin 1)) hij

private theorem emptyMatrix_prefixSpan (t : ℕ) : prefixSpan emptyMatrix t = ⊥ := by
  have hrange :
      Set.range (fun q : {q : Fin 0 // q.val < t} => emptyMatrix.col q.1) = ∅ := by
    ext v
    constructor
    · rintro ⟨q, _⟩
      exact Fin.elim0 q.1
    · simp
  simp [prefixSpan, hrange]

private theorem empty_replay : replay emptyMatrix [] = emptyMatrix := replay_nil _

private theorem empty_traceChange :
    traceChange ([] : List (EarlierColumnOp 0 ℚ)) = (1 : Matrix (Fin 0) (Fin 0) ℚ) :=
  traceChange_nil

private def oneMatrix : Matrix (Fin 1) (Fin 1) ℚ := 1

private theorem one_replay_empty : replay oneMatrix [] = oneMatrix := replay_nil _

private theorem one_traceChange_empty :
    traceChange ([] : List (EarlierColumnOp 1 ℚ)) = (1 : Matrix (Fin 1) (Fin 1) ℚ) :=
  traceChange_nil

private theorem empty_replay_rows :
    matrixRows (replay emptyMatrix ([] : List (EarlierColumnOp 0 ℚ))) = [] := by
  simp [matrixRows]

private theorem empty_traceChange_rows :
    matrixRows (traceChange ([] : List (EarlierColumnOp 0 ℚ))) = [] := by
  simp [matrixRows]

#eval matrixRows (replay emptyMatrix ([] : List (EarlierColumnOp 0 ℚ)))
#eval matrixRows (traceChange ([] : List (EarlierColumnOp 0 ℚ)))
#eval List.ofFn ((replay oneMatrix ([] : List (EarlierColumnOp 1 ℚ))).col 0)

/-! ### Order-sensitive rational trace -/

private def rationalA : EarlierColumnOp 3 ℚ := orderedOp 0 1 2 (by decide)
private def rationalB : EarlierColumnOp 3 ℚ := orderedOp 1 2 3 (by decide)
private def rationalOps : List (EarlierColumnOp 3 ℚ) := [rationalA, rationalB]
private def rationalInput : Matrix (Fin 3) (Fin 3) ℚ := 1
private def rationalAfterA : Matrix (Fin 3) (Fin 3) ℚ :=
  rationalInput * Matrix.transvection 0 1 (2 : ℚ)
private def rationalReplay : Matrix (Fin 3) (Fin 3) ℚ := replay rationalInput rationalOps
private def rationalTraceChange : Matrix (Fin 3) (Fin 3) ℚ := traceChange rationalOps
private def rationalAfterB : Matrix (Fin 3) (Fin 3) ℚ :=
  rationalInput * Matrix.transvection 1 2 (3 : ℚ)
private def rationalReverseReplay : Matrix (Fin 3) (Fin 3) ℚ :=
  replay rationalInput [rationalB, rationalA]
private def rationalReverseTraceChange : Matrix (Fin 3) (Fin 3) ℚ :=
  traceChange [rationalB, rationalA]

private theorem rationalInput_col0 : rationalInput.col 0 = ![1, 0, 0] := by
  ext r
  fin_cases r <;> norm_num [rationalInput, Matrix.one_apply, Fin.ext_iff]

private theorem rationalInput_col1 : rationalInput.col 1 = ![0, 1, 0] := by
  ext r
  fin_cases r <;> norm_num [rationalInput, Matrix.one_apply, Fin.ext_iff]

private theorem rationalInput_col2 : rationalInput.col 2 = ![0, 0, 1] := by
  ext r
  fin_cases r <;> norm_num [rationalInput, Matrix.one_apply, Fin.ext_iff]

private theorem rationalAfterA_col0 : rationalAfterA.col 0 = ![1, 0, 0] := by
  rw [rationalAfterA, col_mul_transvection_of_ne rationalInput 0 1 0 2 (by decide)]
  exact rationalInput_col0

private theorem rationalAfterA_col1 : rationalAfterA.col 1 = ![2, 1, 0] := by
  rw [rationalAfterA, col_mul_transvection]
  rw [rationalInput_col1, rationalInput_col0]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem rationalAfterA_col2 : rationalAfterA.col 2 = ![0, 0, 1] := by
  rw [rationalAfterA, col_mul_transvection_of_ne rationalInput 0 1 2 2 (by decide)]
  exact rationalInput_col2

private theorem rationalReplay_as_products :
    rationalReplay = rationalAfterA * Matrix.transvection 1 2 (3 : ℚ) := rfl

private theorem rationalReplay_col0 : rationalReplay.col 0 = ![1, 0, 0] := by
  rw [rationalReplay_as_products,
    col_mul_transvection_of_ne rationalAfterA 1 2 0 3 (by decide)]
  exact rationalAfterA_col0

private theorem rationalReplay_col1 : rationalReplay.col 1 = ![2, 1, 0] := by
  rw [rationalReplay_as_products,
    col_mul_transvection_of_ne rationalAfterA 1 2 1 3 (by decide)]
  exact rationalAfterA_col1

private theorem rationalReplay_col2 : rationalReplay.col 2 = ![6, 3, 1] := by
  rw [rationalReplay_as_products, col_mul_transvection]
  rw [rationalAfterA_col2, rationalAfterA_col1]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem rational_replay_bridge :
    rationalReplay = rationalInput * rationalTraceChange :=
  replay_eq_mul_traceChange rationalInput rationalOps

private theorem rationalReplay_eq_traceChange : rationalReplay = rationalTraceChange := by
  calc
    rationalReplay = rationalInput * rationalTraceChange := rational_replay_bridge
    _ = rationalTraceChange := by simp [rationalInput]

private theorem rationalTraceChange_col0 : rationalTraceChange.col 0 = ![1, 0, 0] := by
  rw [← rationalReplay_eq_traceChange]
  exact rationalReplay_col0

private theorem rationalTraceChange_col1 : rationalTraceChange.col 1 = ![2, 1, 0] := by
  rw [← rationalReplay_eq_traceChange]
  exact rationalReplay_col1

private theorem rationalTraceChange_col2 : rationalTraceChange.col 2 = ![6, 3, 1] := by
  rw [← rationalReplay_eq_traceChange]
  exact rationalReplay_col2

private theorem rationalAfterB_col2 : rationalAfterB.col 2 = ![0, 3, 1] := by
  rw [rationalAfterB, col_mul_transvection]
  rw [rationalInput_col2, rationalInput_col1]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem rationalAfterB_col0 : rationalAfterB.col 0 = ![1, 0, 0] := by
  rw [rationalAfterB, col_mul_transvection_of_ne rationalInput 1 2 0 3 (by decide)]
  exact rationalInput_col0

private theorem rationalAfterB_col1 : rationalAfterB.col 1 = ![0, 1, 0] := by
  rw [rationalAfterB, col_mul_transvection_of_ne rationalInput 1 2 1 3 (by decide)]
  exact rationalInput_col1

private theorem rationalReverse_as_products :
    rationalReverseReplay = rationalAfterB * Matrix.transvection 0 1 (2 : ℚ) := rfl

private theorem rationalReverseReplay_eq_traceChange :
    rationalReverseReplay = rationalReverseTraceChange := by
  simpa [rationalReverseReplay, rationalReverseTraceChange, rationalInput] using
    (replay_eq_mul_traceChange rationalInput [rationalB, rationalA])

private theorem rationalReverseReplay_col0 : rationalReverseReplay.col 0 = ![1, 0, 0] := by
  rw [rationalReverse_as_products,
    col_mul_transvection_of_ne rationalAfterB 0 1 0 2 (by decide)]
  exact rationalAfterB_col0

private theorem rationalReverseReplay_col1 : rationalReverseReplay.col 1 = ![2, 1, 0] := by
  rw [rationalReverse_as_products, col_mul_transvection]
  rw [rationalAfterB_col1, rationalAfterB_col0]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem rationalReverse_col2 : rationalReverseReplay.col 2 = ![0, 3, 1] := by
  rw [rationalReverse_as_products,
    col_mul_transvection_of_ne rationalAfterB 0 1 2 2 (by decide)]
  exact rationalAfterB_col2

private theorem rationalReverseTraceChange_col0 :
    rationalReverseTraceChange.col 0 = ![1, 0, 0] := by
  rw [← rationalReverseReplay_eq_traceChange]
  exact rationalReverseReplay_col0

private theorem rationalReverseTraceChange_col1 :
    rationalReverseTraceChange.col 1 = ![2, 1, 0] := by
  rw [← rationalReverseReplay_eq_traceChange]
  exact rationalReverseReplay_col1

private theorem rationalReverseTraceChange_col2 :
    rationalReverseTraceChange.col 2 = ![0, 3, 1] := by
  rw [← rationalReverseReplay_eq_traceChange]
  exact rationalReverse_col2

private theorem rational_replay_entry : rationalReplay 0 2 = 6 := by
  have h := congrFun rationalReplay_col2 (0 : Fin 3)
  simpa using h

private theorem rational_reverse_entry : rationalReverseReplay 0 2 = 0 := by
  have h := congrFun rationalReverse_col2 (0 : Fin 3)
  simpa using h

private theorem rational_order_matters : rationalReplay ≠ rationalReverseReplay := by
  intro h
  have he := congrFun (congrFun h (0 : Fin 3)) (2 : Fin 3)
  rw [rational_replay_entry, rational_reverse_entry] at he
  norm_num at he

private theorem rational_traceChange_order_matters :
    rationalTraceChange ≠ rationalReverseTraceChange := by
  intro h
  have he := congrFun (congrFun h (0 : Fin 3)) (2 : Fin 3)
  have hForward : rationalTraceChange 0 2 = 6 := by
    have hc := congrFun rationalTraceChange_col2 (0 : Fin 3)
    simpa using hc
  have hReverse : rationalReverseTraceChange 0 2 = 0 := by
    have hc := congrFun rationalReverseTraceChange_col2 (0 : Fin 3)
    simpa using hc
  rw [hForward, hReverse] at he
  norm_num at he

private theorem rational_append_singletons :
    replay rationalInput ([rationalA] ++ [rationalB]) =
      replay (replay rationalInput [rationalA]) [rationalB] :=
  replay_append rationalInput [rationalA] [rationalB]

private theorem rational_prefix_all (t : ℕ) :
    prefixSpan rationalReplay t = prefixSpan rationalInput t :=
  prefixSpan_replay rationalInput rationalOps t

private theorem rational_prefix_zero :
    prefixSpan rationalReplay 0 = prefixSpan rationalInput 0 := rational_prefix_all 0
private theorem rational_prefix_one :
    prefixSpan rationalReplay 1 = prefixSpan rationalInput 1 := rational_prefix_all 1
private theorem rational_prefix_two :
    prefixSpan rationalReplay 2 = prefixSpan rationalInput 2 := rational_prefix_all 2
private theorem rational_prefix_three :
    prefixSpan rationalReplay 3 = prefixSpan rationalInput 3 := rational_prefix_all 3
private theorem rational_prefix_four :
    prefixSpan rationalReplay 4 = prefixSpan rationalInput 4 := rational_prefix_all 4

#eval List.ofFn (rationalReplay.col 0)
#eval List.ofFn (rationalReplay.col 1)
#eval List.ofFn (rationalReplay.col 2)
#eval List.ofFn (rationalTraceChange.col 0)
#eval List.ofFn (rationalTraceChange.col 1)
#eval List.ofFn (rationalTraceChange.col 2)
#eval List.ofFn (rationalReverseReplay.col 0)
#eval List.ofFn (rationalReverseReplay.col 1)
#eval List.ofFn (rationalReverseReplay.col 2)
#eval List.ofFn (rationalReverseTraceChange.col 0)
#eval List.ofFn (rationalReverseTraceChange.col 1)
#eval List.ofFn (rationalReverseTraceChange.col 2)
#eval rationalReverseReplay 0 2

/-! ### Repeated target, including a target raised after becoming zero -/

private def repeatedInput : Matrix (Fin 3) (Fin 3) ℚ := fun r c =>
  if r = 0 ∧ c = 0 then 2 else
  if r = 0 ∧ c = 1 then 3 else
  if r = 1 ∧ c = 2 then 1 else 0

private def repeatedA : EarlierColumnOp 3 ℚ := orderedOp 0 1 (-(3 / 2 : ℚ)) (by decide)
private def repeatedB : EarlierColumnOp 3 ℚ := orderedOp 0 1 (1 / 2 : ℚ) (by decide)
private def repeatedOps : List (EarlierColumnOp 3 ℚ) := [repeatedA, repeatedB]
private def repeatedAfterA : Matrix (Fin 3) (Fin 3) ℚ :=
  repeatedInput * Matrix.transvection 0 1 (-(3 / 2 : ℚ))
private def repeatedIntermediate : Matrix (Fin 3) (Fin 3) ℚ :=
  replay repeatedInput [repeatedA]
private def repeatedReplay : Matrix (Fin 3) (Fin 3) ℚ := replay repeatedInput repeatedOps
private def repeatedTraceChange : Matrix (Fin 3) (Fin 3) ℚ := traceChange repeatedOps

private theorem repeatedInput_col0 : repeatedInput.col 0 = ![2, 0, 0] := by
  ext r
  fin_cases r <;> norm_num [repeatedInput, Fin.ext_iff]

private theorem repeatedInput_col1 : repeatedInput.col 1 = ![3, 0, 0] := by
  ext r
  fin_cases r <;> norm_num [repeatedInput, Fin.ext_iff]

private theorem repeatedInput_col2 : repeatedInput.col 2 = ![0, 1, 0] := by
  ext r
  fin_cases r <;> norm_num [repeatedInput, Fin.ext_iff]

private theorem repeatedIntermediate_eq_afterA : repeatedIntermediate = repeatedAfterA := rfl

private theorem repeatedIntermediate_col0 : repeatedIntermediate.col 0 = ![2, 0, 0] := by
  rw [repeatedIntermediate_eq_afterA, repeatedAfterA,
    col_mul_transvection_of_ne repeatedInput 0 1 0 (-(3 / 2 : ℚ)) (by decide)]
  exact repeatedInput_col0

private theorem repeatedIntermediate_col1 : repeatedIntermediate.col 1 = ![0, 0, 0] := by
  rw [repeatedIntermediate_eq_afterA, repeatedAfterA, col_mul_transvection]
  rw [repeatedInput_col1, repeatedInput_col0]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem repeatedIntermediate_col2 : repeatedIntermediate.col 2 = ![0, 1, 0] := by
  rw [repeatedIntermediate_eq_afterA, repeatedAfterA,
    col_mul_transvection_of_ne repeatedInput 0 1 2 (-(3 / 2 : ℚ)) (by decide)]
  exact repeatedInput_col2

private theorem repeatedReplay_as_products :
    repeatedReplay = repeatedAfterA * Matrix.transvection 0 1 (1 / 2 : ℚ) := rfl

private theorem repeatedReplay_col0 : repeatedReplay.col 0 = ![2, 0, 0] := by
  rw [repeatedReplay_as_products,
    col_mul_transvection_of_ne repeatedAfterA 0 1 0 (1 / 2 : ℚ) (by decide)]
  exact repeatedIntermediate_col0

private theorem repeatedReplay_col1 : repeatedReplay.col 1 = ![1, 0, 0] := by
  rw [repeatedReplay_as_products, col_mul_transvection]
  rw [← repeatedIntermediate_eq_afterA, repeatedIntermediate_col0, repeatedIntermediate_col1]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem repeatedReplay_col2 : repeatedReplay.col 2 = ![0, 1, 0] := by
  rw [repeatedReplay_as_products,
    col_mul_transvection_of_ne repeatedAfterA 0 1 2 (1 / 2 : ℚ) (by decide)]
  exact repeatedIntermediate_col2

private theorem repeatedTraceChange_product :
    repeatedTraceChange =
      Matrix.transvection (0 : Fin 3) 1 (-(3 / 2 : ℚ)) *
        Matrix.transvection 0 1 (1 / 2 : ℚ) := by
  calc
    repeatedTraceChange = traceChange [repeatedA, repeatedB] := by
      simp [repeatedTraceChange, repeatedOps]
    _ = traceChange [repeatedA] * traceChange [repeatedB] := by
      simpa using (traceChange_append [repeatedA] [repeatedB])
    _ = Matrix.transvection 0 1 (-(3 / 2 : ℚ)) * Matrix.transvection 0 1 (1 / 2 : ℚ) := by
      simp [traceChange, repeatedA, repeatedB, orderedOp, Matrix.TransvectionStruct.toMatrix]

private theorem repeated_traceChange_is_single_transvection :
    repeatedTraceChange = Matrix.transvection (0 : Fin 3) 1 (-1 : ℚ) := by
  rw [repeatedTraceChange_product]
  rw [Matrix.transvection_mul_transvection_same 0 1 (by decide)]
  congr 1
  ring

private theorem repeated_replay_bridge :
    repeatedReplay = repeatedInput * repeatedTraceChange :=
  replay_eq_mul_traceChange repeatedInput repeatedOps

private theorem repeated_prefix_all (t : ℕ) :
    prefixSpan repeatedReplay t = prefixSpan repeatedInput t :=
  prefixSpan_replay repeatedInput repeatedOps t

private theorem repeated_prefix_every_partial (n t : ℕ) :
    prefixSpan (replay repeatedInput (repeatedOps.take n)) t = prefixSpan repeatedInput t :=
  prefixSpan_replay repeatedInput (repeatedOps.take n) t

#eval List.ofFn (repeatedIntermediate.col 1)
#eval List.ofFn (repeatedReplay.col 0)
#eval List.ofFn (repeatedReplay.col 1)
#eval List.ofFn (repeatedReplay.col 2)
#eval List.ofFn (repeatedTraceChange.col 0)
#eval List.ofFn (repeatedTraceChange.col 1)
#eval List.ofFn (repeatedTraceChange.col 2)

/-! ### Characteristic-two specialization -/

private instance f2PrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def f2A : EarlierColumnOp 3 (ZMod 2) := orderedOp 0 1 1 (by decide)
private def f2B : EarlierColumnOp 3 (ZMod 2) := orderedOp 1 2 1 (by decide)
private def f2Ops : List (EarlierColumnOp 3 (ZMod 2)) := [f2A, f2B]
private def f2Input : Matrix (Fin 3) (Fin 3) (ZMod 2) := 1
private def f2AfterA : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  f2Input * Matrix.transvection 0 1 (1 : ZMod 2)
private def f2Replay : Matrix (Fin 3) (Fin 3) (ZMod 2) := replay f2Input f2Ops
private def f2TraceChange : Matrix (Fin 3) (Fin 3) (ZMod 2) := traceChange f2Ops

private theorem f2Input_col0 : f2Input.col 0 = ![1, 0, 0] := by
  ext r
  fin_cases r <;> norm_num [f2Input, Matrix.one_apply, Fin.ext_iff]

private theorem f2Input_col1 : f2Input.col 1 = ![0, 1, 0] := by
  ext r
  fin_cases r <;> norm_num [f2Input, Matrix.one_apply, Fin.ext_iff]

private theorem f2Input_col2 : f2Input.col 2 = ![0, 0, 1] := by
  ext r
  fin_cases r <;> norm_num [f2Input, Matrix.one_apply, Fin.ext_iff]

private theorem f2AfterA_col0 : f2AfterA.col 0 = ![1, 0, 0] := by
  rw [f2AfterA, col_mul_transvection_of_ne f2Input 0 1 0 1 (by decide)]
  exact f2Input_col0

private theorem f2AfterA_col1 : f2AfterA.col 1 = ![1, 1, 0] := by
  rw [f2AfterA, col_mul_transvection, f2Input_col1, f2Input_col0]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem f2AfterA_col2 : f2AfterA.col 2 = ![0, 0, 1] := by
  rw [f2AfterA, col_mul_transvection_of_ne f2Input 0 1 2 1 (by decide)]
  exact f2Input_col2

private theorem f2Replay_as_products :
    f2Replay = f2AfterA * Matrix.transvection 1 2 (1 : ZMod 2) := rfl

private theorem f2Replay_col0 : f2Replay.col 0 = ![1, 0, 0] := by
  rw [f2Replay_as_products, col_mul_transvection_of_ne f2AfterA 1 2 0 1 (by decide)]
  exact f2AfterA_col0

private theorem f2Replay_col1 : f2Replay.col 1 = ![1, 1, 0] := by
  rw [f2Replay_as_products,
    col_mul_transvection_of_ne f2AfterA 1 2 1 1 (by decide)]
  exact f2AfterA_col1

private theorem f2Replay_col2 : f2Replay.col 2 = ![1, 1, 1] := by
  rw [f2Replay_as_products, col_mul_transvection, f2AfterA_col2, f2AfterA_col1]
  ext r
  fin_cases r <;> norm_num [smul_eq_mul]

private theorem f2_replay_bridge : f2Replay = f2Input * f2TraceChange :=
  replay_eq_mul_traceChange f2Input f2Ops

private theorem f2Replay_eq_traceChange : f2Replay = f2TraceChange := by
  calc
    f2Replay = f2Input * f2TraceChange := f2_replay_bridge
    _ = f2TraceChange := by simp [f2Input]

private theorem f2TraceChange_col0 : f2TraceChange.col 0 = ![1, 0, 0] := by
  rw [← f2Replay_eq_traceChange]
  exact f2Replay_col0

private theorem f2TraceChange_col1 : f2TraceChange.col 1 = ![1, 1, 0] := by
  rw [← f2Replay_eq_traceChange]
  exact f2Replay_col1

private theorem f2TraceChange_col2 : f2TraceChange.col 2 = ![1, 1, 1] := by
  rw [← f2Replay_eq_traceChange]
  exact f2Replay_col2

private theorem f2_replay_entry : f2Replay 0 2 = 1 := by
  have h := congrFun f2Replay_col2 (0 : Fin 3)
  simpa using h

private theorem f2_prefix_all (t : ℕ) :
    prefixSpan f2Replay t = prefixSpan f2Input t :=
  prefixSpan_replay f2Input f2Ops t

#eval List.ofFn (f2Replay.col 0)
#eval List.ofFn (f2Replay.col 1)
#eval List.ofFn (f2Replay.col 2)
#eval List.ofFn (f2TraceChange.col 0)
#eval List.ofFn (f2TraceChange.col 1)
#eval List.ofFn (f2TraceChange.col 2)
#eval f2Replay 0 2

/-! ### Zero coefficient and zero input -/

private theorem zeroScalar_transvection_mul {m : ℕ} {k : Type*} [Field k]
    (M : Matrix (Fin m) (Fin m) k) (i j : Fin m) :
    M * Matrix.transvection i j (0 : k) = M := by
  rw [Matrix.transvection_zero, Matrix.mul_one]

private theorem zeroScalar_replay {m : ℕ} {k : Type*} [Field k]
    (M : Matrix (Fin m) (Fin m) k) (i j : Fin m) (hij : i < j) :
    replay M [orderedOp i j (0 : k) hij] = M := by
  rw [replay_cons, replay_nil]
  exact zeroScalar_transvection_mul M i j

private theorem zeroMatrix_replay {m : ℕ} {k : Type*} [Field k]
    (ops : List (EarlierColumnOp m k)) :
    replay (0 : Matrix (Fin m) (Fin m) k) ops = 0 := by
  calc
    replay (0 : Matrix (Fin m) (Fin m) k) ops =
        (0 : Matrix (Fin m) (Fin m) k) * traceChange ops :=
      replay_eq_mul_traceChange _ _
    _ = 0 := zero_mul _

private def zeroOperation : EarlierColumnOp 3 ℚ := orderedOp 0 1 0 (by decide)

private theorem zero_operation_replay :
    replay repeatedInput [zeroOperation] = repeatedInput :=
  zeroScalar_replay repeatedInput 0 1 (by decide)

private theorem zero_operation_target :
    (replay repeatedInput [zeroOperation]).col 1 = ![3, 0, 0] := by
  rw [zero_operation_replay]
  exact repeatedInput_col1

#eval List.ofFn ((replay repeatedInput [zeroOperation]).col 1)
#eval List.ofFn ((replay (0 : Matrix (Fin 3) (Fin 3) ℚ) repeatedOps).col 0)
#eval List.ofFn ((replay (0 : Matrix (Fin 3) (Fin 3) ℚ) repeatedOps).col 1)
#eval List.ofFn ((replay (0 : Matrix (Fin 3) (Fin 3) ℚ) repeatedOps).col 2)

/-! Every private fixture declaration and the private characteristic-two witness is audited. -/
#print axioms TDA.Persistence.Reduction.replay
#print axioms TDA.Persistence.Reduction.traceChange
#print axioms orderedOp
#print axioms matrixRows
#print axioms emptyMatrix
#print axioms noEarlierColumnOp_zero
#print axioms noEarlierColumnOp_one
#print axioms emptyMatrix_prefixSpan
#print axioms empty_replay
#print axioms empty_traceChange
#print axioms empty_replay_rows
#print axioms empty_traceChange_rows
#print axioms oneMatrix
#print axioms one_replay_empty
#print axioms one_traceChange_empty
#print axioms rationalA
#print axioms rationalB
#print axioms rationalOps
#print axioms rationalInput
#print axioms rationalAfterA
#print axioms rationalReverseTraceChange
#print axioms rationalReplay
#print axioms rationalTraceChange
#print axioms rationalAfterB
#print axioms rationalReverseReplay
#print axioms rationalInput_col0
#print axioms rationalInput_col1
#print axioms rationalInput_col2
#print axioms rationalAfterA_col0
#print axioms rationalAfterA_col1
#print axioms rationalAfterA_col2
#print axioms rationalReplay_as_products
#print axioms rationalReplay_col0
#print axioms rationalReplay_col1
#print axioms rationalReplay_col2
#print axioms rational_replay_bridge
#print axioms rationalReplay_eq_traceChange
#print axioms rationalTraceChange_col0
#print axioms rationalTraceChange_col1
#print axioms rationalTraceChange_col2
#print axioms rationalAfterB_col2
#print axioms rationalAfterB_col0
#print axioms rationalAfterB_col1
#print axioms rationalReverse_as_products
#print axioms rationalReverseReplay_eq_traceChange
#print axioms rationalReverseReplay_col0
#print axioms rationalReverseReplay_col1
#print axioms rationalReverse_col2
#print axioms rationalReverseTraceChange_col0
#print axioms rationalReverseTraceChange_col1
#print axioms rationalReverseTraceChange_col2
#print axioms rational_replay_entry
#print axioms rational_reverse_entry
#print axioms rational_order_matters
#print axioms rational_traceChange_order_matters
#print axioms rational_append_singletons
#print axioms rational_prefix_all
#print axioms rational_prefix_zero
#print axioms rational_prefix_one
#print axioms rational_prefix_two
#print axioms rational_prefix_three
#print axioms rational_prefix_four
#print axioms repeatedInput
#print axioms repeatedA
#print axioms repeatedB
#print axioms repeatedOps
#print axioms repeatedAfterA
#print axioms repeatedIntermediate
#print axioms repeatedReplay
#print axioms repeatedTraceChange
#print axioms repeatedInput_col0
#print axioms repeatedInput_col1
#print axioms repeatedInput_col2
#print axioms repeatedIntermediate_eq_afterA
#print axioms repeatedIntermediate_col0
#print axioms repeatedIntermediate_col1
#print axioms repeatedIntermediate_col2
#print axioms repeatedReplay_as_products
#print axioms repeatedReplay_col0
#print axioms repeatedReplay_col1
#print axioms repeatedReplay_col2
#print axioms repeatedTraceChange_product
#print axioms repeated_traceChange_is_single_transvection
#print axioms repeated_replay_bridge
#print axioms repeated_prefix_all
#print axioms repeated_prefix_every_partial
#print axioms f2PrimeFact
#print axioms f2A
#print axioms f2B
#print axioms f2Ops
#print axioms f2Input
#print axioms f2AfterA
#print axioms f2Replay
#print axioms f2TraceChange
#print axioms f2Input_col0
#print axioms f2Input_col1
#print axioms f2Input_col2
#print axioms f2AfterA_col0
#print axioms f2AfterA_col1
#print axioms f2AfterA_col2
#print axioms f2Replay_as_products
#print axioms f2Replay_col0
#print axioms f2Replay_col1
#print axioms f2Replay_col2
#print axioms f2_replay_bridge
#print axioms f2Replay_eq_traceChange
#print axioms f2TraceChange_col0
#print axioms f2TraceChange_col1
#print axioms f2TraceChange_col2
#print axioms f2_replay_entry
#print axioms f2_prefix_all
#print axioms zeroScalar_transvection_mul
#print axioms zeroScalar_replay
#print axioms zeroMatrix_replay
#print axioms zeroOperation
#print axioms zero_operation_replay
#print axioms zero_operation_target

end TDA.Persistence.Reduction.TraceExamples
