import TDA.Persistence.Reduction.TraceCertificate

/-!
# Deterministic single-column pivot cancellation

This construction follows the inner earlier-column elimination in Zomorodian--Carlsson,
*Computing Persistent Homology* (https://geometry.stanford.edu/paper/zc-cph-04/zc-cph-04.pdf),
§§4.1--4.2, and Bauer, *Ripser* (https://arxiv.org/pdf/1908.02518), §3.1/Algorithm 1.
Indices are zero-based `Fin m`; an absent pivot is `none`, so row zero remains a real pivot.
The finite selector takes the least earlier matching source index. Its scalar is the negative
ratio of current target/source pivot entries over any field. The natural fuel is the initial
pivot height; the adequacy induction proves that exhaustion cannot mask a collision.
Shared-pivot source and target have equal homological degree under `LowersDegree`, and replay
propagates that invariant through the chronological trace. The terminal statement excludes
direct earlier-column pivot collisions. With unreduced earlier columns it does not establish
a minimal pivot modulo their span; the unreduced-prefix fixture in
`ColumnReductionExamples` shows the distinction.
-/

namespace TDA.Persistence.Reduction

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

private def earlierPivotSources
    (M : Matrix (Fin m) (Fin m) k) (j p : Fin m) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter
    (fun i => i < j ∧ columnPivot (M.col i) = some p)

private theorem mem_earlierPivotSources
    (M : Matrix (Fin m) (Fin m) k) (j p i : Fin m) :
    i ∈ earlierPivotSources M j p ↔ i < j ∧ columnPivot (M.col i) = some p := by
  simp [earlierPivotSources]

private def nextColumnOp
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) :
    Option (EarlierColumnOp m k) :=
  match columnPivot (M.col j) with
  | none => none
  | some p =>
      let s := earlierPivotSources M j p
      if h : s.Nonempty then
        let i := s.min' h
        have hi : i < j := by
          have himem : i ∈ s := Finset.min'_mem s h
          exact (Finset.mem_filter.mp himem).2.1
        some ⟨{ i := i, j := j, hij := ne_of_lt hi,
                 c := -(M p j / M p i) }, hi⟩
      else
        none

private def columnReductionTraceAux (j : Fin m) :
    ℕ → Matrix (Fin m) (Fin m) k → List (EarlierColumnOp m k)
  | 0, _ => []
  | fuel + 1, M =>
      match nextColumnOp M j with
      | none => []
      | some op => op :: columnReductionTraceAux j fuel (M * op.1.toMatrix)

/-- Deterministically cancel direct earlier-column pivot collisions at target `j`. -/
def columnReductionTrace
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) :
    List (EarlierColumnOp m k) :=
  columnReductionTraceAux j (pivotHeight (columnPivot (M.col j))) M

private theorem nextColumnOp_some_spec
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) (op : EarlierColumnOp m k)
    (hop : nextColumnOp M j = some op) :
    op.1.j = j ∧ ∃ p : Fin m,
      columnPivot (M.col j) = some p ∧
      columnPivot (M.col op.1.i) = some p ∧
      (∀ i : Fin m, i < j → columnPivot (M.col i) = some p → op.1.i ≤ i) ∧
      op.1.c = -(M p j / M p op.1.i) := by
  unfold nextColumnOp at hop
  split at hop
  · simp at hop
  · rename_i p hp
    by_cases h : (earlierPivotSources M j p).Nonempty
    · simp only [dif_pos h, Option.some.injEq] at hop
      subst op
      refine ⟨rfl, p, hp, ?_, ?_, rfl⟩
      · exact (mem_earlierPivotSources M j p _).mp
          (Finset.min'_mem _ h) |>.2
      · intro i hij hi
        have himem : i ∈ earlierPivotSources M j p :=
          (mem_earlierPivotSources M j p i).mpr ⟨hij, hi⟩
        exact Finset.min'_le _ i himem
    · simp [h] at hop

private theorem nextColumnOp_none_iff
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) :
    nextColumnOp M j = none ↔
      ∀ i : Fin m, i < j → ∀ p : Fin m,
        columnPivot (M.col i) = some p → columnPivot (M.col j) ≠ some p := by
  constructor
  · intro hn i hij p hi hj
    unfold nextColumnOp at hn
    rw [hj] at hn
    have hs : (earlierPivotSources M j p).Nonempty :=
      ⟨i, (mem_earlierPivotSources M j p i).mpr ⟨hij, hi⟩⟩
    simp [hs] at hn
  · intro h
    unfold nextColumnOp
    split
    · rfl
    · rename_i p hp
      have hs : ¬ (earlierPivotSources M j p).Nonempty := by
        rintro ⟨i, hi⟩
        have hi' := (mem_earlierPivotSources M j p i).mp hi
        exact h i hi'.1 p hi'.2 hp
      simp [hs]

private theorem nextColumnOp_height_lt
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) (op : EarlierColumnOp m k)
    (hop : nextColumnOp M j = some op) :
    pivotHeight (columnPivot ((M * op.1.toMatrix).col j)) <
      pivotHeight (columnPivot (M.col j)) := by
  obtain ⟨ht, p, hj, hi, _, hc⟩ := nextColumnOp_some_spec M j op hop
  have hij : op.1.i < j := ht ▸ op.2
  rw [Matrix.TransvectionStruct.toMatrix, ht, hc]
  exact pivotHeight_mul_transvection_lt M op.1.i j p hij hi hj

private theorem nextColumnOp_col_of_ne
    (M : Matrix (Fin m) (Fin m) k) (j q : Fin m) (hq : q ≠ j)
    (op : EarlierColumnOp m k) (hop : nextColumnOp M j = some op) :
    (M * op.1.toMatrix).col q = M.col q := by
  have ht := (nextColumnOp_some_spec M j op hop).1
  rw [Matrix.TransvectionStruct.toMatrix, ht]
  exact col_mul_transvection_of_ne M op.1.i j q op.1.c hq

private theorem nextColumnOp_degree
    (degree : Fin m → ℕ) (M : Matrix (Fin m) (Fin m) k)
    (j : Fin m) (hM : LowersDegree degree M)
    (op : EarlierColumnOp m k) (hop : nextColumnOp M j = some op) :
    degree op.1.i = degree op.1.j := by
  obtain ⟨ht, p, hj, hi, _, _⟩ := nextColumnOp_some_spec M j op hop
  rw [ht]
  exact degree_eq_of_common_pivot degree M hM op.1.i j p hi hj

private theorem nextColumnOp_lowersDegree
    (degree : Fin m → ℕ) (M : Matrix (Fin m) (Fin m) k)
    (j : Fin m) (hM : LowersDegree degree M)
    (op : EarlierColumnOp m k) (hop : nextColumnOp M j = some op) :
    LowersDegree degree (M * op.1.toMatrix) := by
  have hd := nextColumnOp_degree degree M j hM op hop
  have hs : TraceRespectsDegree degree [op] := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact hd
  simpa only [replay_cons, replay_nil] using replay_lowersDegree degree M [op] hM hs

private theorem budget_zero
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m)
    (h : pivotHeight (columnPivot (M.col j)) ≤ 0) :
    columnPivot (M.col j) = none :=
  (pivotHeight_eq_zero_iff _).mp (Nat.eq_zero_of_le_zero h)

private theorem budget_succ
    (newHeight oldHeight fuel : ℕ)
    (hstep : newHeight < oldHeight) (hbudget : oldHeight ≤ fuel + 1) :
    newHeight ≤ fuel := by omega

private theorem columnReductionTraceAux_target
    (j : Fin m) (fuel : ℕ) (M : Matrix (Fin m) (Fin m) k)
    (op : EarlierColumnOp m k) (hop : op ∈ columnReductionTraceAux j fuel M) :
    op.1.j = j := by
  induction fuel generalizing M with
  | zero => simp [columnReductionTraceAux] at hop
  | succ fuel ih =>
      unfold columnReductionTraceAux at hop
      split at hop
      · simp at hop
      · rename_i head hhead
        rcases List.mem_cons.mp hop with heq | htail
        · subst op
          exact (nextColumnOp_some_spec M j head hhead).1
        · exact ih _ htail

private theorem columnReductionTraceAux_col_of_ne
    (j q : Fin m) (hq : q ≠ j) (fuel : ℕ)
    (M : Matrix (Fin m) (Fin m) k) :
    (replay M (columnReductionTraceAux j fuel M)).col q = M.col q := by
  induction fuel generalizing M with
  | zero => rfl
  | succ fuel ih =>
      unfold columnReductionTraceAux
      split
      · rfl
      · rename_i op hop
        rw [replay_cons, ih]
        exact nextColumnOp_col_of_ne M j q hq op hop

private theorem columnReductionTraceAux_length_le
    (j : Fin m) (fuel : ℕ) (M : Matrix (Fin m) (Fin m) k) :
    (columnReductionTraceAux j fuel M).length ≤ fuel := by
  induction fuel generalizing M with
  | zero => simp [columnReductionTraceAux]
  | succ fuel ih =>
      unfold columnReductionTraceAux
      split
      · simp
      · rename_i op hop
        simpa only [List.length_cons, Nat.succ_eq_add_one] using
          Nat.add_le_add_right (ih (M * op.1.toMatrix)) 1

private theorem columnReductionTraceAux_terminal
    (j : Fin m) (fuel : ℕ) (M : Matrix (Fin m) (Fin m) k)
    (hbudget : pivotHeight (columnPivot (M.col j)) ≤ fuel) :
    ∀ i : Fin m, i < j → ∀ p : Fin m,
      columnPivot (M.col i) = some p →
        columnPivot ((replay M (columnReductionTraceAux j fuel M)).col j) ≠ some p := by
  induction fuel generalizing M with
  | zero =>
      have hz := budget_zero M j hbudget
      intro i hij p hi
      simp [columnReductionTraceAux, replay_nil, hz]
  | succ fuel ih =>
      intro i hij p hi
      have hne : i ≠ j := ne_of_lt hij
      unfold columnReductionTraceAux
      split
      · rename_i hnone
        rw [replay_nil]
        exact (nextColumnOp_none_iff M j).mp hnone i hij p hi
      · rename_i op hop
        rw [replay_cons]
        have hstep := nextColumnOp_height_lt M j op hop
        have hbudget' : pivotHeight
            (columnPivot ((M * op.1.toMatrix).col j)) ≤ fuel :=
          budget_succ _ _ _ hstep hbudget
        have hi' : columnPivot ((M * op.1.toMatrix).col i) = some p := by
          rw [nextColumnOp_col_of_ne M j i hne op hop]
          exact hi
        exact ih (M * op.1.toMatrix) hbudget' i hij p hi'

private theorem columnReductionTraceAux_respectsDegree
    (degree : Fin m → ℕ) (j : Fin m) (fuel : ℕ)
    (M : Matrix (Fin m) (Fin m) k) (hM : LowersDegree degree M) :
    TraceRespectsDegree degree (columnReductionTraceAux j fuel M) := by
  induction fuel generalizing M with
  | zero => simp [columnReductionTraceAux, TraceRespectsDegree]
  | succ fuel ih =>
      unfold columnReductionTraceAux
      split
      · simp [TraceRespectsDegree]
      · rename_i op hop
        have hhead := nextColumnOp_degree degree M j hM op hop
        have hM' := nextColumnOp_lowersDegree degree M j hM op hop
        have htail := ih (M * op.1.toMatrix) hM'
        intro x hx
        rcases List.mem_cons.mp hx with h | h
        · subst x; exact hhead
        · exact htail x h

private theorem columnReductionTraceAux_step_spec
    (j : Fin m) (fuel : ℕ) (M : Matrix (Fin m) (Fin m) k)
    (pre post : List (EarlierColumnOp m k)) (op : EarlierColumnOp m k)
    (htrace : columnReductionTraceAux j fuel M = pre ++ (op :: post)) :
    let A := replay M pre
    op.1.j = j ∧ ∃ p : Fin m,
      columnPivot (A.col j) = some p ∧
      columnPivot (A.col op.1.i) = some p ∧
      (∀ i : Fin m, i < j → columnPivot (A.col i) = some p → op.1.i ≤ i) ∧
      op.1.c = -(A p j / A p op.1.i) ∧
      pivotHeight (columnPivot ((A * op.1.toMatrix).col j)) <
        pivotHeight (columnPivot (A.col j)) := by
  induction fuel generalizing M pre with
  | zero => simp [columnReductionTraceAux] at htrace
  | succ fuel ih =>
      simp only [columnReductionTraceAux] at htrace
      split at htrace
      · simp at htrace
      · rename_i head hhead
        cases pre with
        | nil =>
            have heq : head = op := (List.cons.inj htrace).1
            subst op
            obtain ⟨ht, p, hj, hi, hmin, hc⟩ :=
              nextColumnOp_some_spec M j head hhead
            simpa only [replay_nil] using
              (show head.1.j = j ∧ ∃ p : Fin m,
                columnPivot (M.col j) = some p ∧
                columnPivot (M.col head.1.i) = some p ∧
                (∀ i : Fin m, i < j → columnPivot (M.col i) = some p → head.1.i ≤ i) ∧
                head.1.c = -(M p j / M p head.1.i) ∧
                pivotHeight (columnPivot ((M * head.1.toMatrix).col j)) <
                  pivotHeight (columnPivot (M.col j)) from
                ⟨ht, p, hj, hi, hmin, hc, nextColumnOp_height_lt M j head hhead⟩)
        | cons first rest =>
            have heq : head = first := (List.cons.inj htrace).1
            have htail : columnReductionTraceAux j fuel (M * head.1.toMatrix) =
                rest ++ (op :: post) := (List.cons.inj htrace).2
            subst first
            simpa only [replay_cons] using
              ih (M * head.1.toMatrix) rest htail

theorem columnReductionTrace_target
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m)
    (op : EarlierColumnOp m k) (hop : op ∈ columnReductionTrace M j) :
    op.1.j = j := by
  exact columnReductionTraceAux_target j _ M op hop

theorem columnReductionTrace_col_of_ne
    (M : Matrix (Fin m) (Fin m) k) (j q : Fin m) (hq : q ≠ j) :
    (replay M (columnReductionTrace M j)).col q = M.col q := by
  exact columnReductionTraceAux_col_of_ne j q hq _ M

theorem columnReductionTrace_step_spec
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m)
    (pre post : List (EarlierColumnOp m k)) (op : EarlierColumnOp m k)
    (htrace : columnReductionTrace M j = pre ++ (op :: post)) :
    let A := replay M pre
    op.1.j = j ∧ ∃ p : Fin m,
      columnPivot (A.col j) = some p ∧
      columnPivot (A.col op.1.i) = some p ∧
      (∀ i : Fin m, i < j → columnPivot (A.col i) = some p → op.1.i ≤ i) ∧
      op.1.c = -(A p j / A p op.1.i) ∧
      pivotHeight (columnPivot ((A * op.1.toMatrix).col j)) <
        pivotHeight (columnPivot (A.col j)) := by
  exact columnReductionTraceAux_step_spec j _ M pre post op htrace

theorem columnReductionTrace_length_le
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) :
    (columnReductionTrace M j).length ≤
      pivotHeight (columnPivot (M.col j)) := by
  exact columnReductionTraceAux_length_le j _ M

theorem columnReductionTrace_terminal
    (M : Matrix (Fin m) (Fin m) k) (j i : Fin m) (hij : i < j)
    (p : Fin m) (hi : columnPivot (M.col i) = some p) :
    columnPivot ((replay M (columnReductionTrace M j)).col j) ≠ some p := by
  exact columnReductionTraceAux_terminal j _ M (le_refl _) i hij p hi

theorem columnReductionTrace_eq_nil_iff
    (M : Matrix (Fin m) (Fin m) k) (j : Fin m) :
    columnReductionTrace M j = [] ↔
      ∀ i : Fin m, i < j → ∀ p : Fin m,
        columnPivot (M.col i) = some p → columnPivot (M.col j) ≠ some p := by
  constructor
  · intro h i hij p hi
    have ht := columnReductionTrace_terminal M j i hij p hi
    simpa only [h, replay_nil] using ht
  · intro h
    unfold columnReductionTrace
    cases hn : pivotHeight (columnPivot (M.col j)) with
    | zero => rfl
    | succ fuel =>
        simp only [columnReductionTraceAux]
        rw [(nextColumnOp_none_iff M j).mpr h]

theorem columnReductionTrace_respectsDegree
    (degree : Fin m → ℕ) (M : Matrix (Fin m) (Fin m) k) (j : Fin m)
    (hM : LowersDegree degree M) :
    TraceRespectsDegree degree (columnReductionTrace M j) := by
  exact columnReductionTraceAux_respectsDegree degree j _ M hM

#check @columnReductionTrace_target
#check @columnReductionTrace_col_of_ne
#check @columnReductionTrace_step_spec
#check @columnReductionTrace_length_le
#check @columnReductionTrace_terminal
#check @columnReductionTrace_eq_nil_iff
#check @columnReductionTrace_respectsDegree


/-! Explicit trust inventory: every named core declaration. -/
#print axioms earlierPivotSources
#print axioms mem_earlierPivotSources
#print axioms nextColumnOp
#print axioms columnReductionTraceAux
#print axioms columnReductionTrace
#print axioms nextColumnOp_some_spec
#print axioms nextColumnOp_none_iff
#print axioms nextColumnOp_height_lt
#print axioms nextColumnOp_col_of_ne
#print axioms nextColumnOp_degree
#print axioms nextColumnOp_lowersDegree
#print axioms budget_zero
#print axioms budget_succ
#print axioms columnReductionTraceAux_target
#print axioms columnReductionTraceAux_col_of_ne
#print axioms columnReductionTraceAux_length_le
#print axioms columnReductionTraceAux_terminal
#print axioms columnReductionTraceAux_respectsDegree
#print axioms columnReductionTraceAux_step_spec
#print axioms columnReductionTrace_target
#print axioms columnReductionTrace_col_of_ne
#print axioms columnReductionTrace_step_spec
#print axioms columnReductionTrace_length_le
#print axioms columnReductionTrace_terminal
#print axioms columnReductionTrace_eq_nil_iff
#print axioms columnReductionTrace_respectsDegree
end TDA.Persistence.Reduction
