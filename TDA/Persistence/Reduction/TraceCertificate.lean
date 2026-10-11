import TDA.Persistence.Reduction.Trace
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Certificates for graded finite column traces

The inverse is an explicit list of reverse-ordered, negated transvections. The supplied
trace is not assumed to have been selected by a reduction algorithm.
-/

namespace TDA.Persistence.Reduction

variable {m : ℕ} {k : Type*} [Field k]

/-- Invert an earlier-column operation without changing its source or target. -/
def inverseEarlierColumnOp (op : EarlierColumnOp m k) : EarlierColumnOp m k :=
  ⟨op.1.inv, by simpa only [Matrix.TransvectionStruct.inv_i,
    Matrix.TransvectionStruct.inv_j] using op.2⟩

/-- Undo a chronological trace in reverse order. -/
def inverseTrace (ops : List (EarlierColumnOp m k)) : List (EarlierColumnOp m k) :=
  ops.reverse.map inverseEarlierColumnOp

/-- The explicit change matrix of the inverse trace. -/
def traceChangeInv (ops : List (EarlierColumnOp m k)) : Matrix (Fin m) (Fin m) k :=
  traceChange (inverseTrace ops)

/-- Every supplied operation joins columns of the same homological dimension. -/
def TraceRespectsDegree (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) : Prop :=
  ∀ op ∈ ops, degree op.1.i = degree op.1.j

/-- Entry support of a boundary-shaped matrix, with natural successor rather than subtraction. -/
def LowersDegree (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ r c, M r c ≠ 0 → degree c = degree r + 1

/-- Two-sided, upper-unitriangular, degree-preserving change-of-basis data. -/
structure TraceChangeCertificate (degree : Fin m → ℕ)
    (V W : Matrix (Fin m) (Fin m) k) : Prop where
  mul_inv : V * W = 1
  inv_mul : W * V = 1
  upper : V.IsUpperTriangular
  diag : ∀ i, V i i = 1
  inv_upper : W.IsUpperTriangular
  inv_diag : ∀ i, W i i = 1
  degree_support : ∀ i j, degree i ≠ degree j → V i j = 0
  inv_degree_support : ∀ i j, degree i ≠ degree j → W i j = 0

theorem traceChangeInv_nil :
    traceChangeInv ([] : List (EarlierColumnOp m k)) = 1 := rfl

theorem traceChangeInv_cons (op : EarlierColumnOp m k)
    (ops : List (EarlierColumnOp m k)) :
    traceChangeInv (op :: ops) = traceChangeInv ops * op.1.inv.toMatrix := by
  simp [traceChangeInv, inverseTrace, inverseEarlierColumnOp, traceChange]

theorem traceChangeInv_append (xs ys : List (EarlierColumnOp m k)) :
    traceChangeInv (xs ++ ys) = traceChangeInv ys * traceChangeInv xs := by
  simp [traceChangeInv, inverseTrace, List.reverse_append, List.map_append,
    traceChange_append]

theorem traceChange_mul_traceChangeInv (ops : List (EarlierColumnOp m k)) :
    traceChange ops * traceChangeInv ops = 1 := by
  let L := ops.map Subtype.val
  have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod L
  simpa [traceChange, traceChangeInv, inverseTrace, inverseEarlierColumnOp,
    L, List.map_reverse, List.map_map, Function.comp_def] using h

theorem traceChangeInv_mul_traceChange (ops : List (EarlierColumnOp m k)) :
    traceChangeInv ops * traceChange ops = 1 := by
  let L := ops.map Subtype.val
  have h := Matrix.TransvectionStruct.reverse_inv_prod_mul_prod L
  simpa [traceChange, traceChangeInv, inverseTrace, inverseEarlierColumnOp,
    L, List.map_reverse, List.map_map, Function.comp_def] using h

private theorem single_upper (op : EarlierColumnOp m k) :
    op.1.toMatrix.IsUpperTriangular := by
  simpa only [Matrix.TransvectionStruct.toMatrix] using
    (Matrix.blockTriangular_transvection (b := id) (le_of_lt op.2) op.1.c)

theorem traceChange_isUpperTriangular (ops : List (EarlierColumnOp m k)) :
    (traceChange ops).IsUpperTriangular := by
  induction ops with
  | nil => simpa only [traceChange_nil] using (Matrix.blockTriangular_one (b := id) (R := k))
  | cons op ops ih =>
      rw [traceChange_cons]
      exact (single_upper op).mul ih

theorem traceChange_apply_diag (ops : List (EarlierColumnOp m k)) (i : Fin m) :
    traceChange ops i i = 1 := by
  induction ops with
  | nil => simp [traceChange_nil]
  | cons op ops ih =>
      rw [traceChange_cons, Matrix.TransvectionStruct.toMatrix]
      by_cases h : i = op.1.i
      · subst i
        rw [Matrix.transvection_mul_apply_same]
        have hz : traceChange ops op.1.j op.1.i = 0 :=
          traceChange_isUpperTriangular ops op.2
        simp [ih, hz]
      · rw [Matrix.transvection_mul_apply_of_ne (ha := h)]
        exact ih

theorem traceRespectsDegree_inverseTrace (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) (hops : TraceRespectsDegree degree ops) :
    TraceRespectsDegree degree (inverseTrace ops) := by
  intro op hop
  rcases List.mem_map.mp hop with ⟨old, hold, rfl⟩
  have hmem : old ∈ ops := List.mem_reverse.mp hold
  simpa [inverseEarlierColumnOp] using hops old hmem

private theorem single_degree_support (degree : Fin m → ℕ)
    (op : EarlierColumnOp m k) (hdegree : degree op.1.i = degree op.1.j)
    (r c : Fin m) (hrc : degree r ≠ degree c) : op.1.toMatrix r c = 0 := by
  simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply]
  rw [Matrix.single_apply]
  by_cases h : r = c
  · exact (hrc (congrArg degree h)).elim
  · simp only [Matrix.one_apply, if_neg h, zero_add]
    split
    · next heq =>
        rcases heq with ⟨rfl, rfl⟩
        exact (hrc hdegree).elim
    · rfl

private theorem degree_support_mul (degree : Fin m → ℕ)
    (A B : Matrix (Fin m) (Fin m) k)
    (hA : ∀ i j, degree i ≠ degree j → A i j = 0)
    (hB : ∀ i j, degree i ≠ degree j → B i j = 0)
    (r c : Fin m) (hrc : degree r ≠ degree c) : (A * B) r c = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hrq : degree r = degree q
  · have hqc : degree q ≠ degree c := by
      intro h
      exact hrc (hrq.trans h)
    simp [hB q c hqc]
  · simp [hA r q hrq]

theorem traceChange_apply_of_degree_ne (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) (hops : TraceRespectsDegree degree ops)
    (i j : Fin m) (hij : degree i ≠ degree j) :
    traceChange ops i j = 0 := by
  induction ops generalizing i j with
  | nil =>
      rw [traceChange_nil]
      have h : i ≠ j := by intro heq; exact hij (congrArg degree heq)
      simp [h]
  | cons op ops ih =>
      rw [traceChange_cons]
      apply degree_support_mul degree op.1.toMatrix (traceChange ops)
      · exact single_degree_support degree op (hops op (by simp))
      · intro r c h
        exact ih (by intro x hx; exact hops x (by simp [hx])) r c h
      · exact hij

theorem traceChange_certificate (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) (hops : TraceRespectsDegree degree ops) :
    TraceChangeCertificate degree (traceChange ops) (traceChangeInv ops) := by
  refine ⟨traceChange_mul_traceChangeInv ops, traceChangeInv_mul_traceChange ops,
    traceChange_isUpperTriangular ops, traceChange_apply_diag ops, ?_, ?_, ?_, ?_⟩
  · exact traceChange_isUpperTriangular (inverseTrace ops)
  · exact traceChange_apply_diag (inverseTrace ops)
  · exact traceChange_apply_of_degree_ne degree ops hops
  · exact traceChange_apply_of_degree_ne degree (inverseTrace ops)
      (traceRespectsDegree_inverseTrace degree ops hops)

theorem replay_inverseTrace (M : Matrix (Fin m) (Fin m) k)
    (ops : List (EarlierColumnOp m k)) :
    replay (replay M ops) (inverseTrace ops) = M := by
  rw [replay_eq_mul_traceChange, replay_eq_mul_traceChange, Matrix.mul_assoc]
  rw [← traceChangeInv, traceChange_mul_traceChangeInv, mul_one]

private theorem lowersDegree_mul_degree_support (degree : Fin m → ℕ)
    (M V : Matrix (Fin m) (Fin m) k) (hM : LowersDegree degree M)
    (hV : ∀ i j, degree i ≠ degree j → V i j = 0) :
    LowersDegree degree (M * V) := by
  intro r c hn
  by_contra hdegree
  have hz : (M * V) r c = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hMq : M r q = 0
    · simp [hMq]
    · have hqc : degree q ≠ degree c := by
        intro h
        exact hdegree (h.symm.trans (hM r q hMq))
      simp [hV q c hqc]
  exact hn hz

theorem replay_lowersDegree (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) (ops : List (EarlierColumnOp m k))
    (hM : LowersDegree degree M) (hops : TraceRespectsDegree degree ops) :
    LowersDegree degree (replay M ops) := by
  rw [replay_eq_mul_traceChange]
  exact lowersDegree_mul_degree_support degree M (traceChange ops) hM
    (traceChange_apply_of_degree_ne degree ops hops)

theorem degree_eq_of_common_pivot [DecidableEq k] (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) (hM : LowersDegree degree M)
    (i j p : Fin m) (hi : columnPivot (M.col i) = some p)
    (hj : columnPivot (M.col j) = some p) : degree i = degree j := by
  have hi' : M p i ≠ 0 := (columnPivot_some_iff (M.col i) p).mp hi |>.1
  have hj' : M p j ≠ 0 := (columnPivot_some_iff (M.col j) p).mp hj |>.1
  exact (hM p i hi').trans (hM p j hj').symm

/-! Complete local trust inventory, including private helpers and fixture data. -/
#print axioms inverseEarlierColumnOp
#print axioms inverseTrace
#print axioms traceChangeInv
#print axioms TraceRespectsDegree
#print axioms LowersDegree
#print axioms TraceChangeCertificate
#print axioms traceChangeInv_nil
#print axioms traceChangeInv_cons
#print axioms traceChangeInv_append
#print axioms traceChange_mul_traceChangeInv
#print axioms traceChangeInv_mul_traceChange
#print axioms single_upper
#print axioms traceChange_isUpperTriangular
#print axioms traceChange_apply_diag
#print axioms traceRespectsDegree_inverseTrace
#print axioms single_degree_support
#print axioms degree_support_mul
#print axioms traceChange_apply_of_degree_ne
#print axioms traceChange_certificate
#print axioms replay_inverseTrace
#print axioms lowersDegree_mul_degree_support
#print axioms replay_lowersDegree
#print axioms degree_eq_of_common_pivot
#print axioms TraceChangeCertificate.mk
#print axioms TraceChangeCertificate.rec
#print axioms TraceChangeCertificate.recOn
#print axioms TraceChangeCertificate.casesOn
#print axioms TraceChangeCertificate.mul_inv
#print axioms TraceChangeCertificate.inv_mul
#print axioms TraceChangeCertificate.upper
#print axioms TraceChangeCertificate.diag
#print axioms TraceChangeCertificate.inv_upper
#print axioms TraceChangeCertificate.inv_diag
#print axioms TraceChangeCertificate.degree_support
#print axioms TraceChangeCertificate.inv_degree_support

end TDA.Persistence.Reduction
