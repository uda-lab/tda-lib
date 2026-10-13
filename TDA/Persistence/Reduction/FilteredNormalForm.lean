import TDA.Persistence.Reduction.MatrixReduction
import TDA.Persistence.Interval
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Filtered normal form of a square-zero boundary

The reduced matrix is a right reduction `R = D * V`, not a new differential.  All
chain and homology statements below use the original differential `D`.
-/

namespace TDA.Persistence.Reduction

open OrderDual

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

/-- A right-reduced matrix has different pivots in different nonzero columns. -/
def DistinctPivots (R : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ i j p, columnPivot (R.col i) = some p →
    columnPivot (R.col j) = some p → i = j

/-- A column with a genuine pivot is a death column. -/
def IsDeath (R : Matrix (Fin m) (Fin m) k) (j : Fin m) : Prop :=
  (columnPivot (R.col j)).isSome

/-- A reduced linear relation has zero coefficient at every nonzero column. -/
theorem reduced_mulVec_kernel (R : Matrix (Fin m) (Fin m) k)
    (hpiv : DistinctPivots R) (a : Fin m → k) (hker : R.mulVec a = 0)
    (j : Fin m) (hj : IsDeath R j) : a j = 0 := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun q => IsDeath R q ∧ a q ≠ 0)
  have hS : S = ∅ := by
    by_contra hne
    have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨q, hqS, hmax⟩ :=
      Finset.exists_max_image S (fun q => pivotHeight (columnPivot (R.col q))) hnonempty
    have hq := (Finset.mem_filter.mp hqS).2
    obtain ⟨p, hp⟩ : ∃ p, columnPivot (R.col q) = some p := by
      cases h : columnPivot (R.col q) with
      | none => simp [IsDeath, h] at hq
      | some p => exact ⟨p, by simp [h]⟩
    have hrow : (∑ l : Fin m, R p l * a l) = 0 := by
      simpa [Matrix.mulVec_eq_sum, mul_comm] using congrFun hker p
    have hsum : (∑ l : Fin m, R p l * a l) = R p q * a q := by
      apply Finset.sum_eq_single q
      · intro l _ hlq
        by_cases hal : a l = 0
        · simp [hal]
        by_cases hpl : columnPivot (R.col l) = none
        · have hz : R p l = 0 := (columnPivot_none_iff (R.col l)).mp hpl p
          simp [hz]
        · obtain ⟨r, hr⟩ : ∃ r, columnPivot (R.col l) = some r := by
            cases h : columnPivot (R.col l) with
            | none => exact (hpl h).elim
            | some r => exact ⟨r, by simp [h]⟩
          have hlS : l ∈ S := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simp [IsDeath, hr, hal]⟩
          have hle : r ≤ p := by
            have hheight := hmax l hlS
            simp only [hr, hp, pivotHeight_some] at hheight
            exact Fin.le_iff_val_le_val.mpr (by omega)
          rcases hle.eq_or_lt with hEq | hLt
          · exact (hlq (hpiv l q r hr (hEq ▸ hp))).elim
          · have hz : R p l = 0 := ((columnPivot_some_iff (R.col l) r).mp hr).2 p hLt
            simp [hz]
      · intro hqno
        exact (hqno (Finset.mem_univ q)).elim
    have hnonzero : R p q * a q ≠ 0 :=
      mul_ne_zero ((columnPivot_some_iff (R.col q) p).mp hp).1 hq.2
    exact hnonzero (hsum.symm.trans hrow)
  by_contra ha
  have : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, ha⟩
  simpa [hS] using this

private theorem col_mul_eq_mulVec (A B : Matrix (Fin m) (Fin m) k) (j : Fin m) :
    (A * B).col j = A.mulVec (B.col j) := by
  ext r
  simp only [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec_apply_eq_sum]

/-- Strictly earlier rows are the only possible nonzero boundary entries. -/
def StrictBoundary (D : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ r c, D r c ≠ 0 → r < c

/-- The right-reduced boundary retains strict upper triangularity. -/
theorem reduced_strict (D V R : Matrix (Fin m) (Fin m) k)
    (hD : StrictBoundary D) (hV : V.IsUpperTriangular) (hR : R = D * V) :
    StrictBoundary R := by
  intro r c hrc
  rw [hR, Matrix.mul_apply] at hrc
  by_contra hnot
  have hle : c ≤ r := le_of_not_gt hnot
  have hz : (∑ q : Fin m, D r q * V q c) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    by_cases hDq : D r q = 0
    · simp [hDq]
    · have hrq := hD r q hDq
      have hqc : c < q := lt_of_le_of_lt hle hrq
      simp [hV hqc]
  exact hrc hz

/-- Degree zero is unaugmented: no degree-zero generator has a boundary. -/
theorem degree_zero_boundary (degree : Fin m → ℕ)
    (D : Matrix (Fin m) (Fin m) k) (hdegree : LowersDegree degree D)
    (j : Fin m) (hj : degree j = 0) : D.col j = 0 := by
  ext r
  by_contra hn
  have h := hdegree r j hn
  omega

/-- The inverse change of basis cannot introduce support above a pivot. -/
private theorem inverse_mulVec_above
    (W R : Matrix (Fin m) (Fin m) k) (hW : W.IsUpperTriangular)
    (j i l : Fin m) (hi : columnPivot (R.col j) = some i)
    (hli : i < l) : (W.mulVec (R.col j)) l = 0 := by
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hql : q < l
  · simp [hW hql]
  · have hiq : i < q := lt_of_lt_of_le hli (le_of_not_gt hql)
    have hz := ((columnPivot_some_iff (R.col j) i).mp hi).2 q hiq
    have hz' : R q j = 0 := hz
    simp [hz']

/-- The inverse change of basis retains the leading coefficient exactly. -/
private theorem inverse_mulVec_pivot
    (W R : Matrix (Fin m) (Fin m) k) (hW : W.IsUpperTriangular)
    (hdiag : ∀ i, W i i = 1) (j i : Fin m)
    (hi : columnPivot (R.col j) = some i) :
    (W.mulVec (R.col j)) i = R i j := by
  rw [Matrix.mulVec_apply_eq_sum]
  calc
    (∑ q : Fin m, W i q * (R.col j) q) = W i i * (R.col j) i := by
      apply Finset.sum_eq_single i
      · intro q _ hqi
        rcases lt_trichotomy q i with hqi' | hqi' | hqi'
        · simp [hW hqi']
        · exact (hqi hqi').elim
        · have hz : R q j = 0 := ((columnPivot_some_iff (R.col j) i).mp hi).2 q hqi'
          simp [hz]
      · intro h; exact (h (Finset.mem_univ i)).elim
    _ = R i j := by simp [hdiag]

/-- A pivot index cannot itself be a death column. The square-zero hypothesis is
used on `D`, and the inverse certificate preserves the top coordinate. -/
theorem pivot_column_zero (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    columnPivot (R.col i) = none := by
  let a := W.mulVec (R.col j)
  have hRW : R * W = D := by rw [hR, Matrix.mul_assoc, hcert.mul_inv, mul_one]
  have hDR : D * R = 0 := by rw [hR, ← Matrix.mul_assoc, hD2, zero_mul]
  have hker : R.mulVec a = 0 := by
    change R.mulVec (W.mulVec (R.col j)) = 0
    rw [Matrix.mulVec_mulVec, hRW, ← col_mul_eq_mulVec, hDR]
    rfl
  have hai : a i = R i j := inverse_mulVec_pivot W R hcert.inv_upper hcert.inv_diag j i hji
  have hnonzero : a i ≠ 0 := by
    rw [hai]
    exact ((columnPivot_some_iff (R.col j) i).mp hji).1
  by_contra hne
  have hdeath : IsDeath R i := by
    cases h : columnPivot (R.col i) with
    | none => exact (hne h).elim
    | some p => simpa only [IsDeath, h, Option.isSome_some]
  exact hnonzero (reduced_mulVec_kernel R hpiv a hker i hdeath)

/-- A row appearing as a pivot in the reduced matrix. -/
def IsPivot (R : Matrix (Fin m) (Fin m) k) (i : Fin m) : Prop :=
  ∃ j, columnPivot (R.col j) = some i

/-- A zero reduced column that is not paired to a death column. -/
def IsEssential (R : Matrix (Fin m) (Fin m) k) (i : Fin m) : Prop :=
  columnPivot (R.col i) = none ∧ ¬ IsPivot R i

/-- The chosen death index for a pivot row. Injectivity of pivots makes it unique. -/
noncomputable def deathOfPivot (R : Matrix (Fin m) (Fin m) k)
    (i : Fin m) (hi : IsPivot R i) : Fin m := Classical.choose hi

theorem deathOfPivot_spec (R : Matrix (Fin m) (Fin m) k)
    (i : Fin m) (hi : IsPivot R i) :
    columnPivot (R.col (deathOfPivot R i hi)) = some i := Classical.choose_spec hi

theorem deathOfPivot_unique (R : Matrix (Fin m) (Fin m) k)
    (hpiv : DistinctPivots R) (i j : Fin m)
    (hi : IsPivot R i) (hj : columnPivot (R.col j) = some i) :
    deathOfPivot R i hi = j :=
  hpiv _ _ i (deathOfPivot_spec R i hi) hj

theorem pivot_not_death (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (i : Fin m) (hi : IsPivot R i) :
    columnPivot (R.col i) = none := by
  obtain ⟨j, hj⟩ := hi
  exact pivot_column_zero degree D R V W hD2 hR hcert hpiv j i hj

/-- Every index has exactly one of the pivot, death, or essential roles. -/
theorem pivot_death_essential (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (i : Fin m) :
    (IsPivot R i ∧ ¬ IsDeath R i ∧ ¬ IsEssential R i) ∨
    (IsDeath R i ∧ ¬ IsPivot R i ∧ ¬ IsEssential R i) ∨
    (IsEssential R i ∧ ¬ IsPivot R i ∧ ¬ IsDeath R i) := by
  classical
  by_cases hp : IsPivot R i
  · left
    have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv i hp
    refine ⟨hp, ?_, ?_⟩
    · simp [IsDeath, hz]
    · simp [IsEssential, hp]
  · right
    by_cases hd : IsDeath R i
    · left
      refine ⟨hd, hp, ?_⟩
      intro he
      have hz := he.1
      unfold IsDeath at hd
      rw [hz] at hd
      cases hd
    · right
      have hz : columnPivot (R.col i) = none := by
        cases h : columnPivot (R.col i) with
        | none => rfl
        | some j => exact (hd (by simp [IsDeath, h])).elim
      exact ⟨⟨hz, hp⟩, hp, hd⟩

/-- Every nonzero reduced column is strictly earlier-supported and degree-lowering. -/
theorem pivot_order_degree (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (hdegree : LowersDegree degree R)
    (j i : Fin m) (hji : columnPivot (R.col j) = some i) :
    i < j ∧ degree j = degree i + 1 := by
  have hnonzero := ((columnPivot_some_iff (R.col j) i).mp hji).1
  exact ⟨hstrict i j hnonzero, hdegree i j hnonzero⟩

/-- The normalized reduced column at a pivot row; all other columns retain `V`. -/
noncomputable def normalColumn (R V : Matrix (Fin m) (Fin m) k)
    (i : Fin m) : Fin m → k := by
  classical
  exact if hi : IsPivot R i then
    (R i (deathOfPivot R i hi))⁻¹ • R.col (deathOfPivot R i hi)
  else V.col i

/-- Matrix whose columns are the fixed cycle/death basis. -/
noncomputable def normalMatrix (R V : Matrix (Fin m) (Fin m) k) :
    Matrix (Fin m) (Fin m) k := Matrix.of (fun r i => normalColumn R V i r)

theorem normalColumn_pivot (R V : Matrix (Fin m) (Fin m) k)
    (i : Fin m) (hi : IsPivot R i) :
    normalColumn R V i =
      (R i (deathOfPivot R i hi))⁻¹ • R.col (deathOfPivot R i hi) := by
  classical
  simp [normalColumn, dif_pos hi]

theorem normalColumn_nonpivot (R V : Matrix (Fin m) (Fin m) k)
    (i : Fin m) (hi : ¬ IsPivot R i) : normalColumn R V i = V.col i := by
  classical
  simp [normalColumn, dif_neg hi]

theorem normalMatrix_upper (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) : (normalMatrix R V).IsUpperTriangular := by
  intro r i hir
  by_cases hi : IsPivot R i
  · rw [show normalMatrix R V r i = normalColumn R V i r from rfl,
      normalColumn_pivot R V i hi]
    have hz : R r (deathOfPivot R i hi) = 0 :=
      ((columnPivot_some_iff (R.col (deathOfPivot R i hi)) i).mp
        (deathOfPivot_spec R i hi)).2 r hir
    simp [hz]
  · rw [show normalMatrix R V r i = normalColumn R V i r from rfl,
      normalColumn_nonpivot R V i hi]
    exact hV hir

theorem normalMatrix_diag (R V : Matrix (Fin m) (Fin m) k)
    (hV : ∀ i, V i i = 1) (i : Fin m) : normalMatrix R V i i = 1 := by
  by_cases hi : IsPivot R i
  · rw [show normalMatrix R V i i = normalColumn R V i i from rfl,
      normalColumn_pivot R V i hi]
    have hn : R i (deathOfPivot R i hi) ≠ 0 :=
      ((columnPivot_some_iff (R.col (deathOfPivot R i hi)) i).mp
        (deathOfPivot_spec R i hi)).1
    simpa using inv_mul_cancel₀ hn
  · rw [show normalMatrix R V i i = normalColumn R V i i from rfl,
      normalColumn_nonpivot R V i hi]
    exact hV i

theorem normalMatrix_degree (degree : Fin m → ℕ)
    (R V : Matrix (Fin m) (Fin m) k)
    (hdegree : LowersDegree degree R)
    (hV : ∀ r i, degree r ≠ degree i → V r i = 0)
    (r i : Fin m) (hri : degree r ≠ degree i) :
    normalMatrix R V r i = 0 := by
  by_cases hi : IsPivot R i
  · rw [show normalMatrix R V r i = normalColumn R V i r from rfl,
      normalColumn_pivot R V i hi]
    by_cases hz : R r (deathOfPivot R i hi) = 0
    · simp [hz]
    · have hd := hdegree r (deathOfPivot R i hi) hz
      have hi' := hdegree i (deathOfPivot R i hi)
        (((columnPivot_some_iff (R.col (deathOfPivot R i hi)) i).mp
          (deathOfPivot_spec R i hi)).1)
      exact (hri (Nat.add_right_cancel (hd.symm.trans hi'))).elim
  · rw [show normalMatrix R V r i = normalColumn R V i r from rfl,
      normalColumn_nonpivot R V i hi]
    exact hV r i hri

/-- The normal matrix has determinant one over every coefficient field. -/
theorem normalMatrix_det (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1) :
    (normalMatrix R V).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (normalMatrix_upper R V hV)]
  simp [normalMatrix_diag R V hdiag]

/-- A fixed inverse exists without requiring a second reduction algorithm. -/
theorem normalMatrix_isUnit (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1) :
    IsUnit (normalMatrix R V) := by
  rw [Matrix.isUnit_iff_isUnit_det, normalMatrix_det R V hV hdiag]
  exact isUnit_one

theorem normalMatrix_mul_inv (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1) :
    normalMatrix R V * (normalMatrix R V)⁻¹ = 1 := by
  letI : Invertible (normalMatrix R V) :=
    (normalMatrix_isUnit R V hV hdiag).nonempty_invertible.some
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (normalMatrix_isUnit R V hV hdiag))

theorem normalMatrix_inv_mul (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1) :
    (normalMatrix R V)⁻¹ * normalMatrix R V = 1 := by
  letI : Invertible (normalMatrix R V) :=
    (normalMatrix_isUnit R V hV hdiag).nonempty_invertible.some
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (normalMatrix_isUnit R V hV hdiag))

theorem normalMatrix_inv_upper (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1) :
    ((normalMatrix R V)⁻¹).IsUpperTriangular := by
  letI : Invertible (normalMatrix R V) :=
    (normalMatrix_isUnit R V hV hdiag).nonempty_invertible.some
  exact Matrix.blockTriangular_inv_of_blockTriangular (normalMatrix_upper R V hV)

theorem normalMatrix_inv_degree (degree : Fin m → ℕ)
    (R V : Matrix (Fin m) (Fin m) k)
    (hVupper : V.IsUpperTriangular) (hVdiag : ∀ i, V i i = 1)
    (hdegree : LowersDegree degree R)
    (hVdegree : ∀ r i, degree r ≠ degree i → V r i = 0)
    (r i : Fin m) (hri : degree r ≠ degree i) :
    (normalMatrix R V)⁻¹ r i = 0 := by
  letI : Invertible (normalMatrix R V) :=
    (normalMatrix_isUnit R V hVupper hVdiag).nonempty_invertible.some
  rcases lt_or_gt_of_ne hri with hlt | hgt
  · have hblock : (normalMatrix R V).BlockTriangular (toDual ∘ degree) := by
      intro x y hxy
      exact normalMatrix_degree degree R V hdegree hVdegree x y (ne_of_lt hxy)
    exact (Matrix.blockTriangular_inv_of_blockTriangular hblock) hlt
  · have hblock : (normalMatrix R V).BlockTriangular degree := by
      intro x y hxy
      exact normalMatrix_degree degree R V hdegree hVdegree x y (ne_of_gt hxy)
    exact (Matrix.blockTriangular_inv_of_blockTriangular hblock) hgt

/-- A vector belongs to the coordinate prefix of length `t`. -/
def PrefixSupported (t : ℕ) (x : Fin m → k) : Prop :=
  ∀ i, t ≤ i.val → x i = 0

theorem upper_mulVec_prefix (A : Matrix (Fin m) (Fin m) k)
    (hA : A.IsUpperTriangular) (t : ℕ) (x : Fin m → k)
    (hx : PrefixSupported t x) : PrefixSupported t (A.mulVec x) := by
  intro i hi
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q.val < t
  · have hqi : q < i := by exact Fin.lt_def.mpr (by omega)
    simp [hA hqi]
  · simp [hx q (by omega)]

theorem normalMatrix_prefix (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (t : ℕ) (x : Fin m → k)
    (hx : PrefixSupported t x) :
    PrefixSupported t ((normalMatrix R V).mulVec x) :=
  upper_mulVec_prefix _ (normalMatrix_upper R V hV) t x hx

theorem normalMatrix_inv_prefix (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1)
    (t : ℕ) (x : Fin m → k) (hx : PrefixSupported t x) :
    PrefixSupported t (((normalMatrix R V)⁻¹).mulVec x) :=
  upper_mulVec_prefix _ (normalMatrix_inv_upper R V hV hdiag) t x hx

theorem strict_boundary_prefix (D : Matrix (Fin m) (Fin m) k)
    (hD : StrictBoundary D) (t : ℕ) (x : Fin m → k)
    (hx : PrefixSupported t x) : PrefixSupported t (D.mulVec x) := by
  apply upper_mulVec_prefix
  · intro i j hji
    by_contra hn
    exact (lt_asymm hji) (hD i j hn)
  · exact hx

/-- The reducer supplies the generic normal-form inputs for every graded
square-zero, strictly upper-triangular boundary. -/
theorem matrixReductionTrace_normalForm_input (degree : Fin m → ℕ)
    (D : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hstrict : StrictBoundary D)
    (hdegree : LowersDegree degree D) :
    let ops := matrixReductionTrace D
    let R := replay D ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = D * V ∧ TraceChangeCertificate degree V W ∧
      LowersDegree degree R ∧ StrictBoundary R ∧ DistinctPivots R ∧
      (∀ j i, columnPivot (R.col j) = some i → columnPivot (R.col i) = none) := by
  let ops := matrixReductionTrace D
  let R := replay D ops
  let V := traceChange ops
  let W := traceChangeInv ops
  obtain ⟨hR, _, _, _, _, _, _, _, _, hcert, hRdegree⟩ :=
    matrixReductionTrace_graded_certificate degree D hdegree
  have hpiv : DistinctPivots R := by
    intro i j p hi hj
    exact matrixReductionTrace_pivots_distinct D i j p hi hj
  exact ⟨hR, hcert, hRdegree, reduced_strict D V R hstrict hcert.upper hR,
    hpiv, fun j i hji => pivot_column_zero degree D R V W hD2 hR hcert hpiv j i hji⟩

/-- Every paired normal column is a cycle in the original differential. -/
theorem normalColumn_pivot_boundary (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (i : Fin m) (hi : IsPivot R i) :
    D.mulVec (normalColumn R V i) = 0 := by
  rw [normalColumn_pivot R V i hi, Matrix.mulVec_smul]
  have hDR : D * R = 0 := by rw [hR, ← Matrix.mul_assoc, hD2, zero_mul]
  rw [← col_mul_eq_mulVec, hDR]
  ext r
  simp

/-- A zero reduced column gives a cycle in the fixed normal basis. -/
theorem normalColumn_zero_boundary (D R V : Matrix (Fin m) (Fin m) k)
    (hR : R = D * V) (i : Fin m)
    (hzero : columnPivot (R.col i) = none)
    (hi : ¬ IsPivot R i) : D.mulVec (normalColumn R V i) = 0 := by
  rw [normalColumn_nonpivot R V i hi, ← col_mul_eq_mulVec, ← hR]
  exact (columnPivot_none_iff (R.col i)).mp hzero |> fun he => by
    ext r; exact he r

/-- A death column kills exactly its normalized paired cycle, with its
actual nonzero coefficient in the original differential. -/
theorem normalColumn_death_boundary (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    D.mulVec (normalColumn R V j) = R i j • normalColumn R V i := by
  have hnot : ¬ IsPivot R j := by
    intro hp
    have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv j hp
    rw [hz] at hji
    cases hji
  rw [normalColumn_nonpivot R V j hnot, ← col_mul_eq_mulVec, ← hR]
  have hpair : IsPivot R i := ⟨j, hji⟩
  rw [normalColumn_pivot R V i hpair,
    deathOfPivot_unique R hpiv i j hpair hji]
  ext r
  simp only [Pi.smul_apply, smul_eq_mul]
  have hn : R i j ≠ 0 := ((columnPivot_some_iff (R.col j) i).mp hji).1
  field_simp

/-- The sparse differential expressed in the fixed normal basis. -/
noncomputable def normalDifferential (R : Matrix (Fin m) (Fin m) k) :
    Matrix (Fin m) (Fin m) k :=
  Matrix.of fun r j => if columnPivot (R.col j) = some r then R r j else 0

theorem normalDifferential_zero_column (R : Matrix (Fin m) (Fin m) k)
    (j : Fin m) (hj : columnPivot (R.col j) = none) :
    (normalDifferential R).col j = 0 := by
  ext r
  simp [normalDifferential, hj]

theorem normalDifferential_pair_column (R : Matrix (Fin m) (Fin m) k)
    (j i : Fin m) (hji : columnPivot (R.col j) = some i) :
    (normalDifferential R).col j = R i j • Pi.single i (1 : k) := by
  ext r
  by_cases hri : r = i
  · subst r
    simp [normalDifferential, hji]
  · simp [normalDifferential, hji, hri, Ne.symm hri]

/-- The new basis conjugates the *original* boundary to the sparse pair
differential. It does not assert that `R` itself is square-zero. -/
theorem normalMatrix_conjugates_boundary (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) :
    D * normalMatrix R V = normalMatrix R V * normalDifferential R := by
  ext r j
  let B := normalMatrix R V
  let N := normalDifferential R
  have hleft : (D * B).col j = D.mulVec (normalColumn R V j) := by
    rw [col_mul_eq_mulVec]
    rfl
  have hright : (B * N).col j = B.mulVec (N.col j) := col_mul_eq_mulVec B N j
  cases h : columnPivot (R.col j) with
  | none =>
      have hl : (D * B).col j = 0 := by
        rw [hleft]
        by_cases hp : IsPivot R j
        · exact normalColumn_pivot_boundary degree D R V W hD2 hR j hp
        · exact normalColumn_zero_boundary D R V hR j h hp
      have hr : (B * N).col j = 0 := by
        rw [hright, normalDifferential_zero_column R j h]
        simp
      exact congrFun (hl.trans hr.symm) r
  | some i =>
      have hl : (D * B).col j = R i j • normalColumn R V i := by
        rw [hleft]
        exact normalColumn_death_boundary degree D R V W hD2 hR hcert hpiv j i h
      have hr : (B * N).col j = R i j • normalColumn R V i := by
        rw [hright, normalDifferential_pair_column R j i h]
        ext q
        simp [Matrix.mulVec_apply_eq_sum, Matrix.col_apply, Finset.sum_ite_eq', B,
          normalMatrix, Pi.single_apply]
        ring
      exact congrFun (hl.trans hr.symm) r

/-- At a pivot row, the sparse boundary reads the coefficient of its unique
death generator. -/
theorem normalDifferential_mulVec_pivot (R : Matrix (Fin m) (Fin m) k)
    (hpiv : DistinctPivots R) (x : Fin m → k)
    (i : Fin m) (hi : IsPivot R i) :
    (normalDifferential R).mulVec x i =
      R i (deathOfPivot R i hi) * x (deathOfPivot R i hi) := by
  rw [Matrix.mulVec_apply_eq_sum]
  calc
    (∑ j : Fin m, normalDifferential R i j * x j) =
        normalDifferential R i (deathOfPivot R i hi) * x (deathOfPivot R i hi) := by
      apply Finset.sum_eq_single (deathOfPivot R i hi)
      · intro j _ hj
        by_cases hji : columnPivot (R.col j) = some i
        · exact (hj (deathOfPivot_unique R hpiv i j hi hji).symm).elim
        · simp [normalDifferential, hji]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    _ = R i (deathOfPivot R i hi) * x (deathOfPivot R i hi) := by
      simp [normalDifferential, deathOfPivot_spec R i hi]

/-- Rows that are not pivots vanish identically in the sparse differential. -/
theorem normalDifferential_mulVec_nonpivot (R : Matrix (Fin m) (Fin m) k)
    (x : Fin m → k) (i : Fin m) (hi : ¬ IsPivot R i) :
    (normalDifferential R).mulVec x i = 0 := by
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  have hji : columnPivot (R.col j) ≠ some i := fun h => hi ⟨j, h⟩
  simp [normalDifferential, hji]

/-- A vector is a cycle precisely when each death coordinate is zero. -/
theorem normalDifferential_cycle_iff (R : Matrix (Fin m) (Fin m) k)
    (hpiv : DistinctPivots R) (x : Fin m → k) :
    (normalDifferential R).mulVec x = 0 ↔
      ∀ j, IsDeath R j → x j = 0 := by
  constructor
  · intro hx j hj
    obtain ⟨i, hji⟩ : ∃ i, columnPivot (R.col j) = some i := by
      cases h : columnPivot (R.col j) with
      | none => simp [IsDeath, h] at hj
      | some i => exact ⟨i, by simp⟩
    have hi : IsPivot R i := ⟨j, hji⟩
    have he := congrFun hx i
    rw [normalDifferential_mulVec_pivot R hpiv x i hi,
      deathOfPivot_unique R hpiv i j hi hji] at he
    exact (mul_eq_zero.mp he).resolve_left
      (((columnPivot_some_iff (R.col j) i).mp hji).1)
  · intro hx
    ext i
    by_cases hi : IsPivot R i
    · rw [normalDifferential_mulVec_pivot R hpiv x i hi]
      have hd : IsDeath R (deathOfPivot R i hi) := by
        simp [IsDeath, deathOfPivot_spec R i hi]
      simp [hx _ hd]
    · rw [normalDifferential_mulVec_nonpivot R x i hi]
      rfl

/-- A normal boundary has no coordinate outside the pivot rows. -/
theorem normalDifferential_image_nonpivot (R : Matrix (Fin m) (Fin m) k)
    (x : Fin m → k) (i : Fin m) (hi : ¬ IsPivot R i) :
    (normalDifferential R).mulVec x i = 0 :=
  normalDifferential_mulVec_nonpivot R x i hi

theorem normalDifferential_strict (R : Matrix (Fin m) (Fin m) k)
    (hR : StrictBoundary R) : StrictBoundary (normalDifferential R) := by
  intro r j hn
  have hrj : R r j ≠ 0 := by
    intro hz
    simp [normalDifferential, hz] at hn
  exact hR r j hrj

theorem normalDifferential_degree (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k)
    (hR : LowersDegree degree R) :
    LowersDegree degree (normalDifferential R) := by
  intro r j hn
  have hrj : R r j ≠ 0 := by
    intro hz
    simp [normalDifferential, hz] at hn
  exact hR r j hrj

/-- A pivot row is active at stage `t` exactly from its birth through the
last stage before its paired death generator enters. -/
def PivotAlive (R : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (i : Fin m) : Prop :=
  ∃ hi : IsPivot R i, i.val < t ∧ t ≤ (deathOfPivot R i hi).val

/-- An essential cycle is active from its birth through the final stage. -/
def EssentialAlive (R : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (i : Fin m) : Prop :=
  IsEssential R i ∧ i.val < t

/-- The explicit surviving coordinates of degree `p` at stage `t`. -/
def AliveCoordinate (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (i : Fin m) : Prop :=
  degree i = p ∧ (PivotAlive R t i ∨ EssentialAlive R t i)

/-- Finite-interval encoding uses stage `i+1` for the birth at index `i`
and stage `j+1` for the death at index `j`. -/
noncomputable def pairedInterval (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    TDA.Persistence.FiniteInterval (m + 1) :=
  ⟨i.val + 1, j.val + 1,
    by have hn := ((columnPivot_some_iff (R.col j) i).mp hji).1
       exact Nat.add_lt_add_right (hstrict i j hn) 1,
    by omega⟩

/-- A surviving birth has terminal sentinel `m+1`, a finite observation
boundary rather than an infinite tail. -/
noncomputable def essentialInterval (i : Fin m) :
    TDA.Persistence.FiniteInterval (m + 1) :=
  ⟨i.val + 1, m + 1, by omega, le_refl _⟩

theorem pairedInterval_alive_iff (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) (t : Fin (m + 1)) :
    (pairedInterval R hstrict j i hji).alive t ↔
      i.val < t.val ∧ t.val ≤ j.val := by
  simp only [TDA.Persistence.FiniteInterval.alive, pairedInterval]
  omega

theorem essentialInterval_alive_iff (i : Fin m) (t : Fin (m + 1)) :
    (essentialInterval i).alive t ↔ i.val < t.val := by
  simp only [TDA.Persistence.FiniteInterval.alive, essentialInterval]
  omega

theorem essentialAlive_iff_essentialInterval (R : Matrix (Fin m) (Fin m) k)
    (i : Fin m) (hi : IsEssential R i) (t : Fin (m + 1)) :
    EssentialAlive R t.val i ↔ (essentialInterval i).alive t := by
  simp [EssentialAlive, hi, essentialInterval_alive_iff]

/-- Exact homological grading of a coordinate vector. -/
def Homogeneous (degree : Fin m → ℕ) (p : ℕ) (x : Fin m → k) : Prop :=
  ∀ i, degree i ≠ p → x i = 0

theorem lowers_mulVec_homogeneous (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) (hM : LowersDegree degree M)
    (p : ℕ) (x : Fin m → k) (hx : Homogeneous degree (p + 1) x) :
    Homogeneous degree p (M.mulVec x) := by
  intro r hr
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases h : M r j = 0
  · simp [h]
  · have hj : degree j ≠ p + 1 := by
      intro he
      exact hr (Nat.add_right_cancel ((hM r j h).symm.trans he))
    simp [hx j hj]

/-- Cycles in the normal coordinates at a filtration prefix. -/
def NormalCycle (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Prop :=
  PrefixSupported t x ∧ Homogeneous degree p x ∧
    (normalDifferential R).mulVec x = 0

/-- Actual boundaries in the normal coordinates at a prefix. -/
def NormalBoundary (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Prop :=
  ∃ y : Fin m → k, PrefixSupported t y ∧ Homogeneous degree (p + 1) y ∧
    (normalDifferential R).mulVec y = x

theorem pivotAlive_iff (R : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (i : Fin m) (hi : IsPivot R i) :
    PivotAlive R t i ↔ i.val < t ∧ t ≤ (deathOfPivot R i hi).val := by
  constructor
  · rintro ⟨hi', hlt, hdeath⟩
    simpa only [Subsingleton.elim hi' hi] using (show i.val < t ∧
      t ≤ (deathOfPivot R i hi').val from ⟨hlt, hdeath⟩)
  · intro h
    exact ⟨hi, h⟩

/-- Each pivot coordinate is present exactly on the corresponding finite
interval, with birth `i+1` and death `j+1`. -/
theorem pivotAlive_iff_pairedInterval (R : Matrix (Fin m) (Fin m) k)
    (hstrict : StrictBoundary R) (i : Fin m) (hi : IsPivot R i)
    (t : Fin (m + 1)) :
    PivotAlive R t.val i ↔
      (pairedInterval R hstrict (deathOfPivot R i hi) i
        (deathOfPivot_spec R i hi)).alive t := by
  rw [pivotAlive_iff R t.val i hi,
    pairedInterval_alive_iff R hstrict _ i (deathOfPivot_spec R i hi) t]

/-- Boundaries have zero coefficient on every live homology coordinate. -/
theorem normalBoundary_alive_zero (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpivR : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalBoundary degree R p t x)
    (i : Fin m) (hi : AliveCoordinate degree R p t i) : x i = 0 := by
  obtain ⟨y, hy, _, rfl⟩ := hx
  rcases hi.2 with hp | he
  · obtain ⟨hpivot, _, hdeath⟩ := hp
    rw [normalDifferential_mulVec_pivot R hpivR y i hpivot]
    simp [hy _ hdeath]
  · exact normalDifferential_mulVec_nonpivot R y i he.1.2

/-- The canonical representative keeps precisely the live homology coordinates. -/
noncomputable def aliveRepresentative (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Fin m → k := by
  classical
  exact fun i => if AliveCoordinate degree R p t i then x i else 0

/-- To erase an expired pivot coordinate, divide it by its actual pivot
coefficient and place it at the paired death generator. -/
noncomputable def expiredPreimage (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Fin m → k :=
  fun j => match h : columnPivot (R.col j) with
    | none => 0
    | some i => if j.val < t ∧ degree i = p then x i / R i j else 0

theorem expiredPreimage_prefix (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    PrefixSupported t (expiredPreimage degree R p t x) := by
  intro j hj
  unfold expiredPreimage
  split
  · rfl
  · simp [show ¬j.val < t by omega]

theorem expiredPreimage_degree (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k)
    (hdegree : LowersDegree degree R) (p t : ℕ) (x : Fin m → k) :
    Homogeneous degree (p + 1) (expiredPreimage degree R p t x) := by
  intro j hj
  unfold expiredPreimage
  split
  · rfl
  · next i hji =>
      by_cases h : j.val < t ∧ degree i = p
      · have hn : R i j ≠ 0 := ((columnPivot_some_iff (R.col j) i).mp hji).1
        exact (hj ((hdegree i j hn).trans (congrArg (· + 1) h.2))).elim
      · simp [h]

theorem expiredPreimage_pivot (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (x : Fin m → k) (j i : Fin m)
    (hji : columnPivot (R.col j) = some i) :
    expiredPreimage degree R p t x j =
      if j.val < t ∧ degree i = p then x i / R i j else 0 := by
  unfold expiredPreimage
  split
  · next h => rw [h] at hji; cases hji
  · next i' h =>
      have he : i' = i := Option.some.inj (h.symm.trans hji)
      subst i'
      rfl

theorem expiredBoundary_pivot (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p t : ℕ) (x : Fin m → k) (i : Fin m) (hi : IsPivot R i) :
    (normalDifferential R).mulVec (expiredPreimage degree R p t x) i =
      if (deathOfPivot R i hi).val < t ∧ degree i = p then x i else 0 := by
  rw [normalDifferential_mulVec_pivot R hpiv _ i hi,
    expiredPreimage_pivot degree R p t x _ i (deathOfPivot_spec R i hi)]
  by_cases h : (deathOfPivot R i hi).val < t ∧ degree i = p
  · simp only [if_pos h]
    have hn : R i (deathOfPivot R i hi) ≠ 0 :=
      ((columnPivot_some_iff (R.col (deathOfPivot R i hi)) i).mp
        (deathOfPivot_spec R i hi)).1
    field_simp [hn]
  · simp [h]

theorem normalDifferential_sq_zero (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (x : Fin m → k) :
    (normalDifferential R).mulVec ((normalDifferential R).mulVec x) = 0 := by
  apply (normalDifferential_cycle_iff R hpiv _).2
  intro j hj
  have hn : ¬ IsPivot R j := by
    intro hp
    have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv j hp
    simp [IsDeath, hz] at hj
  exact normalDifferential_mulVec_nonpivot R x j hn

theorem normalBoundary_isCycle (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalBoundary degree R p t x) :
    (normalDifferential R).mulVec x = 0 := by
  obtain ⟨y, _, _, rfl⟩ := hx
  exact normalDifferential_sq_zero degree D R V W hD2 hR hcert hpiv y

theorem aliveRepresentative_prefix (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    PrefixSupported t (aliveRepresentative degree R p t x) := by
  intro i hi
  have hnot : ¬ AliveCoordinate degree R p t i := by
    rintro ⟨_, hp | he⟩
    · exact (not_lt_of_ge hi) hp.2.1
    · exact (not_lt_of_ge hi) he.2
  simp [aliveRepresentative, hnot]

theorem aliveRepresentative_degree (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    Homogeneous degree p (aliveRepresentative degree R p t x) := by
  intro i hi
  have hnot : ¬ AliveCoordinate degree R p t i := fun h => hi h.1
  simp [aliveRepresentative, hnot]

theorem aliveRepresentative_cycle (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ) (x : Fin m → k) :
    NormalCycle degree R p t (aliveRepresentative degree R p t x) := by
  refine ⟨aliveRepresentative_prefix degree R p t x,
    aliveRepresentative_degree degree R p t x, ?_⟩
  apply (normalDifferential_cycle_iff R hpiv _).2
  intro j hj
  have hnot : ¬ AliveCoordinate degree R p t j := by
    rintro ⟨_, hp | he⟩
    · obtain ⟨hp', _, _⟩ := hp
      have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv j hp'
      simp [IsDeath, hz] at hj
    · simp [IsEssential, IsDeath, he.1.1] at hj
  simp [aliveRepresentative, hnot]

/-- Every graded prefix cycle is a live-coordinate representative plus the
boundary of the explicit expired-coordinate preimage. -/
theorem normalCycle_decompose (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalCycle degree R p t x) :
    x = aliveRepresentative degree R p t x +
      (normalDifferential R).mulVec (expiredPreimage degree R p t x) := by
  obtain ⟨hprefix, hhom, hcycle⟩ := hx
  have hdeath := (normalDifferential_cycle_iff R hpiv x).mp hcycle
  ext i
  simp only [Pi.add_apply]
  by_cases hp : IsPivot R i
  · have hz := pivot_not_death degree D R V W hD2 hR hcert hpiv i hp
    have ha := (pivotAlive_iff R t i hp)
    rw [expiredBoundary_pivot degree R hpiv p t x i hp]
    by_cases hlt : i.val < t
    · by_cases hdeg : degree i = p
      · by_cases hd : (deathOfPivot R i hp).val < t
        · have hn : ¬ AliveCoordinate degree R p t i := by
            rintro ⟨_, hb | he⟩
            · have hge := (ha.mp hb).2
              omega
            · exact he.1.2 hp
          simp [aliveRepresentative, hn, hd, hdeg]
        · have halive : AliveCoordinate degree R p t i :=
            ⟨hdeg, Or.inl ((ha).2 ⟨hlt, by omega⟩)⟩
          simp [aliveRepresentative, halive, hd]
      · have hxi : x i = 0 := hhom i hdeg
        have hn : ¬ AliveCoordinate degree R p t i := fun h => hdeg h.1
        simp [aliveRepresentative, hn, hdeg, hxi]
    · have hxi : x i = 0 := hprefix i (by omega)
      have hn : ¬ AliveCoordinate degree R p t i := by
        rintro ⟨_, hb | he⟩
        · exact (not_lt_of_ge (by omega : t ≤ i.val)) (ha.mp hb).1
        · exact (not_lt_of_ge (by omega : t ≤ i.val)) he.2
      simp [aliveRepresentative, hn, hlt, hxi]
  · rw [normalDifferential_mulVec_nonpivot R _ i hp]
    by_cases hd : IsDeath R i
    · have hxi := hdeath i hd
      have hn : ¬ AliveCoordinate degree R p t i := by
        rintro ⟨_, hb | he⟩
        · exact hp hb.1
        · have hz := he.1.1
          simp [IsDeath, hz] at hd
      simp [aliveRepresentative, hn, hxi]
    · have hz : columnPivot (R.col i) = none := by
        cases h : columnPivot (R.col i) with
        | none => rfl
        | some q => exact (hd (by simp [IsDeath, h])).elim
      have he : IsEssential R i := ⟨hz, hp⟩
      by_cases hlt : i.val < t
      · by_cases hdeg : degree i = p
        · have ha : AliveCoordinate degree R p t i := ⟨hdeg, Or.inr ⟨he, hlt⟩⟩
          simp [aliveRepresentative, ha]
        · have hxi : x i = 0 := hhom i hdeg
          have hn : ¬ AliveCoordinate degree R p t i := fun h => hdeg h.1
          simp [aliveRepresentative, hn, hxi]
      · have hxi : x i = 0 := hprefix i (by omega)
        have hn : ¬ AliveCoordinate degree R p t i := by
          rintro ⟨_, hb | he'⟩
          · exact hp hb.1
          · exact hlt he'.2
        simp [aliveRepresentative, hn, hxi]

/-- Two cycles represent the same prefix-homology class exactly when all
live coordinates agree. In particular, this is an explicit family of
homology bases, not merely a stagewise dimension calculation. -/
theorem normalCycle_boundary_iff_live_zero (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hdegreeR : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : Fin m → k) (hx : NormalCycle degree R p t x) :
    NormalBoundary degree R p t x ↔
      aliveRepresentative degree R p t x = 0 := by
  constructor
  · intro hb
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi,
        normalBoundary_alive_zero degree R hpiv p t x hb i hi]
    · simp [aliveRepresentative, hi]
  · intro hzero
    have hd := normalCycle_decompose degree D R V W hD2 hR hcert hpiv p t x hx
    refine ⟨expiredPreimage degree R p t x,
      expiredPreimage_prefix degree R p t x,
      expiredPreimage_degree degree R hdegreeR p t x, ?_⟩
    simpa [hzero] using hd.symm

/-- Prefix inclusion is the identity on a cycle's original coordinate vector. -/
theorem normalCycle_prefix_inclusion (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (x : Fin m → k) (hx : NormalCycle degree R p s x) :
    NormalCycle degree R p t x := by
  refine ⟨?_, hx.2.1, hx.2.2⟩
  intro i hi
  exact hx.1 i (le_trans hst hi)

theorem normalBoundary_prefix_inclusion (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (x : Fin m → k) (hx : NormalBoundary degree R p s x) :
    NormalBoundary degree R p t x := by
  obtain ⟨y, hy, hg, he⟩ := hx
  exact ⟨y, fun i hi => hy i (le_trans hst hi), hg, he⟩

/-- The coefficient map of every prefix inclusion is coordinate projection:
live generators survive unchanged, and expired ones go to zero. -/
theorem aliveRepresentative_transition (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (x : Fin m → k) (hx : PrefixSupported s x) :
    aliveRepresentative degree R p t (aliveRepresentative degree R p s x) =
      aliveRepresentative degree R p t x := by
  ext i
  by_cases ht : AliveCoordinate degree R p t i
  · by_cases his : i.val < s
    · have hs : AliveCoordinate degree R p s i := by
        refine ⟨ht.1, ?_⟩
        rcases ht.2 with hp | he
        · obtain ⟨hi, _, hdeath⟩ := hp
          exact Or.inl ⟨hi, his, le_trans hst hdeath⟩
        · exact Or.inr ⟨he.1, his⟩
      simp [aliveRepresentative, ht, hs]
    · have hxi : x i = 0 := hx i (by omega)
      simp [aliveRepresentative, ht, hxi]
  · simp [aliveRepresentative, ht]

/-- The coordinate-level interval map sends a live pivot or essential class
identically while it remains live, and sends it to zero after death. -/
theorem aliveRepresentative_single_survives (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (i : Fin m) (hi : AliveCoordinate degree R p t i) :
    aliveRepresentative degree R p t ((Pi.single i (1 : k)) : Fin m → k) =
      Pi.single i (1 : k) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [aliveRepresentative, hi]
  · simp [aliveRepresentative, Pi.single_apply, hji]

theorem aliveRepresentative_single_dies (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (i : Fin m) (hi : ¬ AliveCoordinate degree R p t i) :
    aliveRepresentative degree R p t ((Pi.single i (1 : k)) : Fin m → k) = 0 := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [aliveRepresentative, hi]
  · simp [aliveRepresentative, Pi.single_apply, hji]

/-- The graded cycles of a prefix form a vector subspace. -/
noncomputable def normalCycleSpace (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    Submodule k (Fin m → k) where
  carrier := {x | NormalCycle degree R p t x}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i _; rfl
    · intro i _; rfl
    · simp
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [hx.1 i hi, hy.1 i hi]
    · intro i hi
      simp [hx.2.1 i hi, hy.2.1 i hi]
    · rw [Matrix.mulVec_add, hx.2.2, hy.2.2, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [hx.1 i hi]
    · intro i hi
      simp [hx.2.1 i hi]
    · rw [Matrix.mulVec_smul, hx.2.2, smul_zero]

/-- Vectors supported exactly on the currently live homology coordinates. -/
noncomputable def aliveSpace (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    Submodule k (Fin m → k) where
  carrier := {x | ∀ i, ¬ AliveCoordinate degree R p t i → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

theorem aliveRepresentative_mem_aliveSpace (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) :
    aliveRepresentative degree R p t x ∈ aliveSpace degree R p t := by
  intro i hi
  simp [aliveRepresentative, hi]

/-- Every live-coordinate vector already is its own representative. -/
theorem aliveRepresentative_of_mem (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (x : Fin m → k) (hx : x ∈ aliveSpace degree R p t) :
    aliveRepresentative degree R p t x = x := by
  ext i
  by_cases hi : AliveCoordinate degree R p t i
  · simp [aliveRepresentative, hi]
  · simp [aliveRepresentative, hi, hx i hi]

/-- Projection from cycles to their explicit homology coordinates. -/
noncomputable def cycleLiveMap (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    normalCycleSpace degree R p t →ₗ[k] aliveSpace degree R p t where
  toFun x := ⟨aliveRepresentative degree R p t x.1,
    aliveRepresentative_mem_aliveSpace degree R p t x.1⟩
  map_add' x y := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]
  map_smul' c x := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]

theorem cycleLiveMap_surjective (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    Function.Surjective (cycleLiveMap degree R p t) := by
  intro y
  have hycycle : NormalCycle degree R p t y.1 := by
    have h := aliveRepresentative_cycle degree D R V W hD2 hR hcert hpiv p t y.1
    rwa [aliveRepresentative_of_mem degree R p t y.1 y.2] at h
  refine ⟨⟨y.1, hycycle⟩, ?_⟩
  apply Subtype.ext
  exact aliveRepresentative_of_mem degree R p t y.1 y.2

/-- The quotient of cycles by the kernel of live-coordinate projection is
the degree-`p` homology at this prefix. The next theorem identifies that
kernel with actual boundaries. -/
abbrev normalHomology (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) : Type _ :=
  (normalCycleSpace degree R p t) ⧸
    LinearMap.ker (cycleLiveMap degree R p t)

noncomputable def normalHomologyEquivAlive (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    normalHomology degree R p t ≃ₗ[k] aliveSpace degree R p t :=
  (cycleLiveMap degree R p t).quotKerEquivOfSurjective
    (cycleLiveMap_surjective degree D R V W hD2 hR hcert hpiv p t)

theorem normalHomology_kernel_eq_boundaries (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hdegreeR : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : normalCycleSpace degree R p t) :
    x ∈ LinearMap.ker (cycleLiveMap degree R p t) ↔
      NormalBoundary degree R p t x.1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    change aliveRepresentative degree R p t x.1 = 0 at hv
    exact (normalCycle_boundary_iff_live_zero degree D R V W hD2 hR hcert
      hdegreeR hpiv p t x.1 x.2).mpr hv
  · intro h
    apply Subtype.ext
    exact (normalCycle_boundary_iff_live_zero degree D R V W hD2 hR hcert
      hdegreeR hpiv p t x.1 x.2).mp h

theorem aliveSpace_eq_spanSubset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    aliveSpace degree R p t =
      Pi.spanSubset k {i | AliveCoordinate degree R p t i} := by
  ext x
  exact (Pi.mem_spanSubset_iff (R := k)).symm

theorem aliveSpace_prefix (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ)
    (x : aliveSpace degree R p t) : PrefixSupported t x.1 := by
  rw [← aliveRepresentative_of_mem degree R p t x.1 x.2]
  exact aliveRepresentative_prefix degree R p t x.1

/-- The coefficient map between homology bases at `s ≤ t`. -/
noncomputable def aliveSpaceMap (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    aliveSpace degree R p s →ₗ[k] aliveSpace degree R p t where
  toFun x := ⟨aliveRepresentative degree R p t x.1,
    aliveRepresentative_mem_aliveSpace degree R p t x.1⟩
  map_add' x y := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]
  map_smul' c x := by
    apply Subtype.ext
    ext i
    by_cases hi : AliveCoordinate degree R p t i
    · simp [aliveRepresentative, hi]
    · simp [aliveRepresentative, hi]

theorem aliveSpaceMap_id (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    aliveSpaceMap degree R p t t = LinearMap.id := by
  ext x i
  change aliveRepresentative degree R p t x.1 i = x.1 i
  rw [aliveRepresentative_of_mem degree R p t x.1 x.2]

theorem aliveSpaceMap_comp (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t u : ℕ)
    (hst : s ≤ t) (htu : t ≤ u) :
    (aliveSpaceMap degree R p t u).comp (aliveSpaceMap degree R p s t) =
      aliveSpaceMap degree R p s u := by
  ext x i
  change aliveRepresentative degree R p u (aliveRepresentative degree R p t x.1) i =
    aliveRepresentative degree R p u x.1 i
  have hx : PrefixSupported t x.1 := by
    intro j hj
    exact aliveSpace_prefix degree R p s x j (le_trans hst hj)
  exact congrFun (aliveRepresentative_transition degree R p t u htu x.1 hx) i

/-- The actual normal-coordinate homology map is transported through the
proved quotient/basis equivalences. -/
noncomputable def normalHomologyMap (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) :
    normalHomology degree R p s →ₗ[k] normalHomology degree R p t :=
  ((normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t).symm.toLinearMap).comp
    ((aliveSpaceMap degree R p s t).comp
      (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s).toLinearMap)

/-- The homology transition is exactly the coordinate projection of the
underlying inclusion of prefix cycles. -/
theorem normalHomologyMap_mk (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) (hst : s ≤ t)
    (x : normalCycleSpace degree R p s) :
    (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t)
      (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t
        (Submodule.Quotient.mk x)) =
      ⟨aliveRepresentative degree R p t x.1,
        aliveRepresentative_mem_aliveSpace degree R p t x.1⟩ := by
  simp only [normalHomologyMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  have hsource :
      (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s)
        (Submodule.Quotient.mk x) = cycleLiveMap degree R p s x := by
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ x
  rw [hsource]
  exact aliveRepresentative_transition degree R p s t hst x.1 x.2.1

/-- Coordinates surviving both endpoints of a structure map. -/
def Survivor (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (i : Fin m) : Prop :=
  AliveCoordinate degree R p s i ∧ AliveCoordinate degree R p t i

noncomputable def survivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => Survivor degree R p s t i)

theorem aliveSpaceMap_range_iff (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ)
    (y : aliveSpace degree R p t) :
    y ∈ LinearMap.range (aliveSpaceMap degree R p s t) ↔
      ∀ i, ¬ AliveCoordinate degree R p s i → y.1 i = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ i hi
    have hx : x.1 i = 0 := x.2 i hi
    simp [aliveSpaceMap, aliveRepresentative, hx]
  · intro hy
    let x : aliveSpace degree R p s := ⟨y.1, hy⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact aliveRepresentative_of_mem degree R p t y.1 y.2

noncomputable def aliveSpaceMap_rangeEquiv (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    LinearMap.range (aliveSpaceMap degree R p s t) ≃ₗ[k]
      Pi.spanSubset k {i | Survivor degree R p s t i} where
  toFun y := ⟨y.1.1, by
    rw [Pi.mem_spanSubset_iff]
    intro i hi
    by_cases hs : AliveCoordinate degree R p s i
    · have ht : ¬ AliveCoordinate degree R p t i := by
        intro ht
        exact hi ⟨hs, ht⟩
      exact y.1.2 i ht
    · exact (aliveSpaceMap_range_iff degree R p s t y.1).mp y.2 i hs⟩
  invFun y :=
    ⟨⟨y.1, by
      intro i hi
      apply (Pi.mem_spanSubset_iff.mp y.2) i
      intro h
      exact hi h.2⟩, by
      apply (aliveSpaceMap_range_iff degree R p s t _).mpr
      intro i hi
      apply (Pi.mem_spanSubset_iff.mp y.2) i
      intro h
      exact hi h.1⟩
  left_inv := by intro y; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro y; apply Subtype.ext; rfl
  map_add' := by intro x y; apply Subtype.ext; rfl
  map_smul' := by intro c x; apply Subtype.ext; rfl

/-- The rank of the coefficient map is the number of coordinates live at
both stages. -/
theorem aliveSpaceMap_rank (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    Module.finrank k (LinearMap.range (aliveSpaceMap degree R p s t)) =
      (survivorFinset degree R p s t).card := by
  classical
  rw [(aliveSpaceMap_rangeEquiv degree R p s t).finrank_eq, Pi.dim_spanSubset]
  have hset : ({i | Survivor degree R p s t i} : Set (Fin m)) =
      ↑(survivorFinset degree R p s t) := by
    ext i
    simp [survivorFinset]
  rw [hset]
  simp

theorem survivor_iff_pairs_or_essential (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t)
    (i : Fin m) :
    Survivor degree R p s t i ↔
      (∃ hi : IsPivot R i, degree i = p ∧ i.val < s ∧
        t ≤ (deathOfPivot R i hi).val) ∨
      (IsEssential R i ∧ degree i = p ∧ i.val < s) := by
  constructor
  · rintro ⟨hs, ht⟩
    rcases hs.2 with hp | he
    · have htp : PivotAlive R t i := by
        rcases ht.2 with htp | hte
        · exact htp
        · exact (hte.1.2 hp.1).elim
      left
      refine ⟨hp.1, hs.1, hp.2.1, ?_⟩
      exact (pivotAlive_iff R t i hp.1).mp htp |>.2
    · right
      exact ⟨he.1, hs.1, he.2⟩
  · rintro (⟨hi, hdeg, hbirth, hdeath⟩ | ⟨he, hdeg, hbirth⟩)
    · have hs : PivotAlive R s i :=
        (pivotAlive_iff R s i hi).mpr ⟨hbirth, le_trans hst hdeath⟩
      have ht : PivotAlive R t i :=
        (pivotAlive_iff R t i hi).mpr ⟨lt_of_lt_of_le hbirth hst, hdeath⟩
      exact ⟨⟨hdeg, Or.inl hs⟩, ⟨hdeg, Or.inl ht⟩⟩
    · exact ⟨⟨hdeg, Or.inr ⟨he, hbirth⟩⟩,
        ⟨hdeg, Or.inr ⟨he, lt_of_lt_of_le hbirth hst⟩⟩⟩

noncomputable def pairSurvivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ∃ hi : IsPivot R i, degree i = p ∧
    i.val < s ∧ t ≤ (deathOfPivot R i hi).val)

noncomputable def essentialSurvivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => IsEssential R i ∧ degree i = p ∧ i.val < s)

noncomputable def deathSurvivorFinset (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun j => ∃ i, columnPivot (R.col j) = some i ∧
    degree i = p ∧ i.val < s ∧ t ≤ j.val)

theorem survivorFinset_partition (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) (hst : s ≤ t) :
    survivorFinset degree R p s t =
      pairSurvivorFinset degree R p s t ∪
        essentialSurvivorFinset degree R p s := by
  classical
  ext i
  simp only [survivorFinset, pairSurvivorFinset, essentialSurvivorFinset,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact survivor_iff_pairs_or_essential degree R p s t hst i

theorem pair_essential_disjoint (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p s t : ℕ) :
    Disjoint (pairSurvivorFinset degree R p s t)
      (essentialSurvivorFinset degree R p s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hp he
  have hp' := (Finset.mem_filter.mp hp).2
  have he' := (Finset.mem_filter.mp he).2
  exact he'.1.2 hp'.choose

theorem pair_survivor_card_eq_death_card (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p s t : ℕ) :
    (pairSurvivorFinset degree R p s t).card =
      (deathSurvivorFinset degree R p s t).card := by
  classical
  apply Finset.card_bij
    (fun i hi => deathOfPivot R i ((Finset.mem_filter.mp hi).2.choose))
  · intro i hi
    have hpair := (Finset.mem_filter.mp hi).2
    obtain ⟨hp, hdeg, hbirth, hdeath⟩ := hpair
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, i, deathOfPivot_spec R i hp,
      hdeg, hbirth, hdeath⟩
  · intro i hi q hq heq
    let hip : IsPivot R i := (Finset.mem_filter.mp hi).2.choose
    let hqp : IsPivot R q := (Finset.mem_filter.mp hq).2.choose
    have hi' := deathOfPivot_spec R i hip
    have hq' := deathOfPivot_spec R q hqp
    have hp : some i = some q := by
      calc
        some i = columnPivot (R.col (deathOfPivot R i hip)) := hi'.symm
        _ = columnPivot (R.col (deathOfPivot R q hqp)) := by
          rw [heq]
        _ = some q := hq'
    exact Option.some.inj hp
  · intro j hj
    obtain ⟨i, hji, hdeg, hbirth, hdeath⟩ :=
      (Finset.mem_filter.mp hj).2
    have hi : IsPivot R i := ⟨j, hji⟩
    have hj' := deathOfPivot_unique R hpiv i j hi hji
    have himem : i ∈ pairSurvivorFinset degree R p s t := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hi, hdeg, hbirth, by rwa [hj']⟩
    refine ⟨i, himem, ?_⟩
    exact deathOfPivot_unique R hpiv i j
      (Finset.mem_filter.mp himem).2.choose hji

/-- Rank count in the issue's death-column/essential-column indexing.
The two sums count occurrences, so identical endpoint values retain multiplicity. -/
theorem aliveSpaceMap_rank_formula (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p s t : ℕ) (hst : s ≤ t) :
    Module.finrank k (LinearMap.range (aliveSpaceMap degree R p s t)) =
      (deathSurvivorFinset degree R p s t).card +
        (essentialSurvivorFinset degree R p s).card := by
  rw [aliveSpaceMap_rank, survivorFinset_partition degree R p s t hst,
    Finset.card_union_of_disjoint (pair_essential_disjoint degree R p s t),
    pair_survivor_card_eq_death_card degree R hpiv p s t]

theorem normalHomologyMap_transport (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ)
    (x : normalHomology degree R p s) :
    (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t)
      (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t x) =
    aliveSpaceMap degree R p s t
      ((normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s) x) := by
  simp [normalHomologyMap]

noncomputable def normalHomologyMap_rangeEquiv (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) :
    LinearMap.range (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t) ≃ₗ[k]
      LinearMap.range (aliveSpaceMap degree R p s t) where
  toFun y := ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t) y.1,
    by
      obtain ⟨x, hx⟩ := y.2
      refine ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s) x, ?_⟩
      rw [← hx]
      exact (normalHomologyMap_transport degree D R V W hD2 hR hcert hpiv p s t x).symm⟩
  invFun y := ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t).symm y.1,
    by
      obtain ⟨x, hx⟩ := y.2
      refine ⟨(normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p s).symm x, ?_⟩
      apply (normalHomologyEquivAlive degree D R V W hD2 hR hcert hpiv p t).injective
      rw [normalHomologyMap_transport, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact hx⟩
  left_inv := by
    intro y
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ _
  right_inv := by
    intro y
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ _
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro c x
    apply Subtype.ext
    simp

/-- Structure-map rank on the actual quotient homology spaces. -/
theorem normalHomologyMap_rank_formula (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (p s t : ℕ) (hst : s ≤ t) :
    Module.finrank k (LinearMap.range
      (normalHomologyMap degree D R V W hD2 hR hcert hpiv p s t)) =
      (deathSurvivorFinset degree R p s t).card +
        (essentialSurvivorFinset degree R p s).card := by
  rw [(normalHomologyMap_rangeEquiv degree D R V W hD2 hR hcert hpiv p s t).finrank_eq]
  exact aliveSpaceMap_rank_formula degree R hpiv p s t hst

/-- A matrix that does not mix grades preserves every homogeneous vector. -/
theorem grade_preserving_mulVec (degree : Fin m → ℕ)
    (A : Matrix (Fin m) (Fin m) k)
    (hA : ∀ r i, degree r ≠ degree i → A r i = 0)
    (p : ℕ) (x : Fin m → k) (hx : Homogeneous degree p x) :
    Homogeneous degree p (A.mulVec x) := by
  intro r hr
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : degree i = p
  · have hri : degree r ≠ degree i := by rw [hi]; exact hr
    simp [hA r i hri]
  · simp [hx i hi]

theorem normalMatrix_mulVec_inv (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1)
    (x : Fin m → k) :
    (normalMatrix R V).mulVec (((normalMatrix R V)⁻¹).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, normalMatrix_mul_inv R V hV hdiag]
  simp

theorem normalMatrix_inv_mulVec (R V : Matrix (Fin m) (Fin m) k)
    (hV : V.IsUpperTriangular) (hdiag : ∀ i, V i i = 1)
    (x : Fin m → k) :
    ((normalMatrix R V)⁻¹).mulVec ((normalMatrix R V).mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, normalMatrix_inv_mul R V hV hdiag]
  simp

theorem normalMatrix_boundary_mulVec (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hpiv : DistinctPivots R) (x : Fin m → k) :
    D.mulVec ((normalMatrix R V).mulVec x) =
      (normalMatrix R V).mulVec ((normalDifferential R).mulVec x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    normalMatrix_conjugates_boundary degree D R V W hD2 hR hcert hpiv]

/-- Cycles and boundaries here use the original matrix `D`. -/
def OriginalCycle (degree : Fin m → ℕ)
    (D : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Prop :=
  PrefixSupported t x ∧ Homogeneous degree p x ∧ D.mulVec x = 0

def OriginalBoundary (degree : Fin m → ℕ)
    (D : Matrix (Fin m) (Fin m) k) (p t : ℕ) (x : Fin m → k) : Prop :=
  ∃ y : Fin m → k, PrefixSupported t y ∧ Homogeneous degree (p + 1) y ∧
    D.mulVec y = x

theorem normalCycle_iff_originalCycle (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) (x : Fin m → k) :
    NormalCycle degree R p t x ↔
      OriginalCycle degree D p t ((normalMatrix R V).mulVec x) := by
  constructor
  · rintro ⟨hpre, hgrade, hcycle⟩
    refine ⟨normalMatrix_prefix R V hcert.upper t x hpre,
      grade_preserving_mulVec degree _
        (normalMatrix_degree degree R V
          hRdegree hcert.degree_support) p x hgrade, ?_⟩
    rw [normalMatrix_boundary_mulVec degree D R V W hD2 hR hcert hpiv, hcycle]
    simp
  · rintro ⟨hpre, hgrade, hcycle⟩
    have hpre' : PrefixSupported t x := by
      have h := normalMatrix_inv_prefix R V hcert.upper hcert.diag t
        ((normalMatrix R V).mulVec x) hpre
      rwa [normalMatrix_inv_mulVec R V hcert.upper hcert.diag x] at h
    have hgrade' : Homogeneous degree p x := by
      have h := grade_preserving_mulVec degree _
        (normalMatrix_inv_degree degree R V hcert.upper hcert.diag
          hRdegree hcert.degree_support) p _ hgrade
      rwa [normalMatrix_inv_mulVec R V hcert.upper hcert.diag x] at h
    refine ⟨hpre', hgrade', ?_⟩
    have h := normalMatrix_boundary_mulVec degree D R V W hD2 hR hcert hpiv x
    rw [hcycle] at h
    have hz : (normalMatrix R V).mulVec ((normalDifferential R).mulVec x) = 0 :=
      h.symm
    have hz' := congrArg (fun y => ((normalMatrix R V)⁻¹).mulVec y) hz
    rw [normalMatrix_inv_mulVec R V hcert.upper hcert.diag] at hz'
    simpa using hz'

theorem normalBoundary_iff_originalBoundary (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) (x : Fin m → k) :
    NormalBoundary degree R p t x ↔
      OriginalBoundary degree D p t ((normalMatrix R V).mulVec x) := by
  constructor
  · rintro ⟨y, hpre, hgrade, hboundary⟩
    refine ⟨(normalMatrix R V).mulVec y,
      normalMatrix_prefix R V hcert.upper t y hpre,
      grade_preserving_mulVec degree _
        (normalMatrix_degree degree R V hRdegree hcert.degree_support)
          (p + 1) y hgrade, ?_⟩
    rw [normalMatrix_boundary_mulVec degree D R V W hD2 hR hcert hpiv,
      hboundary]
  · rintro ⟨z, hpre, hgrade, hboundary⟩
    let y := ((normalMatrix R V)⁻¹).mulVec z
    have hypre : PrefixSupported t y :=
      normalMatrix_inv_prefix R V hcert.upper hcert.diag t z hpre
    have hygrade : Homogeneous degree (p + 1) y :=
      grade_preserving_mulVec degree _
        (normalMatrix_inv_degree degree R V hcert.upper hcert.diag
          hRdegree hcert.degree_support) (p + 1) z hgrade
    refine ⟨y, hypre, hygrade, ?_⟩
    have hBy : (normalMatrix R V).mulVec y = z :=
      normalMatrix_mulVec_inv R V hcert.upper hcert.diag z
    have hconj := normalMatrix_boundary_mulVec degree D R V W hD2 hR hcert hpiv y
    rw [hBy, hboundary] at hconj
    have hz := congrArg (fun v => ((normalMatrix R V)⁻¹).mulVec v) hconj
    rw [normalMatrix_inv_mulVec R V hcert.upper hcert.diag,
      normalMatrix_inv_mulVec R V hcert.upper hcert.diag] at hz
    exact hz.symm

/-- Cycles in the original basis and original differential. -/
noncomputable def originalCycleSpace (degree : Fin m → ℕ)
    (D : Matrix (Fin m) (Fin m) k) (p t : ℕ) :
    Submodule k (Fin m → k) where
  carrier := {x | OriginalCycle degree D p t x}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i _; rfl
    · intro i _; rfl
    · simp
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; simp [hx.1 i hi, hy.1 i hi]
    · intro i hi; simp [hx.2.1 i hi, hy.2.1 i hi]
    · rw [Matrix.mulVec_add, hx.2.2, hy.2.2, add_zero]
  smul_mem' := by
    intro c x hx
    refine ⟨?_, ?_, ?_⟩
    · intro i hi; simp [hx.1 i hi]
    · intro i hi; simp [hx.2.1 i hi]
    · rw [Matrix.mulVec_smul, hx.2.2, smul_zero]

/-- One homogeneous, prefix-preserving change of basis at every stage. -/
noncomputable def cycleBasisEquiv (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    normalCycleSpace degree R p t ≃ₗ[k] originalCycleSpace degree D p t where
  toFun x := ⟨(normalMatrix R V).mulVec x.1,
    (normalCycle_iff_originalCycle degree D R V W hD2 hR hcert hRdegree
      hpiv p t x.1).mp x.2⟩
  invFun y := ⟨((normalMatrix R V)⁻¹).mulVec y.1, by
    have h := (normalCycle_iff_originalCycle degree D R V W hD2 hR hcert
      hRdegree hpiv p t (((normalMatrix R V)⁻¹).mulVec y.1)).mpr
    apply h
    rw [normalMatrix_mulVec_inv R V hcert.upper hcert.diag]
    exact y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact normalMatrix_inv_mulVec R V hcert.upper hcert.diag x.1
  right_inv := by
    intro y
    apply Subtype.ext
    exact normalMatrix_mulVec_inv R V hcert.upper hcert.diag y.1
  map_add' := by
    intro x y
    apply Subtype.ext
    change (normalMatrix R V).mulVec (x.1 + y.1) =
      (normalMatrix R V).mulVec x.1 + (normalMatrix R V).mulVec y.1
    exact Matrix.mulVec_add _ _ _
  map_smul' := by
    intro c x
    apply Subtype.ext
    change (normalMatrix R V).mulVec (c • x.1) =
      c • (normalMatrix R V).mulVec x.1
    exact Matrix.mulVec_smul _ _ _

noncomputable def originalLiveMap (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    originalCycleSpace degree D p t →ₗ[k] aliveSpace degree R p t :=
  (cycleLiveMap degree R p t).comp
    (cycleBasisEquiv degree D R V W hD2 hR hcert hRdegree hpiv p t).symm.toLinearMap

abbrev originalHomology (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) : Type _ :=
  (originalCycleSpace degree D p t) ⧸
    LinearMap.ker (originalLiveMap degree D R V W hD2 hR hcert hRdegree hpiv p t)

theorem originalLiveMap_surjective (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    Function.Surjective
      (originalLiveMap degree D R V W hD2 hR hcert hRdegree hpiv p t) := by
  intro y
  obtain ⟨x, hx⟩ := cycleLiveMap_surjective degree D R V W hD2 hR hcert hpiv p t y
  refine ⟨(cycleBasisEquiv degree D R V W hD2 hR hcert hRdegree hpiv p t) x, ?_⟩
  simpa [originalLiveMap] using hx

noncomputable def originalHomologyEquivAlive (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    originalHomology degree D R V W hD2 hR hcert hRdegree hpiv p t ≃ₗ[k]
      aliveSpace degree R p t :=
  (originalLiveMap degree D R V W hD2 hR hcert hRdegree hpiv p t).quotKerEquivOfSurjective
    (originalLiveMap_surjective degree D R V W hD2 hR hcert hRdegree hpiv p t)

theorem originalHomology_kernel_eq_boundaries (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ)
    (x : originalCycleSpace degree D p t) :
    x ∈ LinearMap.ker
      (originalLiveMap degree D R V W hD2 hR hcert hRdegree hpiv p t) ↔
      OriginalBoundary degree D p t x.1 := by
  let E := cycleBasisEquiv degree D R V W hD2 hR hcert hRdegree hpiv p t
  let y := E.symm x
  have hy : NormalCycle degree R p t y.1 := y.2
  have hkernel := normalHomology_kernel_eq_boundaries degree D R V W hD2 hR hcert
    hRdegree hpiv p t y
  have hboundary := normalBoundary_iff_originalBoundary degree D R V W hD2 hR
    hcert hRdegree hpiv p t y.1
  have hx : (normalMatrix R V).mulVec y.1 = x.1 := by
    exact congrArg Subtype.val (E.apply_symm_apply x)
  rw [hx] at hboundary
  simpa [originalLiveMap, y, E] using hkernel.trans hboundary

/-- Structure map of the original-boundary prefix homology. -/
noncomputable def originalHomologyMap (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p s t : ℕ) :
    originalHomology degree D R V W hD2 hR hcert hRdegree hpiv p s →ₗ[k]
      originalHomology degree D R V W hD2 hR hcert hRdegree hpiv p t :=
  ((originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p t).symm.toLinearMap).comp
    ((aliveSpaceMap degree R p s t).comp
      (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p s).toLinearMap)

theorem originalHomologyMap_transport (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p s t : ℕ)
    (x : originalHomology degree D R V W hD2 hR hcert hRdegree hpiv p s) :
    (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p t)
      (originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p s t x) =
    aliveSpaceMap degree R p s t
      ((originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p s) x) := by
  simp [originalHomologyMap]

/-- On a class represented by an original `D`-cycle, the transition takes
the same chain into the later prefix and projects its normal coordinates. -/
theorem originalHomologyMap_mk (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p s t : ℕ) (hst : s ≤ t)
    (x : originalCycleSpace degree D p s) :
    (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p t)
      (originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p s t
        (Submodule.Quotient.mk x)) =
      ⟨aliveRepresentative degree R p t (((normalMatrix R V)⁻¹).mulVec x.1),
        aliveRepresentative_mem_aliveSpace degree R p t
          (((normalMatrix R V)⁻¹).mulVec x.1)⟩ := by
  rw [originalHomologyMap_transport]
  have hsource :
      (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p s)
        (Submodule.Quotient.mk x) =
      originalLiveMap degree D R V W hD2 hR hcert hRdegree hpiv p s x := by
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ x
  rw [hsource]
  apply Subtype.ext
  have hpre : PrefixSupported s (((normalMatrix R V)⁻¹).mulVec x.1) :=
    normalMatrix_inv_prefix R V hcert.upper hcert.diag s x.1 x.2.1
  exact aliveRepresentative_transition degree R p s t hst _ hpre

noncomputable def originalHomologyMap_rangeEquiv (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p s t : ℕ) :
    LinearMap.range (originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p s t) ≃ₗ[k]
      LinearMap.range (aliveSpaceMap degree R p s t) where
  toFun y := ⟨(originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p t) y.1,
    by
      obtain ⟨x, hx⟩ := y.2
      refine ⟨(originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p s) x, ?_⟩
      rw [← hx]
      exact (originalHomologyMap_transport degree D R V W hD2 hR hcert hRdegree hpiv p s t x).symm⟩
  invFun y := ⟨(originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p t).symm y.1,
    by
      obtain ⟨x, hx⟩ := y.2
      refine ⟨(originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p s).symm x, ?_⟩
      apply (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p t).injective
      rw [originalHomologyMap_transport, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact hx⟩
  left_inv := by intro y; apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  right_inv := by intro y; apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  map_add' := by intro x y; apply Subtype.ext; simp
  map_smul' := by intro c x; apply Subtype.ext; simp

/-- Simultaneous prefix-homology rank formula for the original differential.
The rank counts deaths `j` with pivot `i(j)<s` and `t≤j`, plus essential
births `i<s`, in degree `p`. -/
theorem originalHomologyMap_rank_formula (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p s t : ℕ) (hst : s ≤ t) (_ht : t ≤ m) :
    Module.finrank k (LinearMap.range
      (originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p s t)) =
      (deathSurvivorFinset degree R p s t).card +
        (essentialSurvivorFinset degree R p s).card := by
  rw [(originalHomologyMap_rangeEquiv degree D R V W hD2 hR hcert hRdegree hpiv p s t).finrank_eq]
  exact aliveSpaceMap_rank_formula degree R hpiv p s t hst

/-- The concrete reducer supplies the whole input to the original-boundary
interval rank formula; no normal form is assumed. -/
theorem matrixReductionTrace_originalHomologyMap_rank_formula
    (degree : Fin m → ℕ) (D : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hstrict : StrictBoundary D)
    (hdegree : LowersDegree degree D)
    (p s t : ℕ) (hst : s ≤ t) (ht : t ≤ m) :
    let ops := matrixReductionTrace D
    let R := replay D ops
    let V := traceChange ops
    let W := traceChangeInv ops
    Module.finrank k (LinearMap.range
      (originalHomologyMap degree D R V W hD2
        (matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree).1
        (matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree).2.1
        (matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree).2.2.1
        (matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree).2.2.2.2.1
        p s t)) =
      (deathSurvivorFinset degree R p s t).card +
        (essentialSurvivorFinset degree R p s).card := by
  dsimp only
  have h := matrixReductionTrace_normalForm_input degree D hD2 hstrict hdegree
  exact originalHomologyMap_rank_formula degree D _ _ _ hD2 h.1 h.2.1
    h.2.2.1 h.2.2.2.2.1 p s t hst ht

theorem originalHomologyMap_id (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p t : ℕ) :
    originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p t t =
      LinearMap.id := by
  ext x
  apply (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p t).injective
  simp only [LinearMap.comp_apply]
  rw [originalHomologyMap_transport, LinearMap.id_apply,
    aliveSpaceMap_id, LinearMap.id_apply]

theorem originalHomologyMap_comp (degree : Fin m → ℕ)
    (D R V W : Matrix (Fin m) (Fin m) k)
    (hD2 : D * D = 0) (hR : R = D * V)
    (hcert : TraceChangeCertificate degree V W)
    (hRdegree : LowersDegree degree R)
    (hpiv : DistinctPivots R) (p s t u : ℕ)
    (hst : s ≤ t) (htu : t ≤ u) :
    (originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p t u).comp
      (originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p s t) =
    originalHomologyMap degree D R V W hD2 hR hcert hRdegree hpiv p s u := by
  ext x
  apply (originalHomologyEquivAlive degree D R V W hD2 hR hcert hRdegree hpiv p u).injective
  simp only [LinearMap.comp_apply, originalHomologyMap_transport]
  rw [← LinearMap.comp_apply, aliveSpaceMap_comp degree R p s t u hst htu]

#print axioms DistinctPivots
#print axioms IsDeath
#print axioms reduced_mulVec_kernel
#print axioms StrictBoundary
#print axioms reduced_strict
#print axioms degree_zero_boundary
#print axioms pivot_column_zero
#print axioms IsPivot
#print axioms IsEssential
#print axioms deathOfPivot
#print axioms deathOfPivot_spec
#print axioms deathOfPivot_unique
#print axioms pivot_not_death
#print axioms pivot_death_essential
#print axioms pivot_order_degree
#print axioms normalColumn
#print axioms normalMatrix
#print axioms normalColumn_pivot
#print axioms normalColumn_nonpivot
#print axioms normalMatrix_upper
#print axioms normalMatrix_diag
#print axioms normalMatrix_degree
#print axioms normalMatrix_det
#print axioms normalMatrix_isUnit
#print axioms normalMatrix_mul_inv
#print axioms normalMatrix_inv_mul
#print axioms normalMatrix_inv_upper
#print axioms normalMatrix_inv_degree
#print axioms PrefixSupported
#print axioms upper_mulVec_prefix
#print axioms normalMatrix_prefix
#print axioms normalMatrix_inv_prefix
#print axioms strict_boundary_prefix
#print axioms matrixReductionTrace_normalForm_input
#print axioms normalColumn_pivot_boundary
#print axioms normalColumn_zero_boundary
#print axioms normalColumn_death_boundary
#print axioms normalDifferential
#print axioms normalDifferential_zero_column
#print axioms normalDifferential_pair_column
#print axioms normalMatrix_conjugates_boundary
#print axioms normalDifferential_mulVec_pivot
#print axioms normalDifferential_mulVec_nonpivot
#print axioms normalDifferential_cycle_iff
#print axioms normalDifferential_image_nonpivot
#print axioms normalDifferential_strict
#print axioms normalDifferential_degree
#print axioms lowers_mulVec_homogeneous
#print axioms PivotAlive
#print axioms EssentialAlive
#print axioms AliveCoordinate
#print axioms pairedInterval
#print axioms essentialInterval
#print axioms pairedInterval_alive_iff
#print axioms essentialInterval_alive_iff
#print axioms pivotAlive_iff_pairedInterval
#print axioms essentialAlive_iff_essentialInterval
#print axioms Homogeneous
#print axioms NormalCycle
#print axioms NormalBoundary
#print axioms pivotAlive_iff
#print axioms normalBoundary_alive_zero
#print axioms aliveRepresentative
#print axioms expiredPreimage
#print axioms expiredPreimage_prefix
#print axioms expiredPreimage_degree
#print axioms expiredPreimage_pivot
#print axioms expiredBoundary_pivot
#print axioms normalDifferential_sq_zero
#print axioms normalBoundary_isCycle
#print axioms aliveRepresentative_prefix
#print axioms aliveRepresentative_degree
#print axioms aliveRepresentative_cycle
#print axioms normalCycle_decompose
#print axioms normalCycle_boundary_iff_live_zero
#print axioms normalCycle_prefix_inclusion
#print axioms normalBoundary_prefix_inclusion
#print axioms aliveRepresentative_transition
#print axioms aliveRepresentative_single_survives
#print axioms aliveRepresentative_single_dies
#print axioms normalCycleSpace
#print axioms aliveSpace
#print axioms aliveRepresentative_mem_aliveSpace
#print axioms aliveRepresentative_of_mem
#print axioms cycleLiveMap
#print axioms cycleLiveMap_surjective
#print axioms normalHomology
#print axioms normalHomologyEquivAlive
#print axioms normalHomology_kernel_eq_boundaries
#print axioms aliveSpace_eq_spanSubset
#print axioms aliveSpace_prefix
#print axioms aliveSpaceMap
#print axioms aliveSpaceMap_id
#print axioms aliveSpaceMap_comp
#print axioms normalHomologyMap
#print axioms normalHomologyMap_mk
#print axioms Survivor
#print axioms survivorFinset
#print axioms aliveSpaceMap_range_iff
#print axioms aliveSpaceMap_rangeEquiv
#print axioms aliveSpaceMap_rank
#print axioms survivor_iff_pairs_or_essential
#print axioms pairSurvivorFinset
#print axioms essentialSurvivorFinset
#print axioms deathSurvivorFinset
#print axioms survivorFinset_partition
#print axioms pair_essential_disjoint
#print axioms pair_survivor_card_eq_death_card
#print axioms aliveSpaceMap_rank_formula
#print axioms normalHomologyMap_transport
#print axioms normalHomologyMap_rangeEquiv
#print axioms normalHomologyMap_rank_formula
#print axioms grade_preserving_mulVec
#print axioms normalMatrix_mulVec_inv
#print axioms normalMatrix_inv_mulVec
#print axioms normalMatrix_boundary_mulVec
#print axioms OriginalCycle
#print axioms OriginalBoundary
#print axioms normalCycle_iff_originalCycle
#print axioms normalBoundary_iff_originalBoundary
#print axioms originalCycleSpace
#print axioms cycleBasisEquiv
#print axioms originalLiveMap
#print axioms originalHomology
#print axioms originalLiveMap_surjective
#print axioms originalHomologyEquivAlive
#print axioms originalHomology_kernel_eq_boundaries
#print axioms originalHomologyMap
#print axioms originalHomologyMap_transport
#print axioms originalHomologyMap_mk
#print axioms originalHomologyMap_rangeEquiv
#print axioms originalHomologyMap_rank_formula
#print axioms originalHomologyMap_id
#print axioms originalHomologyMap_comp

end TDA.Persistence.Reduction
