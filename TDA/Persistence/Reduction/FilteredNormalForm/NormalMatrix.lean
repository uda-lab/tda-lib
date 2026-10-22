import TDA.Persistence.Reduction.MatrixReduction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Filtered normal form: the normal-form matrix

For a square-zero boundary `D` with right reduction `R = D * V`, this module builds the
unitriangular normal-form matrix `normalMatrix R V` and the normal differential
`normalDifferential R`, which keeps only the pivot entries of `R`, and proves that
`normalMatrix R V` conjugates `D` to `normalDifferential R`.  The reduced matrix `R`
itself is not a differential: `R * R` need not vanish.
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
nonzero coefficient in the original differential. -/
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

end TDA.Persistence.Reduction
