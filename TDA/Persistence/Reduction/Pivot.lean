import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Finite column pivots and one-step cancellation

For a finite coefficient vector, `columnPivot` records the greatest index with nonzero
coefficient, or `none` when the vector is zero. `pivotHeight` gives a natural-number measure
that places every genuine pivot above the zero vector, including a pivot at index zero.

`cancelColumn` performs the elementary column operation that kills a common pivot. Its strict
height decrease is a one-step algebraic result; this file does not package a reduction loop or
assert termination of one.
-/

namespace TDA.Persistence.Reduction

variable {m : ℕ} {k : Type*} [Field k]

/-- The greatest index in the finite support of a coefficient vector, if it is nonzero. -/
def columnPivot [DecidableEq k] (c : Fin m → k) : Option (Fin m) :=
  let nz := (Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)
  if h : nz.Nonempty then some (nz.max' h) else none

/-- A pivot index as a positive height, and the zero vector as height zero. -/
def pivotHeight : Option (Fin m) → ℕ
  | none => 0
  | some i => i.val + 1

/-- Cancel the pivot of `b` by subtracting a scalar multiple of `a`. -/
def cancelColumn (a b : Fin m → k) (p : Fin m) : Fin m → k :=
  b - (b p / a p) • a

/-- The pivot is absent exactly when every coefficient vanishes. -/
theorem columnPivot_none_iff [DecidableEq k] (c : Fin m → k) :
    columnPivot c = none ↔ ∀ r, c r = 0 := by
  classical
  let nz : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)
  change (if h : nz.Nonempty then some (nz.max' h) else none) = none ↔
    ∀ r, c r = 0
  constructor
  · intro h r
    by_contra hr
    have hmem : r ∈ nz := by
      simp [nz, hr]
    have hne : nz.Nonempty := ⟨r, hmem⟩
    simp [hne] at h
  · intro hc
    by_cases hne : nz.Nonempty
    · obtain ⟨r, hr⟩ := hne
      have hnonzero : c r ≠ 0 := (Finset.mem_filter.mp hr).2
      exact (hnonzero (hc r)).elim
    · simp [hne]

/-- The zero coefficient vector has no pivot. -/
@[simp]
theorem columnPivot_zero [DecidableEq k] :
    columnPivot (0 : Fin m → k) = none := by
  apply (columnPivot_none_iff (0 : Fin m → k)).2
  intro r
  rfl

/-- A present pivot is nonzero and every coefficient above it vanishes. -/
theorem columnPivot_some_iff [DecidableEq k] (c : Fin m → k) (p : Fin m) :
    columnPivot c = some p ↔ c p ≠ 0 ∧ ∀ r, p < r → c r = 0 := by
  classical
  let nz : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i => c i ≠ 0)
  change (if h : nz.Nonempty then some (nz.max' h) else none) = some p ↔
    c p ≠ 0 ∧ ∀ r, p < r → c r = 0
  by_cases hne : nz.Nonempty
  · rw [dif_pos hne]
    simp only [Option.some.injEq]
    constructor
    · intro hp
      change nz.max' hne = p at hp
      rw [← hp]
      have hmem : nz.max' hne ∈ nz := Finset.max'_mem nz hne
      refine ⟨(Finset.mem_filter.mp hmem).2, ?_⟩
      intro r hpr
      by_contra hnonzero
      have hr : r ∈ nz := by simp [nz, hnonzero]
      have hrle : r ≤ nz.max' hne := Finset.le_max' nz r hr
      exact (not_lt_of_ge hrle) hpr
    · rintro ⟨hp, hpAbove⟩
      have hpMem : p ∈ nz := by simp [nz, hp]
      have hmax : nz.max' hne = p := by
        apply (Finset.max'_eq_iff nz hne p).2
        refine ⟨hpMem, ?_⟩
        intro r hr
        have hrNonzero : c r ≠ 0 := (Finset.mem_filter.mp hr).2
        by_contra hpr
        exact hrNonzero (hpAbove r (lt_of_not_ge hpr))
      simp [hmax]
  · simp only [dif_neg hne]
    constructor
    · intro h
      cases h
    · rintro ⟨hp, _⟩
      have hfalse : False := hne ⟨p, by simp [nz, hp]⟩
      exact hfalse.elim

/-- The zero vector has height zero. -/
@[simp]
theorem pivotHeight_none : pivotHeight (none : Option (Fin m)) = 0 := rfl

/-- The height of a present pivot is one plus its zero-based index. -/
@[simp]
theorem pivotHeight_some (p : Fin m) : pivotHeight (some p) = p.val + 1 := rfl

/-- Height zero characterizes the absent pivot. -/
theorem pivotHeight_eq_zero_iff (q : Option (Fin m)) :
    pivotHeight q = 0 ↔ q = none := by
  cases q <;> simp [pivotHeight]

/-- A common source pivot is canceled at the pivot row. -/
theorem cancelColumn_apply_pivot [DecidableEq k] (a b : Fin m → k) (p : Fin m)
    (ha : columnPivot a = some p) : cancelColumn a b p p = 0 := by
  have hden : a p ≠ 0 := (columnPivot_some_iff a p).mp ha |>.1
  change b p - (b p / a p) * a p = 0
  rw [div_mul_cancel₀ (b p) hden]
  exact sub_self _

/-- A common pivot operation remains zero at every row above the pivot. -/
theorem cancelColumn_apply_above [DecidableEq k] (a b : Fin m → k) (p r : Fin m)
    (ha : columnPivot a = some p) (hb : columnPivot b = some p) (hpr : p < r) :
    cancelColumn a b p r = 0 := by
  have haAbove := (columnPivot_some_iff a p).mp ha |>.2 r hpr
  have hbAbove := (columnPivot_some_iff b p).mp hb |>.2 r hpr
  simp [cancelColumn, haAbove, hbAbove]

/-- One common-pivot cancellation strictly lowers pivot height, possibly to zero. -/
theorem pivotHeight_cancelColumn_lt [DecidableEq k] (a b : Fin m → k) (p : Fin m)
    (ha : columnPivot a = some p) (hb : columnPivot b = some p) :
    pivotHeight (columnPivot (cancelColumn a b p)) < pivotHeight (some p) := by
  have hnew : columnPivot (cancelColumn a b p) = none ∨
      ∃ q, columnPivot (cancelColumn a b p) = some q ∧ q < p := by
    by_cases hnone : columnPivot (cancelColumn a b p) = none
    · exact Or.inl hnone
    · cases hq : columnPivot (cancelColumn a b p) with
      | none => exact (hnone hq).elim
      | some q =>
        right
        refine ⟨q, rfl, ?_⟩
        have hqNonzero : cancelColumn a b p q ≠ 0 :=
          (columnPivot_some_iff (cancelColumn a b p) q).mp hq |>.1
        by_contra hpq
        have hpq' : p ≤ q := le_of_not_gt hpq
        rcases lt_or_eq_of_le hpq' with hpq'' | hpq''
        · exact hqNonzero (cancelColumn_apply_above a b p q ha hb hpq'')
        · subst q
          exact hqNonzero (cancelColumn_apply_pivot a b p ha)
  rcases hnew with hnone | ⟨q, hq, hqp⟩
  · rw [hnone, pivotHeight]
    exact Nat.succ_pos _
  · rw [hq]
    change q.val + 1 < p.val + 1
    have hval : q.val < p.val := Fin.lt_def.mp hqp
    omega

/-- Right multiplication by a transvection adds `c` times column `i` to column `j`. -/
theorem col_mul_transvection (M : Matrix (Fin m) (Fin m) k) (i j : Fin m) (c : k) :
    (M * Matrix.transvection i j c).col j = M.col j + c • M.col i := by
  ext r
  simp [smul_eq_mul]

/-- Right multiplication by a transvection fixes every column except its target column. -/
theorem col_mul_transvection_of_ne (M : Matrix (Fin m) (Fin m) k)
    (i j q : Fin m) (c : k) (hq : q ≠ j) :
    (M * Matrix.transvection i j c).col q = M.col q := by
  ext r
  simp [hq]

/-- A filtration-ordered right transvection cancels a common pivot in the target column.
The strict height bound is the vector cancellation theorem, and the source column is unchanged
because `i < j` implies `i ≠ j`. -/
theorem pivotHeight_mul_transvection_lt [DecidableEq k]
    (M : Matrix (Fin m) (Fin m) k) (i j p : Fin m) (hij : i < j)
    (hi : columnPivot (M.col i) = some p) (hj : columnPivot (M.col j) = some p) :
    pivotHeight (columnPivot
      ((M * Matrix.transvection i j (-(M p j / M p i))).col j)) <
        pivotHeight (columnPivot (M.col j)) := by
  let c : k := -(M p j / M p i)
  have hijne : i ≠ j := ne_of_lt hij
  have hsource : (M * Matrix.transvection i j c).col i = M.col i :=
    col_mul_transvection_of_ne M i j i c hijne
  have htarget : (M * Matrix.transvection i j c).col j =
      cancelColumn (M.col i) (M.col j) p := by
    calc
      (M * Matrix.transvection i j c).col j = M.col j + c • M.col i :=
        col_mul_transvection M i j c
      _ = cancelColumn (M.col i) (M.col j) p := by
        ext r
        simp [cancelColumn, c, smul_eq_mul]
        ring
  have htarget' : (M * Matrix.transvection i j c).col j =
      cancelColumn ((M * Matrix.transvection i j c).col i) (M.col j) p := by
    calc
      (M * Matrix.transvection i j c).col j = cancelColumn (M.col i) (M.col j) p :=
        htarget
      _ = cancelColumn ((M * Matrix.transvection i j c).col i) (M.col j) p := by
        rw [hsource]
  have hsourcePivot : columnPivot ((M * Matrix.transvection i j c).col i) = some p := by
    rw [hsource]
    exact hi
  change pivotHeight (columnPivot ((M * Matrix.transvection i j c).col j)) <
    pivotHeight (columnPivot (M.col j))
  rw [htarget', hj]
  exact pivotHeight_cancelColumn_lt _ _ p hsourcePivot hj

end TDA.Persistence.Reduction
