import TDA.Persistence.Reduction.FiniteInputSublevelBasis

/-!
# Executable coordinates in the reducer's normal basis

All pivot pairs, including tied-grade pairs, select the same normal columns as
the theoretical normal form. Fixed-size vectors store matrix entries eagerly.
The strict upper part is nilpotent, so a finite geometric iteration computes
the inverse without evaluating the proof-only choice of a death index.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

private abbrev Dense (n : ℕ) := Vector (Vector (ZMod 2) n) n

private def store {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) : Dense n :=
  Vector.ofFn fun r => Vector.ofFn fun c => A r c

private def read {n : ℕ} (A : Dense n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun r c => A[r][c]

@[simp] private theorem read_store {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    read (store A) = A := by
  ext r c
  simp [read, store]

private def normalRows {n : ℕ} (R V : Matrix (Fin n) (Fin n) (ZMod 2))
    (pairs : List (Fin n × Fin n)) : Dense n :=
  let Rdata := store R
  let Vdata := store V
  Vector.ofFn fun r => Vector.ofFn fun i =>
    match pairs.find? (fun q => q.1 == i) with
    | some q => (Rdata[q.1][q.2])⁻¹ * Rdata[r][q.2]
    | none => Vdata[r][i]

private theorem normalRows_apply (xs : Input) (r i : Fin xs.length) :
    read (normalRows (reduced xs) (change xs) (pivotPairs xs)) r i =
      match (pivotPairs xs).find? (fun q => q.1 == i) with
      | some q => ((reduced xs) q.1 q.2)⁻¹ * (reduced xs) r q.2
      | none => (change xs) r i := by
  simp only [normalRows, read, store, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  cases hf : (pivotPairs xs).find? (fun q => q.1 == i) <;> rfl

private theorem normalRows_eq (xs : Input) :
    read (normalRows (reduced xs) (change xs) (pivotPairs xs)) = normalMatrix (reduced xs) (change xs) := by
  ext r i
  rw [normalRows_apply]
  change _ = normalColumn (reduced xs) (change xs) i r
  split
  · next q hq =>
    have hmem := List.mem_of_find?_eq_some hq
    have hi : q.1 = i := by simpa using List.find?_some hq
    have hc := congrFun (pairedVector_eq_normalColumn xs q hmem) r
    simpa only [pairedVector, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, hi] using hc
  · next hn =>
    have hi : ¬ IsPivot (reduced xs) i := by
      rintro ⟨j, hj⟩
      have hm := (pivotPairs_mem xs i j).mpr hj
      exact (List.find?_eq_none.mp hn (i, j) hm) (by simp)
    rw [normalColumn_nonpivot (reduced xs) (change xs) i hi]
    rfl

private theorem strictUpper_power {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 2))
    (hU : ∀ r c, c ≤ r → U r c = 0) (k : ℕ) (r c : Fin n)
    (hc : c.val < r.val + k) : (U ^ k) r c = 0 := by
  induction k generalizing r c with
  | zero =>
    have hne : r ≠ c := by intro he; subst c; omega
    simp only [pow_zero, Matrix.one_apply, if_neg hne]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : c ≤ j
    · rw [hU j c hj, mul_zero]
    · have hlt : j.val < c.val := lt_of_not_ge hj
      rw [ih r j (by omega), zero_mul]

private theorem strictUpper_nilpotent {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 2))
    (hU : ∀ r c, c ≤ r → U r c = 0) : U ^ n = 0 := by
  ext r c
  apply strictUpper_power U hU n r c
  have hc := c.isLt
  omega

private theorem normalRows_strict (xs : Input) :
    ∀ r c, c ≤ r → (1 - read (normalRows (reduced xs) (change xs) (pivotPairs xs))) r c = 0 := by
  rw [normalRows_eq]
  have hu := normalMatrix_upper (reduced xs) (change xs)
    (traceChange_isUpperTriangular (trace xs))
  have hd := normalMatrix_diag (reduced xs) (change xs)
    (traceChange_apply_diag (trace xs))
  intro r c hc
  rcases lt_or_eq_of_le hc with hc | rfl
  · simp only [Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_gt hc), hu hc, sub_self]
  · simp only [Matrix.sub_apply, Matrix.one_apply_eq, hd, sub_self]

private def inverseStage {n : ℕ} (U : Dense n) : ℕ → Dense n
  | 0 => store 0
  | k + 1 => store (1 + read (inverseStage U k) * read U)

private theorem inverseStage_residual {n : ℕ} (U : Dense n) (k : ℕ) :
    (1 - read U) * read (inverseStage U k) = 1 - read U ^ k := by
  induction k with
  | zero => simp only [inverseStage, read_store, mul_zero, pow_zero, sub_self]
  | succ k ih =>
    simp only [inverseStage, read_store, mul_add, mul_one, ← mul_assoc, ih, pow_succ]
    noncomm_ring

private def inverseRows {n : ℕ} (R V : Matrix (Fin n) (Fin n) (ZMod 2))
    (pairs : List (Fin n × Fin n)) : Dense n :=
  inverseStage (store (1 - read (normalRows R V pairs))) n

private theorem inverseRows_eq (xs : Input) :
    read (inverseRows (reduced xs) (change xs) (pivotPairs xs)) = (normalMatrix (reduced xs) (change xs))⁻¹ := by
  let N := normalMatrix (reduced xs) (change xs)
  have hpow : (1 - read (normalRows (reduced xs) (change xs) (pivotPairs xs))) ^ xs.length = 0 :=
    strictUpper_nilpotent _ (normalRows_strict xs)
  have hr := inverseStage_residual (store (1 - read (normalRows (reduced xs) (change xs) (pivotPairs xs)))) xs.length
  simp only [read_store, sub_sub_cancel, hpow, sub_zero] at hr
  have hl : N * read (inverseRows (reduced xs) (change xs) (pivotPairs xs)) = 1 := by
    simpa only [inverseRows, normalRows_eq, N] using hr
  have hi := normalMatrix_inv_mul (reduced xs) (change xs)
    (traceChange_isUpperTriangular (trace xs)) (traceChange_apply_diag (trace xs))
  calc
    read (inverseRows (reduced xs) (change xs) (pivotPairs xs)) = 1 * read (inverseRows (reduced xs) (change xs) (pivotPairs xs)) := (one_mul _).symm
    _ = (N⁻¹ * N) * read (inverseRows (reduced xs) (change xs) (pivotPairs xs)) := by rw [hi]
    _ = N⁻¹ := by rw [mul_assoc, hl, mul_one]

/-- All normal coordinates of any original-face coefficient vector.
The result is stored finite data, not a proof-side inverse matrix. -/
def normalCoordinateVector (xs : Input) (v : Fin xs.length → ZMod 2) :
    Vector (ZMod 2) xs.length :=
  let W := inverseRows (reduced xs) (change xs) (pivotPairs xs)
  Vector.ofFn fun i => ∑ j, W[i][j] * v j

/-- The executable finite iteration agrees with the existing normal-form inverse. -/
theorem normalCoordinateVector_apply (xs : Input) (v : Fin xs.length → ZMod 2)
    (i : Fin xs.length) :
    (normalCoordinateVector xs v)[i] =
      ((normalMatrix (reduced xs) (change xs))⁻¹).mulVec v i := by
  simp only [normalCoordinateVector]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  change (read (inverseRows (reduced xs) (change xs) (pivotPairs xs))).mulVec v i = _
  rw [inverseRows_eq]

end TDA.Persistence.Reduction.FiniteInput
