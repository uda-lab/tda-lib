import TDA.Persistence.Morse.UnitCancellation

/-!
# Filtered contractions of based complexes

A based complex is a finite index type `ι` with a matrix `D : Matrix ι ι k` over a commutative
ring `k`, in the column convention of `TDA.Persistence.Morse.UnitCancellation`: `D r c` is the
coefficient of `r` in `d c`, and matrix product is composition. A
`FilteredContraction degree grade D degree' grade' D'` of `(ι, degree, grade, D)` onto
`(κ, degree', grade', D')` consists of three matrices `proj : Matrix κ ι k`,
`incl : Matrix ι κ k` and `htpy : Matrix ι ι k` with

* the chain-map equations `proj * D = D' * proj` and `D * incl = incl * D'`;
* `proj * incl = 1` and `1 - incl * proj = D * htpy + htpy * D`;
* the side conditions `htpy * htpy = 0`, `proj * htpy = 0` and `htpy * incl = 0`;
* degree support: on their supports, `proj` and `incl` preserve degree and `htpy` raises it
  by one;
* grade bounds: all three matrices are `GradeNonincreasing`.

The differentials, degrees and grades are parameters, not fields, and `D * D = 0` is not a
field. `refl` (the identity contraction), `copy` (the same matrices after rewriting the small
complex's degree, grade and differential along equalities), `trans` (composition, with homotopy
`htpy₁ + incl₁ * htpy₂ * proj₁`) and `reindex` (transport of the small complex along an
equivalence `κ ≃ μ`, by `submatrix`) need no hypothesis beyond their inputs. `ofUnitPair`
packages the single equal-grade unit cancellation of `UnitCancellation` for a filtered
differential.

`differential_eq` proves `D' = proj * D * incl`. From `D * D = 0`, `sq_zero_target` proves
`D' * D' = 0`, and `isBasedDifferential_target` and `isFilteredDifferential_target` transfer
the based and filtered differential properties to the small complex.
`proj_mulVec_incl_mulVec` and `sub_incl_mulVec_proj_mulVec` are the vector forms of
`proj * incl = 1` and of the homotopy identity. Sublevel restriction is not restated: it is
`GradeNonincreasing.mulVec_sublevelSupported` applied to `proj_grade`, `incl_grade` and
`htpy_grade`.

All data are computable matrices. No iteration of cancellations, homology, persistence
isomorphism or bridge to Mathlib `HomotopyEquiv` is provided here.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.Cancellation

section Grades

variable {κ μ : Type*} {k : Type*}

/-- A sum of grade-nonincreasing matrices is grade-nonincreasing. -/
theorem GradeNonincreasing.add [AddZeroClass k] {gr : κ → ℤ} {gc : μ → ℤ}
    {M N : Matrix κ μ k} (hM : GradeNonincreasing gr gc M) (hN : GradeNonincreasing gr gc N) :
    GradeNonincreasing gr gc (M + N) := by
  intro r c h
  by_cases hm : M r c = 0
  · exact hN r c (by simpa [Matrix.add_apply, hm] using h)
  · exact hM r c hm

end Grades

/-- A filtered contraction of the based complex `(ι, degree, grade, D)` onto
`(κ, degree', grade', D')`, in the sense of the fields below: chain maps `proj` and `incl` and a
homotopy `htpy` with `proj * incl = 1`, `1 - incl * proj = D * htpy + htpy * D` and the side
conditions `htpy * htpy = 0`, `proj * htpy = 0`, `htpy * incl = 0`. The three maps preserve
degree (`htpy` raises it by one) and do not increase grade. -/
structure FilteredContraction {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {k : Type*} [CommRing k]
    (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k)
    (degree' : κ → ℕ) (grade' : κ → ℤ) (D' : Matrix κ κ k) where
  /-- The projection onto the small complex. -/
  proj : Matrix κ ι k
  /-- The inclusion of the small complex. -/
  incl : Matrix ι κ k
  /-- The homotopy on the large complex. -/
  htpy : Matrix ι ι k
  /-- `proj` is a chain map. -/
  proj_mul : proj * D = D' * proj
  /-- `incl` is a chain map. -/
  mul_incl : D * incl = incl * D'
  /-- `proj * incl = 1`. -/
  proj_mul_incl : proj * incl = 1
  /-- `htpy` is a homotopy from `incl * proj` to `1`. -/
  one_sub_incl_mul_proj : 1 - incl * proj = D * htpy + htpy * D
  /-- Side condition `htpy * htpy = 0`. -/
  htpy_mul_htpy : htpy * htpy = 0
  /-- Side condition `proj * htpy = 0`. -/
  proj_mul_htpy : proj * htpy = 0
  /-- Side condition `htpy * incl = 0`. -/
  htpy_mul_incl : htpy * incl = 0
  /-- `proj` preserves degree on its support. -/
  proj_degree : ∀ r x, proj r x ≠ 0 → degree' r = degree x
  /-- `incl` preserves degree on its support. -/
  incl_degree : ∀ x r, incl x r ≠ 0 → degree x = degree' r
  /-- `htpy` raises degree by one on its support. -/
  htpy_degree : ∀ x y, htpy x y ≠ 0 → degree x = degree y + 1
  /-- `proj` does not increase grade. -/
  proj_grade : GradeNonincreasing grade' grade proj
  /-- `incl` does not increase grade. -/
  incl_grade : GradeNonincreasing grade grade' incl
  /-- `htpy` does not increase grade. -/
  htpy_grade : GradeNonincreasing grade grade htpy

namespace FilteredContraction

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] {k : Type*} [CommRing k]
  {degree : ι → ℕ} {grade : ι → ℤ} {D : Matrix ι ι k}
  {degree' : κ → ℕ} {grade' : κ → ℤ} {D' : Matrix κ κ k}
  {degree'' : μ → ℕ} {grade'' : μ → ℤ} {D'' : Matrix μ μ k}

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [Fintype μ] [DecidableEq μ] in
private theorem exists_of_mul_ne_zero {M : Matrix ι κ k} {N : Matrix κ μ k} {r : ι} {c : μ}
    (h : (M * N) r c ≠ 0) : ∃ m, M r m ≠ 0 ∧ N m c ≠ 0 := by
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨m, left_ne_zero_of_mul hm, right_ne_zero_of_mul hm⟩

/-- The identity contraction of a based complex onto itself. -/
def refl (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k) :
    FilteredContraction degree grade D degree grade D where
  proj := 1
  incl := 1
  htpy := 0
  proj_mul := by rw [Matrix.one_mul, Matrix.mul_one]
  mul_incl := by rw [Matrix.one_mul, Matrix.mul_one]
  proj_mul_incl := Matrix.one_mul 1
  one_sub_incl_mul_proj := by simp
  htpy_mul_htpy := Matrix.zero_mul 0
  proj_mul_htpy := Matrix.mul_zero 1
  htpy_mul_incl := Matrix.zero_mul 1
  proj_degree := fun r x h => by
    by_cases hrx : r = x
    · rw [hrx]
    · exact absurd (Matrix.one_apply_ne hrx) h
  incl_degree := fun x r h => by
    by_cases hrx : x = r
    · rw [hrx]
    · exact absurd (Matrix.one_apply_ne hrx) h
  htpy_degree := fun x y h => absurd rfl h
  proj_grade := fun r x h => by
    by_cases hrx : r = x
    · rw [hrx]
    · exact absurd (Matrix.one_apply_ne hrx) h
  incl_grade := fun x r h => by
    by_cases hrx : x = r
    · rw [hrx]
    · exact absurd (Matrix.one_apply_ne hrx) h
  htpy_grade := fun x y h => absurd rfl h

/-- The identity contraction has the identity as projection. -/
@[simp] theorem refl_proj (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k) :
    (refl degree grade D).proj = 1 := rfl

/-- The identity contraction has the identity as inclusion. -/
@[simp] theorem refl_incl (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k) :
    (refl degree grade D).incl = 1 := rfl

/-- The identity contraction has zero homotopy. -/
@[simp] theorem refl_htpy (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k) :
    (refl degree grade D).htpy = 0 := rfl

/-- Rebuild a filtered contraction with the same matrices after rewriting the degree, the grade
and the differential of the small complex along equalities. -/
def copy (c : FilteredContraction degree grade D degree' grade' D') {degree₂ : κ → ℕ}
    {grade₂ : κ → ℤ} {D₂ : Matrix κ κ k} (hdeg : degree' = degree₂) (hgr : grade' = grade₂)
    (hD : D' = D₂) : FilteredContraction degree grade D degree₂ grade₂ D₂ where
  proj := c.proj
  incl := c.incl
  htpy := c.htpy
  proj_mul := by subst hD; exact c.proj_mul
  mul_incl := by subst hD; exact c.mul_incl
  proj_mul_incl := c.proj_mul_incl
  one_sub_incl_mul_proj := c.one_sub_incl_mul_proj
  htpy_mul_htpy := c.htpy_mul_htpy
  proj_mul_htpy := c.proj_mul_htpy
  htpy_mul_incl := c.htpy_mul_incl
  proj_degree := by subst hdeg; exact c.proj_degree
  incl_degree := by subst hdeg; exact c.incl_degree
  htpy_degree := c.htpy_degree
  proj_grade := by subst hgr; exact c.proj_grade
  incl_grade := by subst hgr; exact c.incl_grade
  htpy_grade := c.htpy_grade

/-- A copied contraction keeps the projection. -/
@[simp] theorem copy_proj (c : FilteredContraction degree grade D degree' grade' D')
    {degree₂ : κ → ℕ} {grade₂ : κ → ℤ} {D₂ : Matrix κ κ k} (hdeg : degree' = degree₂)
    (hgr : grade' = grade₂) (hD : D' = D₂) : (c.copy hdeg hgr hD).proj = c.proj := rfl

/-- A copied contraction keeps the inclusion. -/
@[simp] theorem copy_incl (c : FilteredContraction degree grade D degree' grade' D')
    {degree₂ : κ → ℕ} {grade₂ : κ → ℤ} {D₂ : Matrix κ κ k} (hdeg : degree' = degree₂)
    (hgr : grade' = grade₂) (hD : D' = D₂) : (c.copy hdeg hgr hD).incl = c.incl := rfl

/-- A copied contraction keeps the homotopy. -/
@[simp] theorem copy_htpy (c : FilteredContraction degree grade D degree' grade' D')
    {degree₂ : κ → ℕ} {grade₂ : κ → ℤ} {D₂ : Matrix κ κ k} (hdeg : degree' = degree₂)
    (hgr : grade' = grade₂) (hD : D' = D₂) : (c.copy hdeg hgr hD).htpy = c.htpy := rfl

private theorem proj_incl_mul {ν' : Type*}
    (c : FilteredContraction degree grade D degree' grade' D') (M : Matrix κ ν' k) :
    c.proj * (c.incl * M) = M := by
  rw [← Matrix.mul_assoc, c.proj_mul_incl, Matrix.one_mul]

private theorem proj_htpy_mul {ν' : Type*}
    (c : FilteredContraction degree grade D degree' grade' D') (M : Matrix ι ν' k) :
    c.proj * (c.htpy * M) = 0 := by
  rw [← Matrix.mul_assoc, c.proj_mul_htpy, Matrix.zero_mul]

private theorem htpy_incl_mul {ν' : Type*}
    (c : FilteredContraction degree grade D degree' grade' D') (M : Matrix κ ν' k) :
    c.htpy * (c.incl * M) = 0 := by
  rw [← Matrix.mul_assoc, c.htpy_mul_incl, Matrix.zero_mul]

private theorem htpy_htpy_mul {ν' : Type*}
    (c : FilteredContraction degree grade D degree' grade' D') (M : Matrix ι ν' k) :
    c.htpy * (c.htpy * M) = 0 := by
  rw [← Matrix.mul_assoc, c.htpy_mul_htpy, Matrix.zero_mul]

/-- Compose two filtered contractions: projections and inclusions compose, and the homotopy
is `htpy₁ + incl₁ * htpy₂ * proj₁`. -/
def trans (c₁ : FilteredContraction degree grade D degree' grade' D')
    (c₂ : FilteredContraction degree' grade' D' degree'' grade'' D'') :
    FilteredContraction degree grade D degree'' grade'' D'' where
  proj := c₂.proj * c₁.proj
  incl := c₁.incl * c₂.incl
  htpy := c₁.htpy + c₁.incl * c₂.htpy * c₁.proj
  proj_mul := by
    rw [Matrix.mul_assoc, c₁.proj_mul, ← Matrix.mul_assoc, c₂.proj_mul, Matrix.mul_assoc]
  mul_incl := by
    rw [← Matrix.mul_assoc, c₁.mul_incl, Matrix.mul_assoc, c₂.mul_incl, Matrix.mul_assoc]
  proj_mul_incl := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc c₁.proj, c₁.proj_mul_incl, Matrix.one_mul,
      c₂.proj_mul_incl]
  one_sub_incl_mul_proj := by
    have e : 1 - c₁.incl * c₂.incl * (c₂.proj * c₁.proj) =
        (1 - c₁.incl * c₁.proj) + c₁.incl * (1 - c₂.incl * c₂.proj) * c₁.proj := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [e, c₁.one_sub_incl_mul_proj, c₂.one_sub_incl_mul_proj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D c₁.incl, c₁.mul_incl, ← c₁.proj_mul]
    simp only [Matrix.mul_assoc]
    abel
  htpy_mul_htpy := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, c₁.htpy_mul_htpy,
      c₁.proj_mul_htpy, c₁.htpy_incl_mul, c₁.proj_incl_mul, c₂.htpy_htpy_mul,
      Matrix.mul_zero, add_zero]
  proj_mul_htpy := by
    simp only [Matrix.mul_add, Matrix.mul_assoc, c₁.proj_mul_htpy, c₁.proj_incl_mul,
      c₂.proj_htpy_mul, Matrix.mul_zero, add_zero]
  htpy_mul_incl := by
    simp only [Matrix.add_mul, Matrix.mul_assoc, c₁.htpy_incl_mul, c₁.proj_incl_mul,
      c₂.htpy_mul_incl, Matrix.mul_zero, zero_add]
  proj_degree := fun r x h => by
    obtain ⟨m, h₂, h₁⟩ := exists_of_mul_ne_zero h
    rw [c₂.proj_degree r m h₂, c₁.proj_degree m x h₁]
  incl_degree := fun x r h => by
    obtain ⟨m, h₁, h₂⟩ := exists_of_mul_ne_zero h
    rw [c₁.incl_degree x m h₁, c₂.incl_degree m r h₂]
  htpy_degree := fun x y h => by
    by_cases h₁ : c₁.htpy x y = 0
    · have h' : (c₁.incl * c₂.htpy * c₁.proj) x y ≠ 0 := by
        simpa [Matrix.add_apply, h₁] using h
      obtain ⟨m, hm, hp⟩ := exists_of_mul_ne_zero h'
      obtain ⟨n, hi, hh⟩ := exists_of_mul_ne_zero hm
      rw [c₁.incl_degree x n hi, c₂.htpy_degree n m hh, c₁.proj_degree m y hp]
    · exact c₁.htpy_degree x y h₁
  proj_grade := c₂.proj_grade.mul c₁.proj_grade
  incl_grade := c₁.incl_grade.mul c₂.incl_grade
  htpy_grade := c₁.htpy_grade.add ((c₁.incl_grade.mul c₂.htpy_grade).mul c₁.proj_grade)

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] in
private theorem submatrix_id_mul {ν' : Type*} (M : Matrix κ ι k) (N : Matrix ι ν' k)
    (f : μ → κ) :
    M.submatrix f id * N = (M * N).submatrix f id := by
  ext; simp [Matrix.mul_apply]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] in
private theorem mul_submatrix_id {ν' : Type*} (M : Matrix ν' ι k) (N : Matrix ι κ k)
    (f : μ → κ) :
    M * N.submatrix id f = (M * N).submatrix id f := by
  ext; simp [Matrix.mul_apply]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] in
private theorem submatrix_mul_submatrix {ν' μ' : Type*} (M : Matrix κ ι k) (N : Matrix ι ν' k)
    (f : μ → κ) (g : μ' → ν') :
    M.submatrix f id * N.submatrix id g = (M * N).submatrix f g := by
  ext; simp [Matrix.mul_apply]

/-- Transport the small complex of a filtered contraction along an equivalence of carriers. -/
def reindex (c : FilteredContraction degree grade D degree' grade' D') (e : κ ≃ μ) :
    FilteredContraction degree grade D (degree' ∘ e.symm) (grade' ∘ e.symm)
      (D'.submatrix e.symm e.symm) where
  proj := c.proj.submatrix e.symm id
  incl := c.incl.submatrix id e.symm
  htpy := c.htpy
  proj_mul := by
    rw [submatrix_id_mul, Matrix.submatrix_mul_equiv, c.proj_mul]
  mul_incl := by
    rw [mul_submatrix_id, Matrix.submatrix_mul_equiv, c.mul_incl]
  proj_mul_incl := by
    rw [submatrix_mul_submatrix, c.proj_mul_incl, Matrix.submatrix_one_equiv]
  one_sub_incl_mul_proj := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, c.one_sub_incl_mul_proj]
  htpy_mul_htpy := c.htpy_mul_htpy
  proj_mul_htpy := by
    rw [submatrix_id_mul, c.proj_mul_htpy]
    rfl
  htpy_mul_incl := by
    rw [mul_submatrix_id, c.htpy_mul_incl]
    rfl
  proj_degree := fun r x h => c.proj_degree (e.symm r) x h
  incl_degree := fun x r h => c.incl_degree x (e.symm r) h
  htpy_degree := c.htpy_degree
  proj_grade := fun r x h => c.proj_grade (e.symm r) x h
  incl_grade := fun x r h => c.incl_grade x (e.symm r) h
  htpy_grade := c.htpy_grade

/-- The composed projection is `proj₂ * proj₁`. -/
@[simp] theorem trans_proj (c₁ : FilteredContraction degree grade D degree' grade' D')
    (c₂ : FilteredContraction degree' grade' D' degree'' grade'' D'') :
    (c₁.trans c₂).proj = c₂.proj * c₁.proj := rfl

/-- The composed inclusion is `incl₁ * incl₂`. -/
@[simp] theorem trans_incl (c₁ : FilteredContraction degree grade D degree' grade' D')
    (c₂ : FilteredContraction degree' grade' D' degree'' grade'' D'') :
    (c₁.trans c₂).incl = c₁.incl * c₂.incl := rfl

/-- The composed homotopy is `htpy₁ + incl₁ * htpy₂ * proj₁`. -/
@[simp] theorem trans_htpy (c₁ : FilteredContraction degree grade D degree' grade' D')
    (c₂ : FilteredContraction degree' grade' D' degree'' grade'' D'') :
    (c₁.trans c₂).htpy = c₁.htpy + c₁.incl * c₂.htpy * c₁.proj := rfl

/-- The transported projection reindexes rows. -/
@[simp] theorem reindex_proj (c : FilteredContraction degree grade D degree' grade' D')
    (e : κ ≃ μ) : (c.reindex e).proj = c.proj.submatrix e.symm id := rfl

/-- The transported inclusion reindexes columns. -/
@[simp] theorem reindex_incl (c : FilteredContraction degree grade D degree' grade' D')
    (e : κ ≃ μ) : (c.reindex e).incl = c.incl.submatrix id e.symm := rfl

/-- Transport keeps the homotopy. -/
@[simp] theorem reindex_htpy (c : FilteredContraction degree grade D degree' grade' D')
    (e : κ ≃ μ) : (c.reindex e).htpy = c.htpy := rfl

/-- Cancelling one equal-grade unit pair of a filtered differential (#1071) is a filtered
contraction onto the survivors. -/
def ofUnitPair (hD : IsFilteredDifferential degree grade D) {a b : ι}
    (hp : IsUnitPair D a b) (hg : grade a = grade b) :
    FilteredContraction degree grade D (degree ∘ Subtype.val) (grade ∘ Subtype.val)
      (reducedDifferential D a b) where
  proj := projection D a b
  incl := inclusion D a b
  htpy := homotopy a b
  proj_mul := projection_mul hD.sq_zero hp
  mul_incl := mul_inclusion hD.sq_zero hp
  proj_mul_incl := projection_mul_inclusion hp.ne
  one_sub_incl_mul_proj := one_sub_inclusion_mul_projection hD.sq_zero hp
  htpy_mul_htpy := homotopy_mul_homotopy hp.ne
  proj_mul_htpy := projection_mul_homotopy hp.ne
  htpy_mul_incl := homotopy_mul_inclusion hp.ne
  proj_degree := projection_degree hD.toIsBasedDifferential hp
  incl_degree := inclusion_degree hD.toIsBasedDifferential hp
  htpy_degree := homotopy_degree hD.toIsBasedDifferential hp
  proj_grade := projection_gradeNonincreasing hD.grade_le hg
  incl_grade := inclusion_gradeNonincreasing hD.grade_le hg
  htpy_grade := homotopy_gradeNonincreasing hg

/-- The projection of `ofUnitPair` is `projection`. -/
@[simp] theorem ofUnitPair_proj (hD : IsFilteredDifferential degree grade D) {a b : ι}
    (hp : IsUnitPair D a b) (hg : grade a = grade b) :
    (ofUnitPair hD hp hg).proj = projection D a b := rfl

/-- The inclusion of `ofUnitPair` is `inclusion`. -/
@[simp] theorem ofUnitPair_incl (hD : IsFilteredDifferential degree grade D) {a b : ι}
    (hp : IsUnitPair D a b) (hg : grade a = grade b) :
    (ofUnitPair hD hp hg).incl = inclusion D a b := rfl

/-- The homotopy of `ofUnitPair` is `homotopy`. -/
@[simp] theorem ofUnitPair_htpy (hD : IsFilteredDifferential degree grade D) {a b : ι}
    (hp : IsUnitPair D a b) (hg : grade a = grade b) :
    (ofUnitPair hD hp hg).htpy = homotopy a b := rfl

/-- The small differential is `proj * D * incl`. -/
theorem differential_eq (c : FilteredContraction degree grade D degree' grade' D') :
    D' = c.proj * D * c.incl := by
  rw [c.proj_mul, Matrix.mul_assoc, c.proj_mul_incl, Matrix.mul_one]

/-- The small differential squares to zero when the large one does. -/
theorem sq_zero_target (c : FilteredContraction degree grade D degree' grade' D')
    (hD : D * D = 0) : D' * D' = 0 := by
  rw [c.differential_eq]
  have e : c.proj * D * c.incl * (c.proj * D * c.incl) =
      c.proj * (D * D) * c.incl - c.proj * D * (1 - c.incl * c.proj) * D * c.incl := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  rw [e, c.one_sub_incl_mul_proj]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, ← Matrix.mul_assoc D D,
    hD, Matrix.zero_mul, Matrix.mul_zero, add_zero, sub_zero]

/-- The small complex of a filtered contraction of a based differential is a based
differential. -/
theorem isBasedDifferential_target
    (c : FilteredContraction degree grade D degree' grade' D')
    (hD : IsBasedDifferential degree D) : IsBasedDifferential degree' D' := by
  refine ⟨c.sq_zero_target hD.sq_zero, ?_⟩
  intro r s h
  rw [c.differential_eq] at h
  obtain ⟨y, hxy, hy⟩ := exists_of_mul_ne_zero h
  obtain ⟨x, hx, hD'⟩ := exists_of_mul_ne_zero hxy
  rw [c.proj_degree r x hx, ← c.incl_degree y s hy, hD.lowers_degree x y hD']

/-- The small complex of a filtered contraction of a filtered differential is a filtered
differential. -/
theorem isFilteredDifferential_target
    (c : FilteredContraction degree grade D degree' grade' D')
    (hD : IsFilteredDifferential degree grade D) :
    IsFilteredDifferential degree' grade' D' := by
  refine ⟨c.isBasedDifferential_target hD.toIsBasedDifferential, ?_⟩
  rw [c.differential_eq]
  exact (c.proj_grade.mul hD.grade_le).mul c.incl_grade

/-- `proj (incl y) = y`. -/
theorem proj_mulVec_incl_mulVec (c : FilteredContraction degree grade D degree' grade' D')
    (y : κ → k) : c.proj.mulVec (c.incl.mulVec y) = y := by
  rw [Matrix.mulVec_mulVec, c.proj_mul_incl, Matrix.one_mulVec]

/-- `x - incl (proj x) = D (htpy x) + htpy (D x)`. -/
theorem sub_incl_mulVec_proj_mulVec
    (c : FilteredContraction degree grade D degree' grade' D') (x : ι → k) :
    x - c.incl.mulVec (c.proj.mulVec x) =
      D.mulVec (c.htpy.mulVec x) + c.htpy.mulVec (D.mulVec x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
    ← c.one_sub_incl_mul_proj, Matrix.sub_mulVec, Matrix.one_mulVec]

end FilteredContraction

end TDA.Persistence.Morse.Cancellation
