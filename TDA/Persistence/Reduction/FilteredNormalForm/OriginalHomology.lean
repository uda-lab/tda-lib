import TDA.Persistence.Reduction.FilteredNormalForm.NormalHomology

/-!
# Filtered normal form: homology of the original differential

Transport of the normal-coordinate description through `normalMatrix R V`.  All chain
and homology statements here use the original differential `D`, not the reduced
matrix `R = D * V`.
-/

namespace TDA.Persistence.Reduction

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

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
