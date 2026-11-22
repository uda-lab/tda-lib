import TDA.Persistence.Morse.FilteredContraction
import TDA.Persistence.Basic

/-!
# Grade-sublevel homology of a filtered based complex

For a based complex `(ι, degree, grade, D)` over a commutative ring `k`, in the column
convention of `TDA.Persistence.Morse.UnitCancellation`, `sublevelChains degree grade p t` is the
submodule of coordinate vectors supported in degree `p` (`DegreeSupported`) and in grades `≤ t`
(`SublevelSupported`). `sublevelCycles` adds `D.mulVec x = 0`, and `sublevelBoundaries` is the
image under `D` of `sublevelChains degree grade (p + 1) t`. `sublevelHomology` is the quotient
of the cycles by the boundaries that lie among them; for a filtered differential every boundary
is a cycle (`sublevelBoundaries_le_sublevelCycles`), so this is the usual homology. No
hypothesis on `D` enters the definitions. The inclusions of sublevels `t ≤ t'` induce
`sublevelHomologyMap`, and `sublevelHomologyPModule degree grade D p : PModule k ℤ` packages
the degree-`p` homology as a persistence module over the integer grades.

A `FilteredContraction degree grade D degree' grade' D'` `c` maps sublevel chains, cycles and
boundaries to sublevel chains, cycles and boundaries, by its degree and grade fields and its
chain-map equations. `c.sublevelHomologyEquiv p t` is the induced isomorphism of sublevel
homology, with forward map induced by `proj` and inverse induced by `incl`; the inverse laws
are `proj * incl = 1` and the homotopy identity, which writes `x - incl (proj x)` as the
boundary `D (htpy x)` of a degree-`p + 1` sublevel chain when `x` is a sublevel cycle.
`c.sublevelHomologyIso p` assembles these into a natural isomorphism of persistence modules,
and `c.finrank_sublevelHomology_eq` equates the dimensions. None of these statements needs
`D * D = 0`.

No simplicial bridge, Morse complex of a matching, or barcode statement is provided here.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.Morse.Cancellation

open CategoryTheory

section Support

variable {κ μ : Type*} {k : Type*}

/-- A coordinate vector vanishes outside homological degree `p`. -/
def DegreeSupported [Zero k] (degree : κ → ℕ) (p : ℕ) (x : κ → k) : Prop :=
  ∀ c, degree c ≠ p → x c = 0

/-- A matrix sending, on its support, columns of degree `p` to rows of degree `q` maps vectors
supported in degree `p` to vectors supported in degree `q`. -/
theorem DegreeSupported.mulVec [CommRing k] [Fintype μ] {dr : κ → ℕ} {dc : μ → ℕ}
    {M : Matrix κ μ k} {p q : ℕ} (hM : ∀ r c, M r c ≠ 0 → dc c = p → dr r = q)
    {x : μ → k} (hx : DegreeSupported dc p x) : DegreeSupported dr q (M.mulVec x) := by
  intro r hr
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : M r c = 0
  · simp [h]
  · by_cases hc : dc c = p
    · exact absurd (hM r c h hc) hr
    · rw [hx c hc, mul_zero]

end Support

section Homology

variable {ι : Type u} [Fintype ι] {k : Type v} [CommRing k]
  (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k)

/-- The chains of degree `p` supported in grades `≤ t`. -/
def sublevelChains (p : ℕ) (t : ℤ) : Submodule k (ι → k) where
  carrier := {x | DegreeSupported degree p x ∧ SublevelSupported grade t x}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨fun c hc => by simp [hx c hc, hy c hc], fun c hc => by simp [hx' c hc, hy' c hc]⟩
  smul_mem' := by
    rintro a x ⟨hx, hx'⟩
    exact ⟨fun c hc => by simp [hx c hc], fun c hc => by simp [hx' c hc]⟩

/-- The cycles of degree `p` supported in grades `≤ t`. -/
def sublevelCycles (p : ℕ) (t : ℤ) : Submodule k (ι → k) :=
  sublevelChains degree grade p t ⊓ LinearMap.ker D.mulVecLin

/-- The boundaries of degree-`p + 1` chains supported in grades `≤ t`. -/
def sublevelBoundaries (p : ℕ) (t : ℤ) : Submodule k (ι → k) :=
  (sublevelChains degree grade (p + 1) t).map D.mulVecLin

/-- Degree-`p` homology of the grade-`≤ t` sublevel: cycles modulo the boundaries among them. -/
abbrev sublevelHomology (p : ℕ) (t : ℤ) : Type (max u v) :=
  sublevelCycles degree grade D p t ⧸
    (sublevelBoundaries degree grade D p t).comap (sublevelCycles degree grade D p t).subtype

variable {degree grade D}

omit [Fintype ι] in
/-- Membership in `sublevelChains`. -/
theorem mem_sublevelChains {p : ℕ} {t : ℤ} {x : ι → k} :
    x ∈ sublevelChains degree grade p t ↔
      DegreeSupported degree p x ∧ SublevelSupported grade t x :=
  Iff.rfl

/-- Membership in `sublevelCycles`. -/
theorem mem_sublevelCycles {p : ℕ} {t : ℤ} {x : ι → k} :
    x ∈ sublevelCycles degree grade D p t ↔
      DegreeSupported degree p x ∧ SublevelSupported grade t x ∧ D.mulVec x = 0 := by
  simp [sublevelCycles, mem_sublevelChains, and_assoc]

/-- Membership in `sublevelBoundaries`. -/
theorem mem_sublevelBoundaries {p : ℕ} {t : ℤ} {x : ι → k} :
    x ∈ sublevelBoundaries degree grade D p t ↔
      ∃ y, DegreeSupported degree (p + 1) y ∧ SublevelSupported grade t y ∧
        D.mulVec y = x := by
  simp [sublevelBoundaries, mem_sublevelChains, and_assoc]

/-- For a filtered differential, the boundaries lie in the cycles. -/
theorem sublevelBoundaries_le_sublevelCycles
    (hD : IsFilteredDifferential degree grade D) (p : ℕ) (t : ℤ) :
    sublevelBoundaries degree grade D p t ≤ sublevelCycles degree grade D p t := by
  rintro x hx
  obtain ⟨y, hy, hy', rfl⟩ := mem_sublevelBoundaries.mp hx
  refine mem_sublevelCycles.mpr ⟨?_, hD.grade_le.mulVec_sublevelSupported hy', ?_⟩
  · exact DegreeSupported.mulVec (fun r c h hc => by
      have := hD.lowers_degree r c h; omega) hy
  · rw [Matrix.mulVec_mulVec, hD.sq_zero, Matrix.zero_mulVec]

omit [Fintype ι] in
/-- Sublevel chains grow with the grade. -/
theorem sublevelChains_mono {p : ℕ} {t t' : ℤ} (h : t ≤ t') :
    sublevelChains degree grade p t ≤ sublevelChains (k := k) degree grade p t' :=
  fun _ hx => ⟨hx.1, fun c hc => hx.2 c (lt_of_le_of_lt h hc)⟩

/-- Sublevel cycles grow with the grade. -/
theorem sublevelCycles_mono {p : ℕ} {t t' : ℤ} (h : t ≤ t') :
    sublevelCycles degree grade D p t ≤ sublevelCycles degree grade D p t' :=
  inf_le_inf_right _ (sublevelChains_mono h)

/-- Sublevel boundaries grow with the grade. -/
theorem sublevelBoundaries_mono {p : ℕ} {t t' : ℤ} (h : t ≤ t') :
    sublevelBoundaries degree grade D p t ≤ sublevelBoundaries degree grade D p t' :=
  Submodule.map_mono (sublevelChains_mono h)

variable (degree grade D)

/-- The map of sublevel homology induced by the inclusion of grade sublevels `t ≤ t'`. -/
noncomputable def sublevelHomologyMap (p : ℕ) {t t' : ℤ} (h : t ≤ t') :
    sublevelHomology degree grade D p t →ₗ[k] sublevelHomology degree grade D p t' :=
  Submodule.mapQ _ _ (Submodule.inclusion (sublevelCycles_mono h))
    (fun _ hx => sublevelBoundaries_mono h hx)

variable {degree grade D}

/-- The structure map keeps the representing cycle. -/
@[simp] theorem sublevelHomologyMap_mk (p : ℕ) {t t' : ℤ} (h : t ≤ t')
    (x : sublevelCycles degree grade D p t) :
    sublevelHomologyMap degree grade D p h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion (sublevelCycles_mono h) x) :=
  rfl

/-- The structure map of `t ≤ t` is the identity. -/
theorem sublevelHomologyMap_id (p : ℕ) (t : ℤ) :
    sublevelHomologyMap degree grade D p (le_refl t) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  rfl

/-- Structure maps compose. -/
theorem sublevelHomologyMap_comp (p : ℕ) {t t' t'' : ℤ} (h : t ≤ t') (h' : t' ≤ t'') :
    sublevelHomologyMap degree grade D p (h.trans h') =
      sublevelHomologyMap degree grade D p h' ∘ₗ sublevelHomologyMap degree grade D p h := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  rfl

variable (degree grade D)

/-- Degree-`p` grade-sublevel homology as a persistence module over `ℤ`. -/
noncomputable def sublevelHomologyPModule (p : ℕ) : PModule.{v, 0, max u v} k ℤ where
  obj t := ModuleCat.of k (sublevelHomology degree grade D p t)
  map f := ModuleCat.ofHom (sublevelHomologyMap degree grade D p (leOfHom f))
  map_id t := by
    rw [sublevelHomologyMap_id]
    rfl
  map_comp f g := by
    rw [sublevelHomologyMap_comp p (leOfHom f) (leOfHom g)]
    rfl

/-- The value of the persistence module at `t` is the sublevel homology at `t`. -/
theorem sublevelHomologyPModule_obj (p : ℕ) (t : ℤ) :
    (sublevelHomologyPModule degree grade D p).obj t =
      ModuleCat.of k (sublevelHomology degree grade D p t) :=
  rfl

/-- The structure maps of the persistence module are `sublevelHomologyMap`. -/
@[simp] theorem structureMapLinear_sublevelHomologyPModule (p : ℕ) {t t' : ℤ} (h : t ≤ t') :
    structureMapLinear (sublevelHomologyPModule degree grade D p) h =
      sublevelHomologyMap degree grade D p h :=
  rfl

end Homology

namespace FilteredContraction

variable {ι : Type u} {κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {k : Type v} [CommRing k]
  {degree : ι → ℕ} {grade : ι → ℤ} {D : Matrix ι ι k}
  {degree' : κ → ℕ} {grade' : κ → ℤ} {D' : Matrix κ κ k}
  (c : FilteredContraction degree grade D degree' grade' D')

/-- `proj` preserves sublevel chains. -/
theorem proj_mem_sublevelChains {p : ℕ} {t : ℤ} {x : ι → k}
    (hx : x ∈ sublevelChains degree grade p t) :
    c.proj.mulVec x ∈ sublevelChains degree' grade' p t :=
  ⟨DegreeSupported.mulVec (fun r y h hy => (c.proj_degree r y h).trans hy) hx.1,
    c.proj_grade.mulVec_sublevelSupported hx.2⟩

/-- `incl` preserves sublevel chains. -/
theorem incl_mem_sublevelChains {p : ℕ} {t : ℤ} {y : κ → k}
    (hy : y ∈ sublevelChains degree' grade' p t) :
    c.incl.mulVec y ∈ sublevelChains degree grade p t :=
  ⟨DegreeSupported.mulVec (fun r y h hy => (c.incl_degree r y h).trans hy) hy.1,
    c.incl_grade.mulVec_sublevelSupported hy.2⟩

/-- `htpy` sends sublevel chains of degree `p` to sublevel chains of degree `p + 1`. -/
theorem htpy_mem_sublevelChains {p : ℕ} {t : ℤ} {x : ι → k}
    (hx : x ∈ sublevelChains degree grade p t) :
    c.htpy.mulVec x ∈ sublevelChains degree grade (p + 1) t :=
  ⟨DegreeSupported.mulVec (fun r y h hy => by rw [c.htpy_degree r y h, hy]) hx.1,
    c.htpy_grade.mulVec_sublevelSupported hx.2⟩

/-- Vector form of `proj * D = D' * proj`. -/
theorem proj_mulVec_mul (x : ι → k) :
    D'.mulVec (c.proj.mulVec x) = c.proj.mulVec (D.mulVec x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, c.proj_mul]

/-- Vector form of `D * incl = incl * D'`. -/
theorem incl_mulVec_mul (y : κ → k) :
    D.mulVec (c.incl.mulVec y) = c.incl.mulVec (D'.mulVec y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, c.mul_incl]

/-- `proj` preserves sublevel cycles. -/
theorem proj_mem_sublevelCycles {p : ℕ} {t : ℤ} {x : ι → k}
    (hx : x ∈ sublevelCycles degree grade D p t) :
    c.proj.mulVec x ∈ sublevelCycles degree' grade' D' p t := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_sublevelCycles.mp hx
  obtain ⟨h₁', h₂'⟩ := c.proj_mem_sublevelChains (p := p) (t := t) ⟨h₁, h₂⟩
  exact mem_sublevelCycles.mpr
    ⟨h₁', h₂', by rw [c.proj_mulVec_mul, h₃, Matrix.mulVec_zero]⟩

/-- `incl` preserves sublevel cycles. -/
theorem incl_mem_sublevelCycles {p : ℕ} {t : ℤ} {y : κ → k}
    (hy : y ∈ sublevelCycles degree' grade' D' p t) :
    c.incl.mulVec y ∈ sublevelCycles degree grade D p t := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_sublevelCycles.mp hy
  obtain ⟨h₁', h₂'⟩ := c.incl_mem_sublevelChains (p := p) (t := t) ⟨h₁, h₂⟩
  exact mem_sublevelCycles.mpr
    ⟨h₁', h₂', by rw [c.incl_mulVec_mul, h₃, Matrix.mulVec_zero]⟩

/-- `proj` preserves sublevel boundaries. -/
theorem proj_mem_sublevelBoundaries {p : ℕ} {t : ℤ} {x : ι → k}
    (hx : x ∈ sublevelBoundaries degree grade D p t) :
    c.proj.mulVec x ∈ sublevelBoundaries degree' grade' D' p t := by
  obtain ⟨y, h₁, h₂, rfl⟩ := mem_sublevelBoundaries.mp hx
  obtain ⟨h₁', h₂'⟩ := c.proj_mem_sublevelChains (p := p + 1) (t := t) ⟨h₁, h₂⟩
  exact mem_sublevelBoundaries.mpr ⟨_, h₁', h₂', c.proj_mulVec_mul y⟩

/-- `incl` preserves sublevel boundaries. -/
theorem incl_mem_sublevelBoundaries {p : ℕ} {t : ℤ} {y : κ → k}
    (hy : y ∈ sublevelBoundaries degree' grade' D' p t) :
    c.incl.mulVec y ∈ sublevelBoundaries degree grade D p t := by
  obtain ⟨z, h₁, h₂, rfl⟩ := mem_sublevelBoundaries.mp hy
  obtain ⟨h₁', h₂'⟩ := c.incl_mem_sublevelChains (p := p + 1) (t := t) ⟨h₁, h₂⟩
  exact mem_sublevelBoundaries.mpr ⟨_, h₁', h₂', c.incl_mulVec_mul z⟩

/-- A cycle differs from `incl (proj x)` by the boundary of `htpy x`. -/
theorem sub_incl_proj_mem_sublevelBoundaries {p : ℕ} {t : ℤ} {x : ι → k}
    (hx : x ∈ sublevelCycles degree grade D p t) :
    x - c.incl.mulVec (c.proj.mulVec x) ∈ sublevelBoundaries degree grade D p t := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_sublevelCycles.mp hx
  obtain ⟨h₁', h₂'⟩ := c.htpy_mem_sublevelChains (p := p) (t := t) ⟨h₁, h₂⟩
  refine mem_sublevelBoundaries.mpr ⟨_, h₁', h₂', ?_⟩
  rw [c.sub_incl_mulVec_proj_mulVec, h₃, Matrix.mulVec_zero, add_zero]

/-- The map of sublevel homology induced by `proj`. -/
noncomputable def homologyProj (p : ℕ) (t : ℤ) :
    sublevelHomology degree grade D p t →ₗ[k] sublevelHomology degree' grade' D' p t :=
  Submodule.mapQ _ _ (c.proj.mulVecLin.restrict fun _ hx => c.proj_mem_sublevelCycles hx)
    (fun _ hx => c.proj_mem_sublevelBoundaries hx)

/-- The map of sublevel homology induced by `incl`. -/
noncomputable def homologyIncl (p : ℕ) (t : ℤ) :
    sublevelHomology degree' grade' D' p t →ₗ[k] sublevelHomology degree grade D p t :=
  Submodule.mapQ _ _ (c.incl.mulVecLin.restrict fun _ hy => c.incl_mem_sublevelCycles hy)
    (fun _ hy => c.incl_mem_sublevelBoundaries hy)

/-- `homologyProj` on a represented class. -/
@[simp] theorem homologyProj_mk (p : ℕ) (t : ℤ) (x : sublevelCycles degree grade D p t) :
    c.homologyProj p t (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨c.proj.mulVec x, c.proj_mem_sublevelCycles x.2⟩ :=
  rfl

/-- `homologyIncl` on a represented class. -/
@[simp] theorem homologyIncl_mk (p : ℕ) (t : ℤ) (y : sublevelCycles degree' grade' D' p t) :
    c.homologyIncl p t (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨c.incl.mulVec y, c.incl_mem_sublevelCycles y.2⟩ :=
  rfl

/-- **Per-grade homology equivalence.** At every degree `p` and grade `t`, `proj` induces an
isomorphism of grade-sublevel homology, with inverse induced by `incl`. -/
noncomputable def sublevelHomologyEquiv (p : ℕ) (t : ℤ) :
    sublevelHomology degree grade D p t ≃ₗ[k] sublevelHomology degree' grade' D' p t :=
  LinearEquiv.ofLinearMap (c.homologyProj p t) (c.homologyIncl p t)
    (Submodule.linearMap_qext _ (LinearMap.ext fun y => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (c.proj_mulVec_incl_mulVec y)))
    (Submodule.linearMap_qext _ (LinearMap.ext fun x => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      have h := (sublevelBoundaries degree grade D p t).neg_mem
        (c.sub_incl_proj_mem_sublevelBoundaries x.2)
      rw [neg_sub] at h
      exact h))

/-- The forward map of `sublevelHomologyEquiv` is `homologyProj`. -/
@[simp] theorem sublevelHomologyEquiv_apply (p : ℕ) (t : ℤ)
    (z : sublevelHomology degree grade D p t) :
    c.sublevelHomologyEquiv p t z = c.homologyProj p t z :=
  rfl

/-- The inverse of `sublevelHomologyEquiv` is `homologyIncl`. -/
@[simp] theorem sublevelHomologyEquiv_symm_apply (p : ℕ) (t : ℤ)
    (z : sublevelHomology degree' grade' D' p t) :
    (c.sublevelHomologyEquiv p t).symm z = c.homologyIncl p t z :=
  rfl

/-- `proj` commutes with the structure maps. -/
theorem homologyProj_comp_sublevelHomologyMap (p : ℕ) {t t' : ℤ} (h : t ≤ t') :
    c.homologyProj p t' ∘ₗ sublevelHomologyMap degree grade D p h =
      sublevelHomologyMap degree' grade' D' p h ∘ₗ c.homologyProj p t := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  rfl

/-- **Natural isomorphism of persistence modules.** A filtered contraction induces, in every
degree `p`, an isomorphism of grade-sublevel homology persistence modules whose components are
induced by `proj`. -/
noncomputable def sublevelHomologyIso (p : ℕ) :
    sublevelHomologyPModule degree grade D p ≅ sublevelHomologyPModule degree' grade' D' p :=
  NatIso.ofComponents (fun t => (c.sublevelHomologyEquiv p t).toModuleIso) (fun {t t'} f => by
    exact ModuleCat.hom_ext (c.homologyProj_comp_sublevelHomologyMap p (leOfHom f)))

/-- The components of `sublevelHomologyIso` are `homologyProj`. -/
@[simp] theorem sublevelHomologyIso_hom_app (p : ℕ) (t : ℤ) :
    ((c.sublevelHomologyIso p).hom.app t).hom = c.homologyProj p t :=
  rfl

/-- The components of the inverse of `sublevelHomologyIso` are `homologyIncl`. -/
@[simp] theorem sublevelHomologyIso_inv_app (p : ℕ) (t : ℤ) :
    ((c.sublevelHomologyIso p).inv.app t).hom = c.homologyIncl p t :=
  rfl

include c in
/-- The two complexes have equal sublevel homology dimensions. -/
theorem finrank_sublevelHomology_eq (p : ℕ) (t : ℤ) :
    Module.finrank k (sublevelHomology degree grade D p t) =
      Module.finrank k (sublevelHomology degree' grade' D' p t) :=
  (c.sublevelHomologyEquiv p t).finrank_eq

end FilteredContraction

end TDA.Persistence.Morse.Cancellation
