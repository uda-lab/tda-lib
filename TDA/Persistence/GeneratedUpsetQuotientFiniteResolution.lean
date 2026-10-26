import TDA.Persistence.GeneratedUpsetQuotientResolution
import TDA.Persistence.FiniteRankProjectiveResolutionKan
import Mathlib.Tactic

/-!
# Finite rank-projective bundles for hook quotients

For a finite occurrence-indexed family of births, the actual hook-quotient complex has a
finite rank-projective resolution with `m` terms indexed by `Fin m`; each term remains the
face-indexed hook sum from `GeneratedUpsetQuotientResolution`. Its rows use the actual
categorical kernels and quotient differentials from that complex.
The last kernel is zero because the quotient term in degree `m` vanishes. For nonempty
families, the same resolution transports to the interval module on the complement of the
generated upset.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GeneratedUpsetQuotientFiniteResolution

open CategoryTheory CategoryTheory.Limits
open GeneratedUpsetResolution

variable {k : Type u} [Field k] {P : Type} [Lattice P] [OrderBot P]

/-- The natural-indexed kernels of the augmented hook-quotient complex.

The initial kernel is the quotient target, the next is the augmentation kernel, and every
later kernel is the kernel of the preceding quotient differential. -/
noncomputable def kernelAt {m : ℕ} (f : Fin m → P) (r : ℕ) : PModule.{u,0,u} k P :=
  match r with
  | 0 => GeneratedUpsetQuotientResolution.target (k := k) f
  | 1 => kernel (GeneratedUpsetQuotientResolution.augmentation (k := k) f)
  | n + 2 => kernel (GeneratedUpsetQuotientResolution.differential (k := k) f n)

@[simp] theorem kernelAt_zero {m : ℕ} (f : Fin m → P) :
    kernelAt (k := k) f 0 = GeneratedUpsetQuotientResolution.target (k := k) f := rfl

@[simp] theorem kernelAt_one {m : ℕ} (f : Fin m → P) :
    kernelAt (k := k) f 1 = kernel (GeneratedUpsetQuotientResolution.augmentation (k := k) f) := rfl

@[simp] theorem kernelAt_succ_succ {m : ℕ} (f : Fin m → P) (r : ℕ) :
    kernelAt (k := k) f (r + 2) =
      kernel (GeneratedUpsetQuotientResolution.differential (k := k) f r) := rfl

/-- The actual kernel inclusion in the row whose middle term is quotient degree `r`. -/
noncomputable def kernelInclusionAt {m : ℕ} (f : Fin m → P) :
    (r : ℕ) → kernelAt (k := k) f (r + 1) ⟶
      GeneratedUpsetQuotientResolution.term (k := k) f r
  | 0 => kernel.ι (GeneratedUpsetQuotientResolution.augmentation (k := k) f)
  | r + 1 => kernel.ι (GeneratedUpsetQuotientResolution.differential (k := k) f r)

@[simp] theorem kernelInclusionAt_zero {m : ℕ} (f : Fin m → P) :
    kernelInclusionAt (k := k) f 0 =
      kernel.ι (GeneratedUpsetQuotientResolution.augmentation (k := k) f) := rfl

@[simp] theorem kernelInclusionAt_succ {m : ℕ} (f : Fin m → P) (r : ℕ) :
    kernelInclusionAt (k := k) f (r + 1) =
      kernel.ι (GeneratedUpsetQuotientResolution.differential (k := k) f r) := rfl

/-- The actual quotient map onto the kernel at the start of the row. -/
noncomputable def kernelQuotientAt {m : ℕ} (f : Fin m → P) :
    (r : ℕ) → GeneratedUpsetQuotientResolution.term (k := k) f r ⟶
      kernelAt (k := k) f r
  | 0 => GeneratedUpsetQuotientResolution.augmentation (k := k) f
  | 1 => kernelRowLift (GeneratedUpsetQuotientResolution.augmentation_range_eq_ker (k := k) f)
  | r + 2 => kernelRowLift (GeneratedUpsetQuotientResolution.differential_range_eq_ker (k := k) f r)

@[simp] theorem kernelQuotientAt_zero {m : ℕ} (f : Fin m → P) :
    kernelQuotientAt (k := k) f 0 =
      GeneratedUpsetQuotientResolution.augmentation (k := k) f := rfl

@[simp] theorem kernelQuotientAt_one {m : ℕ} (f : Fin m → P) :
    kernelQuotientAt (k := k) f 1 =
      kernelRowLift (GeneratedUpsetQuotientResolution.augmentation_range_eq_ker (k := k) f) := rfl

@[simp] theorem kernelQuotientAt_succ_succ {m : ℕ} (f : Fin m → P) (r : ℕ) :
    kernelQuotientAt (k := k) f (r + 2) =
      kernelRowLift (GeneratedUpsetQuotientResolution.differential_range_eq_ker (k := k) f r) := rfl

/-- Every natural-indexed row is the actual rank-exact row proved for the quotient complex. -/
theorem row_rankExact {m : ℕ} (f : Fin m → P) (r : ℕ) :
    IsRankExact (kernelInclusionAt (k := k) f r) (kernelQuotientAt (k := k) f r) := by
  cases r with
  | zero => exact GeneratedUpsetQuotientResolution.augmentation_rankExact (k := k) f
  | succ r =>
    cases r with
    | zero => exact GeneratedUpsetQuotientResolution.zero_kernelRow_rankExact (k := k) f
    | succ r =>
      simpa [kernelInclusionAt, kernelQuotientAt] using
        GeneratedUpsetQuotientResolution.succ_kernelRow_rankExact (k := k) f r

/-- A row quotient followed by the preceding kernel inclusion is the original differential. -/
@[reassoc (attr := simp)] theorem quotient_comp_preceding_inclusion {m : ℕ}
    (f : Fin m → P) (r : ℕ) :
    kernelQuotientAt (k := k) f (r + 1) ≫ kernelInclusionAt (k := k) f r =
      GeneratedUpsetQuotientResolution.differential (k := k) f r := by
  cases r with
  | zero =>
    exact kernelRowLift_ι
      (GeneratedUpsetQuotientResolution.augmentation_range_eq_ker (k := k) f)
  | succ r =>
    exact kernelRowLift_ι
      (GeneratedUpsetQuotientResolution.differential_range_eq_ker (k := k) f r)

/-- The last natural-indexed kernel vanishes, including the empty family.

The row at index `m` makes `Q_m → K_m` epic. The source `Q_m` is zero by the quotient
complex's degree bound; at `m = 0` this is the augmentation row. -/
theorem terminalKernel_isZero {m : ℕ} (f : Fin m → P) :
    IsZero (kernelAt (k := k) f m) := by
  let hrow := row_rankExact (k := k) f m
  haveI : Epi (kernelQuotientAt (k := k) f m) :=
    (NatTrans.epi_iff_epi_app (kernelQuotientAt (k := k) f m)).mpr fun p =>
      (ModuleCat.epi_iff_surjective _).mpr (hrow.surjective p)
  exact IsZero.of_epi (kernelQuotientAt (k := k) f m)
    (GeneratedUpsetQuotientResolution.term_isZero_of_degree_ge (k := k) f (Nat.le_refl m))

/-- The actual hook quotient complex, packaged with exactly `m` occurrence-indexed terms. -/
noncomputable def resolution {m : ℕ} (f : Fin m → P) :
    FiniteRankProjectiveResolution (GeneratedUpsetQuotientResolution.target (k := k) f) := by
  refine ⟨{
    length := m
    kernel := fun i => kernelAt f i.val
    term := fun i => GeneratedUpsetQuotientResolution.term (k := k) f i.val
    inclusion := fun i => kernelInclusionAt f i.val
    quotient := fun i => kernelQuotientAt f i.val
    row_rank_exact := fun i => row_rankExact (k := k) f i.val
    initial_iso := Iso.refl (GeneratedUpsetQuotientResolution.target (k := k) f)
    terminal_iso := IsZero.isoZero (terminalKernel_isZero (k := k) f)
  }, ?_⟩
  intro i
  exact GeneratedUpsetQuotientResolution.term_rankProjective (k := k) f i.val

@[simp] theorem resolution_length {m : ℕ} (f : Fin m → P) :
    (resolution (k := k) f).length = m := rfl

@[simp] theorem resolution_term {m : ℕ} (f : Fin m → P) (i : Fin m) :
    (resolution (k := k) f).term i = GeneratedUpsetQuotientResolution.term (k := k) f i.val := rfl

@[simp] theorem resolution_kernel {m : ℕ} (f : Fin m → P) (i : Fin (m + 1)) :
    (resolution (k := k) f).kernel i = kernelAt (k := k) f i.val := rfl

@[simp] theorem resolution_inclusion {m : ℕ} (f : Fin m → P) (i : Fin m) :
    (resolution (k := k) f).inclusion i = kernelInclusionAt (k := k) f i.val := by
  rfl

@[simp] theorem resolution_quotient {m : ℕ} (f : Fin m → P) (i : Fin m) :
    (resolution (k := k) f).quotient i = kernelQuotientAt (k := k) f i.val := rfl

@[simp] theorem resolution_initial_iso_hom {m : ℕ} (f : Fin m → P) :
    (resolution (k := k) f).initial_iso.hom = 𝟙 _ := rfl

/-- The first row quotient is exactly the actual augmentation to the cokernel target. -/
@[simp] theorem resolution_augmentation {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    (resolution (k := k) f).quotient ⟨0, hm⟩ =
      GeneratedUpsetQuotientResolution.augmentation (k := k) f := rfl

/-- In each positive row, the quotient and preceding inclusion recover the quotient
complex's differential. This law avoids unfolding the finite-indexed bundle. -/
@[reassoc (attr := simp)] theorem resolution_differential {m : ℕ} (f : Fin m → P)
    (r : ℕ) (hr : r + 1 < m) :
    (resolution (k := k) f).quotient
        (Fin.cast (resolution_length (k := k) f).symm ⟨r + 1, hr⟩) ≫
        (resolution (k := k) f).inclusion
          (Fin.cast (resolution_length (k := k) f).symm ⟨r, by omega⟩) =
      GeneratedUpsetQuotientResolution.differential (k := k) f r := by
  simpa [resolution, kernelQuotientAt, kernelInclusionAt] using
    quotient_comp_preceding_inclusion (k := k) f r

/-- The finite bundle resolves the lower-complement interval module for a nonempty family. -/
noncomputable def complementResolution {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    FiniteRankProjectiveResolution
      (SupportInterval.module (k := k)
        (GeneratedUpsetQuotientResolution.complementSupport f)
        (GeneratedUpsetQuotientResolution.complementSupport_ordConnected f)) :=
  FiniteRankProjectiveResolution.ofIso (resolution (k := k) f)
    (GeneratedUpsetQuotientResolution.targetIso (k := k) f hm)

@[simp] theorem complementResolution_length {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    (complementResolution (k := k) f hm).length = m := rfl

@[simp] theorem complementResolution_term {m : ℕ} (f : Fin m → P) (hm : 0 < m)
    (i : Fin m) :
      (complementResolution (k := k) f hm).term
        ⟨i.val, by simpa only [complementResolution_length] using i.isLt⟩ =
          GeneratedUpsetQuotientResolution.term (k := k) f i.val := by
  rfl

@[simp] theorem complementResolution_initial_iso_hom {m : ℕ} (f : Fin m → P)
    (hm : 0 < m) :
    (complementResolution f hm).initial_iso.hom =
      (GeneratedUpsetQuotientResolution.targetIso (k := k) f hm).hom := by
  simp [complementResolution, FiniteRankProjectiveResolution.ofIso, resolution, kernelAt]

/-- The transported augmentation equals the actual quotient augmentation followed by
`targetIso`; its defining projection law is exposed by
`complement_augmentation_projection` below. -/
@[reassoc (attr := simp)] theorem complement_augmentation {m : ℕ} (f : Fin m → P)
    (hm : 0 < m) :
    (complementResolution (k := k) f hm).quotient
        ⟨0, by simpa only [complementResolution_length] using hm⟩ ≫
        (complementResolution (k := k) f hm).initial_iso.hom =
      GeneratedUpsetQuotientResolution.augmentation (k := k) f ≫
        (GeneratedUpsetQuotientResolution.targetIso (k := k) f hm).hom := by
  simp [complementResolution, FiniteRankProjectiveResolution.ofIso, resolution, kernelAt]

/-- Composing the actual first quotient row with the complement identification recovers
the coefficient projection from the constant-bottom support. Together with
`complement_augmentation`, this identifies the transported bundle's initial row with the
actual quotient projection. -/
@[reassoc (attr := simp)] theorem complement_augmentation_projection {m : ℕ}
    (f : Fin m → P) (hm : 0 < m) :
    cokernel.π (GeneratedUpsetQuotientResolution.inclusion (k := k) f 0) ≫
        (resolution (k := k) f).quotient ⟨0, hm⟩ ≫
          (GeneratedUpsetQuotientResolution.targetIso (k := k) f hm).hom =
      GeneratedUpsetResolution.augmentation (GeneratedUpsetQuotientResolution.bottomFamily m) ≫
      GeneratedUpsetQuotientResolution.targetProjection (k := k) f hm := by
  calc
    _ = (cokernel.π (GeneratedUpsetQuotientResolution.inclusion (k := k) f 0) ≫
        GeneratedUpsetQuotientResolution.augmentation (k := k) f) ≫
          (GeneratedUpsetQuotientResolution.targetIso (k := k) f hm).hom := by
      simp
    _ = (GeneratedUpsetResolution.augmentation
        (GeneratedUpsetQuotientResolution.bottomFamily m) ≫
          cokernel.π (GeneratedUpsetQuotientResolution.supportInclusion (k := k) f)) ≫
            (GeneratedUpsetQuotientResolution.targetIso (k := k) f hm).hom := by
      rw [GeneratedUpsetQuotientResolution.projection_augmentation]
    _ = GeneratedUpsetResolution.augmentation
        (GeneratedUpsetQuotientResolution.bottomFamily m) ≫
          GeneratedUpsetQuotientResolution.targetProjection (k := k) f hm := by
      rw [Category.assoc, GeneratedUpsetQuotientResolution.projection_targetIso]

/-- The bundled Euler formula for the actual cokernel target. -/
theorem rank_eq_alternating_sum {m : ℕ} (f : Fin m → P) {a b : P} (hab : a ≤ b) :
    (rankOfStructureMap (k := k) (GeneratedUpsetQuotientResolution.target (k := k) f) hab : ℤ) =
      ∑ i : Fin m, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (k := k)
          (GeneratedUpsetQuotientResolution.term (k := k) f i.val) hab : ℤ) :=
  FiniteRankProjectiveResolution.rank_eq_alternating_sum (resolution (k := k) f) hab

/-- For a nonempty family, the complement interval has the same bundled Euler formula,
with the same `m` occurrence-indexed quotient terms. -/
theorem complement_rank_eq_alternating_sum {m : ℕ} (f : Fin m → P) (hm : 0 < m)
    {a b : P} (hab : a ≤ b) :
      (rankOfStructureMap (k := k)
      (SupportInterval.module (k := k)
        (GeneratedUpsetQuotientResolution.complementSupport f)
        (GeneratedUpsetQuotientResolution.complementSupport_ordConnected f)) hab : ℤ) =
      ∑ i : Fin m, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (k := k)
          (GeneratedUpsetQuotientResolution.term (k := k) f i.val) hab : ℤ) :=
  FiniteRankProjectiveResolution.rank_eq_alternating_sum
    (complementResolution (k := k) f hm) hab

end TDA.Persistence.GeneratedUpsetQuotientFiniteResolution
