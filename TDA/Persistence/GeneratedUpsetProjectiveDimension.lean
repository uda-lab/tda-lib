import TDA.Persistence.GeneratedUpsetResolution
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Ordinary projective dimension of generated upsets

The signed-deletion resolution of a finite indexed family is a canonical categorical
projective resolution. Its zero terms above the number of generator occurrences give
ordinary projective dimension at most `m - 1`. Repeated labels are allowed, and the empty
family gives the zero module. This is the upper-bound part of BOOS Proposition 5.1;
shortestness and minimality are not asserted.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GeneratedUpsetResolution

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [Lattice P]

private theorem exact_of_pointwise {A B C : PModule.{u,0,u} k P}
    (a : A ⟶ B) (b : B ⟶ C) (w : a ≫ b = 0)
    (h : ∀ p (x : B.obj p), (b.app p).hom x = 0 →
      ∃ y : A.obj p, (a.app p).hom y = x) :
    (ShortComplex.mk a b w).Exact := by
  apply (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero _).mpr
  ext p x
  have hx : (b.app p).hom (((kernel.ι b).app p).hom x) = 0 := by
    exact congrArg (fun f => (f.app p).hom x) (kernel.condition b)
  obtain ⟨y, hy⟩ := h p _ hx
  change ((cokernel.π a).app p).hom (((kernel.ι b).app p).hom x) = 0
  rw [← hy]
  exact congrArg (fun f => (f.app p).hom y) (cokernel.condition a)

/-- The actual face-sum complex with its signed-deletion differential. -/
noncomputable abbrev chainComplex {m : ℕ} (f : Fin m → P) :
    ChainComplex (PModule.{u,0,u} k P) ℕ :=
  ChainComplex.of (term (k := k) f) (differential (k := k) f)
    (differential_comp_differential (k := k) f)

/-- The degree-`n + 1` differential is the existing signed-deletion map. -/
@[simp] theorem chainComplex_d {m : ℕ} (f : Fin m → P) (n : ℕ) :
    (chainComplex (k := k) f).d (n + 1) n = differential (k := k) f n :=
  ChainComplex.of_d _ _ _

/-- The degree-`n` object is the existing face sum. -/
@[simp] theorem chainComplex_X {m : ℕ} (f : Fin m → P) (n : ℕ) :
    (chainComplex (k := k) f).X n = term f n := rfl

/-- The canonical ordinary projective resolution of the generated-upset module. -/
noncomputable def projectiveResolution {m : ℕ} (f : Fin m → P) :
    ProjectiveResolution (SupportInterval.module (k := k) (generatedSupport f)
      (generatedSupport_ordConnected f)) where
  complex := chainComplex f
  projective := term_projective f
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation f, by
    rw [chainComplex_d]
    exact differential_comp_augmentation f⟩
  quasiIso := by
    constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _
          (by simp [chainComplex, ChainComplex.of.d]; rfl) (by rfl) (by rfl)]
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨exact_of_pointwise (differential (k := k) f 0) (augmentation f)
            (differential_comp_augmentation f) (augmentation_exact_at_zero f),
            (NatTrans.epi_iff_epi_app _).2 (fun p =>
              (ModuleCat.epi_iff_surjective _).2 (augmentation_surjective_at f p))⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by
            change 𝟙 (term f 1) ≫ differential f 0 =
              (chainComplex f).d 1 0 ≫ 𝟙 (term f 0)
            rw [chainComplex_d]
            simp)
          (by
            change 𝟙 (term f 0) ≫ augmentation f =
              ((ChainComplex.toSingle₀Equiv (chainComplex f)
                (SupportInterval.module (k := k) (generatedSupport f)
                  (generatedSupport_ordConnected f))).symm
                  ⟨augmentation f, _⟩).f 0 ≫ 𝟙 _
            rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
            simp)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
        apply (ShortComplex.exact_iff_of_iso ?_).2
          (exact_of_pointwise (differential (k := k) f (n + 1)) (differential f n)
            (differential_comp_differential f n) (fun p => differential_exact_at_succ f p n))
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by
            change 𝟙 (term f (n + 2)) ≫ differential f (n + 1) =
              (chainComplex f).d (n + 2) (n + 1) ≫ 𝟙 (term f (n + 1))
            rw [chainComplex_d]
            simp)
          (by
            change 𝟙 (term f (n + 1)) ≫ differential f n =
              (chainComplex f).d (n + 1) n ≫ 𝟙 (term f n)
            rw [chainComplex_d]
            simp)
      · apply ChainComplex.exactAt_succ_single_obj

/-- The canonical resolution has the existing face-sum chain complex. -/
@[simp] theorem projectiveResolution_complex {m : ℕ} (f : Fin m → P) :
    (projectiveResolution (k := k) f).complex = chainComplex f := rfl

/-- The canonical resolution uses the existing augmentation in degree zero. -/
@[simp] theorem projectiveResolution_augmentation {m : ℕ} (f : Fin m → P) :
    (projectiveResolution (k := k) f).π.f 0 = augmentation f :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- A module on the upset generated by `m` occurrences has ordinary projective
dimension at most `m - 1`. For `m = 0`, this is a bound on the zero module. -/
theorem generatedSupport_hasProjectiveDimensionLE {m : ℕ} (f : Fin m → P) :
    HasProjectiveDimensionLE (SupportInterval.module (k := k) (generatedSupport f)
      (generatedSupport_ordConnected f)) (m - 1) := by
  let := HasExt.standard (PModule.{u,0,u} k P)
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  obtain ⟨g, hg, rfl⟩ := (projectiveResolution (k := k) f).extMk_surjective e (i + 1) rfl
  have hz : IsZero ((projectiveResolution (k := k) f).complex.X i) :=
    term_isZero_of_degree_ge f (by omega)
  have heq : g = 0 := hz.eq_of_src _ _
  subst g
  simp

/-- The numerical ordinary projective dimension satisfies the occurrence-count bound. -/
theorem generatedSupport_projectiveDimension_le {m : ℕ} (f : Fin m → P) :
    projectiveDimension (SupportInterval.module (k := k) (generatedSupport f)
      (generatedSupport_ordConnected f)) ≤ (m - 1 : ℕ) :=
  (projectiveDimension_le_iff _ _).2 (generatedSupport_hasProjectiveDimensionLE f)


end TDA.Persistence.GeneratedUpsetResolution
