import TDA.Persistence.FiniteDecomposition
import TDA.Persistence.FiniteTranslation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual finite-chain cokernels and translation-triviality

The cokernel is mathlib's cokernel in the functor category. Evaluation and the
concrete module cokernel identify its fibers with the actual range quotients.
Vanishing of its structure maps is equivalent to a target-image inclusion.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

/-- The actual cokernel in the category of finite-chain persistence modules. -/
noncomputable abbrev finiteCokernel (f : M ⟶ N) : PModule.{u,0,u} k (Fin s) :=
  cokernel f

/-- Evaluation of the actual cokernel identifies its fiber with the range quotient. -/
noncomputable def finiteCokernelFiberIso (f : M ⟶ N) (i : Fin s) :
    (finiteCokernel f).obj i ≅ ModuleCat.of k (N.obj i ⧸ LinearMap.range (f.app i).hom) :=
  PreservesCokernel.iso ((evaluation (Fin s) (ModuleCat k)).obj i) f ≪≫
    ModuleCat.cokernelIsoRangeQuotient (f.app i)

/-- This fiber identification takes the actual cokernel projection to the quotient map. -/
theorem finiteCokernel_π_fiberIso (f : M ⟶ N) (i : Fin s) :
    (cokernel.π f).app i ≫ (finiteCokernelFiberIso f i).hom =
      ModuleCat.ofHom (LinearMap.range (f.app i).hom).mkQ := by
  simp only [finiteCokernelFiberIso, Iso.trans_hom]
  have hp := PreservesCokernel.π_iso_hom ((evaluation (Fin s) (ModuleCat k)).obj i) f
  change (cokernel.π f).app i ≫
    (PreservesCokernel.iso ((evaluation (Fin s) (ModuleCat k)).obj i) f).hom =
      cokernel.π (f.app i) at hp
  rw [← Category.assoc, hp, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]

/-- The cokernel fibers inherit finite dimensionality from the target quotients. -/
instance finiteCokernel_finiteDimensional (f : M ⟶ N)
    [∀ i, FiniteDimensional k (N.obj i)] (i : Fin s) :
    FiniteDimensional k ((finiteCokernel f).obj i) :=
  (finiteCokernelFiberIso f i).toLinearEquiv.symm.finiteDimensional

/-- A vector is killed by the actual cokernel projection exactly when it is in the image. -/
theorem finiteCokernel_π_eq_zero_iff (f : M ⟶ N) (i : Fin s) (y : N.obj i) :
    ((cokernel.π f).app i).hom y = 0 ↔ y ∈ LinearMap.range (f.app i).hom := by
  have he := congrArg (fun g : N.obj i ⟶
    ModuleCat.of k (N.obj i ⧸ LinearMap.range (f.app i).hom) => g.hom y)
      (finiteCokernel_π_fiberIso f i)
  change (finiteCokernelFiberIso f i).hom.hom (((cokernel.π f).app i).hom y) =
    (LinearMap.range (f.app i).hom).mkQ y at he
  rw [← Submodule.Quotient.mk_eq_zero]
  change _ ↔ (LinearMap.range (f.app i).hom).mkQ y = 0
  rw [← he]
  exact ((finiteCokernelFiberIso f i).toLinearEquiv.map_eq_zero_iff).symm

/-- Actual cokernel structure maps vanish precisely when the target image lies in the
component image at the later stage. No matching or dimension comparison is assumed. -/
theorem finiteCokernel_map_eq_zero_iff (f : M ⟶ N) {a b : Fin s} (h : a ≤ b) :
    structureMap (finiteCokernel f) h = 0 ↔
      LinearMap.range (structureMapLinear N h) ≤ LinearMap.range (f.app b).hom := by
  have hn := (cokernel.π f).naturality (homOfLE h)
  change structureMap N h ≫ (cokernel.π f).app b =
    (cokernel.π f).app a ≫ structureMap (finiteCokernel f) h at hn
  constructor
  · intro hz y hy
    obtain ⟨x, rfl⟩ := hy
    apply (finiteCokernel_π_eq_zero_iff f b _).mp
    have he := congrArg (fun g : N.obj a ⟶ (finiteCokernel f).obj b => g.hom x) hn
    change ((cokernel.π f).app b).hom (structureMapLinear N h x) =
      (structureMap (finiteCokernel f) h).hom (((cokernel.π f).app a).hom x) at he
    rw [hz] at he
    exact he
  · intro hi
    apply (cancel_epi ((cokernel.π f).app a)).mp
    rw [comp_zero, ← hn]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (finiteCokernel_π_eq_zero_iff f b _).mpr (hi ⟨x, rfl⟩)

/-- Shortness of the actual cokernel is equivalent to the target-image condition. -/
theorem cokernel_translationTrivial_iff (theta : Fin s →o Fin s)
    (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N) :
    TranslationTrivial theta hTheta (finiteCokernel f) ↔
      ∀ i, LinearMap.range (structureMapLinear N (hTheta i)) ≤
        LinearMap.range (f.app (theta i)).hom := by
  exact forall_congr' (fun i => finiteCokernel_map_eq_zero_iff f (hTheta i))

end TDA.Persistence
