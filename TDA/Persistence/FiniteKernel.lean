import TDA.Persistence.FiniteTranslation
import TDA.Persistence.FiniteDecomposition
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual finite-chain kernels and translation-triviality

Evaluation identifies the categorical kernel with the component linear kernel.
Its inclusion and naturality detect exactly when an actual kernel structure map vanishes.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

/-- The actual kernel in the category of finite-chain persistence modules. -/
noncomputable abbrev finiteKernel (f : M ⟶ N) : PModule.{u,0,u} k (Fin s) := kernel f

/-- Evaluation of the actual kernel identifies its fiber with the component kernel. -/
noncomputable def finiteKernelFiberIso (f : M ⟶ N) (i : Fin s) :
    (finiteKernel f).obj i ≅ ModuleCat.of k (LinearMap.ker (f.app i).hom) :=
  PreservesKernel.iso ((evaluation (Fin s) (ModuleCat k)).obj i) f ≪≫
    ModuleCat.kernelIsoKer (f.app i)

/-- The fiber identification takes the actual kernel inclusion to the subtype map. -/
theorem finiteKernel_ι_fiberIso (f : M ⟶ N) (i : Fin s) :
    (finiteKernelFiberIso f i).inv ≫ (kernel.ι f).app i =
      ModuleCat.ofHom (LinearMap.ker (f.app i).hom).subtype := by
  simp only [finiteKernelFiberIso, Iso.trans_inv]
  have hp := PreservesKernel.iso_inv_ι ((evaluation (Fin s) (ModuleCat k)).obj i) f
  change (PreservesKernel.iso ((evaluation (Fin s) (ModuleCat k)).obj i) f).inv ≫
    (kernel.ι f).app i = kernel.ι (f.app i) at hp
  rw [Category.assoc, hp, ModuleCat.kernelIsoKer_inv_kernel_ι]

/-- Kernel fibers inherit finite dimensionality from source subspaces. -/
instance finiteKernel_finiteDimensional (f : M ⟶ N)
    [∀ i, FiniteDimensional k (M.obj i)] (i : Fin s) :
    FiniteDimensional k ((finiteKernel f).obj i) :=
  (finiteKernelFiberIso f i).toLinearEquiv.symm.finiteDimensional

/-- The actual kernel inclusion has precisely the component linear kernel as its range. -/
theorem finiteKernel_ι_range (f : M ⟶ N) (i : Fin s) :
    LinearMap.range ((kernel.ι f).app i).hom = LinearMap.ker (f.app i).hom := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    have h := congrArg (fun g : finiteKernel f ⟶ N => (g.app i).hom z) (kernel.condition f)
    exact h
  · intro hx
    refine ⟨(finiteKernelFiberIso f i).inv.hom ⟨x, hx⟩, ?_⟩
    exact congrArg (fun g : ModuleCat.of k (LinearMap.ker (f.app i).hom) ⟶ M.obj i =>
      g.hom ⟨x, hx⟩) (finiteKernel_ι_fiberIso f i)

/-- Actual kernel maps vanish exactly when the source transition kills the component kernel. -/
theorem finiteKernel_map_eq_zero_iff (f : M ⟶ N) {a b : Fin s} (h : a ≤ b) :
    structureMap (finiteKernel f) h = 0 ↔
      LinearMap.ker (f.app a).hom ≤ LinearMap.ker (structureMapLinear M h) := by
  have hn := (kernel.ι f).naturality (homOfLE h)
  change structureMap (finiteKernel f) h ≫ (kernel.ι f).app b =
    (kernel.ι f).app a ≫ structureMap M h at hn
  constructor
  · intro hz x hx
    rw [← finiteKernel_ι_range f a] at hx
    obtain ⟨z, rfl⟩ := hx
    have he := congrArg (fun g : (finiteKernel f).obj a ⟶ M.obj b => g.hom z) hn
    rw [hz, zero_comp] at he
    exact he.symm
  · intro hk
    apply (cancel_mono ((kernel.ι f).app b)).mp
    rw [zero_comp, hn]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact hk (by rw [← finiteKernel_ι_range f a]; exact ⟨z, rfl⟩)

/-- Shortness of the actual kernel is equivalent to the component kernel-killing condition. -/
theorem kernel_translationTrivial_iff (theta : Fin s →o Fin s)
    (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N) :
    TranslationTrivial theta hTheta (finiteKernel f) ↔
      ∀ i, LinearMap.ker (f.app i).hom ≤ LinearMap.ker (structureMapLinear M (hTheta i)) :=
  forall_congr' (fun i => finiteKernel_map_eq_zero_iff f (hTheta i))

end TDA.Persistence
