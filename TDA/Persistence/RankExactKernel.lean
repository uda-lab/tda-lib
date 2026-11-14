import TDA.Persistence.RankDeflation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Pointwise exact sequences and actual categorical kernels

An injective first map whose image is the second map's kernel identifies
the given left term with the actual categorical kernel. This comparison
preserves the given inclusion, so kernel terms in rank-exact sequences
can be transported without assuming a new kernel representation.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
    {L M N : PModule.{u,0,u} k P} {ι : L ⟶ M} {π : M ⟶ N}

private instance : HasBinaryBiproducts (PModule.{u,0,u} k P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

namespace IsPointwiseShortExact

private noncomputable def kernelComparison (hs : IsPointwiseShortExact ι π) :
    L ⟶ kernel π := kernel.lift π ι hs.comp_eq_zero

private theorem kernelComparison_ι (hs : IsPointwiseShortExact ι π) :
    kernelComparison hs ≫ kernel.ι π = ι := kernel.lift_ι π ι hs.comp_eq_zero

private theorem kernelComparison_injective (hs : IsPointwiseShortExact ι π) (p : P) :
    Function.Injective ((kernelComparison hs).app p).hom := by
  intro x y hxy
  apply hs.injective p
  have hx := congrArg (fun f : L ⟶ M => (f.app p).hom x) (kernelComparison_ι hs)
  have hy := congrArg (fun f : L ⟶ M => (f.app p).hom y) (kernelComparison_ι hs)
  exact hx.symm.trans ((congrArg ((kernel.ι π).app p).hom hxy).trans hy)

private theorem kernelComparison_surjective (hs : IsPointwiseShortExact ι π) (p : P) :
    Function.Surjective ((kernelComparison hs).app p).hom := by
  intro z
  have hz : ((kernel.ι π).app p).hom z ∈ LinearMap.ker (π.app p).hom :=
    congrArg (fun f : kernel π ⟶ N => (f.app p).hom z) (kernel.condition π)
  rw [← hs.range_eq_ker p] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, ?_⟩
  apply RankKernel.injective π p
  have he := congrArg (fun f : L ⟶ M => (f.app p).hom x) (kernelComparison_ι hs)
  exact he.trans hx

/-- The given left term is naturally isomorphic to the actual categorical kernel. -/
noncomputable def kernelIso (hs : IsPointwiseShortExact ι π) : L ≅ kernel π := by
  let : ∀ p, Mono ((kernelComparison hs).app p) :=
    fun p => (ModuleCat.mono_iff_injective _).mpr (kernelComparison_injective hs p)
  let : ∀ p, Epi ((kernelComparison hs).app p) :=
    fun p => (ModuleCat.epi_iff_surjective _).mpr (kernelComparison_surjective hs p)
  let : ∀ p, IsIso ((kernelComparison hs).app p) := fun _ => isIso_of_mono_of_epi _
  let : IsIso (kernelComparison hs) := NatIso.isIso_of_isIso_app _
  exact asIso (kernelComparison hs)

/-- The comparison preserves the original kernel inclusion. -/
theorem kernelIso_hom_ι (hs : IsPointwiseShortExact ι π) :
    hs.kernelIso.hom ≫ kernel.ι π = ι := kernelComparison_ι hs

/-- A pointwise short exact sequence of persistence modules is short exact in
the actual functor category. The proof identifies the given first object with
the categorical kernel and uses pointwise surjectivity for the categorical
epimorphism. -/
theorem shortExact (hs : IsPointwiseShortExact ι π) :
    (ShortComplex.mk ι π hs.comp_eq_zero).ShortExact := by
  let Q := ShortComplex.mk ι π hs.comp_eq_zero
  have hEpi : Epi π := (NatTrans.epi_iff_epi_app π).2 (fun p =>
    (ModuleCat.epi_iff_surjective _).2 (hs.surjective p))
  let K := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hK : K.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_kernel π) inferInstance hEpi
  have hinv : (hs.kernelIso).inv ≫ ι = kernel.ι π := by
    calc
      (hs.kernelIso).inv ≫ ι = (hs.kernelIso).inv ≫
          ((hs.kernelIso).hom ≫ kernel.ι π) := by rw [hs.kernelIso_hom_ι]
      _ = kernel.ι π := by simp [Category.assoc]
  let e : K ≅ Q := ShortComplex.isoMk (hs.kernelIso).symm (Iso.refl _)
    (Iso.refl _) hinv
  exact ShortComplex.shortExact_of_iso e hK

end IsPointwiseShortExact

namespace IsRankDeflation

/-- A rank-exact deflation onto a rank projective splits as its actual kernel
and quotient. The section is derived by lifting identity. -/
noncomputable def splitKernelIso (hs : IsRankDeflation π) (hN : IsRankProjective N) :
    M ≅ kernel π ⊞ N := by
  let h := hN (kernel π) M N (kernel.ι π) π hs.rankExact_kernel (𝟙 N)
  let s := Classical.choose h
  have hsec := Classical.choose_spec h
  let S : ShortComplex (PModule.{u,0,u} k P) :=
    ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  exact (ShortComplex.Splitting.ofExactOfSection S (ShortComplex.exact_kernel π)
    s hsec inferInstance).isoBinaryBiproduct

/-- The splitting recovers the original quotient map as its second projection. -/
theorem splitKernelIso_hom_snd (hs : IsRankDeflation π) (hN : IsRankProjective N) :
    (hs.splitKernelIso hN).hom ≫ biprod.snd = π := by
  change biprod.lift _ π ≫ biprod.snd = π
  exact biprod.lift_snd _ _

/-- The inverse splitting recovers the actual kernel inclusion on its first summand. -/
theorem splitKernelIso_inl_inv (hs : IsRankDeflation π) (hN : IsRankProjective N) :
    biprod.inl ≫ (hs.splitKernelIso hN).inv = kernel.ι π := by
  change biprod.inl ≫ biprod.desc (kernel.ι π) _ = kernel.ι π
  exact biprod.inl_desc _ _

end IsRankDeflation

end TDA.Persistence
