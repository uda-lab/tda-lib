import TDA.Persistence.ConstructibleRefinement
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Constructibility and critical sampling of defects

On a finite real grid, constructibility means a zero left tail and
isomorphic structure maps within each cell, including the right tail.
Naturality between within-cell isomorphisms induces isomorphisms on the kernel and cokernel. Critical sampling preserves these defects as natural
isomorphisms, with their inclusions and projections retained.
These constructions work over a ring with independent carrier universe.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [Ring R] {n : ℕ} {c : Fin n ↪o ℝ}
variable {M N : PModule.{u,0,w} R ℝ}

-- Evaluation compares a defect map with the map induced by the
-- naturality square. Invertible source and target maps make that map invertible.
private theorem kernel_structureMap_isIso (f : M ⟶ N) {s t : ℝ} (h : s ≤ t)
    [IsIso (structureMap M h)] [IsIso (structureMap N h)] :
    IsIso (structureMap (kernel f) h) := by
  let es := PreservesKernel.iso ((evaluation ℝ (ModuleCat R)).obj s) f
  let et := PreservesKernel.iso ((evaluation ℝ (ModuleCat R)).obj t) f
  let ep := kernel.mapIso (f.app s) (f.app t)
    (asIso (structureMap M h)) (asIso (structureMap N h))
    (f.naturality (homOfLE h)).symm
  let p := ep.hom
  have : IsIso p := ep.isIso_hom
  have hs : es.hom ≫ kernel.ι (f.app s) = (kernel.ι f).app s := by
    exact kernelComparison_comp_ι f ((evaluation ℝ (ModuleCat R)).obj s)
  have ht : et.inv ≫ (kernel.ι f).app t = kernel.ι (f.app t) :=
    PreservesKernel.iso_inv_ι ((evaluation ℝ (ModuleCat R)).obj t) f
  have he : structureMap (kernel f) h = es.hom ≫ p ≫ et.inv := by
    apply (cancel_mono ((kernel.ι f).app t)).mp
    rw [Category.assoc, Category.assoc, ht]
    change structureMap (kernel f) h ≫ (kernel.ι f).app t =
      es.hom ≫ kernel.lift _ _ _ ≫ kernel.ι _
    rw [kernel.lift_ι, ← Category.assoc, hs]
    exact (kernel.ι f).naturality (homOfLE h)
  rw [he]
  infer_instance

private theorem cokernel_structureMap_isIso (f : M ⟶ N) {s t : ℝ} (h : s ≤ t)
    [IsIso (structureMap M h)] [IsIso (structureMap N h)] :
    IsIso (structureMap (cokernel f) h) := by
  let es := PreservesCokernel.iso ((evaluation ℝ (ModuleCat R)).obj s) f
  let et := PreservesCokernel.iso ((evaluation ℝ (ModuleCat R)).obj t) f
  let ep := cokernel.mapIso (f.app s) (f.app t)
    (asIso (structureMap M h)) (asIso (structureMap N h))
    (f.naturality (homOfLE h)).symm
  let p := ep.hom
  have : IsIso p := ep.isIso_hom
  have hs : (cokernel.π f).app s ≫ es.hom = cokernel.π (f.app s) :=
    PreservesCokernel.π_iso_hom ((evaluation ℝ (ModuleCat R)).obj s) f
  have ht : cokernel.π (f.app t) ≫ et.inv = (cokernel.π f).app t := by
    have he : (cokernel.π f).app t ≫ et.hom = cokernel.π (f.app t) :=
      PreservesCokernel.π_iso_hom ((evaluation ℝ (ModuleCat R)).obj t) f
    rw [← he]
    simp only [Category.assoc, et.hom_inv_id]
    exact Category.comp_id _
  have he : structureMap (cokernel f) h = es.hom ≫ p ≫ et.inv := by
    apply (cancel_epi ((cokernel.π f).app s)).mp
    rw [← Category.assoc, ← Category.assoc, hs]
    change (cokernel.π f).app s ≫ structureMap (cokernel f) h =
      (cokernel.π _ ≫ cokernel.desc _ _ _) ≫ et.inv
    rw [cokernel.π_desc, Category.assoc, ht]
    exact ((cokernel.π f).naturality (homOfLE h)).symm
  rw [he]
  infer_instance

/-- The kernel of a morphism between modules on the same grid is constructible. -/
theorem IsConstructible.kernel (hM : IsConstructible c M) (hN : IsConstructible c N)
    (f : M ⟶ N) : IsConstructible c (kernel f) where
  zero_left t ht := IsZero.of_mono_eq_zero ((kernel.ι f).app t)
    ((hM.zero_left t ht).eq_zero_of_tgt _)
  isIso_map s t h hc := by
    have := hM.isIso_map s t h hc
    have := hN.isIso_map s t h hc
    exact kernel_structureMap_isIso f h

/-- The cokernel is constructible; its zero left tail comes from the target. -/
theorem IsConstructible.cokernel (hM : IsConstructible c M) (hN : IsConstructible c N)
    (f : M ⟶ N) : IsConstructible c (cokernel f) where
  zero_left t ht := IsZero.of_epi_eq_zero ((cokernel.π f).app t)
    ((hN.zero_left t ht).eq_zero_of_src _)
  isIso_map s t h hc := by
    have := hM.isIso_map s t h hc
    have := hN.isIso_map s t h hc
    exact cokernel_structureMap_isIso f h

/-- Critical sampling, as used by `moduleDiagram`, preserves the kernel.
This sampling has no padded zero stage. -/
noncomputable def criticalKernelIso (c : Fin n ↪o ℝ) (f : M ⟶ N) :
    reindex c.toOrderHom (kernel f) ≅ kernel (reindexNatTrans c.toOrderHom f) :=
  PreservesKernel.iso ((Functor.whiskeringLeft _ _ _).obj c.toOrderHom.toFunctor) f

/-- The natural kernel comparison retains its inclusion. -/
theorem criticalKernelIso_inv_ι (c : Fin n ↪o ℝ) (f : M ⟶ N) :
    (criticalKernelIso c f).inv ≫ reindexNatTrans c.toOrderHom (kernel.ι f) =
      kernel.ι (reindexNatTrans c.toOrderHom f) :=
  PreservesKernel.iso_inv_ι ((Functor.whiskeringLeft _ _ _).obj c.toOrderHom.toFunctor) f

/-- Critical sampling preserves the cokernel as a natural isomorphism. -/
noncomputable def criticalCokernelIso (c : Fin n ↪o ℝ) (f : M ⟶ N) :
    reindex c.toOrderHom (cokernel f) ≅ cokernel (reindexNatTrans c.toOrderHom f) :=
  PreservesCokernel.iso ((Functor.whiskeringLeft _ _ _).obj c.toOrderHom.toFunctor) f

/-- The natural cokernel comparison retains its projection. -/
theorem criticalCokernelIso_π_hom (c : Fin n ↪o ℝ) (f : M ⟶ N) :
    reindexNatTrans c.toOrderHom (cokernel.π f) ≫ (criticalCokernelIso c f).hom =
      cokernel.π (reindexNatTrans c.toOrderHom f) :=
  PreservesCokernel.π_iso_hom ((Functor.whiskeringLeft _ _ _).obj c.toOrderHom.toFunctor) f

end TDA.Persistence.FiniteConstructible
