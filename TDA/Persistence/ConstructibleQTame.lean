import TDA.Persistence.ConstructibleRefinementBarcode
import TDA.Persistence.RealBarcodeRank

/-!
# Q-tameness and ranks of finite-constructible modules

Critical-fiber finiteness determines every fiber. Barcode reconstruction transports
structure-map ranks, so the count formula also applies to nonidentity maps.
-/

set_option autoImplicit false

universe u
namespace TDA.Persistence
open CategoryTheory
variable {k : Type u} [Field k]

/-- Natural module isomorphisms preserve the rank of every structure map. -/
theorem persistenceImage_finrank_eq_of_iso {M N : PModule.{u,0,u} k ℝ}
    (e : M ≅ N) {s t : ℝ} (hst : s ≤ t) :
    Module.finrank k (persistenceImage M hst) =
      Module.finrank k (persistenceImage N hst) := by
  let E₀ := (e.app s).toLinearEquiv
  let E₁ := (e.app t).toLinearEquiv
  have hnat := NatIso.naturality_1 e (homOfLE hst)
  have hlin := congrArg (fun f : N.obj s ⟶ N.obj t => f.hom) hnat
  have hconj : structureMapLinear N hst =
      (E₁ : M.obj t →ₗ[k] N.obj t).comp
        ((structureMapLinear M hst).comp (E₀.symm : N.obj s →ₗ[k] M.obj s)) := by
    simpa only [E₀, E₁, structureMapLinear, structureMap,
      ModuleCat.hom_comp, LinearMap.comp_assoc,
      Iso.toLinearEquiv_symm, Iso.toLinearMap_toLinearEquiv,
      Iso.app_hom, Iso.symm_hom, Iso.app] using hlin.symm
  have hsource : LinearMap.range (E₀.symm : N.obj s →ₗ[k] M.obj s) = ⊤ :=
    LinearMap.range_eq_top.mpr E₀.symm.surjective
  unfold persistenceImage
  rw [hconj, LinearMap.range_comp]
  rw [LinearMap.range_comp_of_range_eq_top _ hsource]
  exact (E₁.finrank_map_eq (LinearMap.range (structureMapLinear M hst))).symm

namespace FiniteConstructible
variable {n : ℕ}

/-- Right-continuous finite constructibility with finite critical fibers implies q-tameness. -/
theorem qTame_of_isConstructible (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hM : IsConstructible c M) (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) :
    M.QTame :=
  PModule.qTame_of_finiteDimensional M (finiteDimensional_of_isConstructible M hM hfd)

/-- The canonical finite diagram counts ranks at arbitrary real parameters. -/
theorem moduleDiagram_rank (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hM : IsConstructible c M) (hfd : ∀ i, FiniteDimensional k (M.obj (c i)))
    (s t : ℝ) (hst : s ≤ t) :
    Module.finrank k (persistenceImage M hst) =
      (moduleDiagram c M hfd).points.countP
        (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) :=
  (persistenceImage_finrank_eq_of_iso (barcodeRealizationIso c M hM hfd) hst).trans
    (RealBarcode.realize_image_rank (moduleDiagram c M hfd) hst)

end FiniteConstructible
end TDA.Persistence
