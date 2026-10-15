import TDA.Persistence.RankBarcode
import Mathlib.CategoryTheory.NatIso

universe u
namespace TDA.Persistence
open CategoryTheory
variable {N : ℕ} {k : Type u} [Field k]
variable {M L : PModule.{u,0,u} k (Fin N)}
variable [∀ i : Fin N, FiniteDimensional k (M.obj i)]
variable [∀ i : Fin N, FiniteDimensional k (L.obj i)]

theorem structureMapRank_eq_of_iso (e : M ≅ L)
    (i j : Fin N) (hij : i ≤ j) :
    structureMapRank M i j hij = structureMapRank L i j hij := by
  let E₀ := (e.app i).toLinearEquiv
  let E₁ := (e.app j).toLinearEquiv
  have hnat := NatIso.naturality_1 e (homOfLE hij)
  have hlin := congrArg (fun f : L.obj i ⟶ L.obj j => f.hom) hnat
  have hconj : structureMapLinear L hij =
      (E₁ : M.obj j →ₗ[k] L.obj j).comp
        ((structureMapLinear M hij).comp (E₀.symm : L.obj i →ₗ[k] M.obj i)) := by
    simpa only [E₀, E₁, structureMapLinear, structureMap,
      ModuleCat.hom_comp, LinearMap.comp_assoc,
      Iso.toLinearEquiv_symm, Iso.toLinearMap_toLinearEquiv,
      Iso.app_hom, Iso.symm_hom, Iso.app] using hlin.symm
  have hsource : LinearMap.range (E₀.symm : L.obj i →ₗ[k] M.obj i) = ⊤ :=
    LinearMap.range_eq_top.mpr E₀.symm.surjective
  unfold structureMapRank
  rw [hconj, LinearMap.range_comp]
  rw [LinearMap.range_comp_of_range_eq_top _ hsource]
  exact (E₁.finrank_map_eq (LinearMap.range (structureMapLinear M hij))).symm

theorem rankBarcode_eq_of_iso (e : M ≅ L) :
    rankBarcode M = rankBarcode L := by
  apply (rankBarcode_eq_iff M L).2
  intro i j hij
  exact structureMapRank_eq_of_iso e i j hij

theorem rankBarcode_eq_of_iso_barcodeModule
    (B : Multiset (FiniteInterval N))
    (e : M ≅ barcodeModule (k := k) B) : rankBarcode M = B := by
  calc
    rankBarcode M = rankBarcode (barcodeModule (k := k) B) :=
      rankBarcode_eq_of_iso e
    _ = B := rankBarcode_barcodeModule B

end TDA.Persistence
