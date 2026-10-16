import TDA.Persistence.FiniteCokernel
import TDA.Persistence.FiniteMonoCounts

/-!
# Shifted same-death counts from actual cokernel shortness

The target image at a later stage lifts through the source image from the translated
birth. At an observed death, injectivity of the component at death also lifts the
kernel condition. Terminal death uses just the last image.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

private theorem naturality_apply (f : M ⟶ N) {a c : Fin s}
    (h : a ≤ c) (x : M.obj a) :
    (f.app c).hom (structureMapLinear M h x) =
      structureMapLinear N h ((f.app a).hom x) :=
  congrArg (fun g : M.obj a ⟶ N.obj c => g.hom x) (f.naturality (homOfLE h))

-- First lift a genuine target image vector at theta b; no dimension or barcode
-- comparison is used to obtain the lift.
private theorem image_le_map_translated_image (theta : Fin s →o Fin s)
    (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (b c : Fin s) (hbc : theta b ≤ c) :
    LinearMap.range (structureMapLinear N ((hTheta b).trans hbc)) ≤
      (LinearMap.range (structureMapLinear M hbc)).map (f.app c).hom := by
  rintro y ⟨x, rfl⟩
  have himg := (cokernel_translationTrivial_iff theta hTheta f).mp hc b
  obtain ⟨z, hz⟩ := himg ⟨x, rfl⟩
  refine ⟨structureMapLinear M hbc z, ⟨z, rfl⟩, ?_⟩
  rw [naturality_apply, hz]
  exact (congrArg (fun L => L x) (structureMapLinear_comp N (hTheta b) hbc)).symm

private theorem deathSubspace_le_map_translated (theta : Fin s →o Fin s)
    (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hf : ∀ i, Function.Injective (f.app i).hom)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (b : Fin s) (d : ℕ) (hbd : b.val < d) (htd : (theta b).val < d) (hd : d < s) :
    deathSubspace N b.val d hbd hd ≤
      (deathSubspace M (theta b).val d htd hd).map (f.app ⟨d - 1, by omega⟩).hom := by
  rintro y ⟨hy, hk⟩
  have htc : theta b ≤ (⟨d - 1, by omega⟩ : Fin s) := by
    change (theta b).val ≤ d - 1
    omega
  obtain ⟨x, hx, hfx⟩ := image_le_map_translated_image theta hTheta f hc b _ htc hy
  refine ⟨x, ⟨hx, ?_⟩, hfx⟩
  apply hf ⟨d, hd⟩
  rw [map_zero, naturality_apply, hfx]
  exact hk

/-- Cokernel shortness gives the reverse prefix comparison after translating the birth.
Finite deaths lift an actual kernel condition; terminal death compares final images. -/
theorem deathPrefixCount_le_translated_of_cokernelTrivial
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hf : ∀ i, Function.Injective (f.app i).hom)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (b : Fin s) (d : ℕ) (htd : (theta b).val < d) (hd : d ≤ s) :
    deathPrefixCount (rankBarcode N) b.val d ≤
      deathPrefixCount (rankBarcode M) (theta b).val d := by
  have hbtheta : b.val ≤ (theta b).val := hTheta b
  have hbd : b.val < d := by omega
  by_cases hds : d < s
  · rw [deathPrefixCount_eq_finrank N b.val d hbd hds,
      deathPrefixCount_eq_finrank M (theta b).val d htd hds]
    exact (Submodule.finrank_mono
      (deathSubspace_le_map_translated theta hTheta f hf hc b d hbd htd hds)).trans
        (Submodule.finrank_map_le _ _)
  · have hdeq : d = s := by omega
    subst d
    rw [deathPrefixCount_terminal N b.val hbd,
      deathPrefixCount_terminal M (theta b).val htd]
    have htc : theta b ≤ (⟨s - 1, by omega⟩ : Fin s) := by
      change (theta b).val ≤ s - 1
      omega
    exact (Submodule.finrank_mono
      (image_le_map_translated_image theta hTheta f hc b _ htc)).trans
        (Submodule.finrank_map_le _ _)

end TDA.Persistence.FiniteBarcode
