import TDA.Persistence.FiniteKernel
import TDA.Persistence.FiniteEpiCounts
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Shifted same-birth survival counts from kernel shortness

The source transition kills the component kernel, so it descends through
an epimorphism. Restriction to birth images and passage to the preceding-image
quotients give genuine surjections before dimensions are compared.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

private theorem naturality_apply (p : M ⟶ N) {a c : Fin s}
    (h : a ≤ c) (x : M.obj a) :
    (p.app c).hom (structureMapLinear M h x) =
      structureMapLinear N h ((p.app a).hom x) :=
  congrArg (fun g : M.obj a ⟶ N.obj c => g.hom x) (p.naturality (homOfLE h))

variable (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i)
variable (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
variable (hk : TranslationTrivial theta hTheta (finiteKernel p))

-- First descend a source transition through the component surjection.
private noncomputable def descendAt (c : Fin s) : N.obj c →ₗ[k] M.obj (theta c) :=
  ((LinearMap.ker (p.app c).hom).liftQ (structureMapLinear M (hTheta c))
    ((kernel_translationTrivial_iff theta hTheta p).mp hk c)).comp
      ((p.app c).hom.quotKerEquivOfSurjective (hp c)).symm.toLinearMap

private theorem descendAt_apply (c : Fin s) (x : M.obj c) :
    descendAt theta hTheta p hp hk c ((p.app c).hom x) =
      structureMapLinear M (hTheta c) x := by
  simp [descendAt, LinearMap.quotKerEquivOfSurjective_symm_apply]

private theorem descend_image_apply {a c : Fin s} (h : a ≤ c) (x : M.obj a) :
    descendAt theta hTheta p hp hk c
      (structureMapLinear N h ((p.app a).hom x)) =
        structureMapLinear M (h.trans (hTheta c)) x := by
  rw [← naturality_apply, descendAt_apply]
  exact (congrArg (fun L => L x) (structureMapLinear_comp M h (hTheta c))).symm

private noncomputable def translatedImageMap (b c : Fin s) (hbc : b ≤ c) :
    LinearMap.range (structureMapLinear N hbc) →ₗ[k]
      LinearMap.range (structureMapLinear M (hbc.trans (hTheta c))) :=
  ((descendAt theta hTheta p hp hk c).comp
    (LinearMap.range (structureMapLinear N hbc)).subtype).codRestrict _ (by
      rintro ⟨_, x, rfl⟩
      obtain ⟨z, rfl⟩ := hp b x
      exact ⟨z, (descend_image_apply theta hTheta p hp hk hbc z).symm⟩)

private theorem translatedImageMap_surjective (b c : Fin s) (hbc : b ≤ c) :
    Function.Surjective (translatedImageMap theta hTheta p hp hk b c hbc) := by
  rintro ⟨_, x, rfl⟩
  refine ⟨⟨structureMapLinear N hbc ((p.app b).hom x), (p.app b).hom x, rfl⟩, ?_⟩
  apply Subtype.ext
  exact descend_image_apply theta hTheta p hp hk hbc x

private theorem translatedImageMap_previous (b c : Fin s) (hb : 0 < b.val) (hbc : b ≤ c) :
    birthPreviousImage N b.val c.val hb hbc c.isLt ≤
      (birthPreviousImage M b.val (theta c).val hb (hbc.trans (hTheta c))
        (theta c).isLt).comap (translatedImageMap theta hTheta p hp hk b c hbc) := by
  rintro x ⟨y, hy⟩
  obtain ⟨z, rfl⟩ := hp ⟨b.val - 1, by omega⟩ y
  change descendAt theta hTheta p hp hk c x.val ∈ LinearMap.range (structureMapLinear M _)
  change structureMapLinear N _ ((p.app _).hom z) = x.val at hy
  rw [← hy]
  exact ⟨z, (descend_image_apply theta hTheta p hp hk
    (show (⟨b.val - 1, by omega⟩ : Fin s) ≤ c from by change b.val - 1 ≤ c.val; omega) z).symm⟩

private noncomputable def translatedBirthQuotientMap (b c : Fin s)
    (hb : 0 < b.val) (hbc : b ≤ c) :
    (LinearMap.range (structureMapLinear N hbc) ⧸ birthPreviousImage N b.val c.val hb hbc c.isLt) →ₗ[k]
      (LinearMap.range (structureMapLinear M (hbc.trans (hTheta c))) ⧸
        birthPreviousImage M b.val (theta c).val hb (hbc.trans (hTheta c)) (theta c).isLt) :=
  (birthPreviousImage N b.val c.val hb hbc c.isLt).mapQ _
    (translatedImageMap theta hTheta p hp hk b c hbc)
      (translatedImageMap_previous theta hTheta p hp hk b c hb hbc)

private theorem translatedBirthQuotientMap_surjective (b c : Fin s)
    (hb : 0 < b.val) (hbc : b ≤ c) :
    Function.Surjective (translatedBirthQuotientMap theta hTheta p hp hk b c hb hbc) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨x, rfl⟩ := translatedImageMap_surjective theta hTheta p hp hk b c hbc y
    exact ⟨Submodule.Quotient.mk x, rfl⟩

include hTheta p hp hk

/-- Kernel shortness bounds source survival after translation by target survival before it.
The positive-birth quotient and initial image are compared by surjections. -/
theorem birthSuffixCount_translated_le_of_kernelTrivial
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]
    (b c : Fin s) (hbc : b ≤ c) :
    birthSuffixCount (rankBarcode M) b.val (theta c).val ≤
      birthSuffixCount (rankBarcode N) b.val c.val := by
  by_cases hb : b.val = 0
  · let z : Fin s := ⟨0, (Nat.zero_le c.val).trans_lt c.isLt⟩
    have hbz : b = z := Fin.ext hb
    subst b
    change birthSuffixCount (rankBarcode M) 0 (theta c).val ≤
      birthSuffixCount (rankBarcode N) 0 c.val
    rw [birthSuffixCount_zero M _ (theta c).isLt, birthSuffixCount_zero N _ c.isLt]
    exact LinearMap.finrank_le_finrank_of_surjective
      (translatedImageMap_surjective theta hTheta p hp hk z c hbc)
  · have hbpos : 0 < b.val := Nat.pos_of_ne_zero hb
    rw [birthSuffixCount_eq_finrank M b.val (theta c).val hbpos
      (hbc.trans (hTheta c)) (theta c).isLt,
      birthSuffixCount_eq_finrank N b.val c.val hbpos hbc c.isLt]
    exact LinearMap.finrank_le_finrank_of_surjective
      (translatedBirthQuotientMap_surjective theta hTheta p hp hk b c hbpos hbc)

end TDA.Persistence.FiniteBarcode
