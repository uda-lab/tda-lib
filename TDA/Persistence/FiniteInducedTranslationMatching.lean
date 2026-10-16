import TDA.Persistence.FiniteEpiTranslationMatching
import TDA.Persistence.FiniteMonoTranslationMatching
import TDA.Persistence.FiniteInducedMatching

/-!
# Quantitative induced matchings through the actual image

Component kernel/range identities transfer actual shortness to the epi/mono
factors. Their quantitative estimates then apply to the unique intermediate
occurrence of the existing induced matching. Kernel and cokernel may use different translations.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}

/-- Actual kernel shortness is unchanged by corestricting to the actual image. -/
theorem kernel_translationTrivial_toFiniteImage_iff (theta : Fin s →o Fin s)
    (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N) :
    TranslationTrivial theta hTheta (finiteKernel (toFiniteImage f)) ↔
      TranslationTrivial theta hTheta (finiteKernel f) := by
  rw [kernel_translationTrivial_iff, kernel_translationTrivial_iff]
  apply forall_congr'
  intro i
  change LinearMap.ker (f.app i).hom.rangeRestrict ≤ _ ↔ _
  rw [LinearMap.ker_rangeRestrict]

/-- Actual cokernel shortness is unchanged by replacing the morphism with its image inclusion. -/
theorem cokernel_translationTrivial_fromFiniteImage_iff (theta : Fin s →o Fin s)
    (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N) :
    TranslationTrivial theta hTheta (finiteCokernel (fromFiniteImage f)) ↔
      TranslationTrivial theta hTheta (finiteCokernel f) := by
  rw [cokernel_translationTrivial_iff, cokernel_translationTrivial_iff]
  apply forall_congr'
  intro i
  change _ ≤ LinearMap.range (LinearMap.range (f.app (theta i)).hom).subtype ↔ _
  rw [Submodule.range_subtype]

namespace FiniteBarcode

variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

/-- Actual kernel shortness controls every matched death, for an arbitrary morphism. -/
theorem inducedMap_death_bounds_of_kernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hk : TranslationTrivial theta hTheta (finiteKernel f))
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N))
    (h : inducedMap f i = some j) :
    (occurrence (rankBarcode N) j).death ≤ (occurrence (rankBarcode M) i).death ∧
      (occurrence (rankBarcode M) i).death ≤
        (occurrence (rankBarcode N) j).translatedDeath theta := by
  obtain ⟨a, rfl, rfl⟩ := (inducedMap_eq_some_iff f i j).mp h
  have he := epiEmbedding_death_bounds_of_kernelTrivial theta hTheta
    (toFiniteImage f) (toFiniteImage_surjective f)
      ((kernel_translationTrivial_toFiniteImage_iff theta hTheta f).mpr hk) a
  have hd := monoEmbedding_death (fromFiniteImage f) (fromFiniteImage_injective f) a
  change (occurrence _ (imageTargetEmbedding f a)).death =
    (occurrence (rankBarcode (finiteImage f)) a).death at hd
  refine ⟨hd.trans_le he.1, ?_⟩
  exact he.2.trans_eq (FiniteInterval.translatedDeath_congr _ _ theta hd.symm)

/-- Actual cokernel shortness controls every matched birth, for an arbitrary morphism. -/
theorem inducedMap_birth_bounds_of_cokernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N))
    (h : inducedMap f i = some j) :
    (occurrence (rankBarcode N) j).birth ≤ (occurrence (rankBarcode M) i).birth ∧
      (occurrence (rankBarcode M) i).birth ≤
        (theta (occurrence (rankBarcode N) j).birthStage).val := by
  obtain ⟨a, rfl, rfl⟩ := (inducedMap_eq_some_iff f i j).mp h
  have hb := epiEmbedding_birth (toFiniteImage f) (toFiniteImage_surjective f) a
  change (occurrence _ (imageSourceEmbedding f a)).birth =
    (occurrence (rankBarcode (finiteImage f)) a).birth at hb
  rw [hb]
  exact monoEmbedding_birth_bounds_of_cokernelTrivial theta hTheta
    (fromFiniteImage f) (fromFiniteImage_injective f)
      ((cokernel_translationTrivial_fromFiniteImage_iff theta hTheta f).mpr hc) a

/-- Both endpoint controls coexist, with independent kernel and cokernel translations. -/
theorem inducedMap_endpoint_bounds_of_shortness
    (thetaK thetaC : Fin s →o Fin s) (hK : ∀ i, i ≤ thetaK i) (hC : ∀ i, i ≤ thetaC i)
    (f : M ⟶ N) (hk : TranslationTrivial thetaK hK (finiteKernel f))
    (hc : TranslationTrivial thetaC hC (finiteCokernel f))
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N))
    (h : inducedMap f i = some j) :
    (occurrence (rankBarcode N) j).birth ≤ (occurrence (rankBarcode M) i).birth ∧
      (occurrence (rankBarcode M) i).birth ≤
        (thetaC (occurrence (rankBarcode N) j).birthStage).val ∧
      (occurrence (rankBarcode M) i).birth < (occurrence (rankBarcode N) j).death ∧
      (occurrence (rankBarcode N) j).death ≤ (occurrence (rankBarcode M) i).death ∧
      (occurrence (rankBarcode M) i).death ≤
        (occurrence (rankBarcode N) j).translatedDeath thetaK := by
  have hb := inducedMap_birth_bounds_of_cokernelTrivial thetaC hC f hc i j h
  have hd := inducedMap_death_bounds_of_kernelTrivial thetaK hK f hk i j h
  exact ⟨hb.1, hb.2, (inducedMap_endpoints f i j h).2.1, hd⟩

/-- Every long source has exactly one selected target, using only actual kernel shortness. -/
theorem inducedMap_covers_long_source_of_kernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hk : TranslationTrivial theta hTheta (finiteKernel f))
    (i : BarcodeOccurrence s (rankBarcode M))
    (hlong : (theta (occurrence (rankBarcode M) i).birthStage).val <
      (occurrence (rankBarcode M) i).death) :
    ∃! j, inducedMap f i = some j := by
  obtain ⟨a, ha, _⟩ := epiEmbedding_covers_long_of_kernelTrivial theta hTheta
    (toFiniteImage f) (toFiniteImage_surjective f)
      ((kernel_translationTrivial_toFiniteImage_iff theta hTheta f).mpr hk) i hlong
  have hj := (inducedMap_eq_some_iff f i (imageTargetEmbedding f a)).mpr ⟨a, ha, rfl⟩
  exact ⟨imageTargetEmbedding f a, hj, fun _ hj' => Option.some.inj (hj'.symm.trans hj)⟩

/-- Every long target has exactly one selected source, using only actual cokernel shortness. -/
theorem inducedMap_covers_long_target_of_cokernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (j : BarcodeOccurrence s (rankBarcode N))
    (hlong : (theta (occurrence (rankBarcode N) j).birthStage).val <
      (occurrence (rankBarcode N) j).death) :
    ∃! i, inducedMap f i = some j := by
  obtain ⟨a, ha, _⟩ := monoEmbedding_covers_long_of_cokernelTrivial theta hTheta
    (fromFiniteImage f) (fromFiniteImage_injective f)
      ((cokernel_translationTrivial_fromFiniteImage_iff theta hTheta f).mpr hc) j hlong
  have hi := (inducedMap_eq_some_iff f (imageSourceEmbedding f a) j).mpr ⟨a, rfl, ha⟩
  exact ⟨imageSourceEmbedding f a, hi, fun i' hi' => inducedMap_injective f i' _ j hi' hi⟩

/-- Any source on which the induced matching is undefined is kernel-short. -/
theorem inducedMap_unmatched_source_short_of_kernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hk : TranslationTrivial theta hTheta (finiteKernel f))
    (i : BarcodeOccurrence s (rankBarcode M)) (hi : inducedMap f i = none) :
    (occurrence (rankBarcode M) i).death ≤
      (theta (occurrence (rankBarcode M) i).birthStage).val := by
  by_contra h
  obtain ⟨j, hj, _⟩ := inducedMap_covers_long_source_of_kernelTrivial
    theta hTheta f hk i (lt_of_not_ge h)
  rw [hi] at hj
  contradiction

/-- Any target absent from the induced range is cokernel-short. -/
theorem inducedMap_unmatched_target_short_of_cokernelTrivial
    (theta : Fin s →o Fin s) (hTheta : ∀ i, i ≤ theta i) (f : M ⟶ N)
    (hc : TranslationTrivial theta hTheta (finiteCokernel f))
    (j : BarcodeOccurrence s (rankBarcode N)) (hj : ∀ i, inducedMap f i ≠ some j) :
    (occurrence (rankBarcode N) j).death ≤
      (theta (occurrence (rankBarcode N) j).birthStage).val := by
  by_contra h
  obtain ⟨i, hi, _⟩ := inducedMap_covers_long_target_of_cokernelTrivial
    theta hTheta f hc j (lt_of_not_ge h)
  exact hj i hi

end FiniteBarcode
end TDA.Persistence
