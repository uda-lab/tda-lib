import TDA.Persistence.FiniteImage
import TDA.Persistence.FiniteEpiMatching

/-!
# Induced occurrence matchings through the image

The epi embedding puts image occurrences inside source occurrences. Its inverse on
that range, followed by the mono embedding, is a partial injection into the target.
Every matched pair retains a unique intermediate occurrence.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory

variable {s : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}
variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

/-- Canonically place image-barcode occurrences in the source barcode. -/
noncomputable def imageSourceEmbedding (f : M ⟶ N) :
    BarcodeOccurrence s (rankBarcode (finiteImage f)) ↪ BarcodeOccurrence s (rankBarcode M) :=
  epiEmbedding (toFiniteImage f) (toFiniteImage_surjective f)

/-- Canonically place image-barcode occurrences in the target barcode. -/
noncomputable def imageTargetEmbedding (f : M ⟶ N) :
    BarcodeOccurrence s (rankBarcode (finiteImage f)) ↪ BarcodeOccurrence s (rankBarcode N) :=
  monoEmbedding (fromFiniteImage f) (fromFiniteImage_injective f)

/-- Precisely those source occurrences selected by the epi part of the factorization. -/
def inducedDomain (f : M ⟶ N) : Set (BarcodeOccurrence s (rankBarcode M)) :=
  Set.range (imageSourceEmbedding f)

/-- Image occurrences identify the exact domain, including all multiplicity labels. -/
noncomputable def imageOccurrenceEquivDomain (f : M ⟶ N) :
    BarcodeOccurrence s (rankBarcode (finiteImage f)) ≃ inducedDomain f :=
  Equiv.ofInjective (imageSourceEmbedding f) (imageSourceEmbedding f).injective

/-- The partial injection, represented as an embedding of its exact domain. -/
noncomputable def inducedMatching (f : M ⟶ N) :
    inducedDomain f ↪ BarcodeOccurrence s (rankBarcode N) :=
  (imageOccurrenceEquivDomain f).symm.toEmbedding.trans (imageTargetEmbedding f)

/-- Evaluate the partial injection on any source label; unselected labels give `none`. -/
noncomputable def inducedMap (f : M ⟶ N) (i : BarcodeOccurrence s (rankBarcode M)) :
    Option (BarcodeOccurrence s (rankBarcode N)) := by
  classical
  exact if h : i ∈ inducedDomain f then some (inducedMatching f ⟨i, h⟩) else none

private theorem source_inverse (f : M ⟶ N) (i : inducedDomain f) :
    imageSourceEmbedding f ((imageOccurrenceEquivDomain f).symm i) = i.val :=
  Equiv.apply_ofInjective_symm (imageSourceEmbedding f).injective i

/-- The partial inverse followed by the mono embedding uses the same image occurrence. -/
theorem inducedMatching_from_image (f : M ⟶ N)
    (a : BarcodeOccurrence s (rankBarcode (finiteImage f))) :
    inducedMatching f ⟨imageSourceEmbedding f a, ⟨a, rfl⟩⟩ = imageTargetEmbedding f a := by
  exact congrArg (imageTargetEmbedding f)
    (Equiv.ofInjective_symm_apply (imageSourceEmbedding f).injective a)

/-- A pair is matched exactly when an intermediate occurrence produces both labels. -/
theorem inducedMap_eq_some_iff (f : M ⟶ N)
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N)) :
    inducedMap f i = some j ↔
      ∃ a, imageSourceEmbedding f a = i ∧ imageTargetEmbedding f a = j := by
  classical
  constructor
  · intro h
    by_cases hi : i ∈ inducedDomain f
    · refine ⟨(imageOccurrenceEquivDomain f).symm ⟨i, hi⟩, source_inverse f _, ?_⟩
      simpa [inducedMap, hi, inducedMatching] using h
    · simp [inducedMap, hi] at h
  · rintro ⟨a, ha, hj⟩
    have hi : i ∈ inducedDomain f := ⟨a, ha⟩
    have he : (⟨i, hi⟩ : inducedDomain f) = ⟨imageSourceEmbedding f a, ⟨a, rfl⟩⟩ :=
      Subtype.ext ha.symm
    have hm : inducedMatching f ⟨i, hi⟩ = j := by
      rw [he, inducedMatching_from_image, hj]
    simp [inducedMap, hi, hm]

/-- Each matched pair has exactly one intermediate occurrence, even for repeated bars. -/
theorem inducedMap_eq_some_iff_unique (f : M ⟶ N)
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N)) :
    inducedMap f i = some j ↔
      ∃! a, imageSourceEmbedding f a = i ∧ imageTargetEmbedding f a = j := by
  rw [inducedMap_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hj⟩
    exact ⟨a, ⟨ha, hj⟩, fun b hb => (imageSourceEmbedding f).injective (hb.1.trans ha.symm)⟩
  · rintro ⟨a, ha, _⟩
    exact ⟨a, ha⟩

/-- The selected domain is exactly the range of the canonical epi embedding. -/
theorem inducedMap_domain (f : M ⟶ N) (i : BarcodeOccurrence s (rankBarcode M)) :
    (∃ j, inducedMap f i = some j) ↔ i ∈ inducedDomain f := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨a, ha, _⟩ := (inducedMap_eq_some_iff f i j).mp hj
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨imageTargetEmbedding f a, (inducedMap_eq_some_iff f _ _).mpr ⟨a, ha, rfl⟩⟩

/-- Unselected source labels are exactly those on which the Option map is undefined. -/
theorem inducedMap_eq_none_iff (f : M ⟶ N) (i : BarcodeOccurrence s (rankBarcode M)) :
    inducedMap f i = none ↔ i ∉ inducedDomain f := by
  classical
  by_cases hi : i ∈ inducedDomain f <;> simp [inducedMap, hi]

/-- The range is exactly the range of the canonical mono embedding. -/
theorem inducedMap_range (f : M ⟶ N) (j : BarcodeOccurrence s (rankBarcode N)) :
    (∃ i, inducedMap f i = some j) ↔ j ∈ Set.range (imageTargetEmbedding f) := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨a, _, ha⟩ := (inducedMap_eq_some_iff f i j).mp hi
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨imageSourceEmbedding f a, (inducedMap_eq_some_iff f _ _).mpr ⟨a, rfl, ha⟩⟩

/-- Selected values cannot identify distinct source occurrence labels. -/
theorem inducedMap_injective (f : M ⟶ N)
    (i i' : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N))
    (hi : inducedMap f i = some j) (hi' : inducedMap f i' = some j) : i = i' := by
  obtain ⟨a, ha, hj⟩ := (inducedMap_eq_some_iff f i j).mp hi
  obtain ⟨a', ha', hj'⟩ := (inducedMap_eq_some_iff f i' j).mp hi'
  have he := (imageTargetEmbedding f).injective (hj.trans hj'.symm)
  exact ha.symm.trans (he ▸ ha')

/-- Image occurrences and matched pairs are equivalent as labeled finite sets. -/
noncomputable def imageOccurrenceEquivPairs (f : M ⟶ N) :
    BarcodeOccurrence s (rankBarcode (finiteImage f)) ≃
      {p : BarcodeOccurrence s (rankBarcode M) × BarcodeOccurrence s (rankBarcode N) //
        inducedMap f p.1 = some p.2} :=
  Equiv.ofBijective (fun a => ⟨(imageSourceEmbedding f a, imageTargetEmbedding f a),
    (inducedMap_eq_some_iff f _ _).mpr ⟨a, rfl, rfl⟩⟩) ⟨by
      intro a b h
      apply (imageSourceEmbedding f).injective
      exact congrArg (fun p => p.val.1) h, by
      rintro ⟨⟨i, j⟩, h⟩
      obtain ⟨a, ha, hj⟩ := (inducedMap_eq_some_iff f i j).mp h
      exact ⟨a, Subtype.ext (Prod.ext ha hj)⟩⟩

/-- The intermediate interval has the source birth and the target death. -/
theorem inducedMap_intermediate_endpoints (f : M ⟶ N)
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N))
    (h : inducedMap f i = some j) :
    ∃ a, imageSourceEmbedding f a = i ∧ imageTargetEmbedding f a = j ∧
      (occurrence (rankBarcode (finiteImage f)) a).birth = (occurrence (rankBarcode M) i).birth ∧
      (occurrence (rankBarcode (finiteImage f)) a).death = (occurrence (rankBarcode N) j).death := by
  obtain ⟨a, rfl, rfl⟩ := (inducedMap_eq_some_iff f i j).mp h
  exact ⟨a, rfl, rfl,
    (epiEmbedding_birth (toFiniteImage f) (toFiniteImage_surjective f) a).symm,
    (monoEmbedding_death (fromFiniteImage f) (fromFiniteImage_injective f) a).symm⟩

/-- Every matched pair satisfies the qualitative endpoint order. -/
theorem inducedMap_endpoints (f : M ⟶ N)
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N))
    (h : inducedMap f i = some j) :
    (occurrence (rankBarcode N) j).birth ≤ (occurrence (rankBarcode M) i).birth ∧
      (occurrence (rankBarcode M) i).birth < (occurrence (rankBarcode N) j).death ∧
      (occurrence (rankBarcode N) j).death ≤ (occurrence (rankBarcode M) i).death := by
  obtain ⟨a, rfl, rfl⟩ := (inducedMap_eq_some_iff f i j).mp h
  have hb := epiEmbedding_birth (toFiniteImage f) (toFiniteImage_surjective f) a
  have hd := monoEmbedding_death (fromFiniteImage f) (fromFiniteImage_injective f) a
  have hblo := monoEmbedding_birth_le (fromFiniteImage f) (fromFiniteImage_injective f) a
  have hdhi := epiEmbedding_death_le (toFiniteImage f) (toFiniteImage_surjective f) a
  change (occurrence _ (imageSourceEmbedding f a)).birth = _ at hb
  change (occurrence _ (imageTargetEmbedding f a)).death = _ at hd
  change _ ≤ (occurrence _ (imageSourceEmbedding f a)).death at hdhi
  have hbar := (occurrence (rankBarcode (finiteImage f)) a).birth_lt_death
  change (occurrence _ (imageTargetEmbedding f a)).birth ≤ _ at hblo
  rw [hb, hd]
  exact ⟨hblo, hbar, hdhi⟩

end TDA.Persistence.FiniteBarcode
