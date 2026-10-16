import TDA.Persistence.ConstructibleSampling
import TDA.Persistence.ConstructibleShiftBarcode
import TDA.Persistence.FiniteInducedTranslationMatching
import TDA.Persistence.MatchingInterleaving

/-!
# Real occurrence labels for the actual finite induced matching

Finite index occurrences identify the finite/essential occurrence presentation
of their real endpoint diagram. Rounded finite translation bounds give exact
real endpoint bounds: the selected critical value is at most the original
parameter plus the requested real displacement. Terminal deaths stay essential.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits RealShift FiniteBarcode
open scoped Classical NNReal ENNReal

namespace RealBarcode

private theorem index_point_multiset {n : ℕ} (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval n)) :
    (Finset.univ : Finset (BarcodeOccurrence n B)).val.map
        (fun i => endpoints c (occurrence B i)) =
      (Finset.univ : Finset (Occurrences (ofIndexBars c c.strictMono B))).val.map
        (occurrencePoint _) := by
  rw [occurrencePoint_multiset, ofIndexBars_points]
  calc
    _ = ((Finset.univ : Finset (BarcodeOccurrence n B)).val.map
          (fun i => occurrence B i)).map (endpoints c) := by rw [Multiset.map_map]; rfl
    _ = B.map (endpoints c) := by
      rw [Fin.univ_val_map]
      change ((List.ofFn (fun i => B.toList.get i) : List (FiniteInterval n)) :
        Multiset (FiniteInterval n)).map _ = _
      rw [List.ofFn_get, Multiset.coe_toList]

/-- Finite index labels and actual real diagram occurrences agree with multiplicity. -/
noncomputable def indexOccurrenceEquiv {n : ℕ} (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval n)) :
    BarcodeOccurrence n B ≃ Occurrences (ofIndexBars c c.strictMono B) :=
  (presentationEquiv (fun i => endpoints c (occurrence B i)) (occurrencePoint _)
    (index_point_multiset c B)).1

/-- The occurrence equivalence retains each actual real endpoint pair. -/
theorem indexOccurrenceEquiv_value {n : ℕ} (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval n)) (i : BarcodeOccurrence n B) :
    occurrencePoint _ (indexOccurrenceEquiv c B i) = endpoints c (occurrence B i) :=
  (presentationEquiv (fun i => endpoints c (occurrence B i)) (occurrencePoint _)
    (index_point_multiset c B)).2 i

/-- Read a real occurrence through its original finite index label. -/
theorem indexOccurrenceEquiv_symm_value {n : ℕ} (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval n)) (i : Occurrences (ofIndexBars c c.strictMono B)) :
    endpoints c (occurrence B ((indexOccurrenceEquiv c B).symm i)) = occurrencePoint _ i := by
  simpa only [Equiv.apply_symm_apply] using
    (indexOccurrenceEquiv_value c B ((indexOccurrenceEquiv c B).symm i)).symm

/-- An observed finite death gives an actual finite diagram occurrence with its endpoints. -/
theorem indexOccurrenceEquiv_finite {n : ℕ} (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval n)) (i : BarcodeOccurrence n B)
    (hi : (occurrence B i).death < n) :
    ∃ p, indexOccurrenceEquiv c B i = .inl p ∧
      (p.1.1, (p.1.2 : WithTop ℝ)) = endpoints c (occurrence B i) := by
  have hv := indexOccurrenceEquiv_value c B i
  cases h : indexOccurrenceEquiv c B i with
  | inl p => exact ⟨p, rfl, by simpa only [h, occurrencePoint] using hv⟩
  | inr b =>
    have hd := congrArg Prod.snd hv
    simp [h, occurrencePoint, endpoints, hi] at hd

/-- A terminal index death gives an actual essential occurrence, never a finite sentinel. -/
theorem indexOccurrenceEquiv_essential {n : ℕ} (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval n)) (i : BarcodeOccurrence n B)
    (hi : (occurrence B i).death = n) :
    ∃ b, indexOccurrenceEquiv c B i = .inr b ∧
      b.1 = c (occurrence B i).birthStage := by
  have hv := indexOccurrenceEquiv_value c B i
  cases h : indexOccurrenceEquiv c B i with
  | inl p =>
    have hd := congrArg Prod.snd hv
    simp [h, occurrencePoint, endpoints, hi] at hd
  | inr b =>
    refine ⟨b, rfl, ?_⟩
    simpa only [h, occurrencePoint, endpoints, FiniteInterval.birthStage]
      using (congrArg Prod.fst hv)

end RealBarcode

/-- One-sided real endpoint control, with finite and essential cases separated.
Different finite/essential death classifications are excluded. -/
def RealEndpointBounds (δK δC : ℝ≥0) (p q : ℝ × WithTop ℝ) : Prop :=
  q.1 ≤ p.1 ∧ p.1 ≤ q.1 + (δC : ℝ) ∧
    match p.2, q.2 with
    | some d, some e => p.1 < e ∧ e ≤ d ∧ d ≤ e + (δK : ℝ)
    | none, none => True
    | _, _ => False

namespace FiniteConstructible

private theorem endpoints_bounds {n : ℕ} (c : Fin n ↪o ℝ)
    (δK δC : ℝ≥0) (I J : FiniteInterval n)
    (hb : J.birth ≤ I.birth) (hb' : I.birth ≤ (sampleTranslation c δC J.birthStage).val)
    (hover : I.birth < J.death) (hd : J.death ≤ I.death)
    (hd' : I.death ≤ J.translatedDeath (sampleTranslation c δK)) :
    RealEndpointBounds δK δC (RealBarcode.endpoints c I) (RealBarcode.endpoints c J) := by
  have hb₀ : c J.birthStage ≤ c I.birthStage := c.monotone hb
  have hb₁ : c I.birthStage ≤ c J.birthStage + (δC : ℝ) :=
    (c.monotone hb').trans (sampleTranslation_value_le c δC J.birthStage)
  refine ⟨hb₀, hb₁, ?_⟩
  by_cases hj : J.death < n
  · rw [FiniteInterval.translatedDeath_of_lt J _ hj] at hd'
    have hi : I.death < n := hd'.trans_lt (sampleTranslation c δK ⟨J.death, hj⟩).isLt
    dsimp only [RealBarcode.endpoints]
    rw [dif_pos hi, dif_pos hj]
    change c I.birthStage < c ⟨J.death, hj⟩ ∧
      c ⟨J.death, hj⟩ ≤ c ⟨I.death, hi⟩ ∧
      c ⟨I.death, hi⟩ ≤ c ⟨J.death, hj⟩ + (δK : ℝ)
    exact ⟨c.strictMono hover, c.monotone hd,
      (c.monotone hd').trans (sampleTranslation_value_le c δK ⟨J.death, hj⟩)⟩
  · have hi : ¬ I.death < n := fun hi => hj (hd.trans_lt hi)
    simp only [RealBarcode.endpoints, dif_neg hi, dif_neg hj]

private theorem endpoints_short {n : ℕ} (c : Fin n ↪o ℝ) (δ : ℝ≥0)
    (I : FiniteInterval n) (h : I.death ≤ (sampleTranslation c δ I.birthStage).val) :
    (RealBarcode.endpoints c I).2 ≤
      ((RealBarcode.endpoints c I).1 + (δ : ℝ) : ℝ) := by
  have hi : I.death < n := h.trans_lt (sampleTranslation c δ I.birthStage).isLt
  change (if hd : I.death < n then (c ⟨I.death, hd⟩ : WithTop ℝ) else ⊤) ≤ _
  rw [dif_pos hi]
  exact WithTop.coe_le_coe.mpr
    ((c.monotone h).trans (sampleTranslation_value_le c δ I.birthStage))

end FiniteConstructible

/-- Proved endpoint and unmatched-length conclusions for a real occurrence matching.
This packages outputs; the induced-matching capstone derives every field. -/
structure RealMatchingBounds (δK δC : ℝ≥0) {D E : Diagram ℝ}
    (A : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) : Prop where
  finite_bounds : ∀ i j, A.finite i = some j →
    RealEndpointBounds δK δC (i.1.1, (i.1.2 : WithTop ℝ)) (j.1.1, (j.1.2 : WithTop ℝ))
  essential_bounds : ∀ b,
    RealEndpointBounds δK δC (b.1, ⊤) ((A.essential b).1, ⊤)
  source_short : ∀ i, A.finite i = none → i.1.2 - i.1.1 ≤ (δK : ℝ)
  target_short : ∀ j, (∀ i, A.finite i ≠ some j) → j.1.2 - j.1.1 ≤ (δC : ℝ)

private def finiteOption {F E : Type} : Option (F ⊕ E) → Option F
  | some (.inl j) => some j
  | _ => none

private theorem finiteOption_some_iff {F E : Type} (o : Option (F ⊕ E)) (j : F) :
    finiteOption o = some j ↔ o = some (.inl j) := by
  cases o with
  | none => simp [finiteOption]
  | some q => cases q <;> simp [finiteOption]

private noncomputable def splitMatching {F G E H : Type}
    (σ : F ⊕ E → Option (G ⊕ H))
    (hinj : ∀ i i' j, σ i = some j → σ i' = some j → i = i')
    (htotal : ∀ b, ∃ c, σ (.inr b) = some (.inr c))
    (hsurj : ∀ c, ∃ b, σ (.inr b) = some (.inr c)) : OccurrenceMatching F G E H := by
  let g : E → H := fun b => (htotal b).choose
  have hg (b : E) : σ (.inr b) = some (.inr (g b)) := (htotal b).choose_spec
  refine ⟨fun i => finiteOption (σ (.inl i)), ?_, Equiv.ofBijective g ⟨?_, ?_⟩⟩
  · intro i i' j hi hi'
    exact Sum.inl.inj (hinj _ _ _ ((finiteOption_some_iff _ _).mp hi)
      ((finiteOption_some_iff _ _).mp hi'))
  · intro b b' h
    exact Sum.inr.inj (hinj _ _ _ (hg b) (h ▸ hg b'))
  · intro c
    obtain ⟨b, hb⟩ := hsurj c
    exact ⟨b, Sum.inr.inj (Option.some.inj ((hg b).symm.trans hb))⟩

private theorem splitMatching_finite_some_iff {F G E H : Type}
    (σ : F ⊕ E → Option (G ⊕ H))
    (hinj : ∀ i i' j, σ i = some j → σ i' = some j → i = i')
    (htotal : ∀ b, ∃ c, σ (.inr b) = some (.inr c))
    (hsurj : ∀ c, ∃ b, σ (.inr b) = some (.inr c)) (i : F) (j : G) :
    (splitMatching σ hinj htotal hsurj).finite i = some j ↔ σ (.inl i) = some (.inl j) :=
  finiteOption_some_iff _ _

private theorem splitMatching_essential_match {F G E H : Type}
    (σ : F ⊕ E → Option (G ⊕ H))
    (hinj : ∀ i i' j, σ i = some j → σ i' = some j → i = i')
    (htotal : ∀ b, ∃ c, σ (.inr b) = some (.inr c))
    (hsurj : ∀ c, ∃ b, σ (.inr b) = some (.inr c)) (b : E) :
    σ (.inr b) = some (.inr ((splitMatching σ hinj htotal hsurj).essential b)) :=
  (htotal b).choose_spec

namespace FiniteBarcode.RealInduced

variable {n : ℕ} {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin n)}
variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

/-- The existing real endpoint diagram of the actual finite rank barcode. -/
noncomputable abbrev diagram (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k (Fin n))
    [∀ i, FiniteDimensional k (M.obj i)] : Diagram ℝ :=
  ofIndexBars c c.strictMono (rankBarcode M)

/-- Transport the actual induced partial injection, including essential index bars. -/
noncomputable def sumMap (c : Fin n ↪o ℝ) (f : M ⟶ N)
    (i : RealBarcode.Occurrences (diagram c M)) :
    Option (RealBarcode.Occurrences (diagram c N)) :=
  (inducedMap f ((RealBarcode.indexOccurrenceEquiv c (rankBarcode M)).symm i)).map
    (RealBarcode.indexOccurrenceEquiv c (rankBarcode N))

/-- The exact selected-pair relation is retained under occurrence relabelling. -/
theorem sumMap_eq_some_iff (c : Fin n ↪o ℝ) (f : M ⟶ N)
    (i : RealBarcode.Occurrences (diagram c M))
    (j : RealBarcode.Occurrences (diagram c N)) :
    sumMap c f i = some j ↔
      inducedMap f ((RealBarcode.indexOccurrenceEquiv c (rankBarcode M)).symm i) =
        some ((RealBarcode.indexOccurrenceEquiv c (rankBarcode N)).symm j) := by
  unfold sumMap
  cases h : inducedMap f ((RealBarcode.indexOccurrenceEquiv c (rankBarcode M)).symm i) with
  | none => simp
  | some q =>
    simp only [Option.map_some, Option.some.injEq]
    exact (Equiv.eq_symm_apply _).symm

/-- Multiplicity labels remain partially injective after real endpoint relabelling. -/
theorem sumMap_injective (c : Fin n ↪o ℝ) (f : M ⟶ N)
    (i i' : RealBarcode.Occurrences (diagram c M))
    (j : RealBarcode.Occurrences (diagram c N))
    (hi : sumMap c f i = some j) (hi' : sumMap c f i' = some j) : i = i' :=
  (RealBarcode.indexOccurrenceEquiv c (rankBarcode M)).symm.injective
    (inducedMap_injective f _ _ _ ((sumMap_eq_some_iff c f i j).mp hi)
      ((sumMap_eq_some_iff c f i' j).mp hi'))

/-- Actual finite defect shortness gives exact real matched bounds without mesh error. -/
theorem sumMap_bounds (c : Fin n ↪o ℝ) (f : M ⟶ N) (δK δC : ℝ≥0)
    (hk : TranslationTrivial (FiniteConstructible.sampleTranslation c δK)
      (FiniteConstructible.le_sampleTranslation c δK) (finiteKernel f))
    (hc : TranslationTrivial (FiniteConstructible.sampleTranslation c δC)
      (FiniteConstructible.le_sampleTranslation c δC) (finiteCokernel f))
    (i : RealBarcode.Occurrences (diagram c M))
    (j : RealBarcode.Occurrences (diagram c N)) (h : sumMap c f i = some j) :
    RealEndpointBounds δK δC (RealBarcode.occurrencePoint _ i) (RealBarcode.occurrencePoint _ j) := by
  rw [← RealBarcode.indexOccurrenceEquiv_symm_value c (rankBarcode M) i,
    ← RealBarcode.indexOccurrenceEquiv_symm_value c (rankBarcode N) j]
  have hb := inducedMap_endpoint_bounds_of_shortness _ _ _ _ f hk hc _ _
    ((sumMap_eq_some_iff c f i j).mp h)
  exact FiniteConstructible.endpoints_bounds c δK δC _ _ hb.1 hb.2.1 hb.2.2.1
    hb.2.2.2.1 hb.2.2.2.2

private theorem sumMap_source_short (c : Fin n ↪o ℝ) (f : M ⟶ N) (δK : ℝ≥0)
    (hk : TranslationTrivial (FiniteConstructible.sampleTranslation c δK)
      (FiniteConstructible.le_sampleTranslation c δK) (finiteKernel f))
    (i : RealBarcode.Occurrences (diagram c M)) (h : sumMap c f i = none) :
    (RealBarcode.occurrencePoint _ i).2 ≤
      ((RealBarcode.occurrencePoint _ i).1 + (δK : ℝ) : ℝ) := by
  have hn : inducedMap f ((RealBarcode.indexOccurrenceEquiv c (rankBarcode M)).symm i) = none :=
    Option.map_eq_none_iff.mp h
  rw [← RealBarcode.indexOccurrenceEquiv_symm_value c (rankBarcode M) i]
  exact FiniteConstructible.endpoints_short c δK _
    (inducedMap_unmatched_source_short_of_kernelTrivial _ _ f hk _ hn)

private theorem sumMap_target_short (c : Fin n ↪o ℝ) (f : M ⟶ N) (δC : ℝ≥0)
    (hc : TranslationTrivial (FiniteConstructible.sampleTranslation c δC)
      (FiniteConstructible.le_sampleTranslation c δC) (finiteCokernel f))
    (j : RealBarcode.Occurrences (diagram c N)) (h : ∀ i, sumMap c f i ≠ some j) :
    (RealBarcode.occurrencePoint _ j).2 ≤
      ((RealBarcode.occurrencePoint _ j).1 + (δC : ℝ) : ℝ) := by
  have hn (a : BarcodeOccurrence n (rankBarcode M)) :
      inducedMap f a ≠ some ((RealBarcode.indexOccurrenceEquiv c (rankBarcode N)).symm j) := by
    intro ha
    apply h (RealBarcode.indexOccurrenceEquiv c (rankBarcode M) a)
    apply (sumMap_eq_some_iff c f _ j).mpr
    simpa only [Equiv.symm_apply_apply] using ha
  rw [← RealBarcode.indexOccurrenceEquiv_symm_value c (rankBarcode N) j]
  exact FiniteConstructible.endpoints_short c δC _
    (inducedMap_unmatched_target_short_of_cokernelTrivial _ _ f hc _ hn)

variable (c : Fin n ↪o ℝ) (f : M ⟶ N) (δK δC : ℝ≥0)
variable (hk : TranslationTrivial (FiniteConstructible.sampleTranslation c δK)
  (FiniteConstructible.le_sampleTranslation c δK) (finiteKernel f))
variable (hc : TranslationTrivial (FiniteConstructible.sampleTranslation c δC)
  (FiniteConstructible.le_sampleTranslation c δC) (finiteCokernel f))

include δK δC hk hc

private theorem no_cross (i : (diagram c M).finiteOccurrences)
    (b : (diagram c N).essentialOccurrences) : sumMap c f (.inl i) ≠ some (.inr b) := by
  intro h
  have hb := sumMap_bounds c f δK δC hk hc _ _ h
  simp [RealEndpointBounds, RealBarcode.occurrencePoint] at hb

private theorem essential_total (b : (diagram c M).essentialOccurrences) :
    ∃ d, sumMap c f (.inr b) = some (.inr d) := by
  cases h : sumMap c f (.inr b) with
  | none =>
    have hs := sumMap_source_short c f δK hk (.inr b) h
    simp [RealBarcode.occurrencePoint] at hs
  | some j =>
    cases j with
    | inl j =>
      have hb := sumMap_bounds c f δK δC hk hc _ _ h
      simp [RealEndpointBounds, RealBarcode.occurrencePoint] at hb
    | inr d => exact ⟨d, rfl⟩

private theorem essential_surjective (d : (diagram c N).essentialOccurrences) :
    ∃ b, sumMap c f (.inr b) = some (.inr d) := by
  have hex : ∃ i, sumMap c f i = some (.inr d) := by
    by_contra! hn
    have hs := sumMap_target_short c f δC hc (.inr d) hn
    simp [RealBarcode.occurrencePoint] at hs
  obtain ⟨i, hi⟩ := hex
  cases i with
  | inl i => exact False.elim (no_cross c f δK δC hk hc i d hi)
  | inr b => exact ⟨b, hi⟩

/-- The actual finite induced partial injection, split into a real finite partial
injection and the derived total essential-occurrence equivalence. -/
noncomputable def matching : OccurrenceMatching (diagram c M).finiteOccurrences
    (diagram c N).finiteOccurrences (diagram c M).essentialOccurrences
    (diagram c N).essentialOccurrences :=
  splitMatching (sumMap c f) (sumMap_injective c f)
    (essential_total c f δK δC hk hc) (essential_surjective c f δK δC hk hc)

/-- A finite pair is selected exactly by the transported actual induced partial injection. -/
theorem matching_finite_eq_some_iff (i : (diagram c M).finiteOccurrences)
    (j : (diagram c N).finiteOccurrences) :
    (matching c f δK δC hk hc).finite i = some j ↔
      sumMap c f (.inl i) = some (.inl j) :=
  splitMatching_finite_some_iff _ _ _ _ i j

/-- Every essential pair is selected by that same actual induced partial injection. -/
theorem matching_essential_match (b : (diagram c M).essentialOccurrences) :
    sumMap c f (.inr b) = some (.inr ((matching c f δK δC hk hc).essential b)) :=
  splitMatching_essential_match _ _ _ _ b

/-- The essential equivalence selects exactly the same pairs as the induced partial map. -/
theorem matching_essential_eq_iff (b : (diagram c M).essentialOccurrences)
    (d : (diagram c N).essentialOccurrences) :
    (matching c f δK δC hk hc).essential b = d ↔
      sumMap c f (.inr b) = some (.inr d) := by
  constructor
  · intro h
    rw [← h]
    exact matching_essential_match c f δK δC hk hc b
  · intro h
    exact Sum.inr.inj (Option.some.inj
      ((matching_essential_match c f δK δC hk hc b).symm.trans h))

/-- All real matched endpoints and unmatched-length conclusions are derived. -/
theorem matching_bounds : RealMatchingBounds δK δC (matching c f δK δC hk hc) := by
  constructor
  · intro i j hij
    exact sumMap_bounds c f δK δC hk hc (.inl i) (.inl j)
      ((matching_finite_eq_some_iff c f δK δC hk hc i j).mp hij)
  · intro b
    exact sumMap_bounds c f δK δC hk hc _ _ (matching_essential_match c f δK δC hk hc b)
  · intro i hi
    have hn : sumMap c f (.inl i) = none := by
      cases h : sumMap c f (.inl i) with
      | none => rfl
      | some j =>
        cases j with
        | inl j =>
          have hh := (matching_finite_eq_some_iff c f δK δC hk hc i j).mpr h
          rw [hi] at hh
          contradiction
        | inr b => exact False.elim (no_cross c f δK δC hk hc i b h)
    have hs := sumMap_source_short c f δK hk (.inl i) hn
    have hr : i.1.2 ≤ i.1.1 + (δK : ℝ) := WithTop.coe_le_coe.mp hs
    linarith
  · intro j hj
    have hn (i : RealBarcode.Occurrences (diagram c M)) :
        sumMap c f i ≠ some (.inl j) := by
      intro hi
      cases i with
      | inl i => exact hj i ((matching_finite_eq_some_iff c f δK δC hk hc i j).mpr hi)
      | inr b =>
        have hb := sumMap_bounds c f δK δC hk hc _ _ hi
        simp [RealEndpointBounds, RealBarcode.occurrencePoint] at hb
    have hs := sumMap_target_short c f δC hc (.inl j) hn
    have hr : j.1.2 ≤ j.1.1 + (δC : ℝ) := WithTop.coe_le_coe.mp hs
    linarith

end FiniteBarcode.RealInduced
namespace RealMatchingBounds

variable {δK δC : ℝ≥0} {D E : Diagram ℝ}
variable {A : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
  D.essentialOccurrences E.essentialOccurrences}

/-- Every strictly kernel-long finite source has a unique selected target. -/
theorem covers_long_source (h : RealMatchingBounds δK δC A) (i : D.finiteOccurrences)
    (hlong : (δK : ℝ) < i.1.2 - i.1.1) : ∃! j, A.finite i = some j := by
  cases hi : A.finite i with
  | none => exact False.elim (not_lt_of_ge (h.source_short i hi) hlong)
  | some j => exact ⟨j, rfl, fun j' hj' => Option.some.inj hj'.symm⟩

/-- Every strictly cokernel-long finite target has a unique selected source. -/
theorem covers_long_target (h : RealMatchingBounds δK δC A) (j : E.finiteOccurrences)
    (hlong : (δC : ℝ) < j.1.2 - j.1.1) : ∃! i, A.finite i = some j := by
  have hex : ∃ i, A.finite i = some j := by
    by_contra! hn
    exact not_lt_of_ge (h.target_short j hn) hlong
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun i' hi' => A.finite_injective i' i j hi' hi⟩

end RealMatchingBounds

end TDA.Persistence
