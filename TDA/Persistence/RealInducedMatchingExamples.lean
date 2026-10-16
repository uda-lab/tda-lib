import TDA.Persistence.ConstructibleInducedMatching
import TDA.Persistence.FiniteInducedSpecialization

/-!
# Identity, duplicate and essential controls for real induced matchings

An actual finite barcode has two finite copies and two essential copies on an
irregular grid. The identity map retains each original occurrence label, even
at parameter zero or when the finite bar equals the shortness threshold.
-/

set_option autoImplicit false

namespace TDA.Persistence.RealInducedMatchingExamples

open CategoryTheory CategoryTheory.Limits FiniteBarcode
open scoped Classical NNReal

private def grid : Fin 4 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (![0, 1, 3, 4] : Fin 4 → ℝ)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private def finiteBar : FiniteInterval 4 := ⟨0, 2, by decide, by decide⟩
private def essentialBar : FiniteInterval 4 := ⟨1, 4, by decide, by decide⟩
private def bars : Multiset (FiniteInterval 4) :=
  finiteBar ::ₘ finiteBar ::ₘ essentialBar ::ₘ essentialBar ::ₘ 0
private noncomputable abbrev input := barcodeModule (k := ℚ) bars
private noncomputable abbrev D := RealInduced.diagram grid input

private theorem kernel_id_short (δ : ℝ≥0) :
    TranslationTrivial (FiniteConstructible.sampleTranslation grid δ)
      (FiniteConstructible.le_sampleTranslation grid δ) (finiteKernel (𝟙 input)) := by
  apply (kernel_translationTrivial_iff _ _ _).mpr
  intro i x hx
  change x = 0 at hx
  simp [hx]

private theorem cokernel_id_short (δ : ℝ≥0) :
    TranslationTrivial (FiniteConstructible.sampleTranslation grid δ)
      (FiniteConstructible.le_sampleTranslation grid δ) (finiteCokernel (𝟙 input)) := by
  apply (cokernel_translationTrivial_iff _ _ _).mpr
  intro i
  change _ ≤ LinearMap.range (LinearMap.id : input.obj _ →ₗ[ℚ] input.obj _)
  rw [LinearMap.range_id]
  exact le_top

private noncomputable def identityMatching (δ : ℝ≥0) :=
  RealInduced.matching grid (𝟙 input) δ δ (kernel_id_short δ) (cokernel_id_short δ)

private theorem sum_id (i : RealBarcode.Occurrences D) :
    RealInduced.sumMap grid (𝟙 input) i = some i := by
  unfold RealInduced.sumMap
  rw [inducedMap_id]
  simp only [Option.map_some, Equiv.apply_symm_apply]

/-- The actual induced identity preserves every finite and essential duplicate label. -/
theorem identity_labels (δ : ℝ≥0) :
    (∀ p : D.finiteOccurrences, (identityMatching δ).finite p = some p) ∧
      (∀ b : D.essentialOccurrences, (identityMatching δ).essential b = b) := by
  constructor
  · intro p
    exact (RealInduced.matching_finite_eq_some_iff grid (𝟙 input) δ δ
      (kernel_id_short δ) (cokernel_id_short δ) p p).mpr (sum_id (.inl p))
  · intro b
    exact (RealInduced.matching_essential_eq_iff grid (𝟙 input) δ δ
      (kernel_id_short δ) (cokernel_id_short δ) b b).mpr (sum_id (.inr b))

private theorem diagram_points : D.points =
    ((0 : ℝ), (3 : WithTop ℝ)) ::ₘ (0, (3 : WithTop ℝ)) ::ₘ (1, ⊤) ::ₘ (1, ⊤) ::ₘ 0 := by
  change (ofIndexBars grid grid.strictMono (rankBarcode (barcodeModule (k := ℚ) bars))).points = _
  rw [rankBarcode_barcodeModule, RealBarcode.ofIndexBars_points]
  simp only [bars, Multiset.map_cons, Multiset.map_zero]
  rfl

/-- Finite and essential duplicates each retain their two actual occurrence labels. -/
theorem multiplicities : D.points.count (0, (3 : WithTop ℝ)) = 2 ∧
    D.points.count (1, ⊤) = 2 := by
  rw [diagram_points]
  norm_num

private theorem finite_value (p : D.finiteOccurrences) : p.1 = (0, 3) := by
  have hp : p.1 ∈ finitePart D.points := Multiset.coe_mem
  have hm := Eq.mp (congrArg (fun s : Multiset (ℝ × WithTop ℝ) =>
    p.1 ∈ finitePart s) diagram_points) hp
  change p.1 ∈ ((0, 3) ::ₘ (0, 3) ::ₘ (0 : Multiset (ℝ × ℝ))) at hm
  simpa using hm

/-- Equal endpoint values still give distinct finite and essential occurrence labels. -/
theorem distinct_duplicate_labels (δ : ℝ≥0) :
    (∃ p q : D.finiteOccurrences, p ≠ q ∧ p.1 = q.1 ∧
      (identityMatching δ).finite p = some p ∧ (identityMatching δ).finite q = some q) ∧
    (∃ b c : D.essentialOccurrences, b ≠ c ∧ b.1 = c.1 ∧
      (identityMatching δ).essential b = b ∧ (identityMatching δ).essential c = c) := by
  have hf : (finitePart D.points).count (0, 3) = 2 := by
    rw [diagram_points]
    change ((0, 3) ::ₘ (0, 3) ::ₘ (0 : Multiset (ℝ × ℝ))).count (0, 3) = 2
    norm_num
  have he : (essentialPart D.points).count 1 = 2 := by
    rw [diagram_points]
    change ((1 : ℝ) ::ₘ 1 ::ₘ (0 : Multiset ℝ)).count 1 = 2
    norm_num
  constructor
  · let p : D.finiteOccurrences := ⟨(0, 3), ⟨0, by omega⟩⟩
    let q : D.finiteOccurrences := ⟨(0, 3), ⟨1, by omega⟩⟩
    refine ⟨p, q, ?_, rfl, (identity_labels δ).1 p, (identity_labels δ).1 q⟩
    intro h
    have hn := congrArg (fun x : D.finiteOccurrences => x.2.val) h
    norm_num [p, q] at hn
  · let b : D.essentialOccurrences := ⟨1, ⟨0, by omega⟩⟩
    let c : D.essentialOccurrences := ⟨1, ⟨1, by omega⟩⟩
    refine ⟨b, c, ?_, rfl, (identity_labels δ).2 b, (identity_labels δ).2 c⟩
    intro h
    have hn := congrArg (fun x : D.essentialOccurrences => x.2.val) h
    norm_num [b, c] at hn

/-- Both finite labels are strictly long at threshold two and have unique partners. -/
theorem strict_long_unique (p : D.finiteOccurrences) :
    (∃! q, (identityMatching 2).finite p = some q) ∧
      (∃! q, (identityMatching 2).finite q = some p) := by
  have h := RealInduced.matching_bounds grid (𝟙 input) 2 2 (kernel_id_short 2) (cokernel_id_short 2)
  have hl : (2 : ℝ) < p.1.2 - p.1.1 := by rw [finite_value p]; norm_num
  exact ⟨h.covers_long_source p hl, h.covers_long_target p hl⟩

/-- Threshold equality permits a match; it is not an exclusion rule. -/
theorem threshold_matched (p : D.finiteOccurrences) :
    p.1.2 - p.1.1 = 3 ∧ (identityMatching 3).finite p = some p := by
  refine ⟨?_, (identity_labels 3).1 p⟩
  rw [finite_value p]
  norm_num

/-- Essential labels survive every finite threshold and are covered bijectively. -/
theorem essential_every_threshold (δ : ℝ≥0) :
    (∀ b : D.essentialOccurrences, (identityMatching δ).essential b = b) ∧
      Function.Bijective (identityMatching δ).essential :=
  ⟨(identity_labels δ).2, (identityMatching δ).essential.bijective⟩

/-- Parameter zero retains all actual labels and derives exact endpoint bounds. -/
theorem zero_parameter : RealMatchingBounds 0 0 (identityMatching 0) ∧
    (∀ p : D.finiteOccurrences, (identityMatching 0).finite p = some p) ∧
      (∀ b : D.essentialOccurrences, (identityMatching 0).essential b = b) :=
  ⟨RealInduced.matching_bounds grid (𝟙 input) 0 0 (kernel_id_short 0) (cokernel_id_short 0),
    identity_labels 0⟩

private def emptyGrid : Fin 0 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
private noncomputable abbrev emptyModule : PModule.{0,0,0} ℚ (Fin 0) := barcodeModule (k := ℚ) 0

/-- Empty sampling constructs the genuine empty real matching without selecting a stage. -/
theorem empty_matching (δK δC : ℝ≥0) :
    ∃ A : OccurrenceMatching (RealInduced.diagram emptyGrid emptyModule).finiteOccurrences
        (RealInduced.diagram emptyGrid emptyModule).finiteOccurrences
        (RealInduced.diagram emptyGrid emptyModule).essentialOccurrences
        (RealInduced.diagram emptyGrid emptyModule).essentialOccurrences,
      RealMatchingBounds δK δC A := by
  let hk : TranslationTrivial (FiniteConstructible.sampleTranslation emptyGrid δK)
      (FiniteConstructible.le_sampleTranslation emptyGrid δK) (finiteKernel (𝟙 emptyModule)) :=
    fun i => Fin.elim0 i
  let hc : TranslationTrivial (FiniteConstructible.sampleTranslation emptyGrid δC)
      (FiniteConstructible.le_sampleTranslation emptyGrid δC) (finiteCokernel (𝟙 emptyModule)) :=
    fun i => Fin.elim0 i
  exact ⟨RealInduced.matching emptyGrid (𝟙 emptyModule) δK δC hk hc,
    RealInduced.matching_bounds emptyGrid (𝟙 emptyModule) δK δC hk hc⟩

end TDA.Persistence.RealInducedMatchingExamples
