import TDA.Persistence.FiniteInducedTranslationMatching
import TDA.Persistence.FiniteInducedSpecialization
import TDA.Persistence.RealInducedMatching
import Mathlib.Data.Rat.Defs

/-! # Actual epimorphisms and canonical barcode embedding consumers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TDA.Persistence.FiniteInducedTranslationExamples

open CategoryTheory FiniteBarcode

private def long : FiniteInterval 4 := ⟨0, 3, by decide, by decide⟩
private def middle : FiniteInterval 4 := ⟨0, 2, by decide, by decide⟩
private def short : FiniteInterval 4 := ⟨0, 1, by decide, by decide⟩
private def laterLong : FiniteInterval 4 := ⟨1, 3, by decide, by decide⟩
private def laterShort : FiniteInterval 4 := ⟨1, 2, by decide, by decide⟩

private theorem singleton_count {n : ℕ} (I : FiniteInterval n) (p : FiniteInterval n → Prop)
    [DecidablePred p] : ({I} : Multiset (FiniteInterval n)).countP p = if p I then 1 else 0 := by
  rw [← Multiset.cons_zero, Multiset.countP_cons]
  simp

private theorem single_barcode (I : FiniteInterval 4) :
    rankBarcode (intervalModule (k := ℚ) I) = {I} := by
  classical
  calc
    _ = rankBarcode (barcodeModule (k := ℚ) {I}) := by
      apply (rankBarcode_eq_iff _ _).mpr
      intro i j hij
      rw [rank_barcodeMap]
      change Module.finrank ℚ (LinearMap.range (intervalMap (k := ℚ) I hij)) = _
      rw [intervalMap_finrank_range]
      simp only [interval_alive_endpoints_iff I hij, singleton_count]
    _ = {I} := rankBarcode_barcodeModule _

private theorem alive_of_target (I J : FiniteInterval 4) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death) (i : Fin 4) (hi : J.alive i) : I.alive i :=
  ⟨hb ▸ hi.1, hi.2.trans_le hd⟩

private noncomputable def truncateLinear (I J : FiniteInterval 4) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death) (i : Fin 4) : I.fiber (k := ℚ) i →ₗ[ℚ] J.fiber (k := ℚ) i := by
  classical
  exact if h : J.alive i then
    Submodule.inclusion (by simp [FiniteInterval.fiber, h, alive_of_target I J hb hd i h])
  else 0

private theorem zero_of_not_alive (I : FiniteInterval 4) (i : Fin 4)
    (hi : ¬ I.alive i) (x : I.fiber (k := ℚ) i) : x = 0 := by
  apply Subtype.ext
  have h := x.property
  simpa [FiniteInterval.fiber, hi] using h

private noncomputable def truncate (I J : FiniteInterval 4) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death) : intervalModule (k := ℚ) I ⟶ intervalModule J where
  app i := ModuleCat.ofHom (truncateLinear I J hb hd i)
  naturality {i j} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change truncateLinear I J hb hd j (intervalMap I (leOfHom f) x) =
      intervalMap J (leOfHom f) (truncateLinear I J hb hd i x)
    by_cases hj : J.alive j
    · have hIj := alive_of_target I J hb hd j hj
      by_cases hi : I.alive i
      · have hJi : J.alive i := ⟨hb ▸ hi.1, (Fin.le_iff_val_le_val.mp (leOfHom f)).trans_lt hj.2⟩
        apply Subtype.ext
        simp [truncateLinear, intervalMap, hi, hj, hIj, hJi]
      · have hx : x = 0 := zero_of_not_alive I i hi x
        rw [hx, map_zero, map_zero, map_zero, map_zero]
    · let : Subsingleton (J.fiber (k := ℚ) j) := by
        rw [FiniteInterval.fiber, if_neg hj]
        infer_instance
      exact Subsingleton.elim _ _

private theorem truncate_surjective (I J : FiniteInterval 4) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death) (i : Fin 4) : Function.Surjective ((truncate I J hb hd).app i).hom := by
  classical
  intro y
  change ∃ x : I.fiber (k := ℚ) i, truncateLinear I J hb hd i x = y
  by_cases hi : J.alive i
  · have hI := alive_of_target I J hb hd i hi
    refine ⟨⟨y.val, by simp [FiniteInterval.fiber, hI]⟩, ?_⟩
    apply Subtype.ext
    simp only [truncateLinear, dif_pos hi]
    rfl
  · have hy : y = 0 := zero_of_not_alive J i hi y
    subst y
    exact ⟨0, map_zero _⟩

private noncomputable def first := truncate long middle rfl (by decide)
private theorem first_surjective (i : Fin 4) : Function.Surjective (first.app i).hom :=
  truncate_surjective long middle rfl (by decide) i

private theorem single_occurrence (I : FiniteInterval 4)
    (a : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) I))) :
    occurrence (rankBarcode (intervalModule (k := ℚ) I)) a = I := by
  have hmem := Multiset.mem_toList.mp (List.get_mem (rankBarcode (intervalModule (k := ℚ) I)).toList a)
  change occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈ _ at hmem
  have hmem' : occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈
      ({I} : Multiset (FiniteInterval 4)) := Eq.mp
    (congrArg (fun B : Multiset (FiniteInterval 4) =>
      occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈ B) (single_barcode I)) hmem
  simpa using hmem'

private def theta : Fin 4 →o Fin 4 where
  toFun i := if i.val < 2 then 1 else 3
  monotone' a b hab := by
    change a.val ≤ b.val at hab
    dsimp
    split_ifs <;> omega

private theorem theta_forward (i : Fin 4) : i ≤ theta i := by
  fin_cases i <;> decide

private theorem truncate_kernel_short (I J : FiniteInterval 4) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death)
    (hkill : ∀ i, I.alive i → ¬ J.alive i → ¬ I.alive (theta i)) :
    TranslationTrivial theta theta_forward (finiteKernel (truncate I J hb hd)) := by
  apply (kernel_translationTrivial_iff _ _ _).mpr
  intro i x hx
  change intervalMap I (theta_forward i) x = 0
  by_cases hi : I.alive i
  · by_cases hj : J.alive i
    · change truncateLinear I J hb hd i x = 0 at hx
      have hxval : x.val = 0 := by
        simpa [truncateLinear, hj] using congrArg Subtype.val hx
      have hxzero : x = 0 := Subtype.ext hxval
      rw [hxzero, map_zero]
    · apply Subtype.ext
      simp [intervalMap, hkill i hi hj]
  · rw [zero_of_not_alive I i hi x, map_zero]

private theorem first_kernel_short : TranslationTrivial theta theta_forward (finiteKernel first) :=
  truncate_kernel_short long middle rfl (by decide) (by
    intro i; fin_cases i <;> norm_num [long, middle, theta, FiniteInterval.alive])

/-- The translation genuinely advances and identifies stages. -/
theorem noninjective_translation : theta 0 = 1 ∧ theta 1 = 1 ∧ ¬ Function.Injective theta := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have he := congrArg Fin.val (h (show theta 0 = theta 1 from rfl))
  norm_num at he

/-- A nonidentity epi attains the finite death upper bound derived from its actual kernel. -/
theorem finite_death_bound_attained :
    TranslationTrivial theta theta_forward (finiteKernel first) ∧
      ∃ j : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) middle)),
        (occurrence _ j).death = 2 ∧
        (occurrence _ (epiEmbedding first first_surjective j)).death = 3 ∧
        (occurrence _ (epiEmbedding first first_surjective j)).death ≤
          (occurrence _ j).translatedDeath theta ∧
        (occurrence _ j).translatedDeath theta = 3 := by
  have hlen : (rankBarcode (intervalModule (k := ℚ) middle)).toList.length = 1 := by
    rw [single_barcode]; simp
  let j : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) middle)) := ⟨0, by omega⟩
  exact ⟨first_kernel_short, j,
    congrArg FiniteInterval.death (single_occurrence middle j),
    congrArg FiniteInterval.death (single_occurrence long _),
    (epiEmbedding_death_bounds_of_kernelTrivial theta theta_forward first first_surjective
      first_kernel_short j).2, by rw [single_occurrence]; rfl⟩

private noncomputable def later := truncate laterLong laterShort rfl (by decide)
private theorem later_surjective (i : Fin 4) : Function.Surjective (later.app i).hom :=
  truncate_surjective laterLong laterShort rfl (by decide) i
private theorem later_kernel_short : TranslationTrivial theta theta_forward (finiteKernel later) :=
  truncate_kernel_short laterLong laterShort rfl (by decide) (by
    intro i; fin_cases i <;> norm_num [laterLong, laterShort, theta, FiniteInterval.alive])

/-- Positive birth uses the preceding-image quotient before comparing translated survival. -/
theorem positive_birth_count :
    TranslationTrivial theta theta_forward (finiteKernel later) ∧
      birthSuffixCount (rankBarcode (intervalModule (k := ℚ) laterLong)) 1 1 = 1 ∧
      birthSuffixCount (rankBarcode (intervalModule (k := ℚ) laterLong)) 1 (theta 1).val ≤
        birthSuffixCount (rankBarcode (intervalModule (k := ℚ) laterShort)) 1 1 := by
  refine ⟨later_kernel_short, ?_, birthSuffixCount_translated_le_of_kernelTrivial
    theta theta_forward later later_surjective later_kernel_short 1 1 (le_refl _)⟩
  simp [single_barcode, birthSuffixCount, singleton_count, laterLong]

private theorem identity_kernel_short {n : ℕ} (M : PModule.{0,0,0} ℚ (Fin n))
    (t : Fin n →o Fin n) (ht : ∀ i, i ≤ t i) : TranslationTrivial t ht (finiteKernel (𝟙 M)) := by
  apply (kernel_translationTrivial_iff _ _ _).mpr
  intro i x hx
  change x = 0 at hx
  simp [hx]

private noncomputable abbrev terminal := intervalModule (k := ℚ)
  (⟨0, 4, by decide, by decide⟩ : FiniteInterval 4)

/-- Every actual terminal source is covered, and the translated terminal endpoint stays four. -/
theorem terminal_coverage (i : BarcodeOccurrence 4 (rankBarcode terminal)) :
    (occurrence _ i).death = 4 ∧ (occurrence _ i).translatedDeath theta = 4 ∧
      ∃! j, epiEmbedding (𝟙 terminal) (fun _ => Function.surjective_id) j = i := by
  have he := single_occurrence (⟨0, 4, by decide, by decide⟩ : FiniteInterval 4) i
  refine ⟨congrArg FiniteInterval.death he, ?_, ?_⟩
  · rw [he]; rfl
  · apply epiEmbedding_covers_long_of_kernelTrivial theta theta_forward
      (𝟙 terminal) (fun _ => Function.surjective_id) (identity_kernel_short _ _ _) i
    rw [he]; decide

private noncomputable abbrev zeroModule : PModule.{0,0,0} ℚ (Fin 4) := barcodeModule (k := ℚ) 0
private noncomputable abbrev shortSource := intervalModule (k := ℚ) short
private noncomputable def eraseShort : shortSource ⟶ zeroModule := 0
private theorem eraseShort_surjective (i : Fin 4) : Function.Surjective (eraseShort.app i).hom := by
  intro x
  refine ⟨0, ?_⟩
  funext t
  have ht := t.isLt
  change t.val < (0 : Multiset (FiniteInterval 4)).toList.length at ht
  have hlen : (0 : Multiset (FiniteInterval 4)).toList.length = 0 := by simp
  omega
private theorem eraseShort_kernel_short :
    TranslationTrivial theta theta_forward (finiteKernel eraseShort) := by
  apply (kernel_translationTrivial_iff _ _ _).mpr
  intro i x _hx
  change intervalMap short (theta_forward i) x = 0
  apply Subtype.ext
  have hi : ¬ short.alive (theta i) := by
    fin_cases i <;> norm_num [short, theta, FiniteInterval.alive]
  simp [intervalMap, hi]

/-- Equality at the shortness threshold can leave a genuine source occurrence unmatched. -/
theorem threshold_unmatched (i : BarcodeOccurrence 4 (rankBarcode shortSource)) :
    TranslationTrivial theta theta_forward (finiteKernel eraseShort) ∧
      (occurrence _ i).death = (theta (occurrence _ i).birthStage).val ∧
      i ∉ Set.range (epiEmbedding eraseShort eraseShort_surjective) := by
  refine ⟨eraseShort_kernel_short, ?_, ?_⟩
  · rw [single_occurrence]; rfl
  · rintro ⟨j, _⟩
    have hlen : (rankBarcode zeroModule).toList.length = 0 := by
      change (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 4)))).toList.length = 0
      rw [rankBarcode_barcodeModule]; simp
    have hj := j.isLt
    omega

/-- A threshold-short source may also be matched, with the quantitative death bound still valid. -/
theorem short_matched_death_bound :
    ∃ i : BarcodeOccurrence 4 (rankBarcode shortSource),
      (occurrence _ i).death = (theta (occurrence _ i).birthStage).val ∧
      epiEmbedding (𝟙 shortSource) (fun _ => Function.surjective_id) i = i ∧
      (occurrence _ i).death ≤ (occurrence _ i).translatedDeath theta := by
  have hlen : (rankBarcode shortSource).toList.length = 1 := by rw [single_barcode]; simp
  let i : BarcodeOccurrence 4 (rankBarcode shortSource) := ⟨0, by omega⟩
  have hd := epiEmbedding_death_bounds_of_kernelTrivial theta theta_forward (𝟙 shortSource)
    (fun _ => Function.surjective_id) (identity_kernel_short _ _ _) i
  refine ⟨i, ?_, ?_, ?_⟩
  · rw [single_occurrence]; rfl
  · rw [epiEmbedding_id]; rfl
  · simpa only [epiEmbedding_id, Function.Embedding.refl_apply] using hd.2

private noncomputable abbrev duplicates : PModule.{0,0,0} ℚ (Fin 4) :=
  barcodeModule (k := ℚ) (Multiset.replicate 2 (⟨0, 4, by decide, by decide⟩ : FiniteInterval 4))

/-- Two duplicate long-source labels have distinct, unique canonical epi preimages. -/
theorem duplicate_long_coverage :
    ∃ i j : BarcodeOccurrence 4 (rankBarcode duplicates), i ≠ j ∧
      (∃! a, epiEmbedding (𝟙 duplicates) (fun _ => Function.surjective_id) a = i) ∧
      (∃! a, epiEmbedding (𝟙 duplicates) (fun _ => Function.surjective_id) a = j) := by
  have hlen : (rankBarcode duplicates).toList.length = 2 := by
    change (rankBarcode (barcodeModule (k := ℚ) (Multiset.replicate 2 _))).toList.length = 2
    rw [rankBarcode_barcodeModule]; simp
  let i : BarcodeOccurrence 4 (rankBarcode duplicates) := ⟨0, by omega⟩
  let j : BarcodeOccurrence 4 (rankBarcode duplicates) := ⟨1, by omega⟩
  have hlong (a : BarcodeOccurrence 4 (rankBarcode duplicates)) :
      (theta (occurrence _ a).birthStage).val < (occurrence (rankBarcode duplicates) a).death := by
    have hm := Multiset.mem_toList.mp (List.get_mem (rankBarcode duplicates).toList a)
    change occurrence (rankBarcode duplicates) a ∈ rankBarcode (barcodeModule (k := ℚ)
      (Multiset.replicate 2 (⟨0, 4, by decide, by decide⟩ : FiniteInterval 4))) at hm
    have hm' := Eq.mp (congrArg (fun B : Multiset (FiniteInterval 4) =>
      occurrence (rankBarcode duplicates) a ∈ B) (rankBarcode_barcodeModule (k := ℚ) _)) hm
    have ha := (Multiset.mem_replicate.mp hm').2
    rw [ha]; decide
  refine ⟨i, j, ?_, ?_, ?_⟩
  · intro h; have := congrArg Fin.val h; norm_num [i, j] at this
  · exact epiEmbedding_covers_long_of_kernelTrivial theta theta_forward (𝟙 duplicates)
      (fun _ => Function.surjective_id) (identity_kernel_short _ _ _) i (hlong i)
  · exact epiEmbedding_covers_long_of_kernelTrivial theta theta_forward (𝟙 duplicates)
      (fun _ => Function.surjective_id) (identity_kernel_short _ _ _) j (hlong j)

/-- Identity translation forces equal deaths and covers the complete actual source barcode. -/
theorem identity_translation (i : BarcodeOccurrence 4 (rankBarcode duplicates)) :
    (occurrence _ (epiEmbedding (𝟙 duplicates) (fun _ => Function.surjective_id) i)).death =
      (occurrence (rankBarcode duplicates) i).death ∧
      ∃! j, epiEmbedding (𝟙 duplicates) (fun _ => Function.surjective_id) j = i := by
  have hk := identity_kernel_short duplicates OrderHom.id (fun _ => le_rfl)
  have hd := epiEmbedding_death_bounds_of_kernelTrivial OrderHom.id (fun _ => le_rfl)
    (𝟙 duplicates) (fun _ => Function.surjective_id) hk i
  rw [FiniteInterval.translatedDeath_id] at hd
  exact ⟨Nat.le_antisymm hd.2 hd.1, epiEmbedding_covers_long_of_kernelTrivial
    OrderHom.id (fun _ => le_rfl) (𝟙 duplicates) (fun _ => Function.surjective_id) hk i
      (occurrence _ i).birth_lt_death⟩

private def fixedBar : FiniteInterval 4 := ⟨1, 2, by decide, by decide⟩
private noncomputable abbrev fixedSource := intervalModule (k := ℚ) fixedBar
private noncomputable def eraseFixed : fixedSource ⟶ zeroModule := 0

/-- A nonzero actual kernel at a fixed point rejects an incorrectly coarse shortness criterion. -/
theorem fixed_point_rejects_shortness :
    ¬ TranslationTrivial theta theta_forward (finiteKernel eraseFixed) := by
  intro hk
  have h := (kernel_translationTrivial_iff theta theta_forward eraseFixed).mp hk 1
  let x : fixedSource.obj (1 : Fin 4) := ⟨1, by
    simp [FiniteInterval.fiber, FiniteInterval.alive, fixedBar]⟩
  have hx : x ∈ LinearMap.ker (eraseFixed.app 1).hom := by
    change (0 : fixedSource.obj (1 : Fin 4) →ₗ[ℚ] zeroModule.obj 1) x = 0
    rfl
  have hz := h hx
  change structureMapLinear fixedSource (show (1 : Fin 4) ≤ 1 from le_rfl) x = 0 at hz
  rw [structureMapLinear_self] at hz
  have he := congrArg Subtype.val hz
  change (1 : ℚ) = 0 at he
  exact one_ne_zero he

private noncomputable abbrev empty : PModule.{0,0,0} ℚ (Fin 0) := barcodeModule (k := ℚ) 0

/-- The empty chain has a genuine short kernel and no source occurrence. -/
theorem empty_chain :
    TranslationTrivial OrderHom.id (fun _ : Fin 0 => le_rfl) (finiteKernel (𝟙 empty)) ∧
      IsEmpty (BarcodeOccurrence 0 (rankBarcode empty)) := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  change IsEmpty (Fin (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 0)))).toList.length)
  rw [rankBarcode_barcodeModule]
  simp only [Multiset.toList_zero, List.length_nil]
  infer_instance

private def sourceBar : FiniteInterval 4 := ⟨1, 3, by decide, by decide⟩
private def targetBar : FiniteInterval 4 := ⟨0, 2, by decide, by decide⟩

private noncomputable def overlapLinear (i : Fin 4) :
    sourceBar.fiber (k := ℚ) i →ₗ[ℚ] targetBar.fiber (k := ℚ) i := by
  classical
  exact if h : sourceBar.alive i ∧ targetBar.alive i then
    Submodule.inclusion (by simp [FiniteInterval.fiber, h.1, h.2])
  else 0

private noncomputable def overlap : intervalModule (k := ℚ) sourceBar ⟶ intervalModule targetBar where
  app i := ModuleCat.ofHom (overlapLinear i)
  naturality {i j} g := by
    have hle := leOfHom g
    fin_cases i <;> fin_cases j
    all_goals norm_num [Fin.le_iff_val_le_val] at hle
    all_goals
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change overlapLinear _ (intervalMap sourceBar (leOfHom g) x) =
        intervalMap targetBar (leOfHom g) (overlapLinear _ x)
      apply Subtype.ext
      norm_num [overlapLinear, intervalMap, sourceBar, targetBar, FiniteInterval.alive]

private theorem overlap_kernel_short : TranslationTrivial theta theta_forward (finiteKernel overlap) := by
  apply (kernel_translationTrivial_iff _ _ _).mpr
  intro i x hx
  change intervalMap sourceBar (theta_forward i) x = 0
  fin_cases i
  · simp [intervalMap, sourceBar, theta, FiniteInterval.alive]
    rfl
  · have h1 : Function.Injective (overlap.app (1 : Fin 4)).hom := by
      change Function.Injective (overlapLinear 1)
      have hactive : sourceBar.alive (1 : Fin 4) ∧ targetBar.alive (1 : Fin 4) := by
        norm_num [sourceBar, targetBar, FiniteInterval.alive]
      simp only [overlapLinear, dif_pos hactive]
      exact Submodule.inclusion_injective _
    have hxzero : x = 0 := h1 (by simpa using hx)
    rw [hxzero, map_zero]
  · simp [intervalMap, sourceBar, theta, FiniteInterval.alive]
    rfl
  · simp [intervalMap, sourceBar, theta, FiniteInterval.alive]
    rfl

private theorem overlap_cokernel_short : TranslationTrivial theta theta_forward (finiteCokernel overlap) := by
  apply (cokernel_translationTrivial_iff _ _ _).mpr
  intro i y _hy
  change y ∈ LinearMap.range (overlapLinear (theta i))
  by_cases ht : targetBar.alive (theta i)
  · have hs : sourceBar.alive (theta i) := by
      fin_cases i <;> simp_all [targetBar, sourceBar, theta, FiniteInterval.alive]
    refine ⟨⟨y.val, by simp [FiniteInterval.fiber, hs]⟩, ?_⟩
    apply Subtype.ext
    simp [overlapLinear, hs, ht]
  · have hy : y = 0 := zero_of_not_alive targetBar (theta i) ht y
    subst y
    exact ⟨0, map_zero _⟩

/-- The overlap map has a genuine kernel and cokernel, both short for this translation. -/
theorem proper_overlap_shortness :
    ¬ (∀ i, Function.Injective (overlap.app i).hom) ∧
      ¬ (∀ i, Function.Surjective (overlap.app i).hom) ∧
      TranslationTrivial theta theta_forward (finiteKernel overlap) ∧
      TranslationTrivial theta theta_forward (finiteCokernel overlap) := by
  refine ⟨?_, ?_, overlap_kernel_short, overlap_cokernel_short⟩
  · intro h
    let x : (intervalModule (k := ℚ) sourceBar).obj (2 : Fin 4) := ⟨1, by
      simp [FiniteInterval.fiber, FiniteInterval.alive, sourceBar]⟩
    have hz : (overlap.app 2).hom x = (overlap.app 2).hom 0 := by
      change overlapLinear 2 x = overlapLinear 2 0
      simp [overlapLinear, sourceBar, targetBar, FiniteInterval.alive]
      rfl
    have he := congrArg Subtype.val (h 2 hz)
    change (1 : ℚ) = 0 at he
    exact one_ne_zero he
  · intro h
    let y : (intervalModule (k := ℚ) targetBar).obj (0 : Fin 4) := ⟨1, by
      simp [FiniteInterval.fiber, FiniteInterval.alive, targetBar]⟩
    obtain ⟨x, hx⟩ := h 0 y
    have he := congrArg Subtype.val hx
    norm_num [overlap, overlapLinear, sourceBar, targetBar, FiniteInterval.alive, y] at he

/-- A genuine overlap map changes both endpoints and attains both quantitative upper bounds. -/
theorem overlap_two_sided_bounds :
    ∃ (i : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) sourceBar)))
      (j : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) targetBar))),
      inducedMap overlap i = some j ∧
      (occurrence _ i).birth = 1 ∧ (occurrence _ i).death = 3 ∧
      (occurrence _ j).birth = 0 ∧ (occurrence _ j).death = 2 ∧
      (occurrence _ i).birth ≤ (theta (occurrence _ j).birthStage).val ∧
      (occurrence _ i).death ≤ (occurrence _ j).translatedDeath theta ∧
      (theta (occurrence _ j).birthStage).val = 1 ∧
      (occurrence _ j).translatedDeath theta = 3 := by
  have hlen : (rankBarcode (intervalModule (k := ℚ) sourceBar)).toList.length = 1 := by
    rw [single_barcode]; simp
  let i : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) sourceBar)) := ⟨0, by omega⟩
  have hlong : (theta (occurrence _ i).birthStage).val < (occurrence _ i).death := by
    rw [single_occurrence]; decide
  obtain ⟨j, hj, _⟩ := inducedMap_covers_long_source_of_kernelTrivial
    theta theta_forward overlap overlap_kernel_short i hlong
  have hbounds := inducedMap_endpoint_bounds_of_shortness theta theta theta_forward theta_forward
    overlap overlap_kernel_short overlap_cokernel_short i j hj
  refine ⟨i, j, hj, congrArg FiniteInterval.birth (single_occurrence sourceBar i),
    congrArg FiniteInterval.death (single_occurrence sourceBar i),
    congrArg FiniteInterval.birth (single_occurrence targetBar j),
    congrArg FiniteInterval.death (single_occurrence targetBar j), hbounds.2.1,
    hbounds.2.2.2.2, ?_, ?_⟩
  · rw [single_occurrence]; rfl
  · rw [single_occurrence]; rfl

/-- Long-target coverage also reaches this same actual overlap matching, independently of kernel shortness. -/
theorem overlap_unique_source (j : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) targetBar))) :
    ∃! i, inducedMap overlap i = some j := by
  apply inducedMap_covers_long_target_of_cokernelTrivial theta theta_forward
    overlap overlap_cokernel_short j
  rw [single_occurrence]; decide

private def realGrid : Fin 4 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i : Fin 4 =>
      if i.val = 0 then (0 : ℝ) else if i.val = 1 then 1 else if i.val = 2 then 3 else 4)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem realGrid_apply (i : Fin 4) : realGrid i =
    if i.val = 0 then (0 : ℝ) else if i.val = 1 then 1 else if i.val = 2 then 3 else 4 := rfl

private theorem realGrid_theta : FiniteConstructible.sampleTranslation realGrid 1 = theta := by
  apply DFunLike.ext
  intro i
  apply Fin.succ_injective 4
  rw [FiniteConstructible.sampleTranslation_succ]
  apply (FiniteConstructible.cellIndex_eq_succ_iff realGrid (theta i) _).mpr
  constructor
  · fin_cases i <;> norm_num [realGrid_apply, theta]
  · intro j hj
    fin_cases i <;> fin_cases j <;> norm_num [theta, realGrid_apply, Fin.lt_def] at *

private theorem overlap_real_kernel :
    TranslationTrivial (FiniteConstructible.sampleTranslation realGrid 1)
      (FiniteConstructible.le_sampleTranslation realGrid 1) (finiteKernel overlap) := by
  simpa only [realGrid_theta] using overlap_kernel_short

private theorem overlap_real_cokernel :
    TranslationTrivial (FiniteConstructible.sampleTranslation realGrid 1)
      (FiniteConstructible.le_sampleTranslation realGrid 1) (finiteCokernel overlap) := by
  simpa only [realGrid_theta] using overlap_cokernel_short

private noncomputable def realOverlapMatching :=
  RealInduced.matching realGrid overlap 1 1 overlap_real_kernel overlap_real_cokernel

private theorem erase_real_kernel :
    TranslationTrivial (FiniteConstructible.sampleTranslation realGrid 1)
      (FiniteConstructible.le_sampleTranslation realGrid 1) (finiteKernel eraseShort) := by
  simpa only [realGrid_theta] using eraseShort_kernel_short

private theorem erase_real_cokernel :
    TranslationTrivial (FiniteConstructible.sampleTranslation realGrid 1)
      (FiniteConstructible.le_sampleTranslation realGrid 1) (finiteCokernel eraseShort) := by
  apply (cokernel_translationTrivial_iff _ _ _).mpr
  intro i
  rw [LinearMap.range_eq_top.mpr (eraseShort_surjective
    (FiniteConstructible.sampleTranslation realGrid 1 i))]
  exact le_top

/-- An actual erased real bar can be unmatched at threshold equality. -/
theorem real_threshold_unmatched :
    ∃ p, (RealInduced.matching realGrid eraseShort 1 1
      erase_real_kernel erase_real_cokernel).finite p = none ∧ p.1 = (0, 1) ∧
      p.1.2 - p.1.1 = 1 := by
  have hlen : (rankBarcode shortSource).toList.length = 1 := by
    rw [single_barcode]; simp
  let i : BarcodeOccurrence 4 (rankBarcode shortSource) := ⟨0, by omega⟩
  obtain ⟨p, _hp, hpv⟩ := RealBarcode.indexOccurrenceEquiv_finite realGrid _ i (by
    rw [single_occurrence]; decide)
  rw [single_occurrence] at hpv
  have hv : (p.1.1, (p.1.2 : WithTop ℝ)) = (0, (1 : WithTop ℝ)) :=
    hpv.trans (by rfl)
  have hv' : p.1 = (0, 1) := by
    apply Prod.ext
    · exact congrArg (fun z : ℝ × WithTop ℝ => z.1) hv
    · exact WithTop.coe_injective (congrArg (fun z : ℝ × WithTop ℝ => z.2) hv)
  have hempty : (RealInduced.diagram realGrid zeroModule).points = 0 := by
    change (ofIndexBars realGrid realGrid.strictMono
      (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 4))))).points = 0
    rw [rankBarcode_barcodeModule, RealBarcode.ofIndexBars_points, Multiset.map_zero]
  refine ⟨p, ?_, hv', by rw [hv']; norm_num⟩
  cases h : (RealInduced.matching realGrid eraseShort 1 1
      erase_real_kernel erase_real_cokernel).finite p with
  | none => rfl
  | some q =>
    have hq : q.1 ∈ finitePart (RealInduced.diagram realGrid zeroModule).points := Multiset.coe_mem
    have hm := Eq.mp (congrArg (fun s : Multiset (ℝ × WithTop ℝ) =>
      q.1 ∈ finitePart s) hempty) hq
    simp [finitePart] at hm

/-- The overlap control has nonzero actual categorical defects, not just changed endpoints. -/
theorem real_overlap_defects_nonzero :
    ¬ CategoryTheory.Limits.IsZero (finiteKernel overlap) ∧
      ¬ CategoryTheory.Limits.IsZero (finiteCokernel overlap) := by
  constructor
  · intro hz
    apply proper_overlap_shortness.1
    intro i
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    intro x hx
    have he := (finiteKernel_map_eq_zero_iff overlap (le_refl i)).mp
      ((hz.obj i).eq_zero_of_src (structureMap (finiteKernel overlap) (le_refl i))) hx
    simpa only [structureMapLinear_self, LinearMap.ker_id, Submodule.mem_bot] using he
  · intro hz
    apply proper_overlap_shortness.2.1
    intro i
    apply LinearMap.range_eq_top.mp
    apply top_unique
    have he := (finiteCokernel_map_eq_zero_iff overlap (le_refl i)).mp
      ((hz.obj i).eq_zero_of_src (structureMap (finiteCokernel overlap) (le_refl i)))
    simpa only [structureMapLinear_self, LinearMap.range_id] using he

/-- On the irregular grid `[0,1,3,4]`, the actual induced real matching attains
both displacement-one bounds. The larger interior gap adds no mesh error. -/
theorem real_overlap_bounds_attained :
    ∃ p q, realOverlapMatching.finite p = some q ∧ p.1 = (1, 4) ∧ q.1 = (0, 3) ∧
      RealEndpointBounds 1 1 (p.1.1, (p.1.2 : WithTop ℝ))
        (q.1.1, (q.1.2 : WithTop ℝ)) := by
  obtain ⟨i, j, hij, _⟩ := overlap_two_sided_bounds
  obtain ⟨p, hp, hpv⟩ := RealBarcode.indexOccurrenceEquiv_finite realGrid _ i (by
    rw [single_occurrence]; decide)
  obtain ⟨q, hq, hqv⟩ := RealBarcode.indexOccurrenceEquiv_finite realGrid _ j (by
    rw [single_occurrence]; decide)
  rw [single_occurrence] at hpv hqv
  have hpv' : (p.1.1, (p.1.2 : WithTop ℝ)) = (1, (4 : WithTop ℝ)) :=
    hpv.trans (by rfl)
  have hqv' : (q.1.1, (q.1.2 : WithTop ℝ)) = (0, (3 : WithTop ℝ)) :=
    hqv.trans (by rfl)
  have hpPair : p.1 = (1, 4) := by
    apply Prod.ext
    · exact congrArg (fun z : ℝ × WithTop ℝ => z.1) hpv'
    · exact WithTop.coe_injective (congrArg (fun z : ℝ × WithTop ℝ => z.2) hpv')
  have hqPair : q.1 = (0, 3) := by
    apply Prod.ext
    · exact congrArg (fun z : ℝ × WithTop ℝ => z.1) hqv'
    · exact WithTop.coe_injective (congrArg (fun z : ℝ × WithTop ℝ => z.2) hqv')
  have hm : RealInduced.sumMap realGrid overlap (.inl p) = some (.inl q) := by
    rw [← hp, ← hq]
    apply (RealInduced.sumMap_eq_some_iff realGrid overlap _ _).mpr
    simpa only [Equiv.symm_apply_apply] using hij
  have hm' := (RealInduced.matching_finite_eq_some_iff realGrid overlap 1 1
    overlap_real_kernel overlap_real_cokernel p q).mpr hm
  exact ⟨p, q, hm', hpPair, hqPair,
    (RealInduced.matching_bounds realGrid overlap 1 1 overlap_real_kernel overlap_real_cokernel).finite_bounds p q hm'⟩

end TDA.Persistence.FiniteInducedTranslationExamples
