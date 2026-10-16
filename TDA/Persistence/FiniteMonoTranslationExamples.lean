import TDA.Persistence.FiniteMonoTranslationMatching
import Mathlib.Data.Rat.Defs

/-! # Actual mono/cokernel translation consumers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TDA.Persistence.FiniteMonoTranslationExamples

open CategoryTheory FiniteBarcode

private def theta : Fin 4 →o Fin 4 where
  toFun i := if i.val < 2 then 1 else 3
  monotone' a b hab := by
    change a.val ≤ b.val at hab
    dsimp
    split_ifs <;> omega

private theorem theta_forward (i : Fin 4) : i ≤ theta i := by
  fin_cases i <;> decide

private theorem theta_positive (i : Fin 4) : 1 ≤ (theta i).val := by
  fin_cases i <;> decide

/-- This genuine translation advances stages and identifies two different stages. -/
theorem noninjective_translation : theta 0 = 1 ∧ theta 1 = 1 ∧
    ¬ Function.Injective theta := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have he := h (show theta 0 = theta 1 from rfl)
  have := congrArg Fin.val he
  norm_num at this

private theorem singleton_count (I : FiniteInterval 4) (p : FiniteInterval 4 → Prop)
    [DecidablePred p] : ({I} : Multiset (FiniteInterval 4)).countP p = if p I then 1 else 0 := by
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

private theorem single_occurrence (I : FiniteInterval 4)
    (a : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) I))) :
    occurrence (rankBarcode (intervalModule (k := ℚ) I)) a = I := by
  have hmem := Multiset.mem_toList.mp
    (List.get_mem (rankBarcode (intervalModule (k := ℚ) I)).toList a)
  change occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈
    rankBarcode (intervalModule (k := ℚ) I) at hmem
  have hm : occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈
      ({I} : Multiset (FiniteInterval 4)) :=
    Eq.mp (congrArg (fun B : Multiset (FiniteInterval 4) =>
      occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈ B) (single_barcode I)) hmem
  exact Multiset.mem_singleton.mp hm

private theorem fiber_le (I J : FiniteInterval 4) (hb : J.birth ≤ I.birth)
    (hd : I.death = J.death) (i : Fin 4) : I.fiber (k := ℚ) i ≤ J.fiber (k := ℚ) i := by
  classical
  change (if I.alive i then (⊤ : Submodule ℚ ℚ) else ⊥) ≤
    (if J.alive i then (⊤ : Submodule ℚ ℚ) else ⊥)
  by_cases hi : I.alive i
  · have hj : J.alive i := ⟨hb.trans hi.1, hi.2.trans_eq hd⟩
    rw [if_pos hi, if_pos hj]
  · rw [if_neg hi]
    exact bot_le

private noncomputable def inclusion (I J : FiniteInterval 4) (hb : J.birth ≤ I.birth)
    (hd : I.death = J.death) : intervalModule (k := ℚ) I ⟶ intervalModule J where
  app i := ModuleCat.ofHom (Submodule.inclusion (fiber_le I J hb hd i))
  naturality {i j} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases hi : I.alive i
    · have hJi : J.alive i := ⟨hb.trans hi.1, hi.2.trans_eq hd⟩
      by_cases hj : I.alive j
      · have hJj : J.alive j := ⟨hb.trans hj.1, hj.2.trans_eq hd⟩
        simp [intervalModule, intervalMap, hi, hj, hJi, hJj]
      · have hJj : ¬ J.alive j := by
          intro h
          apply hj
          exact ⟨hi.1.trans (leOfHom f), h.2.trans_eq hd.symm⟩
        simp [intervalModule, intervalMap, hi, hj, hJi, hJj]
    · have hx : x.val = 0 := by
        have h := x.property
        simpa [FiniteInterval.fiber, hi] using h
      change (Submodule.inclusion (fiber_le I J hb hd j)
        (intervalMap (k := ℚ) I (leOfHom f) x)).val =
        (intervalMap (k := ℚ) J (leOfHom f)
          (Submodule.inclusion (fiber_le I J hb hd i) x)).val
      simp only [intervalMap, hi, false_and, ↓reduceDIte]
      split_ifs <;> simp [hx]

private theorem inclusion_injective (I J : FiniteInterval 4) (hb : J.birth ≤ I.birth)
    (hd : I.death = J.death) (i : Fin 4) : Function.Injective ((inclusion I J hb hd).app i).hom :=
  Submodule.inclusion_injective (fiber_le I J hb hd i)


private theorem inclusion_surjective (I J : FiniteInterval 4) (hb : J.birth ≤ I.birth)
    (hd : I.death = J.death) (i : Fin 4) (hi : I.birth ≤ i.val) :
    Function.Surjective ((inclusion I J hb hd).app i).hom := by
  have halive : I.alive i ↔ J.alive i := by
    constructor
    · intro h
      exact ⟨hb.trans h.1, h.2.trans_eq hd⟩
    · intro h
      exact ⟨hi, h.2.trans_eq hd.symm⟩
  have he : I.fiber (k := ℚ) i = J.fiber (k := ℚ) i := by
    classical
    unfold FiniteInterval.fiber
    by_cases h : I.alive i
    · rw [if_pos h, if_pos (halive.mp h)]
    · rw [if_neg h, if_neg (fun hj => h (halive.mpr hj))]
  intro y
  exact ⟨⟨y.val, he.symm ▸ y.property⟩, Subtype.ext rfl⟩

private def late (d : ℕ) (hd : 1 < d) (hs : d ≤ 4) : FiniteInterval 4 := ⟨1, d, hd, hs⟩
private def early (d : ℕ) (hd : 1 < d) (hs : d ≤ 4) : FiniteInterval 4 := ⟨0, d, by omega, hs⟩
private noncomputable def delayed (d : ℕ) (hd : 1 < d) (hs : d ≤ 4) :=
  inclusion (late d hd hs) (early d hd hs) (by change (0 : ℕ) ≤ 1; decide) rfl
private theorem delayed_injective (d : ℕ) (hd : 1 < d) (hs : d ≤ 4) (i : Fin 4) :
    Function.Injective ((delayed d hd hs).app i).hom :=
  inclusion_injective _ _ _ _ i

private theorem delayed_short (d : ℕ) (hd : 1 < d) (hs : d ≤ 4) :
    TranslationTrivial theta theta_forward (finiteCokernel (delayed d hd hs)) := by
  apply (cokernel_translationTrivial_iff theta theta_forward _).mpr
  intro i
  have hsurj := inclusion_surjective (late d hd hs) (early d hd hs) (by change (0 : ℕ) ≤ 1; decide) rfl
    (theta i) (theta_positive i)
  change Function.Surjective ((delayed d hd hs).app (theta i)).hom at hsurj
  rw [LinearMap.range_eq_top.mpr hsurj]
  exact le_top

/-- A nonidentity inclusion attains the translated birth bound at a genuine finite death. -/
theorem finite_birth_bound_attained :
    ∃ i : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) (late 3 (by decide) (by decide)))),
      (occurrence _ i).birth = 1 ∧
      (occurrence _ (monoEmbedding (delayed 3 (by decide) (by decide))
        (delayed_injective 3 (by decide) (by decide)) i)).birth = 0 ∧
      (occurrence _ i).birth =
        (theta (occurrence _ (monoEmbedding (delayed 3 (by decide) (by decide))
          (delayed_injective 3 (by decide) (by decide)) i)).birthStage).val ∧
      deathPrefixCount (rankBarcode (intervalModule (k := ℚ) (early 3 (by decide) (by decide)))) 0 3 ≤
        deathPrefixCount (rankBarcode (intervalModule (k := ℚ) (late 3 (by decide) (by decide)))) 1 3 := by
  have hlen : (rankBarcode (intervalModule (k := ℚ) (late 3 (by decide) (by decide)))).toList.length = 1 := by
    rw [single_barcode]; simp
  let i : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) (late 3 (by decide) (by decide)))) :=
    ⟨0, by omega⟩
  refine ⟨i, ?_, ?_, ?_, ?_⟩
  · rw [single_occurrence]; rfl
  · rw [single_occurrence]; rfl
  · rw [single_occurrence, single_occurrence]; rfl
  · exact deathPrefixCount_le_translated_of_cokernelTrivial theta theta_forward
      (delayed 3 (by decide) (by decide)) (delayed_injective 3 (by decide) (by decide))
        (delayed_short 3 (by decide) (by decide)) 0 3 (by decide) (by decide)

/-- Terminal targets are long and have a unique actual preimage; no infinite life is inferred. -/
theorem terminal_coverage :
    ∀ a : BarcodeOccurrence 4 (rankBarcode (intervalModule (k := ℚ) (early 4 (by decide) (by decide)))),
      (occurrence _ a).death = 4 ∧
        ∃! i, monoEmbedding (delayed 4 (by decide) (by decide))
          (delayed_injective 4 (by decide) (by decide)) i = a := by
  intro a
  refine ⟨congrArg FiniteInterval.death (single_occurrence _ a), ?_⟩
  apply monoEmbedding_covers_long_of_cokernelTrivial theta theta_forward
    (delayed 4 (by decide) (by decide)) (delayed_injective 4 (by decide) (by decide))
      (delayed_short 4 (by decide) (by decide)) a
  rw [single_occurrence]
  decide

private noncomputable abbrev zeroModule : PModule.{0,0,0} ℚ (Fin 4) := barcodeModule (k := ℚ) 0
private def shortBar : FiniteInterval 4 := ⟨0, 1, by decide, by decide⟩
private noncomputable abbrev shortTarget := intervalModule (k := ℚ) shortBar
private noncomputable def shortInclusion : zeroModule ⟶ shortTarget := 0
private theorem short_injective (i : Fin 4) : Function.Injective (shortInclusion.app i).hom := by
  intro x y _
  have hlen : (0 : Multiset (FiniteInterval 4)).toList.length = 0 := by simp
  apply funext
  intro t
  have ht := t.isLt
  change t.val < (0 : Multiset (FiniteInterval 4)).toList.length at ht
  omega

private theorem short_cokernel :
    TranslationTrivial theta theta_forward (finiteCokernel shortInclusion) := by
  apply (cokernel_translationTrivial_iff theta theta_forward _).mpr
  intro i y _
  have hdead : ¬ shortBar.alive (theta i) := by
    have := theta_positive i
    simp only [FiniteInterval.alive, shortBar] at *
    omega
  have : Subsingleton (shortTarget.obj (theta i)) := by
    change Subsingleton (shortBar.fiber (k := ℚ) (theta i))
    simpa [FiniteInterval.fiber, hdead] using
      (inferInstance : Subsingleton (↥(⊥ : Submodule ℚ ℚ)))
  have hy : y = 0 := Subsingleton.elim _ _
  rw [hy]
  exact Submodule.zero_mem _

/-- At equality with the translated birth, a short target really can remain unmatched. -/
theorem threshold_unmatched :
    TranslationTrivial theta theta_forward (finiteCokernel shortInclusion) ∧
      ∀ a : BarcodeOccurrence 4 (rankBarcode shortTarget),
        (occurrence _ a).death = (theta (occurrence _ a).birthStage).val ∧
          a ∉ Set.range (monoEmbedding shortInclusion short_injective) := by
  refine ⟨short_cokernel, ?_⟩
  intro a
  constructor
  · change (occurrence (rankBarcode (intervalModule (k := ℚ) shortBar)) a).death = _
    rw [single_occurrence]; rfl
  · rintro ⟨i, _⟩
    have hlen : (rankBarcode zeroModule).toList.length = 0 := by
      change (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 4)))).toList.length = 0
      rw [rankBarcode_barcodeModule]; simp
    have := i.isLt
    omega

private theorem identity_short (K : PModule.{0,0,0} ℚ (Fin 4)) :
    TranslationTrivial theta theta_forward (finiteCokernel (𝟙 K)) := by
  apply (cokernel_translationTrivial_iff theta theta_forward _).mpr
  intro i
  change _ ≤ LinearMap.range (LinearMap.id : K.obj (theta i) →ₗ[ℚ] K.obj (theta i))
  rw [LinearMap.range_id]
  exact le_top

/-- A short target can also be matched; the birth bound still holds at the exact threshold. -/
theorem short_matched_birth_bound :
    ∃ a : BarcodeOccurrence 4 (rankBarcode shortTarget),
      (occurrence _ a).death = (theta (occurrence _ a).birthStage).val ∧
      (occurrence _ a).birth ≤ (theta (occurrence _ a).birthStage).val ∧
      monoEmbedding (𝟙 shortTarget) (fun _ => Function.injective_id) a = a := by
  have hlen : (rankBarcode shortTarget).toList.length = 1 := by
    rw [single_barcode]; simp
  let a : BarcodeOccurrence 4 (rankBarcode shortTarget) := ⟨0, by omega⟩
  have hb := monoEmbedding_birth_bounds_of_cokernelTrivial theta theta_forward
    (𝟙 shortTarget) (fun _ => Function.injective_id) (identity_short shortTarget) a
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [single_occurrence]; rfl
  · simpa only [monoEmbedding_id, Function.Embedding.refl_apply] using hb.2
  · rw [monoEmbedding_id]; rfl

private noncomputable abbrev duplicates : PModule.{0,0,0} ℚ (Fin 4) :=
  barcodeModule (k := ℚ) (Multiset.replicate 2 (early 4 (by decide) (by decide)))

/-- Repeated long bars retain distinct target labels and unique preimages. -/
theorem duplicate_long_coverage :
    ∃ a b : BarcodeOccurrence 4 (rankBarcode duplicates), a ≠ b ∧
      (∃! i, monoEmbedding (𝟙 duplicates) (fun _ => Function.injective_id) i = a) ∧
      (∃! i, monoEmbedding (𝟙 duplicates) (fun _ => Function.injective_id) i = b) := by
  have hlen : (rankBarcode duplicates).toList.length = 2 := by
    change (rankBarcode (barcodeModule (k := ℚ) (Multiset.replicate 2 _))).toList.length = 2
    rw [rankBarcode_barcodeModule]; simp
  let a : BarcodeOccurrence 4 (rankBarcode duplicates) := ⟨0, by omega⟩
  let b : BarcodeOccurrence 4 (rankBarcode duplicates) := ⟨1, by omega⟩
  have hlong (x : BarcodeOccurrence 4 (rankBarcode duplicates)) :
      (theta (occurrence (rankBarcode duplicates) x).birthStage).val <
        (occurrence (rankBarcode duplicates) x).death := by
    have hm := Multiset.mem_toList.mp (List.get_mem (rankBarcode duplicates).toList x)
    change occurrence (rankBarcode duplicates) x ∈ rankBarcode (barcodeModule (k := ℚ)
      (Multiset.replicate 2 (early 4 (by decide) (by decide)))) at hm
    have hm' : occurrence (rankBarcode duplicates) x ∈
        Multiset.replicate 2 (early 4 (by decide) (by decide)) :=
      Eq.mp (congrArg (fun B : Multiset (FiniteInterval 4) =>
        occurrence (rankBarcode duplicates) x ∈ B)
          (rankBarcode_barcodeModule (k := ℚ) _)) hm
    have hx := (Multiset.mem_replicate.mp hm').2
    rw [hx]
    decide
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    norm_num [a, b] at this
  · exact monoEmbedding_covers_long_of_cokernelTrivial theta theta_forward
      (𝟙 duplicates) (fun _ => Function.injective_id) (identity_short duplicates) a (hlong a)
  · exact monoEmbedding_covers_long_of_cokernelTrivial theta theta_forward
      (𝟙 duplicates) (fun _ => Function.injective_id) (identity_short duplicates) b (hlong b)

/-- With the identity translation the zero cokernel gives equal births and full coverage. -/
theorem identity_translation :
    ∀ a : BarcodeOccurrence 4 (rankBarcode duplicates),
      (occurrence _ (monoEmbedding (𝟙 duplicates) (fun _ => Function.injective_id) a)).birth =
        (occurrence _ a).birth ∧
      ∃! i, monoEmbedding (𝟙 duplicates) (fun _ => Function.injective_id) i = a := by
  intro a
  have hc : TranslationTrivial OrderHom.id (fun i : Fin 4 => le_rfl)
      (finiteCokernel (𝟙 duplicates)) := by
    apply (cokernel_translationTrivial_iff _ _ _).mpr
    intro i
    change _ ≤ LinearMap.range (LinearMap.id : duplicates.obj i →ₗ[ℚ] duplicates.obj i)
    rw [LinearMap.range_id]
    exact le_top
  have hb := monoEmbedding_birth_bounds_of_cokernelTrivial OrderHom.id
    (fun i : Fin 4 => le_rfl) (𝟙 duplicates) (fun _ => Function.injective_id) hc a
  refine ⟨Nat.le_antisymm hb.1 hb.2, ?_⟩
  exact monoEmbedding_covers_long_of_cokernelTrivial OrderHom.id
    (fun i : Fin 4 => le_rfl) (𝟙 duplicates) (fun _ => Function.injective_id) hc a
      (occurrence _ a).birth_lt_death

private def fixedBar : FiniteInterval 4 := ⟨1, 2, by decide, by decide⟩
private noncomputable abbrev fixedTarget := intervalModule (k := ℚ) fixedBar
private noncomputable def fixedInclusion : zeroModule ⟶ fixedTarget := 0

/-- A nonzero quotient at a fixed point is not translation-trivial.
This detects the false coarse-grid criterion based only on far-apart sample pairs. -/
theorem fixed_point_rejects_shortness :
    ¬ TranslationTrivial theta theta_forward (finiteCokernel fixedInclusion) := by
  intro hc
  have himg := (cokernel_translationTrivial_iff theta theta_forward fixedInclusion).mp hc 1
  let v : fixedTarget.obj (1 : Fin 4) := ⟨1, by
    simp [FiniteInterval.fiber, FiniteInterval.alive, fixedBar]⟩
  have hv : v ∈ LinearMap.range (structureMapLinear fixedTarget (theta_forward 1)) := by
    refine ⟨v, ?_⟩
    change structureMapLinear fixedTarget (show (1 : Fin 4) ≤ 1 from le_rfl) v = v
    rw [structureMapLinear_self]
    rfl
  have hz := himg hv
  change v ∈ LinearMap.range (0 : zeroModule.obj (1 : Fin 4) →ₗ[ℚ] fixedTarget.obj 1) at hz
  rw [LinearMap.range_zero] at hz
  have he : v = 0 := hz
  have := congrArg Subtype.val he
  norm_num [v] at this

private noncomputable abbrev empty : PModule.{0,0,0} ℚ (Fin 0) := barcodeModule (k := ℚ) 0

/-- The empty chain has an actual short cokernel and empty occurrence domain. -/
theorem empty_chain :
    TranslationTrivial OrderHom.id (fun _ : Fin 0 => le_rfl) (finiteCokernel (𝟙 empty)) ∧
      IsEmpty (BarcodeOccurrence 0 (rankBarcode empty)) := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  change IsEmpty (Fin (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 0)))).toList.length)
  rw [rankBarcode_barcodeModule]
  simp only [Multiset.toList_zero, List.length_nil]
  infer_instance

end TDA.Persistence.FiniteMonoTranslationExamples
