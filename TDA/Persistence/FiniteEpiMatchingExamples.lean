import TDA.Persistence.FiniteEpiMatching
import Mathlib.Data.Rat.Defs

/-! # epimorphisms and canonical barcode embedding consumers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TDA.Persistence.FiniteEpiMatchingExamples

open CategoryTheory FiniteBarcode

private def long : FiniteInterval 3 := ⟨0, 3, by decide, by decide⟩
private def middle : FiniteInterval 3 := ⟨0, 2, by decide, by decide⟩
private def short : FiniteInterval 3 := ⟨0, 1, by decide, by decide⟩
private def laterLong : FiniteInterval 3 := ⟨1, 3, by decide, by decide⟩
private def laterShort : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩

private theorem singleton_count {n : ℕ} (I : FiniteInterval n) (p : FiniteInterval n → Prop)
    [DecidablePred p] : ({I} : Multiset (FiniteInterval n)).countP p = if p I then 1 else 0 := by
  rw [← Multiset.cons_zero, Multiset.countP_cons]
  simp

private theorem single_barcode (I : FiniteInterval 3) :
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

private theorem alive_of_target (I J : FiniteInterval 3) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death) (i : Fin 3) (hi : J.alive i) : I.alive i :=
  ⟨hb ▸ hi.1, hi.2.trans_le hd⟩

private noncomputable def truncateLinear (I J : FiniteInterval 3) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death) (i : Fin 3) : I.fiber (k := ℚ) i →ₗ[ℚ] J.fiber (k := ℚ) i := by
  classical
  exact if h : J.alive i then
    Submodule.inclusion (by simp [FiniteInterval.fiber, h, alive_of_target I J hb hd i h])
  else 0

private theorem zero_of_not_alive (I : FiniteInterval 3) (i : Fin 3)
    (hi : ¬ I.alive i) (x : I.fiber (k := ℚ) i) : x = 0 := by
  apply Subtype.ext
  have h := x.property
  simpa [FiniteInterval.fiber, hi] using h

private noncomputable def truncate (I J : FiniteInterval 3) (hb : I.birth = J.birth)
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

private theorem truncate_surjective (I J : FiniteInterval 3) (hb : I.birth = J.birth)
    (hd : J.death ≤ I.death) (i : Fin 3) : Function.Surjective ((truncate I J hb hd).app i).hom := by
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
private noncomputable def second := truncate middle short rfl (by decide)
private theorem first_surjective (i : Fin 3) : Function.Surjective (first.app i).hom :=
  truncate_surjective long middle rfl (by decide) i
private theorem second_surjective (i : Fin 3) : Function.Surjective (second.app i).hom :=
  truncate_surjective middle short rfl (by decide) i

private theorem single_occurrence (I : FiniteInterval 3)
    (a : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) I))) :
    occurrence (rankBarcode (intervalModule (k := ℚ) I)) a = I := by
  have hmem := Multiset.mem_toList.mp (List.get_mem (rankBarcode (intervalModule (k := ℚ) I)).toList a)
  change occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈ _ at hmem
  have hmem' : occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈
      ({I} : Multiset (FiniteInterval 3)) := Eq.mp
    (congrArg (fun B : Multiset (FiniteInterval 3) =>
      occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈ B) (single_barcode I)) hmem
  simpa using hmem'

/-- Truncation at a finite death embeds the target bar back into its longer source bar. -/
theorem unequal_death_embedding :
    ∃ i : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) middle)),
      (occurrence _ i).death = 2 ∧
      (occurrence _ (epiEmbedding first first_surjective i)).death = 3 ∧
      (occurrence _ (epiEmbedding first first_surjective i)).birth = 0 := by
  have hlen : (rankBarcode (intervalModule (k := ℚ) middle)).toList.length = 1 := by
    rw [single_barcode]; simp
  let i : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) middle)) := ⟨0, by omega⟩
  exact ⟨i, congrArg FiniteInterval.death (single_occurrence middle i),
    congrArg FiniteInterval.death (single_occurrence long _),
    congrArg FiniteInterval.birth (single_occurrence long _)⟩

/-- Nonidentity epimorphisms through three distinct deaths compose in the reverse order. -/
theorem three_death_composition :
    epiEmbedding (first ≫ second) (fun i => (second_surjective i).comp (first_surjective i)) =
      (epiEmbedding second second_surjective).trans (epiEmbedding first first_surjective) :=
  epiEmbedding_comp first second first_surjective second_surjective

/-- A positive birth exercises the predecessor-image quotient and its surjection. -/
theorem positive_birth_quotient :
    birthSuffixCount (rankBarcode (intervalModule (k := ℚ) laterShort)) 1 1 = 1 ∧
    birthSuffixCount (rankBarcode (intervalModule (k := ℚ) laterShort)) 1 1 =
      Module.finrank ℚ ((LinearMap.range (structureMapLinear (intervalModule (k := ℚ) laterShort)
        (show (1 : Fin 3) ≤ 1 from le_refl _))) ⧸
          birthPreviousImage (intervalModule (k := ℚ) laterShort) 1 1
            (Nat.zero_lt_succ 0) (le_refl 1) (Nat.lt_succ_of_le (Nat.le_succ 1))) ∧
    birthSuffixCount (rankBarcode (intervalModule (k := ℚ) laterShort)) 1 1 ≤
      birthSuffixCount (rankBarcode (intervalModule (k := ℚ) laterLong)) 1 1 := by
  refine ⟨?_, birthSuffixCount_eq_finrank _ _ _ (by decide) (by decide) (by decide),
    birthSuffixCount_le_of_surjective (truncate laterLong laterShort rfl (by decide))
      (truncate_surjective laterLong laterShort rfl (by decide)) _ _ (by decide) (by decide)⟩
  simp [single_barcode, birthSuffixCount, singleton_count, laterShort]

private def oneBar : FiniteInterval 1 := ⟨0, 1, by decide, by decide⟩
private noncomputable def copies (n : ℕ) : PModule.{0,0,0} ℚ (Fin 1) :=
  (Functor.const (Fin 1)).obj (ModuleCat.of ℚ (Fin n → ℚ))
private instance copies_fd (n : ℕ) (i : Fin 1) : FiniteDimensional ℚ ((copies n).obj i) := by
  change FiniteDimensional ℚ (Fin n → ℚ)
  infer_instance

private theorem replicate_count (n : ℕ) (p : FiniteInterval 1 → Prop) [DecidablePred p] :
    (Multiset.replicate n oneBar).countP p = if p oneBar then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.countP_cons, ih]
    split_ifs <;> omega

private theorem copies_barcode (n : ℕ) : rankBarcode (copies n) = Multiset.replicate n oneBar := by
  calc
    _ = rankBarcode (barcodeModule (k := ℚ) (Multiset.replicate n oneBar)) := by
      apply (rankBarcode_eq_iff _ _).mpr
      intro i j hij
      rw [rank_barcodeMap]
      change Module.finrank ℚ (LinearMap.range
        (LinearMap.id : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ))) =
          (Multiset.replicate n oneBar).countP (fun I => I.birth ≤ i.val ∧ j.val < I.death)
      rw [LinearMap.range_id, replicate_count]
      simp [oneBar]

    _ = _ := rankBarcode_barcodeModule _

private noncomputable def dropLast : copies 3 ⟶ copies 2 where
  app _ := ModuleCat.ofHom {
    toFun := fun x a => x ⟨a.val, by have := a.isLt; omega⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  naturality {i j} f := by simp [copies]

private theorem dropLast_surjective (i : Fin 1) : Function.Surjective (dropLast.app i).hom := by
  intro y
  refine ⟨fun a => if h : a.val < 2 then y ⟨a.val, h⟩ else 0, ?_⟩
  funext a
  change (if h : a.val < 2 then y ⟨a.val, h⟩ else 0) = y a
  rw [dif_pos a.isLt]

/-- A genuine dimension-dropping epi retains two distinct repeated-bar occurrence labels. -/
theorem duplicate_occurrences_distinct :
    ∃ i j : BarcodeOccurrence 1 (rankBarcode (copies 2)),
      i ≠ j ∧ epiEmbedding dropLast dropLast_surjective i ≠
        epiEmbedding dropLast dropLast_surjective j := by
  have hlen : (rankBarcode (copies 2)).toList.length = 2 := by
    rw [copies_barcode]; simp
  let i : BarcodeOccurrence 1 (rankBarcode (copies 2)) := ⟨0, by omega⟩
  let j : BarcodeOccurrence 1 (rankBarcode (copies 2)) := ⟨1, by omega⟩
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  exact ⟨i, j, hne, fun h => hne ((epiEmbedding _ _).injective h)⟩

/-- The initial-stage image includes terminal repeated bars, whose embedded deaths remain terminal. -/
theorem duplicate_terminal_count : birthSuffixCount (rankBarcode (copies 2)) 0 0 = 2 ∧
    birthSuffixCount (rankBarcode (copies 2)) 0 0 = structureMapRank (copies 2) 0 0 (le_refl _) ∧
    ∀ i : BarcodeOccurrence 1 (rankBarcode (copies 2)),
      (occurrence _ (epiEmbedding dropLast dropLast_surjective i)).death = 1 := by
  refine ⟨?_, birthSuffixCount_zero _ _ (by decide), ?_⟩
  · rw [copies_barcode]
    unfold birthSuffixCount
    rw [replicate_count]
    norm_num [oneBar]
  · intro i
    apply epiEmbedding_terminal
    have := (occurrence (rankBarcode (copies 2)) i).birth_lt_death
    have := (occurrence (rankBarcode (copies 2)) i).death_le_size
    omega

private noncomputable def empty : PModule.{0,0,0} ℚ (Fin 0) := barcodeModule (k := ℚ) 0
private instance empty_fd (i : Fin 0) : FiniteDimensional ℚ (empty.obj i) := i.elim0

/-- The empty-chain embedding and identity law select no stage. -/
theorem empty_chain : IsEmpty (BarcodeOccurrence 0 (rankBarcode empty)) ∧
    epiEmbedding (𝟙 empty) (fun _ => Function.surjective_id) = Function.Embedding.refl _ := by
  refine ⟨?_, epiEmbedding_id empty⟩
  change IsEmpty (Fin (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 0)))).toList.length)
  rw [rankBarcode_barcodeModule]
  simp only [Multiset.toList_zero, List.length_nil]
  exact inferInstance

/-- Structure-map rank domination alone cannot supply a birth-preserving embedding. -/
theorem rank_domination_insufficient :
    (∀ (i j : Fin 3) (h : i ≤ j),
      structureMapRank (barcodeModule (k := ℚ) {laterShort}) i j h ≤
        structureMapRank (barcodeModule (k := ℚ) {long}) i j h) ∧
    ¬ ∃ e : BarcodeOccurrence 3 ({laterShort} : Multiset (FiniteInterval 3)) ↪
        BarcodeOccurrence 3 ({long} : Multiset (FiniteInterval 3)),
      ∀ i, (occurrence {long} (e i)).birth = (occurrence {laterShort} i).birth := by
  constructor
  · intro i j h
    rw [rank_barcodeMap, rank_barcodeMap]
    rw [singleton_count, singleton_count]
    have hi := i.isLt
    have hj := j.isLt
    simp [long, laterShort]
    split_ifs <;> omega
  · rintro ⟨e, he⟩
    have h := he ⟨0, by simp⟩
    simp [occurrence, long, laterShort] at h

end TDA.Persistence.FiniteEpiMatchingExamples
