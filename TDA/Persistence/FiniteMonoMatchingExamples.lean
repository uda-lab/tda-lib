import TDA.Persistence.FiniteMonoMatching
import Mathlib.Data.Rat.Defs

/-! # Canonical mono embedding consumers and the rank-domination boundary -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TDA.Persistence.FiniteMonoMatchingExamples

open CategoryTheory FiniteBarcode

private def late : FiniteInterval 3 := ⟨2, 3, by decide, by decide⟩
private def middle : FiniteInterval 3 := ⟨1, 3, by decide, by decide⟩
private def early : FiniteInterval 3 := ⟨0, 3, by decide, by decide⟩
private def short : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩

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

private theorem fiber_le (I J : FiniteInterval 3) (hb : J.birth ≤ I.birth)
    (hd : I.death = J.death) (i : Fin 3) : I.fiber (k := ℚ) i ≤ J.fiber (k := ℚ) i := by
  classical
  change (if I.alive i then (⊤ : Submodule ℚ ℚ) else ⊥) ≤
    (if J.alive i then (⊤ : Submodule ℚ ℚ) else ⊥)
  by_cases hi : I.alive i
  · have hj : J.alive i := ⟨hb.trans hi.1, hi.2.trans_eq hd⟩
    rw [if_pos hi, if_pos hj]
  · rw [if_neg hi]
    exact bot_le

private noncomputable def inclusion (I J : FiniteInterval 3) (hb : J.birth ≤ I.birth)
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

private theorem inclusion_injective (I J : FiniteInterval 3) (hb : J.birth ≤ I.birth)
    (hd : I.death = J.death) (i : Fin 3) : Function.Injective ((inclusion I J hb hd).app i).hom :=
  Submodule.inclusion_injective (fiber_le I J hb hd i)

private noncomputable def first := inclusion late middle (by decide) rfl
private noncomputable def second := inclusion middle early (by decide) rfl
private theorem first_injective (i : Fin 3) : Function.Injective (first.app i).hom :=
  inclusion_injective late middle (by decide) rfl i
private theorem second_injective (i : Fin 3) : Function.Injective (second.app i).hom :=
  inclusion_injective middle early (by decide) rfl i

/-- A genuine later-born submodule embeds into an earlier-born interval with the same death. -/
theorem unequal_birth_embedding :
    ∃ i : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) late)),
      (occurrence _ i).birth = 2 ∧
      (occurrence _ (monoEmbedding first first_injective i)).birth = 1 ∧
      (occurrence _ (monoEmbedding first first_injective i)).death = 3 := by
  have hsource : (rankBarcode (intervalModule (k := ℚ) late)).toList.length = 1 := by
    rw [single_barcode]; simp
  let i : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) late)) := ⟨0, by omega⟩
  have hget (I : FiniteInterval 3) (a : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) I))) :
      occurrence (rankBarcode (intervalModule (k := ℚ) I)) a = I := by
    have hmem := List.get_mem (rankBarcode (intervalModule (k := ℚ) I)).toList a
    have hmem' : occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈
        rankBarcode (intervalModule (k := ℚ) I) := Multiset.mem_toList.mp hmem
    have : occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈ ({I} : Multiset (FiniteInterval 3)) := by
      exact Eq.mp (congrArg (fun B : Multiset (FiniteInterval 3) =>
        occurrence (rankBarcode (intervalModule (k := ℚ) I)) a ∈ B) (single_barcode I)) hmem'
    simpa using this
  exact ⟨i, congrArg FiniteInterval.birth (hget late i),
    congrArg FiniteInterval.birth (hget middle _), congrArg FiniteInterval.death (hget middle _)⟩

/-- Nonidentity inclusions through three distinct birth times satisfy the composition law. -/
theorem three_birth_composition :
    monoEmbedding (first ≫ second) (fun i => (second_injective i).comp (first_injective i)) =
      (monoEmbedding first first_injective).trans (monoEmbedding second second_injective) :=
  monoEmbedding_comp first second first_injective second_injective

/-- An observed finite death uses the image/kernel branch rather than the terminal image. -/
theorem finite_death_count :
    deathPrefixCount (rankBarcode (intervalModule (k := ℚ) short)) 1 2 = 1 ∧
      deathPrefixCount (rankBarcode (intervalModule (k := ℚ) short)) 1 2 =
        Module.finrank ℚ (deathSubspace (intervalModule (k := ℚ) short) 1 2 (by decide) (by decide)) := by
  refine ⟨?_, deathPrefixCount_eq_finrank _ _ _ (by decide) (by decide)⟩
  simp [single_barcode, deathPrefixCount, singleton_count, short]

private def oneBar : FiniteInterval 1 := ⟨0, 1, by decide, by decide⟩
private noncomputable def duplicates : PModule.{0,0,0} ℚ (Fin 1) :=
  barcodeModule (k := ℚ) (Multiset.replicate 2 oneBar)
private instance duplicates_fd (i : Fin 1) : FiniteDimensional ℚ (duplicates.obj i) := by
  change FiniteDimensional ℚ ((barcodeModule (k := ℚ) (Multiset.replicate 2 oneBar)).obj i)
  infer_instance

/-- Equal interval values retain two distinct occurrence labels after the canonical embedding. -/
theorem duplicate_occurrences_distinct :
    ∃ i j : BarcodeOccurrence 1 (rankBarcode duplicates),
      i ≠ j ∧ monoEmbedding (𝟙 duplicates) (fun _ => Function.injective_id) i ≠
        monoEmbedding (𝟙 duplicates) (fun _ => Function.injective_id) j := by
  have hlen : (rankBarcode duplicates).toList.length = 2 := by
    change (rankBarcode (barcodeModule (k := ℚ) (Multiset.replicate 2 oneBar))).toList.length = 2
    rw [rankBarcode_barcodeModule]
    simp
  let i : BarcodeOccurrence 1 (rankBarcode duplicates) := ⟨0, by omega⟩
  let j : BarcodeOccurrence 1 (rankBarcode duplicates) := ⟨1, by omega⟩
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  exact ⟨i, j, hne, fun h => hne ((monoEmbedding _ _).injective h)⟩

/-- The one-stage duplicate example also exercises the terminal image count. -/
theorem duplicate_terminal_count : deathPrefixCount (rankBarcode duplicates) 0 1 = 2 := by
  change deathPrefixCount (rankBarcode (barcodeModule (k := ℚ) (Multiset.replicate 2 oneBar))) 0 1 = 2
  rw [rankBarcode_barcodeModule]
  unfold deathPrefixCount
  rw [Multiset.replicate_succ, Multiset.replicate_one, Multiset.countP_cons, singleton_count]
  norm_num [oneBar]

private noncomputable def empty : PModule.{0,0,0} ℚ (Fin 0) := barcodeModule (k := ℚ) 0
private instance empty_fd (i : Fin 0) : FiniteDimensional ℚ (empty.obj i) := i.elim0

/-- The empty chain has an actual empty occurrence embedding, without selecting a predecessor. -/
theorem empty_chain : IsEmpty (BarcodeOccurrence 0 (rankBarcode empty)) ∧
    monoEmbedding (𝟙 empty) (fun _ => Function.injective_id) = Function.Embedding.refl _ := by
  refine ⟨?_, monoEmbedding_id empty⟩
  change IsEmpty (Fin (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 0)))).toList.length)
  rw [rankBarcode_barcodeModule]
  simp only [Multiset.toList_zero, List.length_nil]
  exact inferInstance

/-- Rank domination alone does not give a death-preserving occurrence embedding. -/
theorem rank_domination_insufficient :
    (∀ (i j : Fin 3) (h : i ≤ j),
      structureMapRank (barcodeModule (k := ℚ) {short}) i j h ≤
        structureMapRank (barcodeModule (k := ℚ) {early}) i j h) ∧
    ¬ ∃ e : BarcodeOccurrence 3 ({short} : Multiset (FiniteInterval 3)) ↪
        BarcodeOccurrence 3 ({early} : Multiset (FiniteInterval 3)),
      ∀ i, (occurrence {early} (e i)).death = (occurrence {short} i).death := by
  constructor
  · intro i j h
    rw [rank_barcodeMap, rank_barcodeMap]
    rw [singleton_count, singleton_count]
    have hi := i.isLt
    have hj := j.isLt
    simp [early, short]
    split_ifs <;> omega
  · rintro ⟨e, he⟩
    have h := he ⟨0, by simp⟩
    simp [occurrence, early, short] at h

end TDA.Persistence.FiniteMonoMatchingExamples
