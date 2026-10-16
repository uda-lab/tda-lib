import TDA.Persistence.FiniteInducedSpecialization
import Mathlib.Data.Rat.Defs

/-! # Actual image-induced matching consumers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace TDA.Persistence.FiniteInducedMatchingExamples

open CategoryTheory FiniteBarcode

private def oneBar : FiniteInterval 1 := ⟨0, 1, by decide, by decide⟩

private theorem replicate_count (n : ℕ) (p : FiniteInterval 1 → Prop) [DecidablePred p] :
    (Multiset.replicate n oneBar).countP p = if p oneBar then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.countP_cons, ih]
    split_ifs <;> omega

private theorem one_stage_barcode (M : PModule.{0,0,0} ℚ (Fin 1))
    [∀ i, FiniteDimensional ℚ (M.obj i)] :
    rankBarcode M = Multiset.replicate (Module.finrank ℚ (M.obj 0)) oneBar := by
  calc
    _ = rankBarcode (barcodeModule (k := ℚ)
        (Multiset.replicate (Module.finrank ℚ (M.obj 0)) oneBar)) := by
      apply (rankBarcode_eq_iff _ _).mpr
      intro i j hij
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i; subst j
      rw [rank_barcodeMap]
      unfold structureMapRank
      rw [structureMapLinear_self, LinearMap.range_id, replicate_count]
      simp [oneBar]
    _ = _ := rankBarcode_barcodeModule _

private noncomputable def two : PModule.{0,0,0} ℚ (Fin 1) :=
  (Functor.const (Fin 1)).obj (ModuleCat.of ℚ (ℚ × ℚ))
private instance two_fd (i : Fin 1) : FiniteDimensional ℚ (two.obj i) := by
  change FiniteDimensional ℚ (ℚ × ℚ)
  infer_instance

private def projectionLinear : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) :=
  (LinearMap.fst ℚ ℚ ℚ).prod 0

private noncomputable def projection : two ⟶ two where
  app _ := ModuleCat.ofHom projectionLinear
  naturality {_i _j} _f := by simp [two]

private noncomputable def projectionRangeEquiv : LinearMap.range projectionLinear ≃ₗ[ℚ] ℚ where
  toFun x := x.val.1
  invFun t := ⟨(t, 0), (t, 0), rfl⟩
  left_inv := by rintro ⟨_, a, rfl⟩; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem projection_dim : Module.finrank ℚ ((finiteImage projection).obj 0) = 1 := by
  change Module.finrank ℚ (LinearMap.range projectionLinear) = 1
  simpa using projectionRangeEquiv.finrank_eq

private theorem projection_barcode : rankBarcode (finiteImage projection) = {oneBar} := by
  rw [one_stage_barcode, projection_dim]
  simp

private theorem two_barcode : rankBarcode two = Multiset.replicate 2 oneBar := by
  rw [one_stage_barcode]
  simp [two]

/-- The rank-one endomorphism is genuinely neither componentwise injective nor surjective. -/
theorem proper_linear_map :
    ¬ (∀ i, Function.Injective (projection.app i).hom) ∧
      ¬ (∀ i, Function.Surjective (projection.app i).hom) := by
  constructor
  · intro h
    have he := h 0 (show (projection.app 0).hom (0, 0) = (projection.app 0).hom (0, 1) from rfl)
    have := congrArg Prod.snd he
    norm_num at this
  · intro h
    obtain ⟨x, hx⟩ := h 0 (0, 1)
    have := congrArg Prod.snd hx
    change (0 : ℚ) = 1 at this
    norm_num at this

/-- Two repeated source and target bars produce exactly one actual matched pair. -/
theorem rank_one_partial_matching :
    Fintype.card (BarcodeOccurrence 1 (rankBarcode two)) = 2 ∧
    Fintype.card {p : BarcodeOccurrence 1 (rankBarcode two) × BarcodeOccurrence 1 (rankBarcode two) //
      inducedMap projection p.1 = some p.2} = 1 := by
  classical
  constructor
  · simp [BarcodeOccurrence, two_barcode]
  · rw [← Fintype.card_congr (imageOccurrenceEquivPairs projection)]
    simp [BarcodeOccurrence, projection_barcode]

/-- Duplicate labels stay distinct under the actual identity induced matching. -/
theorem duplicate_identity :
    ∃ i j : BarcodeOccurrence 1 (rankBarcode two), i ≠ j ∧
      inducedMap (𝟙 two) i = some i ∧ inducedMap (𝟙 two) j = some j := by
  have hlen : (rankBarcode two).toList.length = 2 := by rw [two_barcode]; simp
  let i : BarcodeOccurrence 1 (rankBarcode two) := ⟨0, by omega⟩
  let j : BarcodeOccurrence 1 (rankBarcode two) := ⟨1, by omega⟩
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  exact ⟨i, j, hne, inducedMap_id two i, inducedMap_id two j⟩

/-- The matched terminal bars retain finite observed death one. -/
theorem terminal_pair :
    ∃ i j : BarcodeOccurrence 1 (rankBarcode two), inducedMap projection i = some j ∧
      (occurrence (rankBarcode two) i).death = 1 ∧ (occurrence (rankBarcode two) j).death = 1 := by
  have hlen : (rankBarcode (finiteImage projection)).toList.length = 1 := by
    rw [projection_barcode]; simp
  let a : BarcodeOccurrence 1 (rankBarcode (finiteImage projection)) := ⟨0, by omega⟩
  refine ⟨imageSourceEmbedding projection a, imageTargetEmbedding projection a,
    (inducedMap_eq_some_iff projection _ _).mpr ⟨a, rfl, rfl⟩, ?_, ?_⟩
  all_goals
    have hdeath (x : BarcodeOccurrence 1 (rankBarcode two)) :
        (occurrence (rankBarcode two) x).death = 1 := by
      have hb := (occurrence (rankBarcode two) x).birth_lt_death
      have hd := (occurrence (rankBarcode two) x).death_le_size
      omega
    exact hdeath _

private theorem zero_image_barcode : rankBarcode (finiteImage (0 : two ⟶ two)) = 0 := by
  rw [one_stage_barcode]
  have hd : Module.finrank ℚ ((finiteImage (0 : two ⟶ two)).obj 0) = 0 := by
    change Module.finrank ℚ (LinearMap.range (0 : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ))) = 0
    rw [LinearMap.range_zero]
    simp
  rw [hd]
  simp

/-- An actual zero transformation selects no occurrence, despite nonempty repeated barcodes. -/
theorem zero_matching (i : BarcodeOccurrence 1 (rankBarcode two)) :
    inducedMap (0 : two ⟶ two) i = none := by
  apply (inducedMap_eq_none_iff _ _).mpr
  rintro ⟨a, _⟩
  have hlen : (rankBarcode (finiteImage (0 : two ⟶ two))).toList.length = 0 := by
    rw [zero_image_barcode]; simp
  have := a.isLt
  change a.val < (rankBarcode (finiteImage (0 : two ⟶ two))).toList.length at this
  omega

private def sourceBar : FiniteInterval 3 := ⟨1, 3, by decide, by decide⟩
private def targetBar : FiniteInterval 3 := ⟨0, 2, by decide, by decide⟩

private noncomputable def overlapLinear (i : Fin 3) :
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

private theorem overlap_image_nonzero : rankBarcode (finiteImage overlap) ≠ 0 := by
  let x : (intervalModule (k := ℚ) sourceBar).obj (1 : Fin 3) :=
    ⟨1, by simp [FiniteInterval.fiber, FiniteInterval.alive, sourceBar]⟩
  let v : (finiteImage overlap).obj (1 : Fin 3) := ⟨(overlap.app 1).hom x, x, rfl⟩
  have hv : v ≠ 0 := by
    intro h
    have he := congrArg (fun y : (finiteImage overlap).obj (1 : Fin 3) => y.val.val) h
    norm_num [v, x, overlap, overlapLinear, sourceBar, targetBar, FiniteInterval.alive] at he
    have he' := congrArg Subtype.val he
    change (1 : ℚ) = 0 at he'
    exact one_ne_zero he'
  have hpos : 0 < Module.finrank ℚ ((finiteImage overlap).obj (1 : Fin 3)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
  intro hB
  have hr := structureMapRank_rankBarcode (finiteImage overlap) (1 : Fin 3) 1 (le_refl _)
  rw [hB, rank_barcodeMap] at hr
  simp only [Multiset.countP_zero] at hr
  have hs : structureMapRank (finiteImage overlap) (1 : Fin 3) 1 (le_refl _) =
      Module.finrank ℚ ((finiteImage overlap).obj (1 : Fin 3)) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id]
    simp
  omega

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

/-- The actual overlap map matches [1,3) to [0,2), exercising both strict outer endpoint changes. -/
theorem nontrivial_endpoints :
    ∃ (i : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) sourceBar)))
      (j : BarcodeOccurrence 3 (rankBarcode (intervalModule (k := ℚ) targetBar))),
      inducedMap overlap i = some j ∧
      (occurrence _ i).birth = 1 ∧ (occurrence _ i).death = 3 ∧
      (occurrence _ j).birth = 0 ∧ (occurrence _ j).death = 2 := by
  have hlen : 0 < (rankBarcode (finiteImage overlap)).toList.length := by
    rw [Multiset.length_toList]
    exact Multiset.card_pos.mpr overlap_image_nonzero
  let a : BarcodeOccurrence 3 (rankBarcode (finiteImage overlap)) := ⟨0, hlen⟩
  refine ⟨imageSourceEmbedding overlap a, imageTargetEmbedding overlap a,
    (inducedMap_eq_some_iff overlap _ _).mpr ⟨a, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact congrArg FiniteInterval.birth (single_occurrence sourceBar _)
  · exact congrArg FiniteInterval.death (single_occurrence sourceBar _)
  · exact congrArg FiniteInterval.birth (single_occurrence targetBar _)
  · exact congrArg FiniteInterval.death (single_occurrence targetBar _)

private noncomputable def empty : PModule.{0,0,0} ℚ (Fin 0) := barcodeModule (k := ℚ) 0
private instance empty_fd (i : Fin 0) : FiniteDimensional ℚ (empty.obj i) := i.elim0

/-- Empty-chain image factorization and matching retain an empty occurrence domain. -/
theorem empty_chain : IsEmpty (BarcodeOccurrence 0 (rankBarcode empty)) ∧
    ∀ i : BarcodeOccurrence 0 (rankBarcode empty), inducedMap (𝟙 empty) i = some i := by
  refine ⟨?_, inducedMap_id empty⟩
  change IsEmpty (Fin (rankBarcode (barcodeModule (k := ℚ) (0 : Multiset (FiniteInterval 0)))).toList.length)
  rw [rankBarcode_barcodeModule]
  simp only [Multiset.toList_zero, List.length_nil]
  exact inferInstance

end TDA.Persistence.FiniteInducedMatchingExamples
