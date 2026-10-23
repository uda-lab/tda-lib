import TDA.Persistence.ConstructibleShiftBarcode

/-!
# Shifted duplicate bars, essential tails and occurrence round trips

The input is a finite-barcode pullback with two `[1,3)` copies and
one essential bar born at 3. Its shifted diagrams and support checks use the
positive-evaluation shift, with additional observations on both tails.
-/

set_option autoImplicit false

namespace TDA.Persistence.ConstructibleShiftBarcodeExamples

open CategoryTheory CategoryTheory.Limits FiniteConstructible RealShift
open scoped Classical ZeroObject NNReal ENNReal

private def coarse : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 3)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem coarse_apply (i : Fin 2) : coarse i = if i = 0 then (1 : ℝ) else 3 := rfl

private def finiteBar : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩
private def essentialBar : FiniteInterval 3 := ⟨2, 3, by decide, by decide⟩
private def bars : Multiset (FiniteInterval 3) := finiteBar ::ₘ finiteBar ::ₘ essentialBar ::ₘ 0

private theorem bars_birth_pos (I : FiniteInterval 3) (hI : I ∈ bars) : 0 < I.birth := by
  simp only [bars, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hI
  rcases hI with rfl | rfl | rfl <;> decide

private theorem initial_zero : IsZero ((barcodeModule (k := ℚ) bars).obj 0) := by
  have : Subsingleton ((barcodeModule (k := ℚ) bars).obj 0) := by
    change Subsingleton (∀ i : Fin bars.toList.length,
      FiniteInterval.fiber (k := ℚ) (bars.toList.get i) 0)
    refine ⟨fun x y => funext (fun i => ?_)⟩
    apply Subtype.ext
    have hb := bars_birth_pos _ (Multiset.mem_toList.mp (List.get_mem bars.toList i))
    have hn : ¬ (bars.toList.get i).alive 0 := by
      simp only [FiniteInterval.alive, Fin.val_zero]; omega
    have hx : (x i : ℚ) = 0 := by
      simpa only [FiniteInterval.fiber, if_neg hn, Submodule.mem_bot] using (x i).property
    have hy : (y i : ℚ) = 0 := by
      simpa only [FiniteInterval.fiber, if_neg hn, Submodule.mem_bot] using (y i).property
    exact hx.trans hy.symm
  exact ModuleCat.isZero_of_subsingleton _

private noncomputable def input : PModule.{0,0,0} ℚ ℝ :=
  reindex (cellIndex coarse) (barcodeModule (k := ℚ) bars)

private theorem input_constructible : IsConstructible coarse input :=
  isConstructible_reindex coarse _ initial_zero

private theorem critical_finite (i : Fin 2) : FiniteDimensional ℚ (input.obj (coarse i)) := by
  change FiniteDimensional ℚ ((barcodeModule (k := ℚ) bars).obj (cellIndex coarse (coarse i)))
  infer_instance

private theorem coarse_diagram : moduleDiagram coarse input critical_finite =
    ofIndexBars coarse coarse.strictMono (reindexBarcode (Fin.succOrderEmb 2).toOrderHom bars) := by
  let s : Fin 2 →o Fin 3 := (cellIndex coarse).comp coarse.toOrderHom
  have hs : s = (Fin.succOrderEmb 2).toOrderHom := by
    apply DFunLike.ext
    intro i
    exact cellIndex_critical coarse i
  unfold moduleDiagram
  change ofIndexBars coarse coarse.strictMono
    (rankBarcode (reindex s (barcodeModule (k := ℚ) bars))) = _
  rw [rankBarcode_reindex, rankBarcode_barcodeModule, hs]


private theorem input_points : (moduleDiagram coarse input critical_finite).points =
    ((1 : ℝ), (3 : WithTop ℝ)) ::ₘ (1, (3 : WithTop ℝ)) ::ₘ (3, ⊤) ::ₘ 0 := by
  rw [coarse_diagram, RealBarcode.ofIndexBars_points]
  have hf := RealBarcode.restrictAlong_succ finiteBar (show 0 < finiteBar.birth by decide)
  have he := RealBarcode.restrictAlong_succ essentialBar (show 0 < essentialBar.birth by decide)
  simp only [reindexBarcode, bars, Multiset.filterMap_cons_some _ _ _ hf,
    Multiset.filterMap_cons_some _ _ _ he, Multiset.filterMap_zero,
    Multiset.map_cons, Multiset.map_zero]
  rfl

/-- The shift moves finite births/deaths left and keeps the essential death top. -/
theorem shifted_points :
    (moduleDiagram (shiftGrid 2 coarse) ((shift 2).obj input)
      (finiteDimensional_shiftedCritical coarse input critical_finite 2)).points =
        ((-1 : ℝ), (1 : WithTop ℝ)) ::ₘ (-1, (1 : WithTop ℝ)) ::ₘ (1, ⊤) ::ₘ 0 := by
  rw [moduleDiagram_shift]
  change (moduleDiagram coarse input critical_finite).points.map _ = _
  rw [input_points]
  norm_num [translateDiagramPoint]

/-- Exact finite endpoints remain half-open; the essential birth is included and
its tail survives every parameter at or above that birth. -/
theorem shifted_support (t : ℝ) (ht : 1 ≤ t) :
    ((-1 : ℝ), (1 : WithTop ℝ)) ∈
      (moduleDiagram (shiftGrid 2 coarse) ((shift 2).obj input)
        (finiteDimensional_shiftedCritical coarse input critical_finite 2)).points ∧
      RealBarcode.alive (-1, (1 : WithTop ℝ)) (-1) ∧
      ¬ RealBarcode.alive (-1, (1 : WithTop ℝ)) 1 ∧
      RealBarcode.alive (1, ⊤) 1 ∧ RealBarcode.alive (1, ⊤) t := by
  rw [shifted_points]
  refine ⟨by simp, ⟨le_rfl, ?_⟩, ?_,
    ⟨le_rfl, WithTop.coe_lt_top _⟩, ⟨ht, WithTop.coe_lt_top _⟩⟩
  · exact WithTop.coe_lt_coe.mpr (by norm_num)
  · intro h
    exact lt_irrefl _ h.2

private def fine : Fin 5 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (![(-4 : ℝ), -1, 0, 1, 8])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem shifted_refines : Refines (shiftGrid 2 coarse) fine := by
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact ⟨1, by norm_num [fine, shiftGrid_apply, coarse_apply]; rfl⟩
  · exact ⟨3, by norm_num [fine, shiftGrid_apply, coarse_apply]; rfl⟩

private theorem fine_finite (i : Fin 5) :
    FiniteDimensional ℚ (((shift 2).obj input).obj (fine i)) :=
  finiteDimensional_of_isConstructible ((shift 2).obj input) (input_constructible.shift 2)
    (finiteDimensional_shiftedCritical coarse input critical_finite 2) (fine i)

/-- Adding observations before, inside and after the shifted grid retains all bars. -/
theorem shifted_refined_points :
    (moduleDiagram fine ((shift 2).obj input) fine_finite).points =
      ((-1 : ℝ), (1 : WithTop ℝ)) ::ₘ (-1, (1 : WithTop ℝ)) ::ₘ (1, ⊤) ::ₘ 0 := by
  have h := moduleDiagram_shift_refinement coarse fine input input_constructible
    critical_finite 2 shifted_refines
  rw [h]
  rw [← moduleDiagram_shift coarse input critical_finite 2]
  exact shifted_points

/-- Equal finite bars still give two labels, and the essential tail has its own label. -/
theorem shifted_multiplicities :
    (moduleDiagram fine ((shift 2).obj input) fine_finite).points.count
        (-1, (1 : WithTop ℝ)) = 2 ∧
      (moduleDiagram fine ((shift 2).obj input) fine_finite).points.count (1, ⊤) = 1 := by
  rw [shifted_refined_points]
  norm_num

/-- Equal finite values have distinct occurrence indices before and after translation. -/
theorem distinct_duplicate_labels (a : ℝ) :
    let D := moduleDiagram fine ((shift 2).obj input) fine_finite
    ∃ p q : D.finiteOccurrences, p ≠ q ∧ p.1 = q.1 ∧
      finiteTranslationEquiv D a p ≠ finiteTranslationEquiv D a q := by
  let D := moduleDiagram fine ((shift 2).obj input) fine_finite
  have hc : (finitePart D.points).count (-1, 1) = 2 := by
    change (finitePart (moduleDiagram fine ((shift 2).obj input) fine_finite).points).count
      (-1, 1) = 2
    rw [shifted_refined_points]
    change (((-1, 1) : ℝ × ℝ) ::ₘ (-1, 1) ::ₘ 0).count (-1, 1) = 2
    norm_num
  let p : D.finiteOccurrences := ⟨(-1, 1), ⟨0, by rw [hc]; decide⟩⟩
  let q : D.finiteOccurrences := ⟨(-1, 1), ⟨1, by rw [hc]; decide⟩⟩
  have hpq : p ≠ q := by
    intro h
    have hi := congrArg (fun x : D.finiteOccurrences => x.2.val) h
    norm_num [p, q] at hi
  exact ⟨p, q, hpq, rfl, fun h => hpq ((finiteTranslationEquiv D a).injective h)⟩

/-- The constructed common grid for this source and its shifted target gives the
same shifted diagram without new finiteness assumptions. -/
theorem common_grid_shift (ε : ℝ≥0) :
    let e := commonGrid coarse (shiftGrid ε coarse)
    moduleDiagram e ((shift ε).obj input)
        (fun j => finiteDimensional_of_isConstructible ((shift ε).obj input)
          (input_constructible.shift ε)
          (finiteDimensional_shiftedCritical coarse input critical_finite ε) (e j)) =
      translateDiagram (moduleDiagram coarse input critical_finite) (-(ε : ℝ)) :=
  moduleDiagram_shift_refinement coarse _ input input_constructible critical_finite ε
    (refines_commonGrid_right _ _)

/-- A complete cost-bounded matching is constructed for the refined shift. -/
theorem refined_shift_matching :
    ∃ A : OccurrenceMatching (moduleDiagram coarse input critical_finite).finiteOccurrences
        (moduleDiagram fine ((shift 2).obj input) fine_finite).finiteOccurrences
        (moduleDiagram coarse input critical_finite).essentialOccurrences
        (moduleDiagram fine ((shift 2).obj input) fine_finite).essentialOccurrences,
      (∀ i, ∃ j, A.finite i = some j ∧ j.1 = (i.1.1 - 2, i.1.2 - 2)) ∧
      (∀ j, ∃ i, A.finite i = some j) ∧
      (∀ i, (A.essential i).1 = i.1 - 2) ∧
      A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ 2 :=
  exists_shift_refinement_matching coarse fine input input_constructible critical_finite 2
    shifted_refines

/-- Target untranslation exactly recovers each original occurrence label, rather
than merely its endpoint value. This includes arbitrary repeated occurrences. -/
theorem occurrence_round_trip (D : Diagram ℝ) (a : ℝ) :
    (∀ p : D.finiteOccurrences,
      ((translatedMatching D a).untranslateTarget a).finite p = some p) ∧
    (∀ p : D.essentialOccurrences,
      ((translatedMatching D a).untranslateTarget a).essential p = p) := by
  constructor
  · intro p
    simp [OccurrenceMatching.untranslateTarget, OccurrenceMatching.relabel, translatedMatching]
  · intro p
    simp [OccurrenceMatching.untranslateTarget, OccurrenceMatching.relabel, translatedMatching]

private noncomputable def deletedFiniteMatching (D : Diagram ℝ) (a : ℝ) :
    OccurrenceMatching D.finiteOccurrences (translateDiagram D a).finiteOccurrences
      D.essentialOccurrences (translateDiagram D a).essentialOccurrences where
  finite _ := none
  finite_injective := by intros; contradiction
  essential := essentialTranslationEquiv D a

/-- With both finite bars unselected, target untranslation retains both
unmatched sides and returns every essential label exactly. -/
theorem unmatched_round_trip (a : ℝ) :
    let D := moduleDiagram coarse input critical_finite
    let A := (deletedFiniteMatching D a).untranslateTarget a
    (∀ i, A.finite i = none) ∧ (∀ j, ¬ ∃ i, A.finite i = some j) ∧
      (∀ b, A.essential b = b) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (OccurrenceMatching.untranslateTarget_finite_eq_none_iff a _ i).mpr rfl
  · intro j ⟨i, hi⟩
    have h := (OccurrenceMatching.untranslateTarget_finite_eq_some_iff a _ i j).mp hi
    contradiction
  · intro b
    simp [deletedFiniteMatching, OccurrenceMatching.untranslateTarget, OccurrenceMatching.relabel]

/-- The inverse occurrence correspondence adds ε to finite and essential values. -/
theorem inverse_values (ε : ℝ≥0)
    (p : (translateDiagram (moduleDiagram coarse input critical_finite) (-(ε : ℝ))).finiteOccurrences)
    (b : (translateDiagram (moduleDiagram coarse input critical_finite) (-(ε : ℝ))).essentialOccurrences) :
    ((finiteTranslationEquiv _ (-(ε : ℝ))).symm p).1 =
        (p.1.1 + (ε : ℝ), p.1.2 + (ε : ℝ)) ∧
      ((essentialTranslationEquiv _ (-(ε : ℝ))).symm b).1 = b.1 + (ε : ℝ) := by
  constructor
  · simpa only [sub_neg_eq_add] using finiteTranslationEquiv_symm_value _ (-(ε : ℝ)) p
  · simpa only [sub_neg_eq_add] using essentialTranslationEquiv_symm_value _ (-(ε : ℝ)) b

/-- The constructed complete matching applies to the nonempty shifted module. -/
theorem shift_matching (ε : ℝ≥0) :
    let D := moduleDiagram coarse input critical_finite
    let E := moduleDiagram (shiftGrid ε coarse) ((shift ε).obj input)
      (finiteDimensional_shiftedCritical coarse input critical_finite ε)
    ∃ A : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
        D.essentialOccurrences E.essentialOccurrences,
      (∀ i, ∃ j, A.finite i = some j ∧
        j.1 = (i.1.1 - (ε : ℝ), i.1.2 - (ε : ℝ))) ∧
      (∀ j, ∃ i, A.finite i = some j) ∧
      (∀ i, (A.essential i).1 = i.1 - (ε : ℝ)) ∧
      A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ ε :=
  exists_shift_matching coarse input critical_finite ε

/-- Parameter zero has the same diagram; the constructed complete matching costs zero. -/
theorem zero_shift :
    moduleDiagram (shiftGrid 0 coarse) ((shift 0).obj input)
        (finiteDimensional_shiftedCritical coarse input critical_finite 0) =
      moduleDiagram coarse input critical_finite ∧
    (translatedMatching (moduleDiagram coarse input critical_finite) 0).cost
      (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) = 0 := by
  refine ⟨?_, le_antisymm ?_ zero_le⟩
  · rw [moduleDiagram_shift, NNReal.coe_zero, neg_zero, translateDiagram_zero]
  · simpa using translatedMatching_cost_le (moduleDiagram coarse input critical_finite) 0

private def empty : Fin 0 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- An empty grid chooses no critical stage and supplies the empty shift diagram. -/
theorem empty_shift (ε : ℝ≥0) :
    (moduleDiagram (shiftGrid ε empty) ((shift ε).obj (0 : PModule.{0,0,0} ℚ ℝ))
      (finiteDimensional_shiftedCritical empty _ (fun i => Fin.elim0 i) ε)).points = 0 :=
  moduleDiagram_empty_grid _ _

end TDA.Persistence.ConstructibleShiftBarcodeExamples
