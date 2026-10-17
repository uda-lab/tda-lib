import TDA.Persistence.ConstructibleRefinementBarcode
import TDA.Persistence.ConstructibleIsometry

/-!
# Constructible refinement and shift boundary examples

Extra observations before, within and after the original grid preserve duplicate
finite bars and the essential tail. Shifted critical values may be negative.
-/

set_option autoImplicit false

namespace TDA.Persistence.ConstructibleRefinementExamples

open CategoryTheory CategoryTheory.Limits FiniteConstructible RealShift
open scoped ZeroObject NNReal ENNReal

private def coarse : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 3)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private def fine : Fin 5 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (![(-2 : ℝ), 1, 2, 3, 8])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private def missing : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 2)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem coarse_apply (i : Fin 2) : coarse i = if i = 0 then (1 : ℝ) else 3 := rfl
private theorem fine_apply (i : Fin 5) : fine i = (![(-2 : ℝ), 1, 2, 3, 8] : Fin 5 → ℝ) i := rfl
private theorem missing_apply (i : Fin 2) : missing i = if i = 0 then (1 : ℝ) else 2 := rfl

private theorem coarse_fine : Refines coarse fine := by
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact ⟨1, by norm_num [coarse_apply, fine_apply]⟩
  · exact ⟨3, by norm_num [coarse_apply, fine_apply]; rfl⟩

/-- Adding observations is refinement only when every old critical value is retained. -/
theorem refinement_and_missing_control : Refines coarse fine ∧ ¬ Refines coarse missing := by
  refine ⟨coarse_fine, ?_⟩
  intro h
  obtain ⟨j, hj⟩ := h ⟨(1 : Fin 2), rfl⟩
  fin_cases j <;> norm_num [coarse_apply, missing_apply] at hj

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

private theorem fine_finite (i : Fin 5) : FiniteDimensional ℚ (input.obj (fine i)) :=
  finiteDimensional_of_isConstructible input input_constructible critical_finite (fine i)

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

/-- New observations on both tails and inside a cell preserve both finite copies
and the essential endpoint; no finite death is assigned to the added last point. -/
theorem refined_diagram_points : (moduleDiagram fine input fine_finite).points =
    ((1 : ℝ), (3 : WithTop ℝ)) ::ₘ (1, (3 : WithTop ℝ)) ::ₘ (3, ⊤) ::ₘ 0 := by
  rw [moduleDiagram_refinement input coarse_fine input_constructible critical_finite,
    coarse_diagram, RealBarcode.ofIndexBars_points]
  have hf := RealBarcode.restrictAlong_succ finiteBar (show 0 < finiteBar.birth by decide)
  have he := RealBarcode.restrictAlong_succ essentialBar (show 0 < essentialBar.birth by decide)
  simp only [reindexBarcode, bars, Multiset.filterMap_cons_some _ _ _ hf,
    Multiset.filterMap_cons_some _ _ _ he, Multiset.filterMap_zero,
    Multiset.map_cons, Multiset.map_zero]
  rfl

/-- Multiplicity is unchanged, and the terminal occurrence is still essential. -/
theorem refined_multiplicities :
    (moduleDiagram fine input fine_finite).points.count (1, (3 : WithTop ℝ)) = 2 ∧
      (moduleDiagram fine input fine_finite).points.count (3, ⊤) = 1 := by
  classical
  rw [refined_diagram_points]
  norm_num

/-- Positive evaluation moves critical values left, including to negative values,
and leaves the final cell unbounded. -/
theorem shifted_sign_boundaries_and_tail :
    shiftGrid 2 coarse 0 = -1 ∧ shiftGrid 2 coarse 1 = 1 ∧
    cellIndex (shiftGrid 2 coarse) (-1) = 1 ∧
    cellIndex (shiftGrid 2 coarse) 100 = 2 ∧
    IsConstructible (shiftGrid 2 coarse) ((shift 2).obj input) := by
  refine ⟨by norm_num [shiftGrid_apply, coarse_apply], by norm_num [shiftGrid_apply, coarse_apply],
    ?_, ?_, input_constructible.shift 2⟩
  · apply (cellIndex_eq_succ_iff (shiftGrid 2 coarse) (0 : Fin 2) (-1)).mpr
    refine ⟨by norm_num [shiftGrid_apply, coarse_apply], ?_⟩
    intro j hj
    fin_cases j <;> norm_num [shiftGrid_apply, coarse_apply] at *
  · exact cellIndex_of_last_le (shiftGrid 2 coarse) 100 (by
      change coarse (1 : Fin 2) - (2 : ℝ) ≤ 100
      rw [coarse_apply]
      norm_num)

/-- Zero shift uses the original grid and the actual zero-shift module. -/
theorem zero_shift : shiftGrid 0 coarse = coarse ∧ IsConstructible coarse ((shift 0).obj input) := by
  refine ⟨shiftGrid_zero _, ?_⟩
  simpa only [shiftGrid_zero] using input_constructible.shift 0

/-- The value shared by the original and shifted grid is included once in their union. -/
theorem actual_common_shift_grid :
    (criticalValues coarse ∪ criticalValues (shiftGrid 2 coarse)).card = 3 ∧
    IsConstructible (commonGrid coarse (shiftGrid 2 coarse)) input ∧
    IsConstructible (commonGrid coarse (shiftGrid 2 coarse)) ((shift 2).obj input) := by
  refine ⟨?_, common_shift_constructible input_constructible input_constructible 2⟩
  norm_num [criticalValues, Finset.univ_fin2, shiftGrid_apply, coarse_apply]

private def empty : Fin 0 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

private noncomputable def zeroInput : PModule.{0,0,0} ℚ ℝ := 0

private theorem zero_constructible : IsConstructible empty zeroInput :=
  (isConstructible_empty_iff _ _).mpr (fun t => Functor.zero_obj t)

private theorem zero_fine_finite (i : Fin 5) : FiniteDimensional ℚ (zeroInput.obj (fine i)) :=
  finiteDimensional_of_isConstructible zeroInput zero_constructible (fun i => Fin.elim0 i) (fine i)

/-- Empty grids select no stage; refining their zero module adds no barcode occurrences. -/
theorem empty_refinement (ε : ℝ≥0) :
    shiftGrid ε empty = empty ∧ (criticalValues empty ∪ criticalValues empty).card = 0 ∧
      (moduleDiagram fine zeroInput zero_fine_finite).points = 0 := by
  refine ⟨?_, by simp [criticalValues], ?_⟩
  · apply DFunLike.ext
    intro i
    exact Fin.elim0 i
  · have h : Refines empty fine := by rintro x ⟨i, _⟩; exact Fin.elim0 i
    rw [moduleDiagram_refinement zeroInput h zero_constructible (fun i => Fin.elim0 i)]
    exact moduleDiagram_empty_grid empty zeroInput

/-- An actual self-interleaving gives a cost-bounded original-diagram matching
across unequal grids. The refined fibers are derived from the coarse ones. -/
theorem unequal_grid_isometry_control (ε : ℝ≥0) :
    let A := interleavingMatching input_constructible (input_constructible.refine coarse_fine)
      critical_finite fine_finite (RealInterleaving.refl ε input)
    A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ (ε : ℝ≥0∞) ∧
      Function.Bijective A.essential ∧
      bottleneck (moduleDiagram coarse input critical_finite) (moduleDiagram fine input fine_finite) = 0 := by
  refine ⟨interleavingMatching_cost_le input_constructible (input_constructible.refine coarse_fine)
    critical_finite fine_finite (RealInterleaving.refl ε input), ?_, ?_⟩
  · exact Equiv.bijective _
  · rw [bottleneck_eq_distance input_constructible (input_constructible.refine coarse_fine)
      critical_finite fine_finite, realInterleavingDistance_self]

/-- Empty diagrams and actual zero modules have equal zero distances without
choosing a critical stage or an optimal matching. -/
theorem empty_isometry_control :
    let A := interleavingMatching zero_constructible zero_constructible
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (RealInterleaving.refl 0 zeroInput)
    A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) = 0 ∧
      bottleneck (moduleDiagram empty zeroInput (fun i => Fin.elim0 i))
      (moduleDiagram empty zeroInput (fun i => Fin.elim0 i)) = 0 ∧
      Nonempty (RealInterleaving 0 zeroInput zeroInput) := by
  refine ⟨nonpos_iff_eq_zero.mp (interleavingMatching_cost_le zero_constructible zero_constructible
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (RealInterleaving.refl 0 zeroInput)),
    ?_, ⟨RealInterleaving.refl 0 _⟩⟩
  rw [bottleneck_eq_distance zero_constructible zero_constructible
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i), realInterleavingDistance_self]

end TDA.Persistence.ConstructibleRefinementExamples
