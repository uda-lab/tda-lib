import TDA.Persistence.ConstructibleQTameCompatibility

/-!
# Real-barcode reconstruction boundary cases

The grid has values -2 and 3. Two copies of `[1,2)` in the padded chain become
two real intervals `[-2,3)`, while `[2,3)` becomes the essential interval `[3,∞)`.
An empty grid has an empty barcode and a zero realization.
-/

set_option autoImplicit false

namespace TDA.Persistence.ConstructibleBarcodeExamples

open CategoryTheory CategoryTheory.Limits FiniteConstructible RectangleMeasure
open scoped ZeroObject

private def grid : Fin 2 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (fun i : Fin 2 => if i = 0 then (-2 : ℝ) else 3)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private def finiteBar : FiniteInterval 3 := ⟨1, 2, by decide, by decide⟩
private def essentialBar : FiniteInterval 3 := ⟨2, 3, by decide, by decide⟩
private def bars : Multiset (FiniteInterval 3) :=
  finiteBar ::ₘ finiteBar ::ₘ essentialBar ::ₘ 0

private theorem bars_birth_pos (I : FiniteInterval 3) (hI : I ∈ bars) : 0 < I.birth := by
  simp only [bars, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hI
  rcases hI with rfl | rfl | rfl <;> decide

private noncomputable def diagram : Diagram ℝ :=
  ofIndexBars grid grid.strictMono (reindexBarcode (Fin.succOrderEmb 2).toOrderHom bars)

/-- All three occurrences, including the repeated finite interval, survive unpadding. -/
theorem all_occurrences_retained :
    (reindexBarcode (Fin.succOrderEmb 2).toOrderHom bars).card = 3 := by
  rw [RealBarcode.reindexBarcode_succ_card bars bars_birth_pos]
  rfl

/-- Exact real endpoints retain both finite copies and the essential tail. -/
theorem diagram_points : diagram.points =
    ((-2 : ℝ), ((3 : ℝ) : WithTop ℝ)) ::ₘ (-2, ((3 : ℝ) : WithTop ℝ)) ::ₘ (3, ⊤) ::ₘ 0 := by
  unfold diagram
  rw [RealBarcode.ofIndexBars_points]
  have hf := RealBarcode.restrictAlong_succ finiteBar (show 0 < finiteBar.birth by decide)
  have he := RealBarcode.restrictAlong_succ essentialBar (show 0 < essentialBar.birth by decide)
  simp only [reindexBarcode, bars,
    Multiset.filterMap_cons_some _ _ _ hf, Multiset.filterMap_cons_some _ _ _ he,
    Multiset.filterMap_zero, Multiset.map_cons, Multiset.map_zero]
  rfl

/-- The finite interval includes its birth and excludes its finite death. -/
theorem finite_boundary :
    RealBarcode.alive (-2, (3 : WithTop ℝ)) (-2) ∧
      ¬ RealBarcode.alive (-2, (3 : WithTop ℝ)) 3 := by
  constructor
  · exact ⟨le_rfl, WithTop.coe_lt_coe.mpr (by norm_num)⟩
  · intro h
    exact (lt_irrefl (3 : WithTop ℝ)) h.2

/-- The essential interval remains alive at every parameter at or above its birth. -/
theorem essential_tail (t : ℝ) (ht : 3 ≤ t) : RealBarcode.alive (3, ⊤) t :=
  ⟨ht, WithTop.coe_lt_top t⟩

/-- Multiplicity is two at the finite pair and one at the essential pair. -/
theorem duplicate_multiplicity :
    diagram.points.count (-2, (3 : WithTop ℝ)) = 2 ∧
      diagram.points.count (3, ⊤) = 1 := by
  classical
  rw [diagram_points]
  norm_num

private noncomputable def inputModule : PModule.{0,0,0} ℚ ℝ :=
  reindex (cellIndex grid) (barcodeModule (k := ℚ) bars)

private theorem initial_zero : IsZero ((barcodeModule (k := ℚ) bars).obj 0) := by
  have : Subsingleton ((barcodeModule (k := ℚ) bars).obj 0) := by
    change Subsingleton (∀ i : Fin bars.toList.length, FiniteInterval.fiber (k := ℚ) (bars.toList.get i) 0)
    refine ⟨fun x y => funext (fun i => ?_)⟩
    apply Subtype.ext
    have hb := bars_birth_pos _ (Multiset.mem_toList.mp (List.get_mem bars.toList i))
    have hn : ¬ (bars.toList.get i).alive 0 := by
      simp only [FiniteInterval.alive, Fin.val_zero]
      omega
    have hx : (x i : ℚ) = 0 := by
      simpa only [FiniteInterval.fiber, if_neg hn, Submodule.mem_bot] using (x i).property
    have hy : (y i : ℚ) = 0 := by
      simpa only [FiniteInterval.fiber, if_neg hn, Submodule.mem_bot] using (y i).property
    exact hx.trans hy.symm
  exact ModuleCat.isZero_of_subsingleton _

private theorem input_constructible : IsConstructible grid inputModule :=
  isConstructible_reindex grid _ initial_zero

private theorem critical_finite (i : Fin 2) : FiniteDimensional ℚ (inputModule.obj (grid i)) := by
  change FiniteDimensional ℚ ((barcodeModule (k := ℚ) bars).obj (cellIndex grid (grid i)))
  infer_instance

private theorem input_diagram : moduleDiagram grid inputModule critical_finite = diagram := by
  let s : Fin 2 →o Fin 3 := (cellIndex grid).comp grid.toOrderHom
  have hs : s = (Fin.succOrderEmb 2).toOrderHom := by
    apply DFunLike.ext
    intro i
    exact cellIndex_critical grid i
  unfold moduleDiagram diagram
  change ofIndexBars grid grid.strictMono
    (rankBarcode (reindex s (barcodeModule (k := ℚ) bars))) = _
  rw [rankBarcode_reindex, rankBarcode_barcodeModule, hs]

/-- The canonical decorated diagram keeps both negative-birth finite copies and
the essential tail at its actual infinity boundary. -/
theorem canonical_decorated_counts :
    moduleExtendedDiagramMultiplicity inputModule
        (qTame_of_isConstructible grid inputModule input_constructible critical_finite)
        (minusCut (-2), minusCut 3) = 2 ∧
      moduleExtendedDiagramMultiplicity inputModule
        (qTame_of_isConstructible grid inputModule input_constructible critical_finite)
        (minusCut 3, infinityCut) = 1 := by
  classical
  have hfinite : minusCut (3 : ℝ) ≠ infinityCut := by
    intro h
    have hm : minusCut (3 : ℝ) ∈ cutCell 2 3 := by
      norm_num [cutCell, minusCut]
    exact infinityCut_not_mem_cutCell 2 3 (h ▸ hm)
  have hpair : (minusCut (-2 : ℝ), minusCut (3 : ℝ)) ≠
      (minusCut (3 : ℝ), infinityCut) := by
    intro h
    exact hfinite (congrArg Prod.snd h)
  constructor
  · rw [moduleExtendedDiagramMultiplicity_eq_count grid inputModule
      input_constructible critical_finite, input_diagram, diagram_points]
    simp [diagramDecoratedPoint, hpair]
  · rw [moduleExtendedDiagramMultiplicity_eq_count grid inputModule
      input_constructible critical_finite, input_diagram, diagram_points]
    simp [diagramDecoratedPoint, Ne.symm hpair]

/-- The explicit interval transport gives a natural isomorphism to the expected endpoints. -/
noncomputable def explicitBarcodeIso : inputModule ≅ RealBarcode.realize (k := ℚ) diagram :=
  RealBarcode.barcodePullbackIso grid bars bars_birth_pos

/-- The full finite-decomposition/reconstruction composition applies using only critical fibers. -/
noncomputable def reconstructedBarcodeIso : inputModule ≅
    RealBarcode.realize (k := ℚ) (moduleDiagram grid inputModule critical_finite) :=
  barcodeRealizationIso grid inputModule input_constructible critical_finite

private def emptyGrid : Fin 0 ↪o ℝ :=
  ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩, fun {i} => Fin.elim0 i⟩

private noncomputable def zeroModule : PModule.{0,0,0} ℚ ℝ :=
  (Functor.const ℝ).obj (0 : ModuleCat ℚ)

private theorem zero_constructible : IsConstructible emptyGrid zeroModule :=
  (isConstructible_empty_iff emptyGrid zeroModule).mpr (fun _ => isZero_zero (ModuleCat ℚ))

/-- An empty critical grid produces no canonical decorated occurrences. -/
theorem empty_canonical_decorated_count (p : Cut ℝ × Cut ℝ) :
    moduleExtendedDiagramMultiplicity zeroModule
      (qTame_of_isConstructible emptyGrid zeroModule zero_constructible
        (fun i => Fin.elim0 i)) p = 0 := by
  classical
  rw [moduleExtendedDiagramMultiplicity_eq_count emptyGrid zeroModule
    zero_constructible (fun i => Fin.elim0 i)]
  simp [moduleDiagram_empty_grid]

/-- The empty-grid diagram has no endpoints, so no nonexistent critical value is selected. -/
theorem empty_diagram : (moduleDiagram emptyGrid zeroModule (fun i => Fin.elim0 i)).points = 0 :=
  moduleDiagram_empty_grid emptyGrid zeroModule

/-- The empty-grid realization is a zero module. -/
theorem empty_realization : IsZero (RealBarcode.realize (k := ℚ)
    (moduleDiagram emptyGrid zeroModule (fun i => Fin.elim0 i))) :=
  RealBarcode.realize_isZero_of_points_eq_zero _ empty_diagram

/-- The capstone also constructs its natural isomorphism for an empty critical sequence. -/
noncomputable def emptyBarcodeIso : zeroModule ≅ RealBarcode.realize (k := ℚ)
    (moduleDiagram emptyGrid zeroModule (fun i => Fin.elim0 i)) :=
  barcodeRealizationIso emptyGrid zeroModule
    ((isConstructible_empty_iff emptyGrid zeroModule).mpr (fun _ => isZero_zero (ModuleCat ℚ)))
    (fun i => Fin.elim0 i)

end TDA.Persistence.ConstructibleBarcodeExamples
