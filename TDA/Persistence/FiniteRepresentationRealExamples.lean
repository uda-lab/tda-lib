import TDA.Persistence.MatrixSequenceReal
import TDA.Persistence.MatrixSequenceExamples

/-!
# Matrix observations on unequal real grids

The zero initial stage is followed by the raw matrix sequence `ℚ → ℚ² → ℚ`
with zero composite. Original critical values are `-1`, `1/10`, and `4`.
-/

namespace TDA.Persistence.FiniteRepresentationRealExamples
open CategoryTheory FiniteConstructible Matrix
set_option backward.isDefEq.respectTransparency false
noncomputable section

private def coarse : Fin 3 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (![(-1 : ℝ), 1 / 10, 4])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private def fine : Fin 4 ↪o ℝ :=
  OrderEmbedding.ofStrictMono (![(-1 : ℝ), 1 / 10, 2, 4])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *)

private theorem coarse_apply (i : Fin 3) :
    coarse i = (![-1, 1 / 10, 4] : Fin 3 → ℝ) i := rfl
private theorem fine_apply (i : Fin 4) :
    fine i = (![-1, 1 / 10, 2, 4] : Fin 4 → ℝ) i := rfl

private theorem coarse_fine : Refines coarse fine := by
  rintro x ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩

/-- Raw rectangular observations, padded by a zero-dimensional left tail. -/
def observations : MatrixSequence ℚ 4 where
  dim i := match i.val with | 0 => 0 | 2 => 2 | _ => 1
  step i j _ := match i, j with
    | ⟨1, _⟩, ⟨2, _⟩ => !![1; 0]
    | ⟨2, _⟩, ⟨_ + 3, _⟩ => !![0, 1]
    | _, _ => 0

private theorem initial_zero : observations.dim 0 = 0 := rfl

private def positiveIso :
    reindex (Fin.succOrderEmb 3).toOrderHom observations.toPModule ≅
      MatrixSequenceExamples.compositeZero.toPModule :=
  FiniteLine.isoOfAdjacent (fun i => eqToIso (by fin_cases i <;> rfl)) (by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at h
    · apply ModuleCat.hom_ext
      change structureMapLinear (reindex (Fin.succOrderEmb 3).toOrderHom
        observations.toPModule) (show (0 : Fin 3) ≤ 1 by decide) =
        structureMapLinear MatrixSequenceExamples.compositeZero.toPModule
          (show (0 : Fin 3) ≤ 1 by decide)
      rw [structureMapLinear_reindex,
        MatrixSequence.structureMapLinear_adjacent observations _ _ (by decide),
        MatrixSequence.structureMapLinear_adjacent
          MatrixSequenceExamples.compositeZero _ _ (by decide)]
      rfl
    · apply ModuleCat.hom_ext
      change structureMapLinear (reindex (Fin.succOrderEmb 3).toOrderHom
        observations.toPModule) (show (1 : Fin 3) ≤ 2 by decide) =
        structureMapLinear MatrixSequenceExamples.compositeZero.toPModule
          (show (1 : Fin 3) ≤ 2 by decide)
      rw [structureMapLinear_reindex,
        MatrixSequence.structureMapLinear_adjacent observations _ _ (by decide),
        MatrixSequence.structureMapLinear_adjacent
          MatrixSequenceExamples.compositeZero _ _ (by decide)]
      rfl)

/-- The actual original endpoints survive conversion from rectangular matrices. -/
theorem real_endpoints : (observations.realDiagram coarse).points =
    ((-1 : ℝ), (4 : WithTop ℝ)) ::ₘ (1 / 10, ⊤) ::ₘ 0 := by
  letI : ∀ i : Fin 3, FiniteDimensional ℚ
      ((reindex (Fin.succOrderEmb 3).toOrderHom observations.toPModule).obj i) := fun i =>
    show FiniteDimensional ℚ (observations.toPModule.obj i.succ) from inferInstance
  rw [MatrixSequence.realDiagram_eq_ofIndexBars,
    rankBarcode_eq_of_iso positiveIso]
  change (ofIndexBars coarse coarse.strictMono
    MatrixSequenceExamples.compositeZero.barcode).points = _
  rw [MatrixSequenceExamples.compositeZero_barcode, RealBarcode.ofIndexBars_points]
  rfl

/-- Inserting an observation inside a cell retains both endpoint values and the essential tail. -/
theorem refined_real_endpoints :
    (moduleDiagram fine (observations.realModule coarse) (fun _ => inferInstance)).points =
      ((-1 : ℝ), (4 : WithTop ℝ)) ::ₘ (1 / 10, ⊤) ::ₘ 0 := by
  rw [MatrixSequence.realDiagram_refinement observations coarse fine initial_zero coarse_fine]
  exact real_endpoints

/-- The real extension has the existing reconstruction, with the constant last cell explicit. -/
def reconstruction : observations.realModule coarse ≅
    RealBarcode.realize (k := ℚ) (observations.realDiagram coarse) :=
  observations.realBarcodeIso coarse initial_zero

/-- Critical instants belong to the new cell, and the final observation persists to the right. -/
theorem critical_and_tail_indices :
    cellIndex coarse (-1) = 1 ∧ cellIndex coarse (1 / 10) = 2 ∧
      cellIndex coarse 4 = 3 ∧ cellIndex coarse 100 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cellIndex_critical coarse 0
  · exact cellIndex_critical coarse 1
  · exact cellIndex_critical coarse 2
  · exact cellIndex_of_last_le coarse 100 (by change (4 : ℝ) ≤ 100; norm_num)

end
end TDA.Persistence.FiniteRepresentationRealExamples
