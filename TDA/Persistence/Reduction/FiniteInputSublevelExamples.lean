import TDA.Persistence.Reduction.FiniteInputSublevelHomology
import TDA.Persistence.Reduction.FiniteInputExamples

/-! Executions and actual inclusion laws for computed integer-sublevel classes. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.SublevelExamples

open TDA.Simplicial TDA.Filtration

private local instance : NeZero Examples.filled.length := ⟨by decide⟩
private local instance : NeZero Examples.hollow.length := ⟨by decide⟩
private local instance : NeZero Examples.tied.length := ⟨by decide⟩
private local instance : NeZero Examples.delayed.length := ⟨by decide⟩
private local instance : NeZero Examples.negative.length := ⟨by decide⟩

/-- The same filled triangle, with two distinct integer thresholds before its death. -/
def wideFilled : Input :=
  [({0}, 0), ({1}, 0), ({2}, 0), ({0, 1}, 1), ({1, 2}, 1),
    ({0, 2}, 1), ({0, 1, 2}, 3)]

private local instance : NeZero wideFilled.length := ⟨by decide⟩

theorem wideFilled_valid : Valid wideFilled := (validBool_iff _).mp (by decide +kernel)

theorem wideFilled_boundary : boundary wideFilled = Examples.triangleMatrix := by
  rw [← Examples.filled_boundary]
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

private def filledH0a : Representative Examples.filled.length :=
  ⟨⟨0, 0, .finite 1⟩, 1, some 3, [0, 1], some [3]⟩
private def filledH0b : Representative Examples.filled.length :=
  ⟨⟨0, 0, .finite 1⟩, 2, some 4, [1, 2], some [4]⟩
private def filledH1 : Representative Examples.filled.length :=
  ⟨⟨1, 1, .finite 2⟩, 5, some 6, [3, 4, 5], some [6]⟩
private def filledEssential : Representative Examples.filled.length :=
  ⟨⟨0, 0, .essential⟩, 0, none, [0], none⟩
private def wideH0a : Representative wideFilled.length :=
  ⟨⟨0, 0, .finite 1⟩, 1, some 3, [0, 1], some [3]⟩
private def wideH0b : Representative wideFilled.length :=
  ⟨⟨0, 0, .finite 1⟩, 2, some 4, [1, 2], some [4]⟩
private def wideEssential : Representative wideFilled.length :=
  ⟨⟨0, 0, .essential⟩, 0, none, [0], none⟩
private def wideH1 : Representative wideFilled.length :=
  ⟨⟨1, 1, .finite 3⟩, 5, some 6, [3, 4, 5], some [6]⟩
private def hollowH1 : Representative Examples.hollow.length :=
  ⟨⟨1, 1, .essential⟩, 5, none, [3, 4, 5], none⟩

private theorem filled_data : representedOccurrences Examples.filled =
    [filledH0a, filledH0b, filledH1, filledEssential] := by
  unfold representedOccurrences pairedRepresentative essentialRepresentative pairedVector
    essentialVector change essentialIndices pivotPairs reduced trace
  rw [Examples.filled_boundary]
  decide +kernel

private theorem wide_data : representedOccurrences wideFilled =
    [wideH0a, wideH0b, wideH1, wideEssential] := by
  unfold representedOccurrences pairedRepresentative essentialRepresentative pairedVector
    essentialVector change essentialIndices pivotPairs reduced trace
  rw [wideFilled_boundary]
  decide +kernel

private theorem hollow_mem : hollowH1 ∈ representedOccurrences Examples.hollow := by
  have hi : (5 : Fin Examples.hollow.length) ∈ essentialIndices Examples.hollow := by
    rw [Examples.hollow_essential_raw]; decide +kernel
  have he : essentialRepresentative Examples.hollow 5 = hollowH1 := by
    dsimp only [essentialRepresentative, essentialVector, change, trace]
    rw [Examples.hollow_boundary]
    decide +kernel
  rw [← he]
  exact essentialRepresentative_mem _ _ hi

private theorem filled_mem : filledH1 ∈ representedOccurrences Examples.filled := by
  rw [filled_data]; decide +kernel
private theorem wide_mem : wideH1 ∈ representedOccurrences wideFilled := by
  rw [wide_data]; decide +kernel

private theorem filled_query_at_birth : runAtGrade Examples.filled 1 =
    some [filledH1, filledEssential] := by
  simp only [runAtGrade, runWithRepresentatives,
    (validBool_iff Examples.filled).mpr Examples.filled_valid, ↓reduceIte,
    Option.map_some, filled_data]
  decide +kernel

private theorem filled_query_at_death : runAtGrade Examples.filled 2 = some [filledEssential] := by
  simp only [runAtGrade, runWithRepresentatives,
    (validBool_iff Examples.filled).mpr Examples.filled_valid, ↓reduceIte,
    Option.map_some, filled_data]
  decide +kernel

private theorem duplicate_query : runAtGrade Examples.filled 0 =
    some [filledH0a, filledH0b, filledEssential] ∧
    filledH0a.occurrence = filledH0b.occurrence ∧ filledH0a.birthIndex ≠ filledH0b.birthIndex := by
  constructor
  · simp only [runAtGrade, runWithRepresentatives,
      (validBool_iff Examples.filled).mpr Examples.filled_valid, ↓reduceIte,
      Option.map_some, filled_data]
    decide +kernel
  · decide +kernel

private theorem wide_queries : runAtGrade wideFilled 1 = some [wideH1, wideEssential] ∧
    runAtGrade wideFilled 2 = some [wideH1, wideEssential] ∧
    runAtGrade wideFilled 3 = some [wideEssential] := by
  simp only [runAtGrade, runWithRepresentatives, (validBool_iff wideFilled).mpr wideFilled_valid,
    ↓reduceIte, Option.map_some, wide_data]
  decide +kernel

private theorem tied_query :
    (runAtGrade Examples.tied 1).map (List.map Representative.occurrence) =
      some [⟨0, 0, .essential⟩] := by
  rw [runAtGrade_forget, Examples.tied_run]
  decide +kernel

private theorem prebirth_empty_invalid :
    runAtGrade Examples.filled (-1) = some [] ∧
    runAtGrade Examples.delayed 6 = some [] ∧
    runAtGrade Examples.negative (-5) = some [] ∧
    runAtGrade [] 0 = some [] ∧ runAtGrade [({0, 1}, 0)] 0 = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [runAtGrade, runWithRepresentatives,
      (validBool_iff Examples.filled).mpr Examples.filled_valid, ↓reduceIte,
      Option.map_some, filled_data]
    decide +kernel
  · decide +kernel
  · have hx : (runAtGrade Examples.negative (-5)).map
        (List.map Representative.occurrence) = some [] := by
      rw [runAtGrade_forget, Examples.negative_run]
      decide +kernel
    obtain ⟨out, hout, heq⟩ := Option.map_eq_some_iff.mp hx
    have he : out = [] := List.map_eq_nil_iff.mp heq
    rwa [he] at hout
  · decide +kernel
  · decide +kernel

private theorem filled_nonzero :
    sublevelClass Examples.filled Examples.filled_valid filledH1 filled_mem 1 (by decide) ≠ 0 := by
  have hm := (mem_runAtGrade Examples.filled 1 [filledH1, filledEssential]
    filled_query_at_birth filledH1).mp (by decide +kernel)
  exact sublevelClass_nonzero Examples.filled Examples.filled_valid filledH1 hm.1 1 hm.2

private theorem filled_dies_under_inclusion :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter Examples.filled Examples.filled_valid).sublevel_mono
      (show (1 : ℤ) ≤ 2 by decide)) 1).hom
      (sublevelClass Examples.filled Examples.filled_valid filledH1 filled_mem 1 (by decide)) = 0 := by
  exact (sublevelClass_naturality Examples.filled Examples.filled_valid filledH1 filled_mem
    1 2 (by decide) (by decide) (by decide)).trans
    (sublevelClass_eq_zero_of_death Examples.filled Examples.filled_valid filledH1 filled_mem
      2 rfl 2 (by decide) (by decide))

private theorem filled_returned_filling :
    letI := faceFintype Examples.filled Examples.filled_valid
    ∃ B : Chain ((gradeFilter Examples.filled Examples.filled_valid).sublevel 2) (ZMod 2) 2,
      (prefixChainEquiv (ZMod 2) (compatibleOrder Examples.filled Examples.filled_valid)
        (sublevelStage Examples.filled 2) 2
        (chainIncl (ZMod 2) (sublevel_eq_prefix Examples.filled Examples.filled_valid 2).le 2 B)).1 =
        faceVector Examples.filled Examples.filled_valid (chainVector [6]) ∧
      TDA.Simplicial.boundary ((gradeFilter Examples.filled Examples.filled_valid).sublevel 2)
        (ZMod 2) 1 B = (sublevelCycle Examples.filled Examples.filled_valid filledH1 filled_mem
          2 (by decide)).1 := by
  obtain ⟨b, hb, B, hc, hd⟩ := sublevel_bounding Examples.filled Examples.filled_valid filledH1
    filled_mem 6 rfl 2 (by decide) (by decide)
  change some ([6] : List (Fin Examples.filled.length)) = some b at hb
  cases Option.some.inj hb
  exact ⟨B, hc, hd⟩

private theorem finite_survives_unequal_grades :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter wideFilled wideFilled_valid).sublevel_mono
      (show (1 : ℤ) ≤ 2 by decide)) 1).hom
      (sublevelClass wideFilled wideFilled_valid wideH1 wide_mem 1 (by decide)) =
      sublevelClass wideFilled wideFilled_valid wideH1 wide_mem 2 (by decide) ∧
    sublevelClass wideFilled wideFilled_valid wideH1 wide_mem 2 (by decide) ≠ 0 :=
  ⟨sublevelClass_naturality wideFilled wideFilled_valid wideH1 wide_mem 1 2 (by decide)
      (by decide) (by decide),
    sublevelClass_nonzero wideFilled wideFilled_valid wideH1 wide_mem 2 (by decide)⟩

private theorem finite_grade_coordinate :
    letI := faceFintype wideFilled wideFilled_valid
    (sublevelHomologyToAlive wideFilled wideFilled_valid 1 2
      (sublevelClass wideFilled wideFilled_valid wideH1 wide_mem 2 (by decide))).1 =
      Pi.single ((finCongr (faceCount_eq_length wideFilled wideFilled_valid)).symm 5) (1 : ZMod 2) :=
  sublevelClass_coordinate wideFilled wideFilled_valid wideH1 wide_mem 2 (by decide)

private theorem essential_H1_tail :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter Examples.hollow Examples.hollow_valid).sublevel_mono
      (show (1 : ℤ) ≤ 17 by decide)) 1).hom
      (sublevelClass Examples.hollow Examples.hollow_valid hollowH1 hollow_mem 1 (by decide)) =
      sublevelClass Examples.hollow Examples.hollow_valid hollowH1 hollow_mem 17 (by decide) ∧
    sublevelClass Examples.hollow Examples.hollow_valid hollowH1 hollow_mem 17 (by decide) ≠ 0 :=
  ⟨sublevelClass_naturality Examples.hollow Examples.hollow_valid hollowH1 hollow_mem 1 17
      (by decide) (by decide) (by decide),
    sublevelClass_nonzero Examples.hollow Examples.hollow_valid hollowH1 hollow_mem 17 (by decide)⟩

private def isolated : Representative Examples.delayed.length :=
  ⟨⟨0, 7, .essential⟩, 0, none, [0], none⟩
private theorem isolated_mem : isolated ∈ representedOccurrences Examples.delayed := by
  have he : essentialRepresentative Examples.delayed 0 = isolated := by decide +kernel
  rw [← he]
  exact essentialRepresentative_mem _ _ (by decide +kernel)

private theorem essential_H0_tail :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter Examples.delayed Examples.delayed_valid).sublevel_mono
      (show (7 : ℤ) ≤ 100 by decide)) 0).hom
      (sublevelClass Examples.delayed Examples.delayed_valid isolated isolated_mem 7 (by decide)) =
      sublevelClass Examples.delayed Examples.delayed_valid isolated isolated_mem 100 (by decide) ∧
    sublevelClass Examples.delayed Examples.delayed_valid isolated isolated_mem 100 (by decide) ≠ 0 :=
  ⟨sublevelClass_naturality Examples.delayed Examples.delayed_valid isolated isolated_mem 7 100
      (by decide) (by decide) (by decide),
    sublevelClass_nonzero Examples.delayed Examples.delayed_valid isolated isolated_mem 100 (by decide)⟩

private theorem duplicate_grade_coordinates (r : Representative Examples.filled.length)
    (hr : r = filledH0a ∨ r = filledH0b) :
    ∃ (hm : r ∈ representedOccurrences Examples.filled) (ha : r.occurrence.AliveAt 0),
    letI := faceFintype Examples.filled Examples.filled_valid
    sublevelClass Examples.filled Examples.filled_valid r hm 0 ha.1 ≠ 0 ∧
      (sublevelHomologyToAlive Examples.filled Examples.filled_valid r.occurrence.degree 0
        (sublevelClass Examples.filled Examples.filled_valid r hm 0 ha.1)).1 =
        Pi.single ((finCongr (faceCount_eq_length Examples.filled Examples.filled_valid)).symm
          r.birthIndex) (1 : ZMod 2) := by
  have hm : r ∈ representedOccurrences Examples.filled := by
    rw [filled_data]
    rcases hr with rfl | rfl <;> decide +kernel
  have ha : r.occurrence.AliveAt 0 := by rcases hr with rfl | rfl <;> decide +kernel
  exact ⟨hm, ha, sublevelClass_nonzero Examples.filled Examples.filled_valid r hm 0 ha,
    sublevelClass_coordinate Examples.filled Examples.filled_valid r hm 0 ha⟩

private def negativeEssential : Representative Examples.negative.length :=
  ⟨⟨0, -4, .essential⟩, 0, none, [0], none⟩

private theorem negative_mem : negativeEssential ∈ representedOccurrences Examples.negative := by
  have he : essentialRepresentative Examples.negative 0 = negativeEssential := by
    unfold essentialRepresentative essentialVector change trace
    rw [Examples.negative_boundary]
    decide +kernel
  have hi : (0 : Fin Examples.negative.length) ∈ essentialIndices Examples.negative := by
    unfold essentialIndices pivotPairs reduced trace
    rw [Examples.negative_boundary]
    decide +kernel
  rw [← he]
  exact essentialRepresentative_mem _ _ hi

private theorem negative_query : (runAtGrade Examples.negative (-4)).map
    (List.map Representative.occurrence) = some [⟨0, -4, .finite (-1)⟩, ⟨0, -4, .essential⟩] := by
  rw [runAtGrade_forget, Examples.negative_run]
  decide +kernel

private theorem negative_H0_transport :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter Examples.negative Examples.negative_valid).sublevel_mono
      (show (-4 : ℤ) ≤ 9 by decide)) 0).hom
      (sublevelClass Examples.negative Examples.negative_valid negativeEssential negative_mem (-4) (by decide)) =
      sublevelClass Examples.negative Examples.negative_valid negativeEssential negative_mem 9 (by decide) ∧
    sublevelClass Examples.negative Examples.negative_valid negativeEssential negative_mem 9 (by decide) ≠ 0 :=
  ⟨sublevelClass_naturality Examples.negative Examples.negative_valid negativeEssential negative_mem (-4) 9
      (by decide) (by decide) (by decide),
    sublevelClass_nonzero Examples.negative Examples.negative_valid negativeEssential negative_mem 9 (by decide)⟩

private theorem tied_index_alive :
    AliveCoordinate (degree Examples.tied) (reduced Examples.tied) 1 6
      (5 : Fin Examples.tied.length) := by
  apply paired_alive Examples.tied Examples.tied_valid (5, 6)
  · unfold pivotPairs reduced trace
    rw [Examples.tied_boundary]
    decide +kernel
  · decide
  · decide

private theorem tied_grade_admits_all_faces : sublevelStage Examples.tied 1 = 7 := by decide +kernel

private theorem tied_prefix_nonzero :
    letI := faceFintype Examples.tied Examples.tied_valid
    simplicialClass Examples.tied Examples.tied_valid 1 6
      (columnCycle Examples.tied Examples.tied_valid 1 6 5 tied_index_alive) ≠ 0 :=
  columnClass_nonzero Examples.tied Examples.tied_valid 1 6 5 tied_index_alive

end TDA.Persistence.Reduction.FiniteInput.SublevelExamples
