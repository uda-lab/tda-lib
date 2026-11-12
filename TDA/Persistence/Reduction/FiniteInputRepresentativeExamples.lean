import TDA.Persistence.Reduction.FiniteInputRepresentativeCorrectness
import TDA.Persistence.Reduction.FiniteInputExamples

/-! Executable and semantic consumers of original-index F₂ representatives. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput.RepresentativeExamples

private instance : NeZero Examples.filled.length := ⟨by decide⟩
private instance : NeZero Examples.hollow.length := ⟨by decide⟩
private instance : NeZero Examples.tied.length := ⟨by decide⟩
private instance : NeZero Examples.delayed.length := ⟨by decide⟩

private def summarize {n : ℕ} (r : Representative n) :
    Occurrence × ℕ × Option ℕ × List ℕ × Option (List ℕ) :=
  (r.occurrence, r.birthIndex.val, r.deathIndex.map Fin.val,
    r.cycle.map Fin.val, r.bounding.map (List.map Fin.val))

private theorem filled_output :
    (runWithRepresentatives Examples.filled).map (List.map summarize) = some
      [(⟨0, 0, .finite 1⟩, 1, some 3, [0, 1], some [3]),
        (⟨0, 0, .finite 1⟩, 2, some 4, [1, 2], some [4]),
        (⟨1, 1, .finite 2⟩, 5, some 6, [3, 4, 5], some [6]),
        (⟨0, 0, .essential⟩, 0, none, [0], none)] := by
  simp only [runWithRepresentatives,
    (validBool_iff Examples.filled).mpr Examples.filled_valid, ↓reduceIte, Option.map_some, List.map_append, List.map_filterMap, List.map_map,
    Function.comp_def, representedOccurrences, pairedRepresentative, essentialRepresentative, pairedVector,
    essentialVector, change, pivotPairs, essentialIndices, reduced, trace]
  rw [Examples.filled_boundary]
  decide +kernel

private theorem hollow_output :
    (runWithRepresentatives Examples.hollow).map (List.map summarize) = some
      [(⟨0, 0, .finite 1⟩, 1, some 3, [0, 1], some [3]),
        (⟨0, 0, .finite 1⟩, 2, some 4, [1, 2], some [4]),
        (⟨0, 0, .essential⟩, 0, none, [0], none),
        (⟨1, 1, .essential⟩, 5, none, [3, 4, 5], none)] := by
  simp only [runWithRepresentatives,
    (validBool_iff Examples.hollow).mpr Examples.hollow_valid, ↓reduceIte, Option.map_some, List.map_append, List.map_filterMap, List.map_map,
    Function.comp_def, representedOccurrences, pairedRepresentative, essentialRepresentative, pairedVector,
    essentialVector, change, pivotPairs, essentialIndices, reduced, trace]
  rw [Examples.hollow_boundary]
  decide +kernel

private theorem tied_output :
    (runWithRepresentatives Examples.tied).map (List.map summarize) = some
      [(⟨0, 0, .finite 1⟩, 1, some 3, [0, 1], some [3]),
        (⟨0, 0, .finite 1⟩, 2, some 4, [1, 2], some [4]),
        (⟨0, 0, .essential⟩, 0, none, [0], none)] := by
  simp only [runWithRepresentatives,
    (validBool_iff Examples.tied).mpr Examples.tied_valid, ↓reduceIte, Option.map_some, List.map_append, List.map_filterMap, List.map_map,
    Function.comp_def, representedOccurrences, pairedRepresentative, essentialRepresentative, pairedVector,
    essentialVector, change, pivotPairs, essentialIndices, reduced, trace]
  rw [Examples.tied_boundary]
  decide +kernel

private theorem empty_output : runWithRepresentatives [] = some [] := by decide +kernel

private theorem invalid_output : runWithRepresentatives [({0, 1}, 0)] = none := by decide +kernel

private theorem isolated_essential_H0 :
    (runWithRepresentatives Examples.delayed).map (List.map summarize) =
      some [(⟨0, 7, .essential⟩, 0, none, [0], none)] := by
  decide +kernel

private def filledH1 : Representative Examples.filled.length :=
  ⟨⟨1, 1, .finite 2⟩, 5, some 6, [3, 4, 5], some [6]⟩

private theorem filledH1_mem : filledH1 ∈ representedOccurrences Examples.filled := by
  apply pairedRepresentative_mem Examples.filled (5, 6)
  · rw [Examples.filled_pairs_raw]; decide +kernel
  · simp only [pairedRepresentative, pairOccurrence, pairedVector, reduced, change, trace]
    rw [Examples.filled_boundary]
    decide +kernel

private theorem filledH1_returned :
    ∃ out, runWithRepresentatives Examples.filled = some out ∧ filledH1 ∈ out :=
  ⟨representedOccurrences Examples.filled,
    (runWithRepresentatives_eq_some_iff _ _).mpr ⟨Examples.filled_valid, rfl⟩,
    filledH1_mem⟩

private def hollowH1 : Representative Examples.hollow.length :=
  ⟨⟨1, 1, .essential⟩, 5, none, [3, 4, 5], none⟩

private theorem hollowH1_mem : hollowH1 ∈ representedOccurrences Examples.hollow := by
  have hi : (5 : Fin Examples.hollow.length) ∈ essentialIndices Examples.hollow := by
    rw [Examples.hollow_essential_raw]; decide +kernel
  have he : essentialRepresentative Examples.hollow 5 = hollowH1 := by
    simp only [essentialRepresentative, essentialVector, change, trace]
    rw [Examples.hollow_boundary]
    decide +kernel
  rw [← he]
  exact essentialRepresentative_mem _ _ hi

private def duplicate0 : Representative Examples.filled.length :=
  ⟨⟨0, 0, .finite 1⟩, 1, some 3, [0, 1], some [3]⟩

private def duplicate1 : Representative Examples.filled.length :=
  ⟨⟨0, 0, .finite 1⟩, 2, some 4, [1, 2], some [4]⟩

private theorem duplicates_mem :
    duplicate0 ∈ representedOccurrences Examples.filled ∧
    duplicate1 ∈ representedOccurrences Examples.filled := by
  constructor
  · apply pairedRepresentative_mem Examples.filled (1, 3)
    · rw [Examples.filled_pairs_raw]; decide +kernel
    · simp only [pairedRepresentative, pairOccurrence, pairedVector, reduced, change, trace]
      rw [Examples.filled_boundary]
      decide +kernel
  · apply pairedRepresentative_mem Examples.filled (2, 4)
    · rw [Examples.filled_pairs_raw]; decide +kernel
    · simp only [pairedRepresentative, pairOccurrence, pairedVector, reduced, change, trace]
      rw [Examples.filled_boundary]
      decide +kernel

private theorem duplicates_identity :
    duplicate0.occurrence = duplicate1.occurrence ∧
    duplicate0.birthIndex ≠ duplicate1.birthIndex := by decide +kernel

open TDA.Simplicial TDA.Filtration

private noncomputable def filledCycle :=
  representedCycle Examples.filled Examples.filled_valid filledH1 filledH1_mem 6
    (by decide) (by intro j hj; cases Option.some.inj hj; decide)

private theorem filled_cycle_semantics :
    letI := faceFintype Examples.filled Examples.filled_valid
    simplicialClass Examples.filled Examples.filled_valid 1 6 filledCycle ≠ 0 ∧
      (prefixHomologyToAlive Examples.filled Examples.filled_valid 1 6
        (simplicialClass Examples.filled Examples.filled_valid 1 6 filledCycle)).1 =
        Pi.single ((finCongr (faceCount_eq_length Examples.filled Examples.filled_valid)).symm 5)
          (1 : ZMod 2) ∧
      (prefixChainEquiv (ZMod 2) (compatibleOrder Examples.filled Examples.filled_valid)
        6 1 filledCycle.1).1 = faceVector Examples.filled Examples.filled_valid
          (chainVector [3, 4, 5]) :=
by
  exact ⟨representedClass_nonzero Examples.filled Examples.filled_valid filledH1 filledH1_mem
      6 (by decide) (by intro j hj; cases Option.some.inj hj; decide),
    representedClass_coordinate Examples.filled Examples.filled_valid filledH1 filledH1_mem
      6 (by decide) (by intro j hj; cases Option.some.inj hj; decide),
    representedCycle_coordinates Examples.filled Examples.filled_valid filledH1 filledH1_mem
      6 (by decide) (by intro j hj; cases Option.some.inj hj; decide)⟩

private theorem filled_filling_semantics :
    letI := faceFintype Examples.filled Examples.filled_valid
    ∃ (hp : PrefixSupported 7 (chainVector ([6] : List (Fin Examples.filled.length))))
      (hd : Homogeneous (degree Examples.filled) 2 (chainVector [6])),
      TDA.Simplicial.boundary
        ((compatibleOrder Examples.filled Examples.filled_valid).prefixComplex 7) (ZMod 2) 1
        (simplicialChain Examples.filled Examples.filled_valid 2 7 (chainVector [6]) hp hd) =
        (simplicialCycle Examples.filled Examples.filled_valid 1 7 (chainVector [3, 4, 5])
          (returned_death_cycle _ Examples.filled_valid filledH1 filledH1_mem 6 rfl)).1 := by
  obtain ⟨b, hb, hp, hd, he⟩ := returned_simplicial_bounding Examples.filled
    Examples.filled_valid filledH1 filledH1_mem 6 rfl
  change some ([6] : List (Fin Examples.filled.length)) = some b at hb
  have hbe : b = [6] := Option.some.inj hb.symm
  subst b
  exact ⟨hp, hd, he⟩

private noncomputable def hollowCycle :=
  representedCycle Examples.hollow Examples.hollow_valid hollowH1 hollowH1_mem 6
    (by decide) (by intro j hj; cases hj)

private theorem hollow_cycle_semantics :
    letI := faceFintype Examples.hollow Examples.hollow_valid
    simplicialClass Examples.hollow Examples.hollow_valid 1 6 hollowCycle ≠ 0 ∧
      (prefixHomologyToAlive Examples.hollow Examples.hollow_valid 1 6
        (simplicialClass Examples.hollow Examples.hollow_valid 1 6 hollowCycle)).1 =
        Pi.single ((finCongr (faceCount_eq_length Examples.hollow Examples.hollow_valid)).symm 5)
          (1 : ZMod 2) :=
by
  exact ⟨representedClass_nonzero Examples.hollow Examples.hollow_valid hollowH1 hollowH1_mem
      6 (by decide) (by intro j hj; cases hj),
    representedClass_coordinate Examples.hollow Examples.hollow_valid hollowH1 hollowH1_mem
      6 (by decide) (by intro j hj; cases hj)⟩

private theorem duplicate_coordinates (r : Representative Examples.filled.length)
    (hr : r = duplicate0 ∨ r = duplicate1) :
    ∃ (hm : r ∈ representedOccurrences Examples.filled)
      (hb : r.birthIndex.val < 3)
      (hd : ∀ j, r.deathIndex = some j → 3 ≤ j.val),
    letI := faceFintype Examples.filled Examples.filled_valid
    simplicialClass Examples.filled Examples.filled_valid r.occurrence.degree 3
      (representedCycle Examples.filled Examples.filled_valid r hm 3 hb hd) ≠ 0 ∧
    (prefixHomologyToAlive Examples.filled Examples.filled_valid r.occurrence.degree 3
      (simplicialClass Examples.filled Examples.filled_valid r.occurrence.degree 3
        (representedCycle Examples.filled Examples.filled_valid r hm 3 hb hd))).1 =
      Pi.single ((finCongr (faceCount_eq_length Examples.filled Examples.filled_valid)).symm
        r.birthIndex) (1 : ZMod 2) := by
  have hm : r ∈ representedOccurrences Examples.filled := by
    rcases hr with rfl | rfl
    · exact duplicates_mem.1
    · exact duplicates_mem.2
  have hb : r.birthIndex.val < 3 := by rcases hr with rfl | rfl <;> decide
  have hd : ∀ j, r.deathIndex = some j → 3 ≤ j.val := by
    rcases hr with rfl | rfl <;> intro j hj <;> cases Option.some.inj hj <;> decide
  exact ⟨hm, hb, hd,
    representedClass_nonzero Examples.filled Examples.filled_valid r hm 3 hb hd,
    representedClass_coordinate Examples.filled Examples.filled_valid r hm 3 hb hd⟩

private theorem isolated_H0_semantics :
    ∃ (hm : essentialRepresentative Examples.delayed 0 ∈ representedOccurrences Examples.delayed),
    letI := faceFintype Examples.delayed Examples.delayed_valid
    simplicialClass Examples.delayed Examples.delayed_valid 0 1
      (representedCycle Examples.delayed Examples.delayed_valid
        (essentialRepresentative Examples.delayed 0) hm 1 (by decide)
        (by intro j hj; cases hj)) ≠ 0 := by
  have hm := essentialRepresentative_mem Examples.delayed 0 (by decide +kernel)
  exact ⟨hm, representedClass_nonzero Examples.delayed Examples.delayed_valid
    (essentialRepresentative Examples.delayed 0) hm 1 (by decide) (by intro j hj; cases hj)⟩

/-- Equal grades erase the value bar, although its index coordinate is alive at prefix 6. -/
private theorem tied_index_alive :
    AliveCoordinate (degree Examples.tied) (reduced Examples.tied) 1 6
      (5 : Fin Examples.tied.length) := by
  apply paired_alive Examples.tied Examples.tied_valid (5, 6)
  · simp only [pivotPairs, reduced, trace]
    rw [Examples.tied_boundary]
    decide +kernel
  · decide
  · decide

private theorem tied_index_class_nonzero :
    letI := faceFintype Examples.tied Examples.tied_valid
    simplicialClass Examples.tied Examples.tied_valid 1 6
      (columnCycle Examples.tied Examples.tied_valid 1 6 5 tied_index_alive) ≠ 0 :=
  columnClass_nonzero Examples.tied Examples.tied_valid 1 6 5 tied_index_alive

end TDA.Persistence.Reduction.FiniteInput.RepresentativeExamples
