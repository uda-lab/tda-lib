import TDA.Mapper.GraphPLReebMergeFold

/-!
# Exact merge-fold distance: fixtures

For apex heights `1` and `3` below top height `4`, the fold gives distance `3/2`, strictly below
the vertex-height budget `2`. At `b = M = 3`, the top edge is horizontal, the section still
selects the lower edge, and the distance is `3/2`. Reflection gives the same value for the split
tree. Above the top height, the clamped section has height `M`, not the input height.
-/

namespace TDA.Mapper.GraphPLReebMergeFoldExamples

open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.RGraph
open TDA.Reeb.GraphRealization
open TDA.Mapper.GraphPL
open scoped NNReal ENNReal

private def mergeYExampleD23 : mergeY.Dart :=
  ⟨(2, 3), (mergeY_adj 2 3).2 (by decide)⟩

@[simp] private theorem mergeYExampleD23_fst : mergeYExampleD23.fst = 2 := rfl
@[simp] private theorem mergeYExampleD23_snd : mergeYExampleD23.snd = 3 := rfl

/-- F1: the branch heights `1` and `3` below top height `4` give distance `3/2`. -/
theorem mergeY_beyond_twice_exact :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 4))
      (graphPLReebGraph mergeY (mergeHeights 3 4)) = ENNReal.ofReal (3 / 2) := by
  norm_num [geometricInterleavingDistance_mergeY_eq_min]

/-- F2: on the exact old range, the minimum formula recovers the branch-height value. -/
theorem mergeY_below_twice_matches_mergeY {a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (h2a : b ≤ 2 * a) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
      (graphPLReebGraph mergeY (mergeHeights b M)) =
      ENNReal.ofReal (b - a) := by
  rw [geometricInterleavingDistance_mergeY_eq_min ha hab hbM,
    min_eq_left (by linarith : b - a ≤ b / 2)]

/-- F2: the exact formula rederives the numeric distance `1` for apex heights `2` and `3`. -/
theorem mergeY_numeric_from_exact :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 2 4))
      (graphPLReebGraph mergeY (mergeHeights 3 4)) = 1 := by
  rw [geometricInterleavingDistance_mergeY_eq_min (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- F3: reflection gives distance `3/2` for the split heights with apices `1` and `3`. -/
theorem splitY_beyond_twice_exact :
    geometricInterleavingDistance (graphPLReebGraph mergeY (splitHeights 1 4))
      (graphPLReebGraph mergeY (splitHeights 3 4)) = ENNReal.ofReal (3 / 2) := by
  rw [geometricInterleavingDistance_splitY_eq_min (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- F4: at `b = M`, the section lands at vertex 2, edge `2 — 3` is horizontal, and the
distance remains `3/2`. The all-input lower-edge formula is `mergeSection_at_top_apex`. -/
theorem mergeY_top_boundary_fold :
    mergeSection 3 3 (by norm_num) le_rfl 3 = vertex mergeY 2 ∧
      mergeHeights 3 3 2 = mergeHeights 3 3 3 ∧
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 3))
        (graphPLReebGraph mergeY (mergeHeights 3 3)) = ENNReal.ofReal (3 / 2) ∧
      ∃ γ : Path (edgePoint mergeY mergeYExampleD23 (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval))
          (mergeSection 3 3 (by norm_num) le_rfl
            (plHeight mergeY (mergeHeights 3 3)
              (edgePoint mergeY mergeYExampleD23 (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)))),
        ∀ t, plHeight mergeY (mergeHeights 3 3) (γ t) = 3 := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · calc
      mergeSection 3 3 (by norm_num) le_rfl 3 =
      mergeSection 3 3 (by norm_num) le_rfl
            (3 * ((1 : unitInterval) : ℝ)) := by
        congr 1
        norm_num
      _ = edgePoint mergeY _ 1 := mergeSection_lower 3 3 (by norm_num) le_rfl 1
      _ = vertex mergeY 2 := by rw [edgePoint_one]; rfl
  · rw [geometricInterleavingDistance_mergeY_eq_min (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · have hstart :
        plHeight mergeY (mergeHeights 3 3)
          (edgePoint mergeY mergeYExampleD23 (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)) = 3 := by
      simp [GraphPL.plHeight_edgePoint, GraphPL.dartHeight, mergeHeights, mergeYExampleD23]
      norm_num
    obtain ⟨γ, hγ⟩ := exists_mergeSection_path 3 3 (by norm_num) le_rfl
      (edgePoint mergeY mergeYExampleD23 (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval))
    refine ⟨γ, ?_⟩
    intro t
    obtain ⟨hlo, hhi⟩ := (hγ t).1 (by rw [hstart])
    have hlo' : 3 ≤ plHeight mergeY (mergeHeights 3 3) (γ t) := by
      calc
        3 = plHeight mergeY (mergeHeights 3 3)
            (edgePoint mergeY mergeYExampleD23
              (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)) := hstart.symm
        _ ≤ plHeight mergeY (mergeHeights 3 3) (γ t) := hlo
    exact le_antisymm hhi hlo'

/-- N1: the identity-map vertex budget is `2`, strictly above the folded value `3/2`. -/
theorem mergeY_fold_improves_vertex_budget :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 4))
        (graphPLReebGraph mergeY (mergeHeights 3 4)) = ENNReal.ofReal (3 / 2) ∧
      edist (mergeHeights 1 4) (mergeHeights 3 4) = ENNReal.ofReal 2 ∧
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 4))
        (graphPLReebGraph mergeY (mergeHeights 3 4)) <
          edist (mergeHeights 1 4) (mergeHeights 3 4) := by
  refine ⟨mergeY_beyond_twice_exact, ?_, ?_⟩
  · rw [edist_mergeHeights (by norm_num)]
    norm_num
  · rw [mergeY_beyond_twice_exact, edist_mergeHeights (by norm_num)]
    norm_num

/-- N2: at input `3 > 2`, the clamped section has height `2`, so it does not preserve that
input height. -/
theorem mergeSection_clamps_above_top :
    plHeight mergeY (mergeHeights 2 2)
        (mergeSection 2 2 (by norm_num) le_rfl 3) = 2 ∧
      plHeight mergeY (mergeHeights 2 2)
        (mergeSection 2 2 (by norm_num) le_rfl 3) ≠ 3 := by
  have hclamp3 : Set.projIcc 0 (2 : ℝ) (by norm_num) 3 = Set.projIcc 0 2 (by norm_num) 2 := by
    rw [Set.projIcc_of_right_le (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3),
      Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 2) ⟨by norm_num, by norm_num⟩]
  have hsection :
      mergeSection 2 2 (by norm_num) le_rfl 3 =
        mergeSection 2 2 (by norm_num) le_rfl 2 := by
    rw [mergeSection_at_top_apex 2 (by norm_num) 3,
      mergeSection_at_top_apex 2 (by norm_num) 2, hclamp3]
  have hheight := plHeight_mergeSection 2 2 (by norm_num) le_rfl
    (y := 2) (by norm_num : (2 : ℝ) ∈ Set.Icc 0 2)
  rw [hsection, hheight]
  norm_num

end TDA.Mapper.GraphPLReebMergeFoldExamples
