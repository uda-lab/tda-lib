import TDA.Mapper.GraphPLReebScaling
import TDA.Mapper.GraphPLReebMergeHeightExamples
import TDA.Mapper.GraphPLReebStabilityExamples

/-!
# Height scaling and branch-height bounds: examples

A point realizes the absolute scaling factor. Scaling the numeric merge tree by `1/2` and
applying the merge-height theorem directly give the same distance `1/2`. Reflection gives a
split-tree distance of `1` with zero extremal displacements. Beyond the exact range, branch
heights `1` and `3` below top height `4` give the bracket `[3/2, 2]`.

Zero scaling preserves the infinite distance between two disjoint edges and a single edge,
so exact homogeneity requires a nonzero scalar. The obstruction interval `(0, b - 2ε)` is
empty for `ε ≥ b/2`; this says nothing about the true distance at or beyond that threshold.
-/

namespace TDA.Mapper.GraphPLReebScalingExamples

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.RGraph TDA.Reeb.OpenInterval
open TDA.Mapper.GraphPL
open TDA.Mapper.GraphPLReebMergeHeightExamples
open TDA.Mapper.GraphPLReebStabilityExamples (point_geometricInterleavingDistance)
open TDA.Reeb.Examples.GraphRealization (pointGraph twoEdges edgeGraph)
open scoped NNReal ENNReal

/-- A point at two scaled heights realizes the factor `|s|`. -/
theorem point_scaled (a b : ℝ) {s : ℝ} (hs : s ≠ 0) :
    geometricInterleavingDistance (graphPLReebGraph pointGraph fun _ => s * a)
      (graphPLReebGraph pointGraph fun _ => s * b) = ENNReal.ofReal (|s| * |a - b|) := by
  rw [geometricInterleavingDistance_graphPLReebGraph_smul pointGraph (fun _ => a)
    pointGraph (fun _ => b) hs, point_geometricInterleavingDistance, ENNReal.ofReal_mul (abs_nonneg s)]

/-- The homogeneity route applied to the distance-one numeric merge tree gives `1/2`. -/
theorem mergeY_half_by_scaling :
    geometricInterleavingDistance
      (graphPLReebGraph mergeY (fun v => (1 / 2 : ℝ) * mergeHeights 2 4 v))
      (graphPLReebGraph mergeY (fun v => (1 / 2 : ℝ) * mergeHeights 3 4 v)) =
        ENNReal.ofReal (1 / 2) := by
  rw [geometricInterleavingDistance_graphPLReebGraph_smul mergeY (mergeHeights 2 4)
    mergeY (mergeHeights 3 4) (by norm_num : (1 / 2 : ℝ) ≠ 0), mergeY_numeric.1]
  norm_num

/-- The merge-height theorem gives the same scaled numeric distance directly. -/
theorem mergeY_half_direct :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 2))
      (graphPLReebGraph mergeY (mergeHeights (3 / 2) 2)) = ENNReal.ofReal (1 / 2) := by
  rw [geometricInterleavingDistance_mergeY (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  norm_num

/-- The scaling and direct routes evaluate the same distance to `1/2`. -/
theorem mergeY_half_routes_agree :
    geometricInterleavingDistance
      (graphPLReebGraph mergeY (fun v => (1 / 2 : ℝ) * mergeHeights 2 4 v))
      (graphPLReebGraph mergeY (fun v => (1 / 2 : ℝ) * mergeHeights 3 4 v)) =
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 2))
      (graphPLReebGraph mergeY (mergeHeights (3 / 2) 2)) :=
  mergeY_half_by_scaling.trans mergeY_half_direct.symm

/-- The maximum of the reflected numeric heights is `0`. -/
private theorem sup'_splitHeights {a : ℝ} (ha : 0 ≤ a) :
    Finset.univ.sup' Finset.univ_nonempty (splitHeights a 4) = 0 :=
  le_antisymm (Finset.sup'_le _ _ fun v _ => by
    fin_cases v <;> simp [splitHeights, mergeHeights]
    linarith)
    (by
      calc 0 = splitHeights a 4 0 := by simp [splitHeights, mergeHeights]
           _ ≤ _ := Finset.le_sup' (splitHeights a 4) (Finset.mem_univ 0))

/-- The minimum of the reflected numeric heights is `-4`. -/
private theorem inf'_splitHeights {a : ℝ} (ha : a ≤ 4) :
    Finset.univ.inf' Finset.univ_nonempty (splitHeights a 4) = -4 :=
  le_antisymm (Finset.inf'_le (splitHeights a 4) (Finset.mem_univ 3))
    (Finset.le_inf' _ _ fun v _ => by
      fin_cases v <;> simp [splitHeights, mergeHeights]
      linarith)

/-- Heights `(0,0,-2,-4)` and `(0,0,-3,-4)` have distance `1` and both extremal displacements `0`. -/
theorem splitY_numeric :
    geometricInterleavingDistance (graphPLReebGraph mergeY (splitHeights 2 4))
        (graphPLReebGraph mergeY (splitHeights 3 4)) = 1 ∧
      ENNReal.ofReal |Finset.univ.sup' Finset.univ_nonempty (splitHeights 2 4) -
        Finset.univ.sup' Finset.univ_nonempty (splitHeights 3 4)| = 0 ∧
      ENNReal.ofReal |Finset.univ.inf' Finset.univ_nonempty (splitHeights 2 4) -
        Finset.univ.inf' Finset.univ_nonempty (splitHeights 3 4)| = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [geometricInterleavingDistance_splitY (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [sup'_splitHeights (by norm_num), sup'_splitHeights (by norm_num)]
    simp
  · rw [inf'_splitHeights (by norm_num), inf'_splitHeights (by norm_num)]
    simp

/-- Apex heights `1` and `3`: distance in `[3/2,2]`; neither end is claimed to be the value. -/
theorem mergeY_beyond_twice :
    ENNReal.ofReal (3 / 2) ≤
        geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 4))
          (graphPLReebGraph mergeY (mergeHeights 3 4)) ∧
      geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 1 4))
        (graphPLReebGraph mergeY (mergeHeights 3 4)) ≤ ENNReal.ofReal 2 := by
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using
    geometricInterleavingDistance_mergeY_bounds (a := 1) (b := 3) (M := 4)
      (by norm_num) (by norm_num) (by norm_num)

/-- The exact merge-height value is also recovered by the bracket when `b ≤ 2a`. -/
theorem mergeY_eq_from_bracket {a b M : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b ≤ 2 * a) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
      (graphPLReebGraph mergeY (mergeHeights b M)) = ENNReal.ofReal (b - a) := by
  refine le_antisymm ?_ ?_
  · rw [← edist_mergeHeights hab.le]
    exact geometricInterleavingDistance_graphPLReebGraph_le_edist mergeY _ _
  · simpa only [min_eq_left (by linarith : b - a ≤ b / 2)] using
      ofReal_min_le_geometricInterleavingDistance_mergeY ha hab hbM

/-- Zero scaling leaves this distance infinite, whereas `0 * ⊤ = 0`: homogeneity fails. -/
theorem zero_scaling_fails (h : Bool × Bool → ℝ) (g : Bool → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph twoEdges (fun v => 0 * h v))
        (graphPLReebGraph edgeGraph (fun v => 0 * g v)) = ⊤ ∧
      geometricInterleavingDistance (graphPLReebGraph twoEdges (fun v => 0 * h v))
          (graphPLReebGraph edgeGraph (fun v => 0 * g v)) ≠
        ENNReal.ofReal |(0 : ℝ)| *
          geometricInterleavingDistance (graphPLReebGraph twoEdges h) (graphPLReebGraph edgeGraph g) := by
  rw [twoEdges_edge_geometricInterleavingDistance, twoEdges_edge_geometricInterleavingDistance]
  simp

/-- At `ε ≥ b/2` this obstruction interval is empty; no exact-distance claim follows. -/
theorem obstruction_interval_empty {b : ℝ} {ε : ℝ≥0} (hε : b / 2 ≤ ε) :
    Set.Ioo (0 : ℝ) (b - 2 * ε) = ∅ :=
  Set.Ioo_eq_empty_of_le (by linarith)

end TDA.Mapper.GraphPLReebScalingExamples
