import TDA.Mapper.GraphPLReebExtremal
import TDA.Mapper.GraphPLReebStabilityExamples
import TDA.Reeb.GraphCycleObstructionExamples

/-!
# Extremal vertex heights and the graph-PL Reeb distance: fixtures

X1. On the single edge, heights `(0, 1)` and `(-1, 1)` have the same maximum; the minimum
displacement gives distance exactly `1`.

X2. Vertical translation is exact on two disjoint edges (a disconnected graph) and on the
triangle (a cycle).

X3. The reversal `(0, 1)` to `(1, 0)` has equal maxima and equal minima, lower bound `0`, distance
`0` and `edist = 1`: the lower bounds are attained and the upper bound `edist` is not.

X4. On an empty vertex type the distance is `0`; the extremal statements need `Nonempty`.

X5. The single-vertex and `(0, 0)` to `(0, 1)` distances of the stability fixtures follow from the
extremal statements.
-/

namespace TDA.Mapper.GraphPLReebExtremalExamples

open Set SimpleGraph
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.RGraph
open TDA.Mapper.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph pointGraph twoEdges fst_eq_of_reachable)
open TDA.Reeb.Examples.GraphPLVertexPerturbation (flat tilted edist_flat_tilted)
open TDA.Mapper.GraphPLReebStabilityExamples (reversed twoEdgesHeight reversal_geometricInterleavingDistance)
open scoped ENNReal

noncomputable section

private theorem sup'_bool (f : Bool → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty f = max (f false) (f true) := by
  simp
  exact max_comm _ _

private theorem inf'_bool (f : Bool → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty f = min (f false) (f true) := by
  simp
  exact min_comm _ _

/-! ## X1. Minimum-only displacement -/

/-- Height `-1` at `false` and `1` at `true`. -/
def widened : Bool → ℝ := fun b => if b then 1 else -1

/-- The maxima of `tilted` and `widened` agree, so the supremum bound is `0`, and the minimum
displacement gives distance exactly `1`. -/
theorem tilted_widened_geometricInterleavingDistance :
    Finset.univ.sup' Finset.univ_nonempty tilted = Finset.univ.sup' Finset.univ_nonempty widened ∧
      geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
        (graphPLReebGraph edgeGraph widened) = 1 := by
  have hedist : edist tilted widened = 1 := by
    apply le_antisymm
    · refine edist_pi_le_iff.2 fun b => ?_
      cases b <;> norm_num [tilted, widened, edist_dist, Real.dist_eq]
    · calc (1 : ℝ≥0∞) = edist (tilted false) (widened false) := by
            norm_num [tilted, widened, edist_dist, Real.dist_eq]
        _ ≤ edist tilted widened := edist_le_pi_edist tilted widened false
  refine ⟨by simp [tilted, widened], ?_⟩
  rw [← hedist]
  apply geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_inf'
  rw [hedist, inf'_bool, inf'_bool]
  norm_num [tilted, widened]

/-! ## X2. Vertical translation -/

/-- On two disjoint edges, a graph that is not connected, vertical translation by `c` moves the
Reeb quotient by exactly `|c|`. -/
theorem twoEdges_translate_geometricInterleavingDistance (c : ℝ) :
    ¬ twoEdges.Connected ∧
      geometricInterleavingDistance (graphPLReebGraph twoEdges twoEdgesHeight)
        (graphPLReebGraph twoEdges fun v => twoEdgesHeight v + c) = ENNReal.ofReal |c| :=
  ⟨fun hc => Bool.false_ne_true
    (fst_eq_of_reachable (hc.preconnected (false, false) (true, false))),
    geometricInterleavingDistance_graphPLReebGraph_add_const c⟩

/-- On the triangle, a cycle, vertical translation by `c` moves the Reeb quotient by exactly
`|c|`. -/
theorem triangle_translate_geometricInterleavingDistance (c : ℝ) :
    ¬ TDA.Reeb.Examples.GraphCycleObstruction.triangle.IsAcyclic ∧
      geometricInterleavingDistance
        (graphPLReebGraph TDA.Reeb.Examples.GraphCycleObstruction.triangle fun v => (v : ℝ))
        (graphPLReebGraph TDA.Reeb.Examples.GraphCycleObstruction.triangle
          fun v => (v : ℝ) + c) = ENNReal.ofReal |c| :=
  ⟨TDA.Reeb.Examples.GraphCycleObstruction.triangle_not_isAcyclic,
    geometricInterleavingDistance_graphPLReebGraph_add_const c⟩

/-! ## X3. Upper bound not attained -/

/-- The reversal `(0, 1)` to `(1, 0)`: equal maxima and equal minima give lower bound `0`, which
is the distance, while `edist = 1`. -/
theorem reversal_extremal_bounds :
    Finset.univ.sup' Finset.univ_nonempty tilted =
        Finset.univ.sup' Finset.univ_nonempty reversed ∧
      Finset.univ.inf' Finset.univ_nonempty tilted =
        Finset.univ.inf' Finset.univ_nonempty reversed ∧
      edist tilted reversed = 1 ∧
      geometricInterleavingDistance (graphPLReebGraph edgeGraph tilted)
        (graphPLReebGraph edgeGraph reversed) = 0 := by
  obtain ⟨-, -, hedist, hdist⟩ := reversal_geometricInterleavingDistance
  exact ⟨by simp [tilted, reversed], by simp [tilted, reversed], hedist,
    hdist⟩

/-! ## X4. The empty vertex type -/

/-- On an empty vertex type there is no vertex, so the extremal heights are unavailable, and the
distance is `0`. -/
theorem empty_extremal (G : SimpleGraph Empty) (h g : Empty → ℝ) :
    ¬ Nonempty Empty ∧
      geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G g) = 0 :=
  ⟨fun ⟨e⟩ => e.elim, geometricInterleavingDistance_graphPLReebGraph_of_isEmpty (G := G) h g⟩

/-! ## X5. The stability fixtures from the extremal statements -/

/-- One vertex at heights `a` and `b`: the distance is `|a - b|`. -/
theorem point_geometricInterleavingDistance (a b : ℝ) :
    geometricInterleavingDistance (graphPLReebGraph pointGraph fun _ => a)
      (graphPLReebGraph pointGraph fun _ => b) = ENNReal.ofReal |a - b| := by
  have hab : edist (fun _ : Unit => a) (fun _ => b) = ENNReal.ofReal |a - b| := by
    rw [edist_pi_const, edist_dist, Real.dist_eq]
  rw [← hab]
  apply geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_sup'
  rw [hab]
  simp

/-- The single edge with heights `(0, 0)` and `(0, 1)`: the distance is `1`. -/
theorem flat_tilted_geometricInterleavingDistance :
    geometricInterleavingDistance (graphPLReebGraph edgeGraph flat)
      (graphPLReebGraph edgeGraph tilted) = 1 := by
  rw [← edist_flat_tilted]
  apply geometricInterleavingDistance_graphPLReebGraph_eq_edist_of_sup'
  rw [edist_flat_tilted, sup'_bool, sup'_bool]
  norm_num [flat, tilted]

end

end TDA.Mapper.GraphPLReebExtremalExamples
