import TDA.Mapper.GraphPLReebMergeHeight
import TDA.Reeb.GeometricSmoothInterleaving
import TDA.Reeb.GraphRealizationExamples

/-!
# The Reeb distance of a merge-height change: fixtures

N1. Heights `(0, 0, 2, 4)` against `(0, 0, 3, 4)` on the merge tree: the graph-PL Reeb quotients
are at geometric distance exactly `1`, which is `edist` of the heights. The extremal-height bound
is `0`, and so is the Hausdorff distance of the height ranges, both equal to `[0, 4]`.

N2. Heights `(0, 0, a, M)` against `(0, 0, 0, M)` for `0 < a ≤ M`, at `ε = a` and `I = (0, a/2)`:
the first incidence components have two classes at `I`, the second have one at `T_ε I`, but the
restriction of the first from `I` to `T_ε T_ε I = (-2a, 5a/2)` is not injective, and the vertex
budget `a` gives an `a`-interleaving. The injectivity hypothesis of the cardinality obstruction
cannot be dropped.

N3. Two disjoint edges and a single edge have different numbers of connected components, so their
graph-PL Reeb quotients are at geometric distance `⊤` for all heights.
-/

namespace TDA.Mapper.GraphPLReebMergeHeightExamples

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.RGraph TDA.Reeb.OpenInterval
open TDA.Mapper.GraphPL
open TDA.Reeb.Examples.GraphRealization (twoEdges twoEdgesSide edgeGraph)
open scoped NNReal ENNReal

/-! ## N1. A numeric merge-height change -/

/-- The merge tree is connected. -/
theorem mergeY_connected : mergeY.Connected := by
  have hr : ∀ u : Fin 4, mergeY.Reachable u 2 := by
    intro u
    fin_cases u
    · exact ((mergeY_adj 0 2).2 (by decide)).reachable
    · exact ((mergeY_adj 1 2).2 (by decide)).reachable
    · exact Reachable.refl _
    · exact ((mergeY_adj 3 2).2 (by decide)).reachable
  exact ⟨fun u v => (hr u).trans (hr v).symm⟩

/-- For `0 ≤ a ≤ 4`, the heights `(0, 0, a, 4)` attain exactly `[0, 4]`. -/
theorem range_plHeight_mergeHeights {a : ℝ} (ha : 0 ≤ a) (ha4 : a ≤ 4) :
    range (plHeight mergeY (mergeHeights a 4)) = Icc 0 4 := by
  have := (connected_iff_pathConnectedSpace mergeY).1 mergeY_connected
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine plHeight_mem_Icc_of_forall (fun v => ?_) x
    fin_cases v <;> simp [mergeHeights, ha, ha4]
  · exact (isPreconnected_range (plHeight mergeY (mergeHeights a 4)).continuous).Icc_subset
      ⟨vertex mergeY 0, rfl⟩ ⟨vertex mergeY 3, rfl⟩

/-- Moving the apex from `2` to `3` below the top vertex at `4`: distance exactly `1`, equal to
`edist` of the heights, while the extremal-height bound and the height-range bound are `0`. -/
theorem mergeY_numeric :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights 2 4))
        (graphPLReebGraph mergeY (mergeHeights 3 4)) = 1 ∧
      edist (mergeHeights 2 4) (mergeHeights 3 4) = 1 ∧
      max (ENNReal.ofReal |Finset.univ.sup' Finset.univ_nonempty (mergeHeights 2 4) -
          Finset.univ.sup' Finset.univ_nonempty (mergeHeights 3 4)|)
        (ENNReal.ofReal |Finset.univ.inf' Finset.univ_nonempty (mergeHeights 2 4) -
          Finset.univ.inf' Finset.univ_nonempty (mergeHeights 3 4)|) = 0 ∧
      Metric.hausdorffEDist (heightRange (graphPLReebGraph mergeY (mergeHeights 2 4)))
        (heightRange (graphPLReebGraph mergeY (mergeHeights 3 4))) = 0 := by
  refine ⟨?_, ?_, max_ofReal_abs_sub_mergeHeights_eq_zero (by norm_num) (by norm_num)
    (by norm_num), ?_⟩
  · rw [geometricInterleavingDistance_mergeY (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [edist_mergeHeights (by norm_num)]
    norm_num
  · rw [heightRange_graphPLReebGraph, heightRange_graphPLReebGraph,
      range_plHeight_mergeHeights (by norm_num) (by norm_num),
      range_plHeight_mergeHeights (by norm_num) (by norm_num)]
    exact Metric.hausdorffEDist_self

/-! ## N2. The injectivity hypothesis cannot be dropped -/

/-- At `ε = a` and `I = (0, a/2)`, the counts satisfy `1 < 2`, but the restriction from `I` to
`T_ε T_ε I` is not injective and an `a`-interleaving exists. -/
theorem mergeY_injective_needed {a M : ℝ} (ha : 0 < a) (haM : a ≤ M) :
    Nat.card ((cellComponentFunctor mergeY (mergeHeights a M)).obj (ioo 0 (a / 2))) = 2 ∧
      Nat.card ((cellComponentFunctor mergeY (mergeHeights 0 M)).obj
        (thicken ⟨a, ha.le⟩ (ioo 0 (a / 2)))) = 1 ∧
      ¬ Function.Injective ((cellComponentFunctor mergeY (mergeHeights a M)).map
        (homOfLE ((le_thicken ⟨a, ha.le⟩ (ioo 0 (a / 2))).trans
          (le_thicken ⟨a, ha.le⟩ (thicken ⟨a, ha.le⟩ (ioo 0 (a / 2))))))) ∧
      Nonempty (Interleaving ⟨a, ha.le⟩ (cellComponentFunctor mergeY (mergeHeights a M))
        (cellComponentFunctor mergeY (mergeHeights 0 M))) := by
  have hc : (0 : ℝ) < a / 2 := by linarith
  have hthick : thicken ⟨a, ha.le⟩ (ioo 0 (a / 2)) = ioo (0 - a) (a / 2 + a) := thicken_ioo hc _
  have hthick₂ : thicken ⟨a, ha.le⟩ (thicken ⟨a, ha.le⟩ (ioo 0 (a / 2))) =
      ioo (0 - a - a) (a / 2 + a + a) := by
    rw [hthick]
    exact thicken_ioo (by linarith) _
  have htwo := card_cellComponents_mergeHeights_ioo (M := M) hc (by linarith) haM
  refine ⟨htwo, card_cellComponents_mergeHeights_eq_one (by rw [hthick]; constructor <;> linarith),
    fun hinj => ?_, ⟨((vertexHeightInterleaving mergeY (ε := ⟨a, ha.le⟩) fun v => ?_).isoLeft
      (intervalComponentsIso _ _)).isoRight (intervalComponentsIso _ _)⟩⟩
  · have hone : Nat.card ((cellComponentFunctor mergeY (mergeHeights a M)).obj
        (thicken ⟨a, ha.le⟩ (thicken ⟨a, ha.le⟩ (ioo 0 (a / 2))))) = 1 :=
      card_cellComponents_mergeHeights_eq_one (by rw [hthick₂]; constructor <;> linarith)
    have : Finite ((cellComponentFunctor mergeY (mergeHeights a M)).obj
        (thicken ⟨a, ha.le⟩ (thicken ⟨a, ha.le⟩ (ioo 0 (a / 2))))) := by
      change Finite (cellGraph _ _ _).ConnectedComponent
      infer_instance
    have hle := Nat.card_le_card_of_injective _ hinj
    change Nat.card (cellGraph _ _ _).ConnectedComponent ≤ _ at hle
    rw [htwo, hone] at hle
    exact absurd hle (by decide)
  · change |mergeHeights a M v - mergeHeights 0 M v| ≤ a
    fin_cases v <;> simp [mergeHeights, abs_of_pos ha, ha.le]

/-! ## N3. Different numbers of components -/

/-- Two disjoint edges and a single edge have graph-PL Reeb quotients at distance `⊤`. -/
theorem twoEdges_edge_geometricInterleavingDistance (h : Bool × Bool → ℝ) (g : Bool → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph twoEdges h) (graphPLReebGraph edgeGraph g) =
      ⊤ := by
  apply geometricInterleavingDistance_graphPLReebGraph_eq_top_of_card_ne
  have hedge : Nat.card edgeGraph.ConnectedComponent = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨preconnected_top.subsingleton_connectedComponent,
      ⟨edgeGraph.connectedComponentMk false⟩⟩
  rw [Nat.card_congr twoEdgesSide, hedge, Nat.card_eq_fintype_card, Fintype.card_bool]
  decide

end TDA.Mapper.GraphPLReebMergeHeightExamples
