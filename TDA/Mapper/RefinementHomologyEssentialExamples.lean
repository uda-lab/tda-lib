import TDA.Mapper.RefinementHomologyEssential
import TDA.Mapper.RefinementHomologyCappedTowerExamples
import TDA.Mapper.RefinementHomologyDiagramExamples
import TDA.Reeb.GraphCycleObstructionExamples

/-!
# Essential-bar fixtures

The triangle has no degree-one essential bar under a full cap despite its nontrivial loop:
capped centred diagrams record cycles only as finite bars, if at all. Constants on a point
and a two-label single edge have one degree-zero essential bar. Truncating the 4-cycle tower
before its full stage leaves an essential loop, while two disjoint edges have two essential
degree-zero bars and are at infinite bottleneck distance from the single edge. An empty grid
has no essential bars in any degree.
-/

namespace TDA.Mapper.RefinementHomologyEssentialExamples

open CategoryTheory CategoryTheory.Limits
open TDA.Topology TDA.Simplicial TDA.Persistence TDA.Persistence.FiniteConstructible
open TDA.Reeb TDA.Reeb.GraphRealization TDA.Reeb.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph twoEdges twoEdgesSide twoEdgesComponents)
open TDA.Reeb.Examples.GraphCycleObstruction
open TDA.Mapper.RefinementHomologyBarcodeExamples
open TDA.Mapper.RefinementHomologyDiagramExamples
open TDA.Mapper.RefinementHomologyCappedTowerExamples
open TDA.Reeb.Examples.GraphPL (C4 h4)
open scoped ENNReal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

local instance {X Y ι : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (U : ι → Set Y) : LinearOrder (ComponentIndex f U) := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/-- The triangle has a nontrivial loop but no degree-one essential bar under a full cap.
Capped centred diagrams record cycles only as finite bars, if at all. -/
theorem triangle_no_essential_loop (k : Type) [Field k] (h : Fin 3 → ℝ)
    (a s : ℝ) (ℓ : Unit → ℤ) {m : ℕ} (c : Fin (m + 1) ↪o ℝ) :
    (essentialPart (cappedCentredDiagram k (plHeight triangle h) a s ℓ c 1).points).card = 0 ∧
      ¬ SimplyConnectedSpace (Realization triangle) ∧ ¬ triangle.IsAcyclic :=
  ⟨card_essentialPart_cappedCentredDiagram_plHeight triangle h k a s ℓ c
    SimpleGraph.connected_top 1, triangle_not_simplyConnectedSpace, triangle_not_isAcyclic⟩

private instance {Y ι : Type} [TopologicalSpace Y] [Finite ι] (f : C(Unit, Y)) (U : ι → Set Y)
    (n : ℕ) : Finite (Face (mapper f U) n) := by
  have : ∀ i, Finite (ZerothHomotopy (PullbackSpace f U i)) := fun i =>
    have := RefinementHomologyExamples.subsingleton_zerothHomotopy (Z := PullbackSpace f U i)
    inferInstance
  have : Finite (ComponentIndex f U) :=
    inferInstanceAs (Finite (Σ i, ZerothHomotopy (PullbackSpace f U i)))
  exact faceFiniteOfTotalFinite _ n

/-- Both constant diagrams of the exact-distance fixture have one essential bar, from the cap
computation alone, without inspecting their endpoints. -/
theorem const_essential_counts (k : Type) [Field k] :
    (essentialPart (constDiagram k 0 quarterGrid).points).card = 1 ∧
      (essentialPart (constDiagram k (1 / 2) quarterGrid).points).card = 1 :=
  ⟨card_essentialPart_cappedCentredDiagram_zero k _ 0 1 zeroLabel quarterGrid,
    card_essentialPart_cappedCentredDiagram_zero k _ 0 1 zeroLabel quarterGrid⟩

/-- Heights `(0, 1)`, two labels and a uniform grid give one essential degree-zero bar. -/
theorem edge_essential_zero (k : Type) [Field k] :
    (essentialPart (cappedCentredDiagram k (plHeight edgeGraph h01) 0 1
      (fun w : Fin 2 => (w : ℤ)) edgeGrid 0).points).card = 1 :=
  card_essentialPart_cappedCentredDiagram_plHeight edgeGraph h01 k 0 1 _ edgeGrid
    SimpleGraph.connected_top 0

/-- The three-member stage of the loop tower, kept as the only observed stage. -/
private abbrev truncatedCover (_ : Fin 1) := loopCover 0

private def truncatedRefinement {i j : Fin 1} (_ : i ≤ j) :
    Refinement (truncatedCover i) (truncatedCover j) :=
  loopRefinement (q := 0) (t := 0) le_rfl

/-- Truncating before the full stage leaves one essential loop; the two-stage tower has none. -/
theorem truncated_loop_essential :
    (essentialPart (stepMapperDiagram ℚ (plHeight C4 h4) (uniformGrid 0 1 zero_lt_one 1)
      (padCover truncatedCover) (padRefinement truncatedCover truncatedRefinement) 1).points).card = 1 ∧
      (essentialPart (stepMapperDiagram ℚ (plHeight C4 h4) grid01 (padCover loopCover)
        (padRefinement loopCover loopRefinement) 1).points).card = 0 := by
  constructor
  · rw [card_essentialPart_stepMapperDiagram]
    exact loop_finrank_H1
  · rw [loop_stepMapperDiagram.2, Multiset.card_zero]

/-- Two disjoint edges have two essential degree-zero bars with a single full cap. -/
theorem twoEdges_essential_zero (k : Type) [Field k] (h : Bool × Bool → ℝ)
    (a s : ℝ) (ℓ : Unit → ℤ) {m : ℕ} (c : Fin (m + 1) ↪o ℝ) :
    (essentialPart (cappedCentredDiagram k (plHeight twoEdges h) a s ℓ c 0).points).card = 2 := by
  rw [card_essentialPart_cappedCentredDiagram_plHeight_zero_of_unique,
    Nat.card_congr twoEdgesSide, Nat.card_eq_fintype_card, Fintype.card_bool]

/-- The disconnected two-edge input and the connected single-edge input have diagrams at
infinite bottleneck distance in degree zero. -/
theorem twoEdges_edge_bottleneck_eq_top (k : Type) [Field k] (h : Bool × Bool → ℝ) :
    bottleneck (cappedCentredDiagram k (plHeight twoEdges h) 0 1 zeroLabel quarterGrid 0)
      (cappedCentredDiagram k (plHeight edgeGraph h01) 0 1 zeroLabel quarterGrid 0) = ⊤ := by
  rw [bottleneck_eq_top_iff, twoEdges_essential_zero,
    card_essentialPart_cappedCentredDiagram_plHeight_zero_of_unique,
    ← Nat.card_congr (componentsEquiv edgeGraph)]
  have : Subsingleton (ZerothHomotopy (Realization edgeGraph)) := by
    have : PathConnectedSpace (Realization edgeGraph) :=
      (connected_iff_pathConnectedSpace edgeGraph).mp SimpleGraph.connected_top
    infer_instance
  have : Nonempty (ZerothHomotopy (Realization edgeGraph)) := ⟨ZerothHomotopy.mk (vertex edgeGraph false)⟩
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
  decide

/-- With no grid values, the last stage is the empty initial stage in every degree. -/
theorem emptyGrid_essential_count {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : Type) [Field k] (f : C(X, Y)) (n : ℕ) :
    (essentialPart (stepMapperDiagram k f emptyGrid emptyStage emptyStageRefinement n).points).card =
      0 := by
  rw [card_essentialPart_stepMapperDiagram]
  have := ModuleCat.subsingleton_of_isZero
    (isZero_simplicialHomology_mapper_of_isEmpty k f (emptyStage (Fin.last 0)) n)
  exact Module.finrank_zero_of_subsingleton

end
end TDA.Mapper.RefinementHomologyEssentialExamples
