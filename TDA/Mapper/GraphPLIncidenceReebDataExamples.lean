import TDA.Mapper.GraphPLIncidenceReebData
import TDA.Mapper.GraphPLIncidenceExamples
import TDA.Reeb.FiniteDataGraph

/-!
# The executed incidence lists as graph-PL Reeb data: fixtures

* `empty`: the realization of the executed lists is empty.
* `triangle`: two distinct listed edges over the gap have the same left and the same right
  endpoint; both are elements of the edge type, and the forgetful map to the simple incidence
  graph is not injective.
* `crossing`: the crossing cell at the middle level is the left endpoint of the upper listed
  edge, and the comparison sends it to the edge `{0, 1}` of the actual graph as a crossing edge.
* `diamond`: the Reeb quotient of the graph-PL height of the four-cycle is the realization of
  its executed lists.
-/

set_option autoImplicit false

namespace TDA.Mapper.GraphPL.GraphPLIncidenceReebDataExamples

open CategoryTheory TDA.Reeb TDA.Reeb.RGraph HeightGraph GraphPLIncidenceExamples

theorem empty_valid : empty.Valid := by decide +kernel

/-- With no vertex the realization of the executed lists is empty. -/
theorem empty_isEmpty_realization :
    IsEmpty ((CylinderPresentation.ofFiniteData (empty.reebData empty_valid)).Realization
      empty.criticalValues) :=
  isEmpty_realization empty empty_valid

theorem triangle_valid : triangle.Valid := by decide +kernel

/-- The gap of the triangle. -/
def triangleGap : Fin triangle.gapCount := ⟨0, by decide +kernel⟩

/-- The listed edge `0 — 1` of the triangle. -/
def triangleEdgeOne : (triangle.reebData triangle_valid).E triangleGap :=
  ⟨((0, 1), .inl 0, .inl 1), by decide +kernel⟩

/-- The listed edge `0 — 2` of the triangle. -/
def triangleEdgeTwo : (triangle.reebData triangle_valid).E triangleGap :=
  ⟨((0, 2), .inl 0, .inl 1), by decide +kernel⟩

/-- The two listed edges are different elements of the edge type with the same endpoints. -/
theorem triangle_parallel_edges :
    triangleEdgeOne ≠ triangleEdgeTwo ∧
      (triangle.reebData triangle_valid).left triangleGap triangleEdgeOne =
        (triangle.reebData triangle_valid).left triangleGap triangleEdgeTwo ∧
      (triangle.reebData triangle_valid).right triangleGap triangleEdgeOne =
        (triangle.reebData triangle_valid).right triangleGap triangleEdgeTwo :=
  ⟨fun h => absurd (congrArg (fun z => z.1.1.2) h) (by decide), Subtype.ext rfl,
    Subtype.ext rfl⟩

/-- Forgetting parallel edges identifies them: the simple incidence graph has one edge for the
two listed edges. -/
theorem triangle_incidenceEdgeSet_not_injective :
    ¬ Function.Injective (triangle.reebData triangle_valid).incidenceEdgeSet := by
  rw [FiniteReebData.incidenceEdgeSet_injective_iff]
  intro h
  exact triangle_parallel_edges.1
    (h triangleGap _ _ triangle_parallel_edges.2.1 triangle_parallel_edges.2.2)

theorem crossing_valid : crossing.Valid := by decide +kernel

/-- The upper gap of `crossing`. -/
def crossingUpperGap : Fin crossing.gapCount := ⟨1, by decide +kernel⟩

/-- The listed edge over the upper gap of `crossing`. -/
def crossingUpperEdge : (crossing.reebData crossing_valid).E crossingUpperGap :=
  ⟨((0, 1), .inr (0, 1), .inl 1), by decide +kernel⟩

/-- Its left endpoint is the crossing cell and its right endpoint the component of vertex `1`. -/
theorem crossing_upper_ends :
    ((crossing.reebData crossing_valid).left crossingUpperGap crossingUpperEdge).1 =
        .inr (0, 1) ∧
      ((crossing.reebData crossing_valid).right crossingUpperGap crossingUpperEdge).1 =
        .inl 1 :=
  ⟨rfl, rfl⟩

/-- At the middle level of `crossing`, the crossing cell goes to the edge `{0, 1}` of the actual
graph as a crossing edge. -/
theorem crossing_hom_v_inr :
    ∃ he hc, ((crossing.reebDataIso crossing_valid).hom.v crossingUpperGap.castSucc
        ⟨.inr (0, 1), by decide +kernel⟩ :
          LevelVertex (crossing.graph crossing_valid) crossing.realHeight
            (crossing.level crossingUpperGap.castSucc : ℝ)) =
      Sum.inr ⟨⟨s(0, 1), he⟩, hc⟩ :=
  crossing.reebDataIso_hom_v_inr crossing_valid crossingUpperGap.castSucc (0, 1)
    (by decide +kernel)

theorem diamond_valid : diamond.Valid := by decide +kernel

/-- The Reeb quotient of the graph-PL height of the four-cycle is the realization of its
executed incidence lists. -/
noncomputable def diamond_reebQuotientIso :
    (ReebQuotient.quotientFunctor ℝ).obj
        (graphPLOver (diamond.graph diamond_valid) diamond.realHeight) ≅
      toOver diamond.criticalValues (diamond.reebData diamond_valid) :=
  diamond.reebQuotientIso diamond_valid

end TDA.Mapper.GraphPL.GraphPLIncidenceReebDataExamples
