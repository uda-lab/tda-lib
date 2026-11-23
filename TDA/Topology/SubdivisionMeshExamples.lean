import TDA.Topology.SubdivisionMesh
import TDA.Topology.RealizationExamples

/-! # Subdivision geometry of the triangle boundary inside the filled triangle -/

namespace TDA.Topology.SubdivisionMeshExamples

open TDA.Simplicial SubdivisionRealization Convexity RealizationExamples
noncomputable section
local notation "Label" => Fin 3
local notation "triangle" => (⊤ : PreAbstractSimplicialComplex Label)
local notation "boundaryIncl" => (le_top : triangleBoundary ≤ triangle)

/-- The first triangle corner as a singleton face. -/
def firstCorner : Finset Label := {0}

/-- The common edge joining labels zero and one. -/
def firstEdge : Finset Label := {0, 1}

/-- The flag of a corner inside the common edge. -/
def cornerEdgeFlag : Finset (Finset Label) := {firstCorner, firstEdge}

private theorem firstEdge_mem : firstEdge ∈ triangleBoundary :=
  NerveExamples.pairwiseFamily_has_all_edges.1
private theorem firstCorner_mem : firstCorner ∈ triangleBoundary :=
  (triangleBoundary.isRelLowerSet_faces firstEdge_mem).2 (by decide) (by decide)

private theorem pair_mem_subdivision {X : Type*} [Fintype X] [DecidableEq X] (N : PreAbstractSimplicialComplex X)
    (S T : Finset X) (hs : S ∈ N) (ht : T ∈ N) (hst : S ⊆ T) :
    {S, T} ∈ barycentricSubdivision N := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl <;> exact ⟨by assumption, by positivity⟩
  · intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;>
      first | exact Or.inl hst | exact Or.inr hst | exact Or.inl (Finset.Subset.refl _)

private theorem cornerEdgeFlag_mem : cornerEdgeFlag ∈ complex triangleBoundary 1 :=
  pair_mem_subdivision triangleBoundary firstCorner firstEdge firstCorner_mem firstEdge_mem (by decide)

private theorem edge_position (i : Label) :
    vertexPosition unitVertex 1 firstEdge i = if i = 0 ∨ i = 1 then 1 / 2 else 0 := by
  fin_cases i <;>
    norm_num [vertexPosition, barycenter, unitVertex, firstEdge, Finset.sum_insert, Pi.smul_apply, Pi.add_apply]

private theorem flag_position (i : Label) :
    vertexPosition unitVertex 2 cornerEdgeFlag i = if i = 0 then 3 / 4 else if i = 1 then 1 / 4 else 0 := by
  have hneq : firstCorner ≠ firstEdge := by decide
  have hc : cornerEdgeFlag.card = 2 := by decide
  change ((cornerEdgeFlag.card : ℝ)⁻¹ • ∑ u ∈ cornerEdgeFlag, vertexPosition unitVertex 1 u) i = _
  have hs : (∑ u ∈ cornerEdgeFlag, vertexPosition unitVertex 1 u) =
      vertexPosition unitVertex 1 firstCorner + vertexPosition unitVertex 1 firstEdge := by
    simp [cornerEdgeFlag, hneq]
  rw [hc, hs, Pi.smul_apply, Pi.add_apply, edge_position]
  fin_cases i <;> norm_num [vertexPosition, barycenter, unitVertex, firstCorner, Pi.smul_apply]

/-- The shared edge as a depth-one realization point on the boundary. -/
def edgePoint : Realization (complex triangleBoundary 1) :=
  vertexPoint _ firstEdge
    (singleton_mem_subdivision triangleBoundary firstEdge firstEdge_mem)

/-- The shared corner–edge flag as a depth-two realization point on the boundary. -/
def flagPoint : Realization (complex triangleBoundary 2) :=
  vertexPoint _ cornerEdgeFlag
    (singleton_mem_subdivision (complex triangleBoundary 1) cornerEdgeFlag cornerEdgeFlag_mem)

/-- On the boundary and after inclusion, the shared edge barycenter is `(1 / 2, 1 / 2, 0)`. -/
theorem triangle_edge_coordinates (i : Label) :
    (barycentricProjection triangleBoundary 1 edgePoint).val.weights i = (if i = 0 ∨ i = 1 then 1 / 2 else 0) ∧
    (barycentricProjection triangle 1 (Realization.incl (complex_mono boundaryIncl 1)
      edgePoint)).val.weights i = (if i = 0 ∨ i = 1 then 1 / 2 else 0) := by
  rw [← realize_unitVertex_apply, ← realize_unitVertex_apply]
  have e := congrFun (realize_vertexPoint triangleBoundary unitVertex 1 firstEdge
    (singleton_mem_subdivision triangleBoundary firstEdge firstEdge_mem)) i
  exact ⟨e.trans (edge_position i), e.trans (edge_position i)⟩

/-- The depth-two vertex of the corner–edge flag projects to `(3 / 4, 1 / 4, 0)` on both sides. -/
theorem triangle_flag_coordinates (i : Label) :
    (barycentricProjection triangleBoundary 2 flagPoint).val.weights i =
      (if i = 0 then 3 / 4 else if i = 1 then 1 / 4 else 0) ∧
    (barycentricProjection triangle 2 (Realization.incl (complex_mono boundaryIncl 2)
      flagPoint)).val.weights i =
      (if i = 0 then 3 / 4 else if i = 1 then 1 / 4 else 0) := by
  rw [← realize_unitVertex_apply, ← realize_unitVertex_apply]
  have e := congrFun (realize_vertexPoint triangleBoundary unitVertex 2 cornerEdgeFlag
    (singleton_mem_subdivision (complex triangleBoundary 1) cornerEdgeFlag cornerEdgeFlag_mem)) i
  exact ⟨e.trans (flag_position i), e.trans (flag_position i)⟩

private theorem boundary_size (s : Finset Label) (hs : s ∈ triangleBoundary) : s.card ≤ 2 := by
  have hn : s ≠ Finset.univ := by
    rintro rfl
    exact RealizationExamples.triangle_star_intersections.2.1
      ((Realization.interMember_nonempty_iff Finset.univ_nonempty).2 hs)
  have hcard := (Finset.card_lt_iff_ne_univ s).2 hn
  have h3 : s.card < 3 := by simpa using hcard
  omega

/-- At the shared flag the boundary and filled triangle give the corresponding dimension bounds. -/
theorem triangle_flag_closedStar : triangleBoundary < triangle ∧ cornerEdgeFlag ∈ complex triangleBoundary 1 ∧
    closedStarImage triangleBoundary unitVertex 2 cornerEdgeFlag ⊆ closedStarImage triangle unitVertex 2 cornerEdgeFlag ∧
    Metric.diam (closedStarImage triangleBoundary unitVertex 2 cornerEdgeFlag) ≤ 1 / 2 ∧
    Metric.diam (closedStarImage triangle unitVertex 2 cornerEdgeFlag) ≤ 8 / 9 := by
  have ha := (diam_le triangleBoundary unitVertex 1 (M := 1) zero_le_one boundary_size
    (fun _ _ i _ j _ => dist_unitVertex_le_one i j) 2).2 cornerEdgeFlag
  have hb := (diam_le triangle unitVertex 2 (M := 1) zero_le_one
    (fun s _ => by simpa using Finset.card_le_univ s)
    (fun _ _ i _ j _ => dist_unitVertex_le_one i j) 2).2 cornerEdgeFlag
  norm_num at ha hb
  exact ⟨RealizationExamples.triangle_star_intersections.1, cornerEdgeFlag_mem,
    closedStarImage_mono le_top unitVertex 2 cornerEdgeFlag, ha, hb⟩

end
end TDA.Topology.SubdivisionMeshExamples
