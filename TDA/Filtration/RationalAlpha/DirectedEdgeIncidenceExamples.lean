import TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
import TDA.Filtration.RationalAlpha.SignedBoundaryExamples

set_option autoImplicit false

/-!
# Directed edge counts in the exact rational trapezoid

The certified split along AC has one occurrence of each orientation on its diagonal.
The overlapping triangle list repeats B→C.
-/

namespace TDA.Filtration.RationalAlpha.DirectedEdgeIncidenceExamples

open Set
open TDA.Filtration.RationalAlpha (castPoint orient)
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.SignedBoundaryExamples
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence

private theorem quad_inj : Function.Injective quad := by
  change ∀ a b : Fin 4, quad a = quad b → a = b
  decide +kernel

private theorem quad_mem (a : Fin 4) : castPoint (quad a) ∈ siteHull quad cycle :=
  subset_convexHull ℝ _ ⟨a, rfl⟩

/-- Each certified hull side occurs once in the hull direction. Both diagonal directions occur in
distinct triangles. -/
theorem trapezoid_actual_counts :
    Function.Injective (occurrenceEdge good) ∧
    (∀ j, directedMultiplicity (occurrenceEdge good) (cycleEdges cycle j) = 1 ∧
      directedMultiplicity (occurrenceEdge good) (cycleEdges cycle j).swap = 0) ∧
    directedMultiplicity (occurrenceEdge good) (0, 2) = 1 ∧
    directedMultiplicity (occurrenceEdge good) (2, 0) = 1 ∧
    ∃ p q : Fin 2 × Fin 3, occurrenceEdge good p = (0, 2) ∧
      occurrenceEdge good q = (2, 0) ∧ p.1 ≠ q.1 := by
  have hccw : ∀ i, 0 < orient (quad (good i 0)) (quad (good i 1)) (quad (good i 2)) := by
    decide +kernel
  obtain ⟨hu, hb, hi⟩ := rational_edge_counts quad quad_inj cycle (fun _ _ h => h) good
    trapezoid_certificate hccw good_boundary
  refine ⟨hu, hb, hi (0, 2) (by decide +kernel) ?_⟩
  exact ⟨(1, 0), Or.inl rfl⟩

/-- The entire open AC diagonal lies in the interior of the certified trapezoid. -/
theorem trapezoid_open_AC_interior :
    openSegment ℝ (castPoint (quad 0)) (castPoint (quad 2)) ⊆ interior (siteHull quad cycle) := by
  apply nonhull_open_site_edge_subset_interior quad cycle (fun _ _ h => h)
    trapezoid_certificate quad_mem
  · decide +kernel
  · decide
  · decide +kernel

/-- The overlapping list ABC + BCD repeats the directed edge from B to C. -/
theorem overlap_repeated_BC : directedMultiplicity (occurrenceEdge overlap) (1, 2) = 2 := by
  decide +kernel

end TDA.Filtration.RationalAlpha.DirectedEdgeIncidenceExamples
