import TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration
import TDA.Filtration.RationalAlpha.SuppliedCarrierExamples

set_option autoImplicit false

/-!
# Exact fixtures for supplied rational alpha grades

The certified trapezoid gives the full reference row set. The two edge
fixtures check both query orders on a non-Gabriel hull ray and an interior
segment. The face lookup of the interior edge reduces in the kernel through
`kernelGrade?`. A cocircular square gives a reference row on all four labels.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedGradeEnumerationExamples

open Set
open scoped BigOperators Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha TDA.Simplicial
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.EdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedCarrier

open TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration
open TDA.Filtration.RationalAlpha.SignedBoundaryExamples
open TDA.Filtration.RationalAlpha.SuppliedCarrierExamples (quadSites squareSplit)

theorem trapezoid_reference : suppliedGrades quadSites good = gradedFaces quadSites := by
  apply suppliedGrades_eq_reference (k := 1) quadSites cycle (fun _ _ h => h)
    good trapezoid_certificate
  · intro i
    exact subset_convexHull ℝ _ ⟨i,rfl⟩
  · decide +kernel
  · exact good_boundary
  · decide +kernel
  · right
    unfold NoFourIncircleZeros
    decide +kernel

theorem trapezoid_exact_rows :
    suppliedGrades quadSites good =
      {({0},0),({1},0),({2},0),({3},0),({0,1},4),({1,2},5/4),({2,3},9/4),
        ({0,3},1),({0,2},13/4),({0,1,2},65/16),({0,2,3},13/4)} := by
  rw [trapezoid_reference]
  decide +kernel

/-- The single triangle `0 1 2` on three labels. -/
def oneTriangle : Fin 1 → Fin 3 → Fin 3 := ![![0,1,2]]

theorem obtuse_exact_edge :
    edgeGrade? Examples.obtuse oneTriangle 0 1 = some 5 ∧
    edgeGrade? Examples.obtuse oneTriangle 1 0 = some 5 := by
  have hf : directedCenter? Examples.obtuse oneTriangle 0 1 = some (2,-1) := by
    unfold directedCenter?
    rw [occurrence_found oneTriangle (i := (0,0))
      (show occurrenceEdge oneTriangle (0,0) = (0,1) by decide +kernel)
      (by decide +kernel)]
    change centerAt? Examples.obtuse oneTriangle 0 = some (2,-1)
    decide +kernel
  have hb : directedCenter? Examples.obtuse oneTriangle 1 0 = none := by
    unfold directedCenter?
    rw [occurrence_absent oneTriangle (show ∀ j, occurrenceEdge oneTriangle j ≠ (1,0) by
      decide +kernel)]
    rfl
  constructor <;> simp only [edgeGrade?,hf,hb] <;> decide +kernel

/-- Sites A = (-2,0), B = (2,0), C = (0,1), D = (0,-5). -/
def innerSites : Fin 4 ↪ Point :=
  ⟨![(-2,0),(2,0),(0,1),(0,-5)],by decide +kernel⟩

/-- Triangles ABC and BAD share the interior edge AB. -/
def innerSplit : Fin 2 → Fin 3 → Fin 4 := ![![0,1,2],![1,0,3]]

theorem interior_nonGabriel_exact_edge :
    edgeGrade? innerSites innerSplit 0 1 = some (25/4) ∧
    edgeGrade? innerSites innerSplit 1 0 = some (25/4) := by
  have hf : directedCenter? innerSites innerSplit 0 1 = some (0,-3/2) := by
    unfold directedCenter?
    rw [occurrence_found innerSplit (i := (0,0))
      (show occurrenceEdge innerSplit (0,0) = (0,1) by decide +kernel)
      (by decide +kernel)]
    change centerAt? innerSites innerSplit 0 = some (0,-3/2)
    decide +kernel
  have hb : directedCenter? innerSites innerSplit 1 0 = some (0,-21/10) := by
    unfold directedCenter?
    rw [occurrence_found innerSplit (i := (1,0))
      (show occurrenceEdge innerSplit (1,0) = (1,0) by decide +kernel)
      (by decide +kernel)]
    change centerAt? innerSites innerSplit 1 = some (0,-21/10)
    decide +kernel
  constructor <;> simp only [edgeGrade?,hf,hb] <;> decide +kernel

/-- The face lookup returns the interior edge grade, and the enumerator emits its row. -/
theorem interior_nonGabriel_grade :
    grade? innerSites innerSplit {0,1} = some (25/4) ∧
    (({0,1} : Finset (Fin 4)), (25/4 : ℚ)) ∈ suppliedGrades innerSites innerSplit := by
  have hg : grade? innerSites innerSplit {0,1} = some (25/4) := by
    rw [← kernelGrade?_eq_grade?]
    decide +kernel
  refine ⟨hg, (mem_suppliedGrades innerSites innerSplit).2 ⟨?_, hg⟩⟩
  exact ⟨⟨0, by decide⟩, 0, by decide +kernel⟩

private theorem not_reference_of_missing_face {m n : ℕ} (p : Fin n ↪ Point)
    (tri : Fin m → Fin 3 → Fin n) {s : Finset (Fin n)} {q : ℚ}
    (hmiss : s ∉ labelComplex tri) (href : (s,q) ∈ gradedFaces p) :
    suppliedGrades p tri ≠ gradedFaces p := by
  intro he
  have hrow : (s,q) ∈ suppliedGrades p tri := he ▸ href
  exact hmiss ((mem_suppliedGrades p tri).1 hrow).1

theorem square_not_reference :
    suppliedGrades Examples.square squareSplit ≠ gradedFaces Examples.square := by
  apply not_reference_of_missing_face Examples.square squareSplit
    (s := ({0,1,2,3} : Finset (Fin 4))) (q := 2)
  · have heq : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel
    exact heq ▸ (SuppliedCarrierExamples.square_four_face_regression squareSplit).2
  · rw [Examples.square_grades]
    decide +kernel

end TDA.Filtration.RationalAlpha.SuppliedGradeEnumerationExamples
