import TDA.Filtration.RationalAlpha.SuppliedStages
import TDA.Filtration.RationalAlpha.SuppliedGradeEnumerationExamples

set_option autoImplicit false

/-!
# Exact cutoff fixtures for supplied Alpha stages

The certified trapezoid has a shared entry grade for AC and ACD. The rational
hull check supplies the certificate for the all-grade stage identification of
the trapezoid and of an input whose interior edge is not Gabriel; that edge
enters the actual Alpha filtration at `25/4`, above its Gabriel value `4`. The
cocircular square has a four-label actual Alpha face at grade 2, while the
supplied split omits it at every grade.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedStagesExamples

open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration
open TDA.Filtration.RationalAlpha.SuppliedGradeEnumerationExamples
open TDA.Filtration.RationalAlpha.SuppliedCarrierExamples
open TDA.Filtration.RationalAlpha.SignedBoundaryExamples
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedStages
open scoped Matrix

private def quadSites : Fin 4 ↪ Point := ⟨quad, by
  change ∀ a b : Fin 4, quad a = quad b → a = b
  decide +kernel⟩

/-- Exact closed stages below zero, at zero, before AC, at the AC/ACD tie, and at ABC. -/
theorem trapezoid_exact_stages :
    stageTable (suppliedGrades quadSites good) (-1) = ∅ ∧
    stageTable (suppliedGrades quadSites good) 0 = {{0}, {1}, {2}, {3}} ∧
    stageTable (suppliedGrades quadSites good) 3 =
      {{0}, {1}, {2}, {3}, {0,3}, {1,2}, {2,3}} ∧
    stageTable (suppliedGrades quadSites good) (13/4) =
      {{0}, {1}, {2}, {3}, {0,3}, {1,2}, {2,3}, {0,2}, {0,2,3}} ∧
    stageTable (suppliedGrades quadSites good) (65/16) =
      {{0}, {1}, {2}, {3}, {0,3}, {1,2}, {2,3}, {0,2}, {0,2,3}, {0,1}, {0,1,2}} := by
  rw [show suppliedGrades quadSites good = _ from trapezoid_exact_rows]
  decide +kernel

/-- Every real threshold gives the same stage membership for the two tied trapezoid faces. -/
theorem trapezoid_shared_cutoff (t : ℝ) :
    (({0,2} : Finset (Fin 4)) ∈ Alpha.complex (realSites quadSites) t ↔ (13 : ℝ)/4 ≤ t) ∧
    (({0,2,3} : Finset (Fin 4)) ∈ Alpha.complex (realSites quadSites) t ↔ (13 : ℝ)/4 ≤ t) := by
  have hreference : suppliedGrades quadSites good = gradedFaces quadSites := trapezoid_reference
  have hcut (s : Finset (Fin 4)) (hrow : (s, 13/4) ∈ suppliedGrades quadSites good) :
      s ∈ Alpha.complex (realSites quadSites) t ↔ ((13/4 : ℚ) : ℝ) ≤ t := by
    change s ∈ Alpha.complexFiltration (realSites quadSites) t ↔ _
    rw [reference_hasGradeTable, ← hreference, ← mem_realStageTable_iff]
    exact supplied_row_cutoff quadSites good hrow t
  have hAC : (({0,2} : Finset (Fin 4)), 13/4) ∈ suppliedGrades quadSites good := by
    rw [show suppliedGrades quadSites good = _ from trapezoid_exact_rows]
    decide +kernel
  have hACD : (({0,2,3} : Finset (Fin 4)), 13/4) ∈ suppliedGrades quadSites good := by
    rw [show suppliedGrades quadSites good = _ from trapezoid_exact_rows]
    decide +kernel
  exact ⟨by simpa using hcut _ hAC, by simpa using hcut _ hACD⟩

private theorem trapezoid_hull_check :
    cornerHullCheck (quadSites : Fin 4 → Point) cycle = true := by
  decide +kernel

/-- With the hull certificate from `cornerHullCheck`, the supplied trapezoid rows give
actual Alpha membership at every real squared grade. -/
theorem trapezoid_checked_stages (s : Finset (Fin 4)) (t : ℝ) :
    s ∈ realStageTable (suppliedGrades quadSites good) t ↔
      s ∈ Alpha.complex (realSites quadSites) t :=
  supplied_realStage_iff quadSites (k := 1) cycle (fun _ _ h => h) good
    (cornerHullCheck_sound _ _ trapezoid_hull_check).1
    ((cornerHullCheck_true_iff _ _).1 trapezoid_hull_check).2
    (by decide +kernel) good_boundary (by decide +kernel)
    (Or.inr (by unfold NoFourIncircleZeros; decide +kernel)) s t

/-- Sites A = (-2,0), B = (2,0), C = (0,1), D = (0,-5). -/
private def innerSites : Fin 4 ↪ Point := ⟨![(-2,0),(2,0),(0,1),(0,-5)], by decide +kernel⟩

/-- Triangles ABC and BAD share the interior edge AB. -/
private def innerSplit : Fin 2 → Fin 3 → Fin 4 := ![![0,1,2],![1,0,3]]

/-- The strict hull corners A, D, B, C. -/
private def innerHull : Fin 4 → Fin 4 := ![0,3,1,2]

private theorem inner_hull_check :
    cornerHullCheck (innerSites : Fin 4 → Point) innerHull = true := by
  decide +kernel

private theorem inner_boundary :
    (∑ i, ∑ j, signedEdge (occurrenceEdge innerSplit (i,j))) =
      ∑ j, signedEdge (cycleEdges innerHull j) := by
  have hL : (∑ i, ∑ j, signedEdge (occurrenceEdge innerSplit (i,j))) =
      signedEdge ((0 : Fin 4), (1 : Fin 4)) + signedEdge (1,2) + signedEdge (2,0) +
        (signedEdge (1,0) + signedEdge (0,3) + signedEdge (3,1)) := by
    simp only [Fin.sum_univ_two, Fin.sum_univ_three]
    rfl
  have hR : (∑ j, signedEdge (cycleEdges innerHull j)) =
      signedEdge ((0 : Fin 4), (3 : Fin 4)) + signedEdge (3,1) + signedEdge (1,2) +
        signedEdge (2,0) :=
    Fin.sum_univ_four _
  rw [hL, hR]
  simp only [signedEdge, Prod.swap_prod_mk]
  abel

/-- With the hull certificate from `cornerHullCheck`, the supplied rows of the input with
interior edge AB give actual Alpha membership at every real squared grade. -/
theorem inner_checked_stages (s : Finset (Fin 4)) (t : ℝ) :
    s ∈ realStageTable (suppliedGrades innerSites innerSplit) t ↔
      s ∈ Alpha.complex (realSites innerSites) t :=
  supplied_realStage_iff innerSites (k := 1) innerHull (by decide +kernel) innerSplit
    (cornerHullCheck_sound _ _ inner_hull_check).1
    ((cornerHullCheck_true_iff _ _).1 inner_hull_check).2
    (by decide +kernel) inner_boundary (by decide +kernel)
    (Or.inr (by unfold NoFourIncircleZeros; decide +kernel)) s t

private theorem inner_ab_face : ({0,1} : Finset (Fin 4)) ∈ labelComplex innerSplit :=
  ⟨⟨0, by decide⟩, 0, by decide +kernel⟩

private theorem inner_ab_grade : grade? innerSites innerSplit {0,1} = some (25/4) := by
  rw [← kernelGrade?_eq_grade?]
  decide +kernel

private theorem inner_ab_row_iff :
    (({0,1} : Finset (Fin 4)), (25/4 : ℚ)) ∈ suppliedGrades innerSites innerSplit ↔
      (({0,1} : Finset (Fin 4)) ∈ labelComplex innerSplit ∧
        grade? innerSites innerSplit {0,1} = some (25/4)) :=
  mem_suppliedGrades innerSites innerSplit

private theorem inner_ab_row :
    (({0,1} : Finset (Fin 4)), (25/4 : ℚ)) ∈ suppliedGrades innerSites innerSplit :=
  inner_ab_row_iff.2 ⟨inner_ab_face, inner_ab_grade⟩

/-- The interior edge AB has squared length 16, so its Gabriel value is `4`. It enters the
actual Alpha complex exactly at the squared grade `25/4`. -/
theorem inner_nonGabriel_cutoff (t : ℝ) :
    ({0,1} : Finset (Fin 4)) ∈ Alpha.complex (realSites innerSites) t ↔ (25 : ℝ)/4 ≤ t := by
  have hcut : ({0,1} : Finset (Fin 4)) ∈ realStageTable (suppliedGrades innerSites innerSplit) t ↔
      ((25/4 : ℚ) : ℝ) ≤ t :=
    supplied_row_cutoff innerSites innerSplit inner_ab_row t
  rw [← inner_checked_stages, hcut]
  norm_num

private def squareSplit : Fin 2 → Fin 3 → Fin 4 := ![![0,1,3],![0,3,2]]

/-- The square has an actual four-label face at grade 2 and the supplied split omits it. -/
theorem square_stage_obstruction :
    (Finset.univ : Finset (Fin 4)) ∈ Alpha.complex (realSites Examples.square) 2 ∧
    ∀ t : ℝ, (Finset.univ : Finset (Fin 4)) ∉
      realStageTable (suppliedGrades Examples.square squareSplit) t := by
  refine ⟨?_, ?_⟩
  · change (Finset.univ : Finset (Fin 4)) ∈ Alpha.complexFiltration (realSites Examples.square) 2
    apply (reference_hasGradeTable Examples.square _ _).2
    refine ⟨2, ?_, by norm_num⟩
    rw [Examples.square_grades]
    decide +kernel
  · intro t
    rw [mem_realStageTable_iff]
    rintro ⟨q, hq, _⟩
    exact (SuppliedCarrierExamples.square_four_face_regression squareSplit).2
      ((mem_suppliedGrades Examples.square squareSplit).1 hq).1

end TDA.Filtration.RationalAlpha.SuppliedStagesExamples
