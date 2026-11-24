import TDA.Filtration.RationalAlpha.SuppliedStages
import TDA.Filtration.RationalAlpha.SuppliedGradeEnumerationExamples

set_option autoImplicit false

/-!
# Exact cutoff fixtures for supplied Alpha stages

The certified trapezoid has a shared entry grade for AC and ACD. The
cocircular square has a four-label actual Alpha face at grade 2, while the
supplied split omits it at every grade.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedStagesExamples

open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration
open TDA.Filtration.RationalAlpha.SuppliedGradeEnumerationExamples
open TDA.Filtration.RationalAlpha.SuppliedCarrierExamples
open TDA.Filtration.RationalAlpha.SignedBoundaryExamples
open TDA.Filtration.RationalAlpha.SuppliedStages

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
