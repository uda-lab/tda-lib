import TDA.Filtration.RationalAlpha.SubdividedStages
import TDA.Filtration.RationalAlpha.SuppliedStagesExamples

set_option autoImplicit false

/-!
# Exact stage fixtures for a subdivided hull side

The triangle `A = (0,0)`, `M = (1,0)`, `B = (2,0)`, `C = (0,2)` has `M` in the relative
interior of the hull side `AB`; its supplied triangles are `AMC` and `MBC`. All real stages
come from the supplied rows through `supplied_realStage_iff_of_subdivided_boundary`, with the
public certificate, ordered cuts and signed boundary of the split fixture.

The edge `BC` is not Gabriel: `M` lies in its diametral disk, so its Gabriel value 2 is below
its actual grade `5/2`, the circumradius of `MBC`. The refined piece `AM` of the split side
enters at its Gabriel value `1/4`, where the ray of its `HullDual` points away from `C`.
-/

namespace TDA.Filtration.RationalAlpha.SubdividedStagesExamples

open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedCarrier
open TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration
open TDA.Filtration.RationalAlpha.SuppliedStages
open TDA.Filtration.RationalAlpha.SubdividedStages
open TDA.Filtration.RationalAlpha.SubdividedBoundaryExamples
open TDA.Filtration.RationalAlpha.SuppliedCarrierExamples

/-- All real stages of the split triangle A, M, B, C from its supplied rows. -/
theorem split_checked_stages (s : Finset (Fin 4)) (t : ℝ) :
    s ∈ realStageTable (suppliedGrades splitEmb splitTriangles) t ↔
      s ∈ Alpha.complex (realSites splitEmb) t :=
  supplied_realStage_iff_of_subdivided_boundary splitEmb (k := 0) coarseCycle cuts splitTriangles
    coarse_certificate ordered_cuts sites_contained (by decide +kernel) signed_boundary
    (by decide +kernel) (Or.inr (by unfold NoFourIncircleZeros; decide +kernel)) s t

theorem split_bc_row : (({1, 2} : Finset (Fin 4)), (5/2 : ℚ)) ∈
    suppliedGrades splitEmb splitTriangles := by
  refine (mem_suppliedGrades splitEmb splitTriangles).2
    ⟨(pair_mem_iff_occurrence splitTriangles (show (1 : Fin 4) ≠ 2 by decide)).2
      ⟨(1, 1), Or.inl rfl⟩, ?_⟩
  rw [← kernelGrade?_eq_grade?]
  decide +kernel

theorem split_am_row : (({0, 3} : Finset (Fin 4)), (1/4 : ℚ)) ∈
    suppliedGrades splitEmb splitTriangles := by
  refine (mem_suppliedGrades splitEmb splitTriangles).2
    ⟨(pair_mem_iff_occurrence splitTriangles (show (0 : Fin 4) ≠ 3 by decide)).2
      ⟨(0, 0), Or.inl rfl⟩, ?_⟩
  rw [← kernelGrade?_eq_grade?]
  decide +kernel

/-- BC has squared length 8, so its Gabriel value is 2; M lies in the diametral disk of BC,
and BC enters actual α together with MBC at the squared grade 5/2. -/
theorem split_bc_cutoff (t : ℝ) :
    ({1, 2} : Finset (Fin 4)) ∈ Alpha.complex (realSites splitEmb) t ↔ (5 : ℝ) / 2 ≤ t := by
  have hcut : ({1, 2} : Finset (Fin 4)) ∈ realStageTable (suppliedGrades splitEmb splitTriangles) t ↔
      ((5/2 : ℚ) : ℝ) ≤ t :=
    supplied_row_cutoff splitEmb splitTriangles split_bc_row t
  rw [← split_checked_stages, hcut]
  norm_num

/-- The refined piece AM of the split side enters at its Gabriel value 1/4. -/
theorem split_am_cutoff (t : ℝ) :
    ({0, 3} : Finset (Fin 4)) ∈ Alpha.complex (realSites splitEmb) t ↔ (1 : ℝ) / 4 ≤ t := by
  have hcut : ({0, 3} : Finset (Fin 4)) ∈ realStageTable (suppliedGrades splitEmb splitTriangles) t ↔
      ((1/4 : ℚ) : ℝ) ≤ t :=
    supplied_row_cutoff splitEmb splitTriangles split_am_row t
  rw [← split_checked_stages, hcut]
  norm_num

end TDA.Filtration.RationalAlpha.SubdividedStagesExamples
