import TDA.Filtration.CollapseCertificateFamily
import TDA.Filtration.AlphaCollapseExamples
import TDA.Simplicial.CollapseCertificateExamples

set_option autoImplicit false

/-!
# A certificate family for the obtuse triangle across its critical grades

The actual squared-grade Čech and α filtrations of `RationalAlpha.Examples.obtuse` have the
grade tables `cechGrades` and `gradedFaces obtuse` (`hasGradeTable_cech`,
`hasGradeTable_alpha`). Their critical grades are `0, 1/2, 5/2, 4, 5` (`criticalGrades_obtuse`).
The supplied family `obtuseCertificate` removes the long edge through the triangle at grade `4`
and is empty at every other grade. It is accepted (`checkCertificates_obtuse`), so the Čech
stage collapses to the α stage at every real grade through the generic verifier
(`collapsesTo_of_certificate`).

The fixtures exercise every regime on the actual stages: below the least critical grade both
are empty (`stages_of_neg`); on `[4, 5)` they have the face tables `triangle` and `alphaTable`,
and the removal is needed (`stages_of_mem_Ico_four`, `checkCertificates_nil`); on the
unbounded tail `[5, ∞)` both are the full triangle, and the pair must be retained
(`stages_of_five_le`). Keeping the removal at grade `5` is rejected: the long edge is still free
in the Čech table there, but the run ends at `alphaTable`, not at the α table of grade `5`
(`checkCertificates_removal_from_four`).
-/

namespace TDA.Filtration.AlphaCollapseFamilyExamples

open TDA.Simplicial TDA.Simplicial.CollapseCertificateExamples TDA.Filtration.RationalAlpha
  TDA.Filtration.RationalAlpha.Examples TDA.Filtration.AlphaCollapseExamples

/-- The squared-grade Čech stage of the obtuse triangle. -/
local notation "cech" => Alpha.squaredCechFiltration (realSites obtuse)

/-- The squared-grade α stage of the obtuse triangle. -/
local notation "alpha" => Alpha.labelledComplexFiltration (realSites obtuse)

/-- The actual squared-grade Čech filtration has the grade table `cechGrades`. -/
theorem hasGradeTable_cech : HasGradeTable cech cechGrades :=
  mem_cech_iff

/-- The actual α filtration has the grade table `gradedFaces obtuse`. -/
theorem hasGradeTable_alpha : HasGradeTable alpha (gradedFaces obtuse) :=
  mem_alpha_iff

/-- The critical grades of the pair are `0, 1/2, 5/2, 4, 5`. -/
theorem criticalGrades_obtuse :
    criticalGrades (gradedFaces obtuse) cechGrades = {0, 1/2, 5/2, 4, 5} := by
  rw [obtuse_grades]
  decide +kernel

/-- At grade `4` the stage tables are `triangle` and `alphaTable`; at grade `5` both are
`triangle`. -/
theorem stageTable_four_five :
    stageTable cechGrades 4 = triangle ∧ stageTable (gradedFaces obtuse) 4 = alphaTable ∧
      stageTable cechGrades 5 = triangle ∧ stageTable (gradedFaces obtuse) 5 = triangle := by
  rw [obtuse_grades]
  decide +kernel

/-- The supplied family: the long edge is collapsed through the triangle at grade `4`, and the
certificate is empty at every other grade. -/
def obtuseCertificate (c : ℚ) : List (Finset (Fin 3) × Finset (Fin 3)) :=
  if c = 4 then [({0,1}, {0,1,2})] else []

/-- The supplied family is accepted at every critical grade, with exact endpoints. -/
theorem checkCertificates_obtuse :
    checkCertificates (gradedFaces obtuse) cechGrades obtuseCertificate = true := by
  rw [obtuse_grades]
  decide +kernel

/-- The empty family is rejected: at grade `4` the two stage tables differ. -/
theorem checkCertificates_nil :
    checkCertificates (gradedFaces obtuse) cechGrades (fun _ => []) = false ∧
      stageTable cechGrades 4 ≠ stageTable (gradedFaces obtuse) 4 := by
  rw [obtuse_grades]
  decide +kernel

/-- Keeping the removal from grade `4` on is rejected: at grade `5` the long edge is still free
in the Čech table, but the run ends at `alphaTable`, not at the α table of grade `5`. -/
theorem checkCertificates_removal_from_four :
    checkCertificates (gradedFaces obtuse) cechGrades
        (fun c => if 4 ≤ c then [({0,1}, {0,1,2})] else []) = false ∧
      IsFreePairTable (stageTable cechGrades 5) {0,1} {0,1,2} ∧
      runSteps (stageTable cechGrades 5) [({0,1}, {0,1,2})] = some alphaTable ∧
      alphaTable ≠ stageTable (gradedFaces obtuse) 5 := by
  rw [obtuse_grades]
  decide +kernel

/-- Below the least critical grade `0`, neither stage has a face. -/
theorem stages_of_neg {t : ℝ} (ht : t < 0) (s : Finset (Fin 3)) : s ∉ alpha t ∧ s ∉ cech t := by
  refine stages_of_lt_criticalGrades hasGradeTable_alpha hasGradeTable_cech (fun q hq => ?_) s
  rw [criticalGrades_obtuse] at hq
  have h0 : (0 : ℚ) ≤ q := by revert q; decide +kernel
  exact ht.trans_le (by exact_mod_cast h0)

/-- On `[4, 5)` the Čech stage has the face table `triangle` and the α stage `alphaTable`. -/
theorem stages_of_mem_Ico_four {t : ℝ} (ht : t ∈ Set.Ico (4 : ℝ) 5) (s : Finset (Fin 3)) :
    (s ∈ alpha t ↔ s ∈ alphaTable) ∧ (s ∈ cech t ↔ s ∈ triangle) := by
  have hnext : ∀ q ∈ criticalGrades (gradedFaces obtuse) cechGrades, (4 : ℚ) < q → 5 ≤ q := by
    rw [criticalGrades_obtuse]
    decide +kernel
  have e := stages_eq_stageTable_of_mem_Ico hasGradeTable_alpha hasGradeTable_cech hnext
    (by exact_mod_cast ht) s
  rw [stageTable_four_five.1, stageTable_four_five.2.1] at e
  exact e

/-- On the unbounded tail `[5, ∞)` both stages have the face table `triangle`. -/
theorem stages_of_five_le {t : ℝ} (ht : 5 ≤ t) (s : Finset (Fin 3)) :
    (s ∈ alpha t ↔ s ∈ triangle) ∧ (s ∈ cech t ↔ s ∈ triangle) := by
  have hlast : ∀ q ∈ criticalGrades (gradedFaces obtuse) cechGrades, q ≤ 5 := by
    rw [criticalGrades_obtuse]
    decide +kernel
  have e := stages_eq_stageTable_of_le_of_forall_le hasGradeTable_alpha hasGradeTable_cech hlast
    (by exact_mod_cast ht) s
  rw [stageTable_four_five.2.2.1, stageTable_four_five.2.2.2] at e
  exact e

/-- Through the generic verifier, the Čech stage collapses to the α stage at every real
grade. -/
theorem collapsesTo_of_certificate (t : ℝ) : CollapsesTo (cech t) (alpha t) :=
  collapsesTo_of_checkCertificates hasGradeTable_alpha hasGradeTable_cech
    checkCertificates_obtuse t

end TDA.Filtration.AlphaCollapseFamilyExamples
