import TDA.Filtration.AlphaCollapseExamples
import TDA.Simplicial.CollapseCertificateExamples

set_option autoImplicit false

/-!
# The checker on the obtuse triangle at grade 4

At the squared grade `4`, the Čech stage of `RationalAlpha.Examples.obtuse` has the face table
`CollapseCertificateExamples.triangle` and the α stage has the face table
`CollapseCertificateExamples.alphaTable`. Both tables are read off the exact grade tables
`cechGrades` and `gradedFaces obtuse` by keeping the rows of grade at most `4`. The accepted
one-step certificate `[({0,1}, {0,1,2})]` then gives `CollapsesTo (cech 4) (alpha 4)` through the
checker, independently of `AlphaCollapseExamples.collapsesTo`. Other grades, the critical grades
and the unbounded tail are not treated here.
-/

namespace TDA.Filtration.AlphaCollapseCertificateExamples

open TDA.Simplicial TDA.Simplicial.CollapseCertificateExamples TDA.Filtration.RationalAlpha
  TDA.Filtration.RationalAlpha.Examples TDA.Filtration.AlphaCollapseExamples

/-- The squared-grade Čech stage of the obtuse triangle. -/
local notation "cech" => Alpha.squaredCechFiltration (realSites obtuse)

/-- The squared-grade α stage of the obtuse triangle. -/
local notation "alpha" => Alpha.labelledComplexFiltration (realSites obtuse)

/-- A face has a row of grade at most `4` exactly when it is in the table of those rows. -/
private theorem exists_grade_le_four_iff (g : Finset (Finset (Fin 3) × ℚ)) (s : Finset (Fin 3)) :
    (∃ q, (s, q) ∈ g ∧ (q : ℝ) ≤ 4) ↔ s ∈ (g.filter fun r => r.2 ≤ 4).image Prod.fst := by
  simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  exact_mod_cast Iff.rfl

/-- The Čech stage at grade `4` has the face table of the full triangle. -/
theorem mem_cech_four_iff (s : Finset (Fin 3)) : s ∈ cech 4 ↔ s ∈ triangle := by
  rw [mem_cech_iff, exists_grade_le_four_iff]
  revert s
  decide +kernel

/-- The α stage at grade `4` has the face table `alphaTable`. -/
theorem mem_alpha_four_iff (s : Finset (Fin 3)) : s ∈ alpha 4 ↔ s ∈ alphaTable := by
  rw [mem_alpha_iff, exists_grade_le_four_iff, obtuse_grades]
  revert s
  decide +kernel

/-- The accepted certificate collapses the Čech stage at grade `4` to the α stage. -/
theorem collapsesTo_four : CollapsesTo (cech 4) (alpha 4) :=
  collapsesTo_of_checkSteps mem_cech_four_iff mem_alpha_four_iff checkSteps_triangle_alphaTable

end TDA.Filtration.AlphaCollapseCertificateExamples
