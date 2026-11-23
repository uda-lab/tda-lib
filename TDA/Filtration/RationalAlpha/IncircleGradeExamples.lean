import TDA.Filtration.RationalAlpha.IncircleGrade
import TDA.Filtration.RationalAlpha.SignedBoundaryExamples

set_option autoImplicit false

/-!
# Exact incircle and triangle alpha grade examples

The certified trapezoid split along AC gives two occupied triangles. Both triangles from
the other diagonal are rejected. The square checks admission of a cocircular tie.
-/

open scoped Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.IncircleGrade

namespace TDA.Filtration.RationalAlpha.IncircleGradeExamples

open TDA.Filtration.RationalAlpha.SignedBoundaryExamples

private def quadSites : Fin 4 ↪ Point := ⟨quad, by
  change ∀ i j : Fin 4, quad i = quad j → i = j
  decide +kernel⟩

/-- The certified triangle ABC enters at squared grade 65/16. -/
theorem trapezoid_ABC_exact_stage (t : ℝ) :
    ({0, 1, 2} : Finset (Fin 4)) ∈ Alpha.complex (castSites quadSites) t ↔ (65 : ℝ)/16 ≤ t := by
  have hc : circumcenter? (quadSites 0) (quadSites 1) (quadSites 2) = some (2, 1/4) :=
    by decide +kernel
  have hccw : 0 < orient (quadSites 0) (quadSites 1) (quadSites 2) := by decide +kernel
  have hpass : ∀ d, incircle (quadSites 0) (quadSites 1) (quadSites 2) (quadSites d) ≤ 0 :=
    by decide +kernel
  have hq : sqDist (2, 1/4) (quadSites 0) = 65/16 := by decide +kernel
  have he : (sqDist (2, 1/4) (quadSites 0) : ℝ) = 65/16 := by rw [hq]; norm_num
  rw [triangle_mem_actual_stage_iff quadSites 0 1 2 hccw hc, he]
  exact ⟨fun h => h.2, fun h => ⟨hpass, h⟩⟩

/-- The certified triangle ACD enters at squared grade 13/4. -/
theorem trapezoid_ACD_exact_stage (t : ℝ) :
    ({0, 2, 3} : Finset (Fin 4)) ∈ Alpha.complex (castSites quadSites) t ↔ (13 : ℝ)/4 ≤ t := by
  have hc : circumcenter? (quadSites 0) (quadSites 2) (quadSites 3) = some (3/2, 1) :=
    by decide +kernel
  have hccw : 0 < orient (quadSites 0) (quadSites 2) (quadSites 3) := by decide +kernel
  have hpass : ∀ d, incircle (quadSites 0) (quadSites 2) (quadSites 3) (quadSites d) ≤ 0 :=
    by decide +kernel
  have hq : sqDist (3/2, 1) (quadSites 0) = 13/4 := by decide +kernel
  have he : (sqDist (3/2, 1) (quadSites 0) : ℝ) = 13/4 := by rw [hq]; norm_num
  rw [triangle_mem_actual_stage_iff quadSites 0 2 3 hccw hc, he]
  exact ⟨fun h => h.2, fun h => ⟨hpass, h⟩⟩

/-- Triangle ABD from the other diagonal is absent at every alpha stage. -/
theorem trapezoid_wrong_ABD_absent (t : ℝ) :
    ({0, 1, 3} : Finset (Fin 4)) ∉ Alpha.complex (castSites quadSites) t := by
  have hc : circumcenter? (quadSites 0) (quadSites 1) (quadSites 3) = some (2, 1) :=
    by decide +kernel
  have hccw : 0 < orient (quadSites 0) (quadSites 1) (quadSites 3) := by decide +kernel
  have hbad : ¬ incircle (quadSites 0) (quadSites 1) (quadSites 3) (quadSites 2) ≤ 0 :=
    by decide +kernel
  intro ht
  exact hbad (((triangle_mem_actual_stage_iff quadSites 0 1 3 hccw hc t).1 ht).1 2)

/-- The second triangle from the other trapezoid diagonal is absent at every stage. -/
theorem trapezoid_wrong_BCD_absent (t : ℝ) :
    ({1, 2, 3} : Finset (Fin 4)) ∉ Alpha.complex (castSites quadSites) t := by
  have hc : circumcenter? (quadSites 1) (quadSites 2) (quadSites 3) = some (3/2, 0) :=
    by decide +kernel
  have hccw : 0 < orient (quadSites 1) (quadSites 2) (quadSites 3) := by decide +kernel
  have hbad : ¬ incircle (quadSites 1) (quadSites 2) (quadSites 3) (quadSites 0) ≤ 0 :=
    by decide +kernel
  intro ht
  exact hbad (((triangle_mem_actual_stage_iff quadSites 1 2 3 hccw hc t).1 ht).1 0)

private def square : Fin 4 → Point := ![(0, 0),(4, 0),(4, 4),(0, 4)]

private def squareSites : Fin 4 ↪ Point := ⟨square, by
  change ∀ i j : Fin 4, square i = square j → i = j
  decide +kernel⟩

/-- A cocircular fourth site passes the closed comparison, and the triangle enters at grade 8. -/
theorem square_boundary_tie_admitted :
    checkIncircle squareSites 0 1 2 = true ∧
    incircle (squareSites 0) (squareSites 1) (squareSites 2) (squareSites 3) = 0 ∧
    ∀ t : ℝ, ({0, 1, 2} : Finset (Fin 4)) ∈ Alpha.complex (castSites squareSites) t ↔ 8 ≤ t := by
  have hc : circumcenter? (squareSites 0) (squareSites 1) (squareSites 2) = some (2, 2) :=
    by decide +kernel
  have hccw : 0 < orient (squareSites 0) (squareSites 1) (squareSites 2) := by decide +kernel
  have hpass : ∀ d, incircle (squareSites 0) (squareSites 1) (squareSites 2) (squareSites d) ≤ 0 :=
    by decide +kernel
  have hq : sqDist (2, 2) (squareSites 0) = 8 := by decide +kernel
  have he : (sqDist (2, 2) (squareSites 0) : ℝ) = 8 := by exact_mod_cast hq
  refine ⟨(checkIncircle_eq_true_iff _ _ _ _).2 hpass, by decide +kernel, fun t => ?_⟩
  rw [triangle_mem_actual_stage_iff squareSites 0 1 2 hccw hc, he]
  exact ⟨fun h => h.2, fun h => ⟨hpass, h⟩⟩

end TDA.Filtration.RationalAlpha.IncircleGradeExamples
