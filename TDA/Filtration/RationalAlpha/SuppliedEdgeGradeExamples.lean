import TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
import TDA.Filtration.RationalAlpha.EdgeGradeExamples

set_option autoImplicit false

/-!
# Supplied-edge Voronoi regions in the exact trapezoid

The ABC and ACD incidences determine the closed outward ray of AB and the closed
segment of AC. Both examples use the supplied-edge theorems and check the actual
alpha stages at every squared grade.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedEdgeGradeExamples

open Set
open scoped BigOperators Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.EdgeGrade
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.IncircleGrade

noncomputable section

open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade

open TDA.Filtration.RationalAlpha.SignedBoundaryExamples

private def quadSites : Fin 4 ↪ Point := ⟨quad, by
  change ∀ a b : Fin 4, quad a = quad b → a = b
  decide +kernel⟩

private theorem quad_contained (i : Fin 4) : castPoint (quadSites i) ∈ siteHull quadSites cycle :=
  subset_convexHull ℝ _ ⟨i,rfl⟩

private theorem goodCCW : ∀ i, 0 < orient
    (quadSites (good i 0)) (quadSites (good i 1)) (quadSites (good i 2)) :=
  by decide +kernel

private theorem goodPasses : ∀ i, checkIncircle quadSites (good i 0) (good i 1) (good i 2) = true :=
  by decide +kernel

private theorem quadNoFour : NoFourIncircleZeros quadSites := by
  unfold NoFourIncircleZeros
  decide +kernel

private theorem ac_not_hull : ∀ j, cycleEdges cycle j ≠ (0,2) ∧ cycleEdges cycle j ≠ (2,0) :=
  by decide +kernel

private theorem ac_face : ({0,2} : Finset (Fin 4)) ∈ (labelComplex good).faces :=
  (pair_mem_iff_occurrence good (show (0 : Fin 4) ≠ 2 by decide)).2
    ⟨(1,0),Or.inl rfl⟩

private theorem ac_lower_coords :
    bisectorPoint (quadSites 0) (quadSites 2) (-1/4) = castPoint (2,1/4) := by
  ext i
  fin_cases i
  · change (((0 : ℚ) : ℝ) + ((3 : ℚ) : ℝ)) / 2 - (-1/4)*(((2 : ℚ) : ℝ) -
      ((0 : ℚ) : ℝ)) = ((2 : ℚ) : ℝ)
    norm_num
  · change (((0 : ℚ) : ℝ) + ((2 : ℚ) : ℝ)) / 2 + (-1/4)*(((3 : ℚ) : ℝ) -
      ((0 : ℚ) : ℝ)) = ((1/4 : ℚ) : ℝ)
    norm_num

private theorem ac_upper_coords :
    bisectorPoint (quadSites 0) (quadSites 2) 0 = castPoint (3/2,1) := by
  rw [bisectorPoint_zero]
  congr 1
  decide +kernel

/-- The supplied AC diagonal has the closed dual segment between the two computed centers
and enters the actual alpha complex at squared grade 13/4. -/
theorem exact_trapezoid_ac (t : ℝ) :
    ∃ D : InteriorDual quadSites good 0 2,
      D.lower = -1/4 ∧ D.upper = 0 ∧ D.lower < D.upper ∧
      D.right.center = (2,1/4) ∧ D.left.center = (3/2,1) ∧
      (Alpha.commonCells (realSites quadSites) ({0,2} : Finset (Fin 4)) =
        segment ℝ (castPoint (2,1/4)) (castPoint (3/2,1))) ∧
      (({0,2} : Finset (Fin 4)) ∈ Alpha.complex (realSites quadSites) t ↔ (13 : ℝ)/4 ≤ t) := by
  obtain ⟨D⟩ := supplied_interior_dual (k := 1) quadSites cycle (fun _ _ h => h)
    good trapezoid_certificate goodCCW good_boundary goodPasses (by decide) ac_face ac_not_hull
  have hint : edgeParameters quadSites 0 2 = Icc (-1/4) 0 :=
    EdgeGradeExamples.trapezoid_ac_interval
  have hlo : IsLeast (edgeParameters quadSites 0 2) D.lower :=
    D.parameters ▸ isLeast_Icc D.ordered
  have hhi : IsGreatest (edgeParameters quadSites 0 2) D.upper :=
    D.parameters ▸ isGreatest_Icc D.ordered
  have hl : D.lower = -1/4 := hlo.unique (hint ▸ isLeast_Icc (by norm_num))
  have hu : D.upper = 0 := hhi.unique (hint ▸ isGreatest_Icc (by norm_num))
  have hb := D.lower_center
  rw [hl, ac_lower_coords] at hb
  have hc := D.upper_center
  rw [hu, ac_upper_coords] at hc
  refine ⟨D,hl,hu,D.strict quadNoFour,(castPoint_injective hb).symm,
    (castPoint_injective hc).symm,?_,?_⟩
  · rw [D.region, ← hb, ← hc]
  · have he : directionSq (quadSites 0) (quadSites 2) = 13 := by
      rw [directionSq_eq_sqDist]
      exact_mod_cast (show sqDist (quadSites 2) (quadSites 0) = 13 by decide +kernel)
    simpa [hl,hu,he,show (-1/4 : ℝ) ≤ 0 by norm_num] using D.stage t

private theorem ab_center_coord :
    bisectorPoint (quadSites 0) (quadSites 1) (1/16) = castPoint (2,1/4) := by
  ext i
  fin_cases i
  · change (((0 : ℚ) : ℝ) + ((4 : ℚ) : ℝ)) / 2 - (1/16)*(((0 : ℚ) : ℝ) -
      ((0 : ℚ) : ℝ)) = ((2 : ℚ) : ℝ)
    norm_num
  · change (((0 : ℚ) : ℝ) + ((0 : ℚ) : ℝ)) / 2 + (1/16)*(((4 : ℚ) : ℝ) -
      ((0 : ℚ) : ℝ)) = ((1/4 : ℚ) : ℝ)
    norm_num

private theorem ab_outward : outward (quadSites 0) (quadSites 1) = castPoint (0, -4) := by
  ext i
  fin_cases i
  · change ((0 : ℚ) : ℝ) - ((0 : ℚ) : ℝ) = ((0 : ℚ) : ℝ)
    norm_num
  · change -(((4 : ℚ) : ℝ) - ((0 : ℚ) : ℝ)) = ((-4 : ℚ) : ℝ)
    norm_num

/-- The supplied AB side has the downward closed ray from the incident center and enters
the actual alpha complex at squared grade 4. -/
theorem exact_trapezoid_ab (t : ℝ) :
    ∃ D : HullDual quadSites good 0 1,
      D.upper = 1/16 ∧ D.incident.center = (2,1/4) ∧
      (Alpha.commonCells (realSites quadSites) ({0,1} : Finset (Fin 4)) =
        closedRay (castPoint (2,1/4)) (castPoint (0, -4))) ∧
      (({0,1} : Finset (Fin 4)) ∈ Alpha.complex (realSites quadSites) t ↔ 4 ≤ t) := by
  obtain ⟨D⟩ := supplied_hull_dual (k := 1) quadSites cycle (fun _ _ h => h)
    good trapezoid_certificate goodCCW good_boundary goodPasses quad_contained (0 : Fin 4)
  change HullDual quadSites good 0 1 at D
  have hocc : (0,0) = D.occurrence := D.unique (0,0) rfl
  have hidx : (0 : Fin 2) = D.occurrence.1 := congrArg Prod.fst hocc
  have hcalc := (congrArg (fun j : Fin 2 => circumcenter? (quadSites (good j 0))
    (quadSites (good j 1)) (quadSites (good j 2))) hidx).trans D.incident.computed
  have hknown : circumcenter? (quadSites (good 0 0)) (quadSites (good 0 1))
      (quadSites (good 0 2)) = some (2,1/4) := by decide +kernel
  rw [hknown] at hcalc
  have hc := (Option.some.inj hcalc).symm
  have hab : quadSites 0 ≠ quadSites 1 := quadSites.injective.ne (by decide)
  have hu : D.upper = 1/16 := bisectorPoint_injective hab
    (D.upper_center.trans ((congrArg castPoint hc).trans ab_center_coord.symm))
  refine ⟨D,hu,hc,?_,?_⟩
  · rw [D.region, hc, ab_outward]
  · have he : directionSq (quadSites 0) (quadSites 1) = 16 := by
      rw [directionSq_eq_sqDist]
      exact_mod_cast (show sqDist (quadSites 1) (quadSites 0) = 16 by decide +kernel)
    simpa [hu,he,show (0 : ℝ) ≤ 1/16 by norm_num, show (16 : ℝ)/4 = 4 by norm_num]
      using D.stage t

end
end TDA.Filtration.RationalAlpha.SuppliedEdgeGradeExamples
