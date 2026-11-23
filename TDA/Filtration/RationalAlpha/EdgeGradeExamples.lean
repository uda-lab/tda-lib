import TDA.Filtration.RationalAlpha.EdgeGrade
import TDA.Filtration.RationalAlpha.SignedBoundaryExamples
import TDA.Filtration.RationalAlphaExamples
import TDA.Filtration.AlphaExamples

set_option autoImplicit false

/-!
# Exact planar edge grade examples

The two AC examples have the same Čech grade and different alpha grades. In the
first, the midpoint lies on the boundary of a third cell. In the second, it is
infeasible. An interior edge with two negative endpoints checks which one enters
first. Collinear, cocircular, and two-site inputs exercise the degenerate shapes.
-/

namespace TDA.Filtration.RationalAlpha.EdgeGradeExamples

open Set
open scoped Matrix
open EdgeGrade

private def sites {n : ℕ} (p : Fin n → Point) (h : ∀ i j, p i = p j → i = j) :
    Fin n ↪ Point :=
  ⟨p, h⟩

private def trapezoid : Fin 4 ↪ Point :=
  sites SignedBoundaryExamples.quad (by decide +kernel)

private def variantPoints : Fin 4 → Point := ![(0,0),(4,0),(2,3),(0,2)]

private def variant : Fin 4 ↪ Point := sites variantPoints (by decide +kernel)

private def interiorPoints : Fin 4 → Point := ![(-2,0),(2,0),(0,1),(0,-5)]

private def interiorSites : Fin 4 ↪ Point := sites interiorPoints (by decide +kernel)

private theorem four_comparisons {P : Fin 4 → Prop} :
    (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3⟩, ?_⟩
  rintro ⟨h₀,h₁,h₂,h₃⟩ j
  fin_cases j <;> assumption

private theorem parameter_rows {n : ℕ} (p : Fin n ↪ Point) (a b : Fin n)
    (slopes bounds : Fin n → ℚ)
    (h : ∀ j, orient (p a) (p b) (p j) = slopes j ∧ edgeRhsRat (p a) (p b) (p j) = bounds j)
    (s : ℝ) :
    s ∈ edgeParameters p a b ↔ ∀ j, ((slopes j : ℚ) : ℝ) * s ≤ (bounds j : ℝ) := by
  change (∀ j : Fin n, (orient (p a) (p b) (p j) : ℝ) * s ≤
    (edgeRhsRat (p a) (p b) (p j) : ℝ)) ↔ _
  simp_rw [(h _).1, (h _).2]

private theorem trapezoid_rows :
    ∀ j, orient (trapezoid 0) (trapezoid 2) (trapezoid j) = (![0,-8,0,6] : Fin 4 → ℚ) j ∧
      edgeRhsRat (trapezoid 0) (trapezoid 2) (trapezoid j) = (![0,2,0,0] : Fin 4 → ℚ) j :=
  by decide +kernel

/-- With C = (3, 2), the AC midpoint is the upper endpoint of the feasible interval. -/
theorem trapezoid_ac_interval : edgeParameters trapezoid 0 2 = Icc (-1/4) 0 := by
  ext s
  rw [parameter_rows _ _ _ _ _ trapezoid_rows, four_comparisons, mem_Icc]
  change (((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧ ((-8 : ℚ) : ℝ) * s ≤ ((2 : ℚ) : ℝ) ∧
    ((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧ ((6 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ)) ↔ _
  norm_num
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- At the feasible midpoint of AC, D ties in the closed comparison and B is farther. -/
theorem trapezoid_ac_midpoint_tie :
    (0 : ℝ) ∈ edgeParameters trapezoid 0 2 ∧
    (orient (trapezoid 0) (trapezoid 2) (trapezoid 3) : ℝ) * 0 =
      (edgeRhsRat (trapezoid 0) (trapezoid 2) (trapezoid 3) : ℝ) ∧
    (orient (trapezoid 0) (trapezoid 2) (trapezoid 1) : ℝ) * 0 <
      (edgeRhsRat (trapezoid 0) (trapezoid 2) (trapezoid 1) : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trapezoid_ac_interval]
    exact ⟨by norm_num, le_rfl⟩
  · rw [mul_zero, (trapezoid_rows 3).2]
    change 0 = ((0 : ℚ) : ℝ)
    norm_num
  · rw [mul_zero, (trapezoid_rows 1).2]
    change 0 < ((2 : ℚ) : ℝ)
    norm_num

/-- Reversing AC reflects the feasible interval and preserves the closed endpoint. -/
theorem trapezoid_ca_interval : edgeParameters trapezoid 2 0 = Icc 0 (1/4) := by
  ext s
  have h := (edgeParameters_swap_iff trapezoid 0 2 (-s)).symm
  rw [neg_neg, trapezoid_ac_interval] at h
  rw [← h, mem_Icc, mem_Icc]
  constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩

private theorem zero_minimizes (s : ℝ) : (0 : ℝ)^2 ≤ s^2 := by
  simpa only [zero_pow (by decide : 2 ≠ 0)] using sq_nonneg s

private theorem upper_nonpositive_minimizes {s u : ℝ} (hs : s ≤ u) (hu : u ≤ 0) :
    u^2 ≤ s^2 := by
  simpa only [neg_sq] using
    (sq_le_sq₀ (neg_nonneg.mpr hu) (neg_nonneg.mpr (hs.trans hu))).2 (neg_le_neg hs)

private theorem trapezoid_ac_direction : directionSq (trapezoid 0) (trapezoid 2) = 13 := by
  rw [directionSq_eq_sqDist]
  exact_mod_cast (show sqDist (trapezoid 2) (trapezoid 0) = 13 by decide +kernel)

/-- The actual AC alpha edge enters at squared grade 13/4, including equality. -/
theorem trapezoid_ac_exact_stage (t : ℝ) :
    ({0,2} : Finset (Fin 4)) ∈ Alpha.complex (realSites trapezoid) t ↔ (13 : ℝ)/4 ≤ t := by
  simpa [trapezoid_ac_direction] using
    edge_stage_of_parameter_min trapezoid (a := 0) (b := 2) (by decide)
      trapezoid_ac_midpoint_tie.1 (fun s _ => zero_minimizes s) t

/-- The exhaustive rational computation records the same grade and the midpoint tie. -/
theorem trapezoid_ac_reference_record :
    entry? trapezoid ({0,2} : Finset (Fin 4)) = some ⟨(3/2,1),13/4,{0,2,3}⟩ :=
  by decide +kernel

private theorem variant_rows :
    ∀ j, orient (variant 0) (variant 2) (variant j) = (![0,-12,0,4] : Fin 4 → ℚ) j ∧
      edgeRhsRat (variant 0) (variant 2) (variant j) = (![0,4,0,-1] : Fin 4 → ℚ) j :=
  by decide +kernel

/-- With C = (2, 3), the AC midpoint is infeasible. -/
theorem variant_ac_interval : edgeParameters variant 0 2 = Icc (-1/3) (-1/4) := by
  ext s
  rw [parameter_rows _ _ _ _ _ variant_rows, four_comparisons, mem_Icc]
  change (((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧ ((-12 : ℚ) : ℝ) * s ≤ ((4 : ℚ) : ℝ) ∧
    ((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧ ((4 : ℚ) : ℝ) * s ≤ ((-1 : ℚ) : ℝ)) ↔ _
  norm_num
  constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem variant_ac_direction : directionSq (variant 0) (variant 2) = 13 := by
  rw [directionSq_eq_sqDist]
  exact_mod_cast (show sqDist (variant 2) (variant 0) = 13 by decide +kernel)

/-- The actual alpha stage of the variant AC edge starts at squared grade 65/16. -/
theorem variant_ac_alpha_exact_stage (t : ℝ) :
    ({0,2} : Finset (Fin 4)) ∈ Alpha.complex (realSites variant) t ↔ (65 : ℝ)/16 ≤ t := by
  have hz : (-1/4 : ℝ) ∈ edgeParameters variant 0 2 := by
    rw [variant_ac_interval]
    exact ⟨by norm_num, le_rfl⟩
  have hm (s : ℝ) (hs : s ∈ edgeParameters variant 0 2) : (-1/4 : ℝ)^2 ≤ s^2 := by
    rw [variant_ac_interval] at hs
    exact upper_nonpositive_minimizes hs.2 (by norm_num)
  convert edge_stage_of_parameter_min variant (a := 0) (b := 2) (by decide) hz hm t using 2
  rw [variant_ac_direction]
  norm_num

/-- The closed Čech stage of the variant AC edge starts at squared grade 13/4. -/
theorem variant_ac_cech_exact_stage (t : ℝ) :
    ({0,2} : Finset (Fin 4)) ∈ Cech.complex (realSites variant) (Alpha.radius t) ↔ (13 : ℝ)/4 ≤ t := by
  constructor
  · intro h
    have hd := Cech.dist_le_two_mul_of_mem_complex _ h
      (show (0 : Fin 4) ∈ ({0,2} : Finset (Fin 4)) by simp)
      (show (2 : Fin 4) ∈ ({0,2} : Finset (Fin 4)) by simp)
    change dist (castPoint (variant 0)) (castPoint (variant 2)) ≤ 2 * Real.sqrt t at hd
    have hsq := (sq_le_sq₀ dist_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg t))).2 hd
    rw [dist_comm, distSq_cast, ← directionSq_eq_sqDist, variant_ac_direction] at hsq
    by_cases ht : 0 ≤ t
    · rw [mul_pow, Real.sq_sqrt ht] at hsq
      linarith
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ht)] at hsq
      norm_num at hsq
  · intro ht
    rw [Cech.mem_complex_iff]
    refine ⟨⟨0, by simp⟩, castPoint (1,3/2), ?_⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · apply Real.le_sqrt_of_sq_le
      rw [show realSites variant 0 = castPoint (variant 0) by rfl, distSq_cast]
      have hq : sqDist (1,3/2) (variant 0) = 13/4 := by decide +kernel
      rw [hq]
      norm_num at ht ⊢
      exact ht
    · apply Real.le_sqrt_of_sq_le
      rw [show realSites variant 2 = castPoint (variant 2) by rfl, distSq_cast]
      have hq : sqDist (1,3/2) (variant 2) = 13/4 := by decide +kernel
      rw [hq]
      norm_num at ht ⊢
      exact ht

private theorem interior_rows :
    ∀ j, orient (interiorSites 0) (interiorSites 1) (interiorSites j) = (![0,0,4,-20] : Fin 4 → ℚ) j ∧
      edgeRhsRat (interiorSites 0) (interiorSites 1) (interiorSites j) =
        (![0,0,-3/2,21/2] : Fin 4 → ℚ) j :=
  by decide +kernel

/-- For the internal AB edge, both endpoints are on the negative side of the midpoint. -/
theorem interior_ab_interval : edgeParameters interiorSites 0 1 = Icc (-21/40) (-3/8) := by
  ext s
  rw [parameter_rows _ _ _ _ _ interior_rows, four_comparisons, mem_Icc]
  change (((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧ ((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧
    ((4 : ℚ) : ℝ) * s ≤ ((-3/2 : ℚ) : ℝ) ∧ ((-20 : ℚ) : ℝ) * s ≤ ((21/2 : ℚ) : ℝ)) ↔ _
  norm_num
  constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩

private theorem interior_y (s : ℝ) : bisectorPoint (interiorSites 0) (interiorSites 1) s 1 = 4 * s := by
  change (((0 : ℚ) : ℝ) + ((0 : ℚ) : ℝ)) / 2 +
    s * (((2 : ℚ) : ℝ) - ((-2 : ℚ) : ℝ)) = 4 * s
  push_cast
  ring

/-- The y-coordinates of the actual common closed cells form the prescribed interval. -/
theorem interior_ab_y_range :
    (fun x : Plane => x 1) '' Alpha.commonCells (realSites interiorSites) ({0,1} : Finset (Fin 4)) =
      Icc (-21/10) (-3/2) := by
  rw [edge_commonCells_eq_image interiorSites (show (0 : Fin 4) ≠ 1 by decide),
    interior_ab_interval, Set.image_image]
  ext y
  constructor
  · rintro ⟨s,hs,rfl⟩
    change bisectorPoint (interiorSites 0) (interiorSites 1) s 1 ∈ _
    rw [interior_y]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · intro hy
    refine ⟨y/4, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
    change bisectorPoint (interiorSites 0) (interiorSites 1) (y/4) 1 = y
    rw [interior_y]
    ring

private theorem interior_ab_direction : directionSq (interiorSites 0) (interiorSites 1) = 16 := by
  rw [directionSq_eq_sqDist]
  exact_mod_cast (show sqDist (interiorSites 1) (interiorSites 0) = 16 by decide +kernel)

/-- The nearer endpoint gives the first actual squared alpha grade 25/4. -/
theorem interior_ab_exact_stage (t : ℝ) :
    ({0,1} : Finset (Fin 4)) ∈ Alpha.complex (realSites interiorSites) t ↔ (25 : ℝ)/4 ≤ t := by
  have hz : (-3/8 : ℝ) ∈ edgeParameters interiorSites 0 1 := by
    rw [interior_ab_interval]
    exact ⟨by norm_num, le_rfl⟩
  have hm (s : ℝ) (hs : s ∈ edgeParameters interiorSites 0 1) : (-3/8 : ℝ)^2 ≤ s^2 := by
    rw [interior_ab_interval] at hs
    exact upper_nonpositive_minimizes hs.2 (by norm_num)
  convert edge_stage_of_parameter_min interiorSites (a := 0) (b := 1) (by decide) hz hm t using 2
  rw [interior_ab_direction]
  norm_num

/-- The farther endpoint is feasible and its squared distance is 841/100. -/
theorem interior_ab_far_endpoint :
    (-21/40 : ℝ) ∈ edgeParameters interiorSites 0 1 ∧
    dist (bisectorPoint (interiorSites 0) (interiorSites 1) (-21/40))
      (castPoint (interiorSites 0))^2 = (841 : ℝ)/100 := by
  refine ⟨?_, ?_⟩
  · rw [interior_ab_interval]
    exact ⟨le_rfl, by norm_num⟩
  · rw [squared_radius_on_bisector, interior_ab_direction]
    norm_num

/-- The collinear outer pair has no common-cell parameter. -/
theorem collinear_outer_parameters_empty : edgeParameters Examples.collinear 0 2 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have h := hs 1
  have hslope : orient (Examples.collinear 0) (Examples.collinear 2) (Examples.collinear 1) = 0 :=
    by decide +kernel
  have hbound : edgeRhsRat (Examples.collinear 0) (Examples.collinear 2) (Examples.collinear 1) = -2 :=
    by decide +kernel
  change (orient (Examples.collinear 0) (Examples.collinear 2) (Examples.collinear 1) : ℝ) * s ≤
    (edgeRhsRat (Examples.collinear 0) (Examples.collinear 2) (Examples.collinear 1) : ℝ) at h
  rw [hslope, hbound] at h
  norm_num at h

/-- The square diagonal's common cells consist of the single center parameter. -/
theorem square_diagonal_parameters_singleton : edgeParameters Examples.square 0 3 = {0} := by
  have hrows : ∀ j, orient (Examples.square 0) (Examples.square 3) (Examples.square j) =
      (![0,-4,4,0] : Fin 4 → ℚ) j ∧
      edgeRhsRat (Examples.square 0) (Examples.square 3) (Examples.square j) =
        (![0,0,0,0] : Fin 4 → ℚ) j := by decide +kernel
  ext s
  rw [parameter_rows _ _ _ _ _ hrows, four_comparisons, mem_singleton_iff]
  change (((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧ ((-4 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧
    ((4 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ) ∧ ((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ)) ↔ _
  norm_num
  exact ⟨fun h => by linarith [h.1,h.2], fun h => by simp [h]⟩

/-- The obtuse example's long edge has a single finite parameter bound. -/
theorem obtuse_hull_parameters_ray : edgeParameters Examples.obtuse 0 1 = Iic (-1/4) := by
  have hrows : ∀ j, orient (Examples.obtuse 0) (Examples.obtuse 1) (Examples.obtuse j) =
      (![0,0,4] : Fin 3 → ℚ) j ∧
      edgeRhsRat (Examples.obtuse 0) (Examples.obtuse 1) (Examples.obtuse j) =
        (![0,0,-1] : Fin 3 → ℚ) j := by decide +kernel
  ext s
  rw [parameter_rows _ _ _ _ _ hrows, mem_Iic]
  constructor
  · intro h
    have h₂ := h 2
    change ((4 : ℚ) : ℝ) * s ≤ ((-1 : ℚ) : ℝ) at h₂
    norm_num at h₂
    linarith
  · intro h j
    fin_cases j
    · change ((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ)
      norm_num
    · change ((0 : ℚ) : ℝ) * s ≤ ((0 : ℚ) : ℝ)
      norm_num
    · change ((4 : ℚ) : ℝ) * s ≤ ((-1 : ℚ) : ℝ)
      push_cast
      linarith

/-- The two-site edge has no finite parameter bounds. -/
theorem two_site_parameters_univ (p : Fin 2 ↪ Point) : edgeParameters p 0 1 = univ := by
  ext s
  refine ⟨fun _ => mem_univ _,fun _ => ?_⟩
  apply (bisector_mem_commonCells_iff p 0 1 s).1
  rw [RationalAlpha.mem_commonCells_iff p
    (show (0 : Fin 2) ∈ ({0,1} : Finset (Fin 2)) by simp)]
  have h (j : Fin 2) : linearForm (normal (p 0) (p j)) (bisectorPoint (p 0) (p 1) s) =
      (offset (p 0) (p j) : ℝ) := by
    fin_cases j
    · simp [linearForm, normal, offset]
    · exact bisector_equation _ _ _
  exact ⟨fun j => (h j).le, fun j _ => h j⟩

/-- The existing two-site Alpha theorem agrees with the squared-length normalization. -/
theorem two_site_exact_stage (p : Fin 2 ↪ Point) (t : ℝ) :
    ({0,1} : Finset (Fin 2)) ∈ Alpha.complex (realSites p) t ↔ directionSq (p 0) (p 1) / 4 ≤ t := by
  rw [show ({0,1} : Finset (Fin 2)) = Finset.univ by decide,
    Alpha.Examples.two_site_edge_iff]
  change (dist (castPoint (p 0)) (castPoint (p 1)) / 2)^2 ≤ t ↔ _
  rw [div_pow, dist_comm, distSq_cast, ← directionSq_eq_sqDist]
  norm_num

end TDA.Filtration.RationalAlpha.EdgeGradeExamples
