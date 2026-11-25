import TDA.Filtration.RationalAlpha.TriangulationAssembly

set_option autoImplicit false

/-!
# Incircle admission and exact alpha grades of supplied triangles

The CCW incircle comparison excludes every site from the open circumdisk. The same
comparisons place the computed circumcenter in all three closed Voronoi cells. A real
point in these common cells is equidistant from the vertices and hence is that center.
The squared circumradius therefore gives the exact first occupied alpha grade.
-/

open Set
open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Simplicial

namespace TDA.Filtration.RationalAlpha.IncircleGrade

/-- Check the CCW incircle inequality at every site label, including the triangle vertices. -/
def checkIncircle {V : Type*} [Fintype V] (site : V → Point) (a b c : V) : Bool :=
  decide (∀ d : V, incircle (site a) (site b) (site c) (site d) ≤ 0)

/-- The finite Boolean test reflects nonpositivity at all labels. -/
theorem checkIncircle_eq_true_iff {V : Type*} [Fintype V] (site : V → Point) (a b c : V) :
    checkIncircle site a b c = true ↔
      ∀ d : V, incircle (site a) (site b) (site c) (site d) ≤ 0 :=
  decide_eq_true_iff

private theorem ccw_center_data {V : Type*} (site : V ↪ Point) (a b c : V)
    (hccw : 0 < orient (site a) (site b) (site c)) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o) :
    dist (castPoint o) (castSites site b) = dist (castPoint o) (castSites site a) ∧
    dist (castPoint o) (castSites site c) = dist (castPoint o) (castSites site a) ∧
    ∀ d : V, (0 < incircle (site a) (site b) (site c) (site d) ↔
      castSites site d ∈ Metric.ball (castPoint o) (dist (castPoint o) (castSites site a))) ∧
      (incircle (site a) (site b) (site c) (site d) = 0 ↔
      castSites site d ∈ Metric.sphere (castPoint o) (dist (castPoint o) (castSites site a))) := by
  obtain ⟨z, hz, hb, hc, hd⟩ := incircle_geometry_ccw (site a) (site b) (site c) hccw
  have he : z = o := Option.some.inj (hz.symm.trans ho)
  subst z
  exact ⟨hb, hc, fun d => ⟨(hd (site d)).1, (hd (site d)).2.1⟩⟩

/-- For a CCW triangle, nonpositivity means no site lies in its real open circumdisk. -/
theorem all_nonpos_iff_empty_open_disk {V : Type*} (site : V ↪ Point) (a b c : V)
    (hccw : 0 < orient (site a) (site b) (site c)) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o) :
    (∀ d : V, incircle (site a) (site b) (site c) (site d) ≤ 0) ↔
      ∀ d : V, castSites site d ∉ Metric.ball (castPoint o) (dist (castPoint o) (castSites site a)) := by
  have hd (d : V) := ((ccw_center_data site a b c hccw ho).2.2 d).1
  simp only [← hd, not_lt]

/-- For either ordering of a noncollinear triangle, the orientation-normalized incircle
comparison excludes all sites from the open circumdisk. -/
theorem all_orient_mul_incircle_nonpos_iff_empty_open_disk {V : Type*}
    (site : V ↪ Point) (a b c : V) (hn : orient (site a) (site b) (site c) ≠ 0)
    {o : Point} (ho : circumcenter? (site a) (site b) (site c) = some o) :
    (∀ d : V, orient (site a) (site b) (site c) *
        incircle (site a) (site b) (site c) (site d) ≤ 0) ↔
      ∀ d : V, castSites site d ∉ Metric.ball (castPoint o) (dist (castPoint o) (castSites site a)) := by
  have hnc := (orient_zero_iff_collinear (site a) (site b) (site c)).not.mp hn
  obtain ⟨z, hz, _, _, hd⟩ := incircle_geometry_of_noncollinear (site a) (site b) (site c) hnc
  have he : z = o := Option.some.inj (hz.symm.trans ho)
  subst z
  have hSign (d : V) : 0 < orient (site a) (site b) (site c) *
      incircle (site a) (site b) (site c) (site d) ↔
      castSites site d ∈ Metric.ball (castPoint o) (dist (castPoint o) (castSites site a)) :=
    (hd (site d)).1
  simp only [← hSign, not_lt]

/-- The open circumdisk is empty exactly when the computed center lies in the three closed cells. -/
theorem empty_open_disk_iff_center_commonCells {V : Type*} [DecidableEq V]
    (site : V ↪ Point) (a b c : V)
    (hccw : 0 < orient (site a) (site b) (site c)) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o) :
    (∀ d : V, castSites site d ∉ Metric.ball (castPoint o) (dist (castPoint o) (castSites site a))) ↔
      castPoint o ∈ Alpha.commonCells (castSites site) ({a, b, c} : Finset V) := by
  obtain ⟨hb, hc, _⟩ := ccw_center_data site a b c hccw ho
  simp only [Metric.mem_ball', not_lt]
  constructor
  · intro h j hj d
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact h d
    · exact hb ▸ h d
    · exact hc ▸ h d
  · intro h d
    exact h a (by simp) d

/-- Any real point of the three common closed cells is the computed circumcenter. -/
theorem commonCells_triangle_point_eq {V : Type*} [DecidableEq V]
    (site : V ↪ Point) (a b c : V)
    (hn : orient (site a) (site b) (site c) ≠ 0) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o)
    {x : Plane} (hx : x ∈ Alpha.commonCells (castSites site) ({a, b, c} : Finset V)) :
    x = castPoint o := by
  have hcol := (orient_zero_iff_collinear (site a) (site b) (site c)).not.mp hn
  let T := realTriangle (site a) (site b) (site c) hcol
  have hSpan : x ∈ affineSpan ℝ (Set.range T.points) := by
    rw [T.affineSpan_eq_top finrank_euclideanSpace_fin]
    exact AffineSubspace.mem_top ℝ _ _
  have hb := Alpha.dist_eq_of_mem_commonCells (castSites site)
    (show b ∈ ({a, b, c} : Finset V) by simp) (show a ∈ ({a, b, c} : Finset V) by simp) hx
  have hc := Alpha.dist_eq_of_mem_commonCells (castSites site)
    (show c ∈ ({a, b, c} : Finset V) by simp) (show a ∈ ({a, b, c} : Finset V) by simp) hx
  have hDist : ∀ i, dist (T.points i) x = dist x (castSites site a) := by
    intro i
    rw [dist_comm (T.points i)]
    fin_cases i
    · rfl
    · exact hb
    · exact hc
  obtain ⟨z, hz, hzCenter, _⟩ := incircle_circumsphere_signs (site a) (site b) (site c) hcol
  have he : z = o := Option.some.inj (hz.symm.trans ho)
  subst z
  exact (T.eq_circumcenter_of_dist_eq hSpan hDist).trans hzCenter.symm

/-- Passing the finite test is equivalent to nonempty common closed Voronoi cells.
Every point in those cells is the computed center. -/
theorem checkIncircle_eq_true_iff_commonCells_nonempty {V : Type*} [DecidableEq V] [Fintype V]
    (site : V ↪ Point) (a b c : V)
    (hccw : 0 < orient (site a) (site b) (site c)) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o) :
    checkIncircle site a b c = true ↔
      (Alpha.commonCells (castSites site) ({a, b, c} : Finset V)).Nonempty := by
  have hCenter := (checkIncircle_eq_true_iff site a b c).trans
    ((all_nonpos_iff_empty_open_disk site a b c hccw ho).trans
      (empty_open_disk_iff_center_commonCells site a b c hccw ho))
  constructor
  · intro hc
    exact ⟨castPoint o, hCenter.mp hc⟩
  · rintro ⟨x, hx⟩
    rw [commonCells_triangle_point_eq site a b c hccw.ne' ho hx] at hx
    exact hCenter.mpr hx

/-- A CCW triangle belongs to the actual alpha stage precisely when its open circumdisk is empty
and its squared circumradius is at most the stage grade. -/
theorem triangle_mem_actual_stage_iff {V : Type*} [DecidableEq V]
    (site : V ↪ Point) (a b c : V)
    (hccw : 0 < orient (site a) (site b) (site c)) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o) (t : ℝ) :
    ({a, b, c} : Finset V) ∈ Alpha.complex (castSites site) t ↔
      (∀ d : V, incircle (site a) (site b) (site c) (site d) ≤ 0) ∧
      (sqDist o (site a) : ℝ) ≤ t := by
  have ha : a ∈ ({a, b, c} : Finset V) := by simp
  have hAdmit := (all_nonpos_iff_empty_open_disk site a b c hccw ho).trans
    (empty_open_disk_iff_center_commonCells site a b c hccw ho)
  rw [Alpha.mem_complex_iff _ ha t]
  constructor
  · rintro ⟨x, hx, hxt⟩
    obtain rfl := commonCells_triangle_point_eq site a b c hccw.ne' ho hx
    rw [castSites_apply, distSq_cast] at hxt
    exact ⟨hAdmit.mpr hx, hxt⟩
  · rintro ⟨h, ht⟩
    refine ⟨castPoint o, hAdmit.mp h, ?_⟩
    exact (distSq_cast o (site a)).trans_le ht

/-- The all-site test characterizes this CCW triangle in the actual alpha carrier. -/
theorem triangle_actual_carrier_iff {V : Type*} [DecidableEq V]
    (site : V ↪ Point) (a b c : V)
    (hccw : 0 < orient (site a) (site b) (site c)) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o) :
    ({a, b, c} : Finset V) ∈ Alpha.carrier (castSites site) ↔
      ∀ d : V, incircle (site a) (site b) (site c) (site d) ≤ 0 := by
  rw [← Alpha.exists_mem_complex_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ((triangle_mem_actual_stage_iff site a b c hccw ho t).1 ht).1
  · intro ha
    exact ⟨_, (triangle_mem_actual_stage_iff site a b c hccw ho _).2 ⟨ha, le_rfl⟩⟩

/-- The first occupied alpha grade of a feasible triangle is its squared circumradius. -/
theorem triangle_actual_grade {V : Type*} [DecidableEq V]
    (site : V ↪ Point) (a b c : V)
    (hccw : 0 < orient (site a) (site b) (site c)) {o : Point}
    (ho : circumcenter? (site a) (site b) (site c) = some o)
    (hFace : ({a, b, c} : Finset V) ∈ Alpha.carrier (castSites site)) :
    (Alpha.filter (castSites site)).value ⟨{a, b, c},hFace⟩ = (sqDist o (site a) : ℝ) := by
  have ha := (triangle_actual_carrier_iff site a b c hccw ho).1 hFace
  have hg := Alpha.isLeast_grade (castSites site) ⟨{a, b, c},hFace⟩
  apply le_antisymm
  · exact hg.2 ((triangle_mem_actual_stage_iff site a b c hccw ho _).2 ⟨ha, le_rfl⟩)
  · exact ((triangle_mem_actual_stage_iff site a b c hccw ho _).1 hg.1).2

private theorem labelVertices_eq_triple {V : Type*} [DecidableEq V] (v : Fin 3 → V) :
    labelVertices v = {v 0, v 1, v 2} := by
  ext a
  rw [mem_labelVertices]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- Apply the finite test and exact grade threshold to the label set of a supplied assembly facet. -/
theorem supplied_facet_mem_actual_stage_iff {V I : Type*} [DecidableEq V] [Fintype V]
    (site : V ↪ Point) (tri : I → Fin 3 → V)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (i : I) {o : Point} (ho : circumcenter? (site (tri i 0)) (site (tri i 1))
      (site (tri i 2)) = some o) :
    labelVertices (tri i) ∈ maximalFaces (labelComplex tri) ∧
    ∀ t : ℝ, labelVertices (tri i) ∈ Alpha.complex (castSites site) t ↔
      checkIncircle site (tri i 0) (tri i 1) (tri i 2) = true ∧
        (sqDist o (site (tri i 0)) : ℝ) ≤ t := by
  constructor
  · rw [maximal_label_faces site tri hccw]
    exact ⟨i, rfl⟩
  · intro t
    rw [labelVertices_eq_triple, checkIncircle_eq_true_iff]
    exact triangle_mem_actual_stage_iff site _ _ _ (hccw i) ho t

/-- All three self labels give equality in the CCW incircle comparison. -/
theorem triangle_self_incircles_eq_zero {V : Type*}
    (site : V ↪ Point) (a b c : V) (hccw : 0 < orient (site a) (site b) (site c))
    {o : Point} (ho : circumcenter? (site a) (site b) (site c) = some o) :
    incircle (site a) (site b) (site c) (site a) = 0 ∧
    incircle (site a) (site b) (site c) (site b) = 0 ∧
    incircle (site a) (site b) (site c) (site c) = 0 := by
  obtain ⟨hb, hc, hd⟩ := ccw_center_data site a b c hccw ho
  refine ⟨(hd a).2.mpr ?_, (hd b).2.mpr ?_, (hd c).2.mpr ?_⟩
  · exact Metric.mem_sphere'.2 rfl
  · simpa only [Metric.mem_sphere'] using hb
  · simpa only [Metric.mem_sphere'] using hc

end TDA.Filtration.RationalAlpha.IncircleGrade
