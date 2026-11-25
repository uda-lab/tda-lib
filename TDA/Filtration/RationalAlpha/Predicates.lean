import TDA.Filtration.RationalAlpha.Geometry
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.Circumcenter

set_option autoImplicit false

/-!
# Exact rational planar predicates

Orientation gives the signed doubled area of a triangle. The oriented incircle determinant
is positive inside the circumcircle of a counterclockwise triangle, zero on the circle and
negative outside. The executable predicates use rational polynomial arithmetic.
-/

namespace TDA.Filtration.RationalAlpha
open Module
open scoped Matrix EuclideanSpace

/-- Signed doubled area of the triangle with vertices `a`, `b` and `c`. -/
def orient (a b c : Point) : ℚ := det (normal a b) (normal a c)

/-- The oriented incircle determinant with query `d`, evaluated after translating `d`
to the origin. For a counterclockwise triangle a positive value means strictly inside
its circumcircle. Total; meaningful as a circle test only for a non-degenerate triangle
(`orient a b c ≠ 0`). On collinear triples it is a side-of-line test, and it is `0` on repeated
vertices. -/
def incircle (a b c d : Point) : ℚ :=
  sqDist d a * det (normal d b) (normal d c) -
    sqDist d b * det (normal d a) (normal d c) +
    sqDist d c * det (normal d a) (normal d b)

/-- An equidistant center factors incircle into orientation times the squared radius gap. -/
theorem incircle_eq_radius_gap (a b c d o : Point)
    (hb : sqDist o b = sqDist o a) (hc : sqDist o c = sqDist o a) :
    incircle a b c d = orient a b c * (sqDist o a - sqDist o d) := by
  calc
    incircle a b c d =
        (sqDist o a - sqDist o d) * det (normal d b) (normal d c) -
        (sqDist o b - sqDist o d) * det (normal d a) (normal d c) +
        (sqDist o c - sqDist o d) * det (normal d a) (normal d b) := by
      rcases a with ⟨ax, ay⟩
      rcases b with ⟨bx, by'⟩
      rcases c with ⟨cx, cy⟩
      rcases d with ⟨dx, dy⟩
      rcases o with ⟨ox, oy⟩
      simp only [incircle, sqDist, det, normal]
      ring
    _ = orient a b c * (sqDist o a - sqDist o d) := by
      rw [hb, hc]
      rcases a with ⟨ax, ay⟩
      rcases b with ⟨bx, by'⟩
      rcases c with ⟨cx, cy⟩
      rcases d with ⟨dx, dy⟩
      simp only [orient, det, normal]
      ring

/-- For a counterclockwise triangle, incircle is positive exactly when the query is
closer to the circumcenter than the vertices, in squared distance. -/
theorem incircle_pos_iff_sqDist_lt (a b c d o : Point) (hccw : 0 < orient a b c)
    (hb : sqDist o b = sqDist o a) (hc : sqDist o c = sqDist o a) :
    0 < incircle a b c d ↔ sqDist o d < sqDist o a := by
  rw [incircle_eq_radius_gap a b c d o hb hc, mul_pos_iff_of_pos_left hccw, sub_pos]

/-- Either adjacent transposition reverses orientation. -/
theorem orient_swaps (a b c : Point) :
    orient b a c = -orient a b c ∧ orient a c b = -orient a b c := by
  simp only [orient, det, normal]
  constructor <;> ring

/-- Every adjacent transposition of the four determinant arguments reverses the sign. -/
theorem incircle_swaps (a b c d : Point) :
    incircle b a c d = -incircle a b c d ∧
    incircle a c b d = -incircle a b c d ∧
    incircle a b d c = -incircle a b c d := by
  simp only [incircle, sqDist, det, normal]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- The orientation of the standard orthonormal coordinate basis of the real plane. -/
noncomputable def planeOrientation : Orientation ℝ Plane (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

private theorem plane_areaForm (u v : Plane) :
    planeOrientation.areaForm u v = u 0 * v 1 - u 1 * v 0 := by
  rw [planeOrientation.areaForm_to_volumeForm,
    planeOrientation.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Basis.det_apply, Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm]

private theorem castPoint_zero (p : Point) : castPoint p 0 = (p.1 : ℝ) := rfl
private theorem castPoint_one (p : Point) : castPoint p 1 = (p.2 : ℝ) := rfl

/-- The rational orientation agrees with the real area form in the coordinate orientation. -/
theorem orient_eq_areaForm (a b c : Point) :
    (orient a b c : ℝ) =
      planeOrientation.areaForm (castPoint b - castPoint a) (castPoint c - castPoint a) := by
  rw [plane_areaForm]
  simp [orient, det, normal, PiLp.sub_apply, castPoint_zero, castPoint_one]

/-- Orientation is the projection score against the left normal of the directed base. -/
theorem orient_eq_left_normal (a b c : Point) :
    (orient a b c : ℝ) =
      inner ℝ (planeOrientation.rightAngleRotation (castPoint b - castPoint a))
        (castPoint c - castPoint a) := by
  rw [planeOrientation.inner_rightAngleRotation_left, orient_eq_areaForm]

/-- With a nonzero base, orientation is twice the signed base-height area.
The signed height is the projection onto the unit left normal. -/
theorem orient_eq_twice_signed_area (a b c : Point) (hab : a ≠ b) :
    (orient a b c : ℝ) =
      2 * (‖castPoint b - castPoint a‖ *
        (inner ℝ (planeOrientation.rightAngleRotation (castPoint b - castPoint a))
          (castPoint c - castPoint a) / ‖castPoint b - castPoint a‖) / 2) := by
  rw [orient_eq_left_normal]
  have h : ‖castPoint b - castPoint a‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (castPoint_injective.ne (Ne.symm hab)))
  field_simp

private theorem det_zero_iff_smul (u v : Plane) (hu : u ≠ 0) :
    u 0 * v 1 - u 1 * v 0 = 0 ↔ ∃ t : ℝ, v = t • u := by
  constructor
  · intro hd
    by_cases h₀ : u 0 = 0
    · have h₁ : u 1 ≠ 0 := by
        intro h₁
        apply hu
        ext i
        fin_cases i
        · exact h₀
        · exact h₁
      refine ⟨v 1 / u 1, ?_⟩
      ext i
      fin_cases i
      · change v 0 = (v 1 / u 1) * u 0
        rw [h₀, mul_zero]
        have hh : u 1 * v 0 = 0 := by simpa [h₀] using hd
        exact (mul_eq_zero.mp hh).resolve_left h₁
      · change v 1 = (v 1 / u 1) * u 1
        exact (div_mul_cancel₀ _ h₁).symm
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i
      · change v 0 = (v 0 / u 0) * u 0
        exact (div_mul_cancel₀ _ h₀).symm
      · change v 1 = (v 0 / u 0) * u 1
        rw [div_mul_eq_mul_div, eq_div_iff h₀]
        linarith only [hd]
  · rintro ⟨t, rfl⟩
    change u 0 * (t * u 1) - u 1 * (t * u 0) = 0
    ring

/-- Orientation vanishes exactly when the cast vertices are collinear, including coincidences. -/
theorem orient_zero_iff_collinear (a b c : Point) :
    orient a b c = 0 ↔ Collinear ℝ ({castPoint a, castPoint b, castPoint c} : Set Plane) := by
  by_cases hab : a = b
  · subst b
    simpa [orient, normal, det] using (collinear_pair ℝ (castPoint a) (castPoint c))
  have hn : castPoint b - castPoint a ≠ 0 :=
    sub_ne_zero.mpr (castPoint_injective.ne (Ne.symm hab))
  have hz : (orient a b c : ℝ) = 0 ↔ orient a b c = 0 := by exact_mod_cast Iff.rfl
  rw [← hz, orient_eq_areaForm, plane_areaForm]
  rw [collinear_iff_of_mem (p₀ := castPoint a)
    (s := ({castPoint a, castPoint b, castPoint c} : Set Plane)) (by simp)]
  constructor
  · intro ha
    obtain ⟨t, ht⟩ := (det_zero_iff_smul _ _ hn).1 ha
    refine ⟨castPoint b - castPoint a, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨t, ?_⟩
      change castPoint c = t • (castPoint b - castPoint a) + castPoint a
      rw [← ht, sub_add_cancel]
  · rintro ⟨v, hv⟩
    obtain ⟨s, hs⟩ := hv (castPoint b) (by simp)
    obtain ⟨t, ht⟩ := hv (castPoint c) (by simp)
    have hs' : castPoint b - castPoint a = s • v := by simp [hs]
    have ht' : castPoint c - castPoint a = t • v := by simp [ht]
    rw [hs', ht']
    change (s * v 0) * (t * v 1) - (s * v 1) * (t * v 0) = 0
    ring

/-- The rational circumcenter computation returns an equidistant point for a noncollinear triple. -/
theorem circumcenter_exists_eq_sqDist (a b c : Point) (h : orient a b c ≠ 0) :
    ∃ o : Point, circumcenter? a b c = some o ∧
      sqDist o b = sqDist o a ∧ sqDist o c = sqDist o a := by
  let u := normal a b
  let v := normal a c
  let z := det u v
  have hz : z ≠ 0 := h
  let o : Point := ((offset a b * v.2 - u.2 * offset a c) / z,
      (u.1 * offset a c - offset a b * v.1) / z)
  refine ⟨o, ?_, ?_⟩
  · change (if z = 0 then none else some o) = some o
    exact ite_eq_right hz
  have hb : u.1 * o.1 + u.2 * o.2 = offset a b := by
    dsimp only [o]
    field_simp [hz]
    dsimp only [z, det]
    ring
  have hc : v.1 * o.1 + v.2 * o.2 = offset a c := by
    dsimp only [o]
    field_simp [hz]
    dsimp only [z, det]
    ring
  dsimp only [u, v, normal, offset] at hb hc
  constructor
  · unfold sqDist
    nlinarith only [hb]
  · unfold sqDist
    nlinarith only [hc]

private theorem dist_lt_iff_sqDist_lt (o u v : Point) :
    dist (castPoint o) (castPoint u) < dist (castPoint o) (castPoint v) ↔
      sqDist o u < sqDist o v := by
  rw [← sq_lt_sq₀ dist_nonneg dist_nonneg, distSq_cast, distSq_cast]
  exact_mod_cast Iff.rfl

private theorem dist_eq_iff_sqDist_eq (o u v : Point) :
    dist (castPoint o) (castPoint u) = dist (castPoint o) (castPoint v) ↔
      sqDist o u = sqDist o v := by
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, distSq_cast, distSq_cast]
  exact_mod_cast Iff.rfl

private theorem mul_neg_iff_pos_left {a b : ℚ} (ha : 0 < a) :
    a * b < 0 ↔ b < 0 := by
  rw [← neg_pos, ← mul_neg, mul_pos_iff_of_pos_left ha, neg_pos]

/-- On a noncollinear triangle, the product of orientation and incircle is positive inside
the circumcircle and negative outside. Incircle vanishes exactly on the circumcircle. -/
theorem incircle_geometry_of_noncollinear (a b c : Point)
    (h : ¬ Collinear ℝ ({castPoint a, castPoint b, castPoint c} : Set Plane)) :
    ∃ o : Point, circumcenter? a b c = some o ∧
      dist (castPoint o) (castPoint b) = dist (castPoint o) (castPoint a) ∧
      dist (castPoint o) (castPoint c) = dist (castPoint o) (castPoint a) ∧
      ∀ d : Point,
        let r := dist (castPoint o) (castPoint a)
        (0 < orient a b c * incircle a b c d ↔ castPoint d ∈ Metric.ball (castPoint o) r) ∧
        (incircle a b c d = 0 ↔ castPoint d ∈ Metric.sphere (castPoint o) r) ∧
        (orient a b c * incircle a b c d < 0 ↔ r < dist (castPoint o) (castPoint d)) := by
  have hn : orient a b c ≠ 0 := (orient_zero_iff_collinear a b c).not.mpr h
  obtain ⟨o, ho, hb, hc⟩ := circumcenter_exists_eq_sqDist a b c hn
  refine ⟨o, ho, (dist_eq_iff_sqDist_eq ..).2 hb, (dist_eq_iff_sqDist_eq ..).2 hc, ?_⟩
  intro d
  dsimp only
  have hh := incircle_eq_radius_gap a b c d o hb hc
  have hp : 0 < orient a b c * orient a b c := mul_self_pos.mpr hn
  rw [Metric.mem_ball', Metric.mem_sphere', dist_lt_iff_sqDist_lt, dist_eq_iff_sqDist_eq,
    dist_lt_iff_sqDist_lt, hh]
  refine ⟨?_, ?_, ?_⟩
  · rw [← mul_assoc, mul_pos_iff_of_pos_left hp, sub_pos]
  · rw [mul_eq_zero, or_iff_right hn, sub_eq_zero, eq_comm]
  · rw [← mul_assoc, mul_neg_iff_pos_left hp, sub_neg]

/-- For a counterclockwise triangle, the positive, zero and negative incircle signs
characterize the open circumdisk, circumcircle and strict exterior, respectively. -/
theorem incircle_geometry_ccw (a b c : Point) (h : 0 < orient a b c) :
    ∃ o : Point, circumcenter? a b c = some o ∧
      dist (castPoint o) (castPoint b) = dist (castPoint o) (castPoint a) ∧
      dist (castPoint o) (castPoint c) = dist (castPoint o) (castPoint a) ∧
      ∀ d : Point,
        let r := dist (castPoint o) (castPoint a)
        (0 < incircle a b c d ↔ castPoint d ∈ Metric.ball (castPoint o) r) ∧
        (incircle a b c d = 0 ↔ castPoint d ∈ Metric.sphere (castPoint o) r) ∧
        (incircle a b c d < 0 ↔ r < dist (castPoint o) (castPoint d)) := by
  obtain ⟨o, ho, hb, hc, hd⟩ := incircle_geometry_of_noncollinear a b c
    ((orient_zero_iff_collinear a b c).not.mp (ne_of_gt h))
  refine ⟨o, ho, hb, hc, fun d => ?_⟩
  simpa only [mul_pos_iff_of_pos_left h, mul_neg_iff_pos_left h] using hd d

/-- The real simplex given by three noncollinear rational sites. -/
noncomputable def realTriangle (a b c : Point)
    (h : ¬ Collinear ℝ ({castPoint a, castPoint b, castPoint c} : Set Plane)) :
    Affine.Simplex ℝ Plane 2 :=
  ⟨![castPoint a, castPoint b, castPoint c], affineIndependent_iff_not_collinear_set.mpr h⟩

/-- The rational circumcenter and all three incircle signs agree with the canonical
real circumcenter and circumsphere of the noncollinear triangle. -/
theorem incircle_circumsphere_signs (a b c : Point)
    (h : ¬ Collinear ℝ ({castPoint a, castPoint b, castPoint c} : Set Plane)) :
    let t := realTriangle a b c h
    ∃ o : Point, circumcenter? a b c = some o ∧ castPoint o = t.circumcenter ∧
      ∀ d : Point,
        (0 < orient a b c * incircle a b c d ↔
          castPoint d ∈ Metric.ball t.circumcenter t.circumradius) ∧
        (incircle a b c d = 0 ↔ castPoint d ∈ t.circumsphere) ∧
        (orient a b c * incircle a b c d < 0 ↔
          t.circumradius < dist t.circumcenter (castPoint d)) := by
  let t := realTriangle a b c h
  change ∃ o : Point, circumcenter? a b c = some o ∧ castPoint o = t.circumcenter ∧ _
  obtain ⟨o, ho, hb, hc, hd⟩ := incircle_geometry_of_noncollinear a b c h
  have hSpan : castPoint o ∈ affineSpan ℝ (Set.range t.points) := by
    rw [t.affineSpan_eq_top finrank_euclideanSpace_fin]
    exact AffineSubspace.mem_top ℝ _ _
  have hDist : ∀ i, dist (t.points i) (castPoint o) = dist (castPoint o) (castPoint a) := by
    intro i
    rw [dist_comm (t.points i)]
    fin_cases i
    · rfl
    · exact hb
    · exact hc
  have hO := t.eq_circumcenter_of_dist_eq hSpan hDist
  have hR := t.eq_circumradius_of_dist_eq hSpan hDist
  refine ⟨o, ho, hO, fun d => ?_⟩
  have hs := hd d
  dsimp only at hs
  rw [hR, hO] at hs
  rw [EuclideanGeometry.mem_sphere, Affine.Simplex.circumsphere_center,
    Affine.Simplex.circumsphere_radius, dist_comm (castPoint d)]
  simpa only [Metric.mem_sphere'] using hs

end TDA.Filtration.RationalAlpha
