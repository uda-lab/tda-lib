import TDA.Filtration.RationalAlpha
import TDA.Filtration.RationalAlpha.Predicates
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Set.ProjIcc

set_option autoImplicit false

/-!
# Exact alpha grades of rational planar edges

The common closed cells of two distinct labels lie on their perpendicular bisector.
Along that line, the other sites impose weak affine comparisons. The smallest
squared radius is attained at the feasible parameter closest to the midpoint.
-/

namespace TDA.Filtration.RationalAlpha.EdgeGrade

open Set TDA.Simplicial
open scoped Matrix

noncomputable section

private theorem castPoint_x (p : Point) : castPoint p 0 = (p.1 : ℝ) := rfl
private theorem castPoint_y (p : Point) : castPoint p 1 = (p.2 : ℝ) := rfl

/-- The midpoint plus the parameter times the counterclockwise quarter-turn of the edge vector. -/
def bisectorPoint (p q : Point) (t : ℝ) : Plane :=
  !₂[((p.1 : ℝ) + q.1) / 2 - t * ((q.2 : ℝ) - p.2),
    ((p.2 : ℝ) + q.2) / 2 + t * ((q.1 : ℝ) - p.1)]

private theorem bisector_x (p q : Point) (t : ℝ) :
    bisectorPoint p q t 0 = ((p.1 : ℝ) + q.1) / 2 - t * ((q.2 : ℝ) - p.2) := rfl
private theorem bisector_y (p q : Point) (t : ℝ) :
    bisectorPoint p q t 1 = ((p.2 : ℝ) + q.2) / 2 + t * ((q.1 : ℝ) - p.1) := rfl

/-- Zero gives the rational midpoint, embedded in the real plane. -/
theorem bisectorPoint_zero (p q : Point) : bisectorPoint p q 0 = castPoint (RationalAlpha.midpoint p q) := by
  ext i
  fin_cases i
  · change bisectorPoint p q 0 0 = castPoint (RationalAlpha.midpoint p q) 0
    rw [bisector_x, castPoint_x]
    simp [RationalAlpha.midpoint]
  · change bisectorPoint p q 0 1 = castPoint (RationalAlpha.midpoint p q) 1
    rw [bisector_y, castPoint_y]
    simp [RationalAlpha.midpoint]

/-- Each parameter satisfies the perpendicular-bisector equation. -/
theorem bisector_equation (p q : Point) (t : ℝ) :
    linearForm (normal p q) (bisectorPoint p q t) = (offset p q : ℝ) := by
  simp only [linearForm, normal, offset, bisector_x, bisector_y]
  push_cast
  ring

private theorem normal_nonzero (p q : Point) (hne : p ≠ q) :
    ((q.1 : ℝ) - p.1 ≠ 0) ∨ ((q.2 : ℝ) - p.2 ≠ 0) := by
  by_contra! hn
  apply hne
  apply Prod.ext
  · exact_mod_cast (sub_eq_zero.mp hn.1).symm
  · exact_mod_cast (sub_eq_zero.mp hn.2).symm

/-- Every real point on the bisector of distinct sites has a parameter. -/
theorem exists_bisectorPoint {p q : Point} (hne : p ≠ q) {x : Plane}
    (hx : linearForm (normal p q) x = (offset p q : ℝ)) :
    ∃ t, bisectorPoint p q t = x := by
  let u : ℝ := (q.1 : ℝ) - p.1
  let v : ℝ := (q.2 : ℝ) - p.2
  let m : ℝ := ((p.1 : ℝ) + q.1) / 2
  let k : ℝ := ((p.2 : ℝ) + q.2) / 2
  have hdot : u * (x 0 - m) + v * (x 1 - k) = 0 := by
    have hm := bisector_equation p q 0
    simp only [linearForm, normal, Rat.cast_sub, bisector_x, bisector_y,
      zero_mul, sub_zero, add_zero] at hm hx
    dsimp only [u,v,m,k]
    linear_combination hx - hm
  have hcoords : ∃ t : ℝ, m - t * v = x 0 ∧ k + t * u = x 1 := by
    by_cases hu : u = 0
    · have hv : v ≠ 0 := (normal_nonzero p q hne).resolve_left (fun h => h hu)
      have hy : x 1 = k := by
        rw [hu, zero_mul, zero_add] at hdot
        exact sub_eq_zero.mp ((mul_eq_zero.mp hdot).resolve_left hv)
      refine ⟨(m - x 0) / v, ?_, by simp [hu,hy]⟩
      rw [div_mul_cancel₀ _ hv]
      ring
    · refine ⟨(x 1 - k) / u, ?_, ?_⟩
      · apply (mul_left_cancel₀ hu)
        calc
          u * (m - (x 1 - k) / u * v) =
              u * m - (x 1 - k) * v := by field_simp
          _ = u * x 0 := by linear_combination -hdot
      · rw [div_mul_cancel₀ _ hu]
        ring
  obtain ⟨t,hx0,hx1⟩ := hcoords
  refine ⟨t, ?_⟩
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

/-- A nonzero edge vector gives a unique parameter on its bisector. -/
theorem bisectorPoint_injective {p q : Point} (hne : p ≠ q) :
    Function.Injective (bisectorPoint p q) := by
  intro s t h
  rcases normal_nonzero p q hne with hu | hv
  · have he := congrArg (fun x : Plane => x 1) h
    simp only [bisector_y] at he
    have hp : (s - t) * ((q.1 : ℝ) - p.1) = 0 := by linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hu)
  · have he := congrArg (fun x : Plane => x 0) h
    simp only [bisector_x] at he
    have hp : (s - t) * ((q.2 : ℝ) - p.2) = 0 := by linear_combination -he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hv)

/-- The rational residual in the closed comparison with a site at the midpoint of the edge. -/
def edgeRhsRat (p q d : Point) : ℚ :=
  offset p d - ((normal p d).1 * (RationalAlpha.midpoint p q).1 +
    (normal p d).2 * (RationalAlpha.midpoint p q).2)

private def edgeRhs (p q d : Point) : ℝ := edgeRhsRat p q d

private theorem edgeRhs_eq (p q d : Point) :
    edgeRhs p q d =
      (offset p d : ℝ) - linearForm (normal p d) (castPoint (RationalAlpha.midpoint p q)) := by
  simp [edgeRhs, edgeRhsRat, linearForm, castPoint_x, castPoint_y]

/-- The linear comparison with a site has the orientation determinant as its slope. -/
theorem linearForm_bisectorPoint (p q d : Point) (t : ℝ) :
    linearForm (normal p d) (bisectorPoint p q t) =
      linearForm (normal p d) (castPoint (RationalAlpha.midpoint p q)) + (orient p q d : ℝ) * t := by
  simp only [linearForm, normal, RationalAlpha.midpoint, bisector_x, bisector_y, castPoint_x,
    castPoint_y, orient, det]
  push_cast
  ring

/-- Parameters satisfying the closed nearest-site comparison against every label. -/
def edgeParameters {n : ℕ} (p : Fin n ↪ Point) (a b : Fin n) : Set ℝ :=
  {t | ∀ j : Fin n, (orient (p a) (p b) (p j) : ℝ) * t ≤ (edgeRhsRat (p a) (p b) (p j) : ℝ)}

/-- On the bisector, the affine inequalities characterize the actual common closed cells. -/
theorem bisector_mem_commonCells_iff {n : ℕ} (p : Fin n ↪ Point) (a b : Fin n) (t : ℝ) :
    bisectorPoint (p a) (p b) t ∈ Alpha.commonCells (realSites p) ({a,b} : Finset (Fin n)) ↔
      t ∈ edgeParameters p a b := by
  rw [mem_commonCells_iff p (show a ∈ ({a,b} : Finset (Fin n)) by simp)]
  change (_ ∧ _) ↔ ∀ j : Fin n,
    (orient (p a) (p b) (p j) : ℝ) * t ≤ edgeRhs (p a) (p b) (p j)
  constructor
  · rintro ⟨h, _⟩ j
    have hj := h j
    rw [linearForm_bisectorPoint] at hj
    rw [edgeRhs_eq]
    exact le_sub_iff_add_le.mpr (by simpa only [add_comm] using hj)
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · rw [linearForm_bisectorPoint, add_comm, ← le_sub_iff_add_le]
      simpa only [edgeRhs_eq] using h j
    · intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simp [linearForm, normal, offset]
      · exact bisector_equation _ _ _

/-- The common closed cells of two distinct labels form exactly the feasible part of the bisector. -/
theorem edge_commonCells_eq_image {n : ℕ} (p : Fin n ↪ Point) {a b : Fin n} (hab : a ≠ b) :
    Alpha.commonCells (realSites p) ({a,b} : Finset (Fin n)) =
      bisectorPoint (p a) (p b) '' edgeParameters p a b := by
  ext x
  constructor
  · intro hx
    have he := (mem_commonCells_iff p (show a ∈ ({a,b} : Finset (Fin n)) by simp) x).1 hx
    obtain ⟨t,rfl⟩ := exists_bisectorPoint (p.injective.ne hab) (he.2 b (by simp))
    exact ⟨t,(bisector_mem_commonCells_iff p a b t).1 hx,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact (bisector_mem_commonCells_iff p a b t).2 ht

/-- The squared length of the directed edge, in real coordinates. -/
def directionSq (p q : Point) : ℝ :=
  ((q.1 : ℝ) - p.1)^2 + ((q.2 : ℝ) - p.2)^2

/-- The squared edge length is positive for distinct sites. -/
theorem directionSq_pos {p q : Point} (hne : p ≠ q) : 0 < directionSq p q := by
  unfold directionSq
  rcases normal_nonzero p q hne with hx | hy
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hy)

/-- The squared radius at parameter $t$ is $D/4 + D t^2$ for squared edge length $D$. -/
theorem squared_radius_on_bisector (p q : Point) (t : ℝ) :
    dist (bisectorPoint p q t) (castPoint p)^2 =
      directionSq p q / 4 + directionSq p q * t^2 := by
  rw [distSq_coordinates, bisector_x, bisector_y, castPoint_x, castPoint_y]
  unfold directionSq
  ring

private def affineParameters {ι : Type*} (slope rhs : ι → ℝ) : Set ℝ :=
  {t | ∀ j, slope j * t ≤ rhs j}

private def lowerCuts {ι : Type*} (slope rhs : ι → ℝ) : Set ℝ :=
  {l | ∃ j, slope j < 0 ∧ rhs j / slope j = l}

private def upperCuts {ι : Type*} (slope rhs : ι → ℝ) : Set ℝ :=
  {u | ∃ j, 0 < slope j ∧ rhs j / slope j = u}

private theorem affine_mem_iff {ι : Type*} (a b : ι → ℝ) (t : ℝ) :
    t ∈ affineParameters a b ↔
      (∀ j, a j = 0 → 0 ≤ b j) ∧
      (∀ l ∈ lowerCuts a b, l ≤ t) ∧ (∀ u ∈ upperCuts a b, t ≤ u) := by
  constructor
  · intro ht
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · simpa [hj] using ht j
    · rintro _ ⟨j,hj,rfl⟩
      exact (div_le_iff_of_neg hj).2 (by simpa only [mul_comm] using ht j)
    · rintro _ ⟨j,hj,rfl⟩
      exact (le_div_iff₀ hj).2 (by simpa only [mul_comm] using ht j)
  · rintro ⟨hz,hl,hu⟩ j
    rcases lt_trichotomy (a j) 0 with hn | he | hp
    · simpa only [mul_comm] using
        (div_le_iff_of_neg hn).1 (hl _ ⟨j,hn,rfl⟩)
    · simpa [he] using hz j he
    · simpa only [mul_comm] using (le_div_iff₀ hp).1 (hu _ ⟨j,hp,rfl⟩)

private theorem affine_parameter_shapes {ι : Type*} [Finite ι] (a b : ι → ℝ) :
    let K := affineParameters a b
    K = ∅ ∨ K = univ ∨ (∃ l, K = Ici l) ∨ (∃ u, K = Iic u) ∨
      (∃ l u, l < u ∧ K = Icc l u) ∨ (∃ t, K = {t}) := by
  dsimp only
  by_cases hz : ∀ j, a j = 0 → 0 ≤ b j
  · have hmem (t : ℝ) : t ∈ affineParameters a b ↔
        (∀ l ∈ lowerCuts a b, l ≤ t) ∧ (∀ u ∈ upperCuts a b, t ≤ u) := by
      rw [affine_mem_iff]
      exact ⟨And.right, fun h => ⟨hz,h⟩⟩
    have hLf : (lowerCuts a b).Finite :=
      (finite_range (fun j => b j / a j)).subset (by rintro _ ⟨j,_,rfl⟩; exact mem_range_self j)
    have hUf : (upperCuts a b).Finite :=
      (finite_range (fun j => b j / a j)).subset (by rintro _ ⟨j,_,rfl⟩; exact mem_range_self j)
    rcases (lowerCuts a b).eq_empty_or_nonempty with hl | hl
    · rcases (upperCuts a b).eq_empty_or_nonempty with hu | hu
      · exact Or.inr (Or.inl (by ext t; simp [hmem, hl, hu]))
      · have hU := hu.isLeast_csInf hUf
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨sInf (upperCuts a b), ?_⟩)))
        ext t
        simp only [hmem, hl, mem_empty_iff_false, false_implies, implies_true,
          true_and, mem_Iic]
        exact ⟨fun h => h _ hU.1, fun h u hu' => h.trans (hU.2 hu')⟩
    · have hL := hl.isGreatest_csSup hLf
      rcases (upperCuts a b).eq_empty_or_nonempty with hu | hu
      · refine Or.inr (Or.inr (Or.inl ⟨sSup (lowerCuts a b), ?_⟩))
        ext t
        simp only [hmem, hu, mem_empty_iff_false, false_implies, implies_true,
          and_true, mem_Ici]
        exact ⟨fun h => h _ hL.1, fun h l hl' => (hL.2 hl').trans h⟩
      · have hU := hu.isLeast_csInf hUf
        let l := sSup (lowerCuts a b)
        let u := sInf (upperCuts a b)
        have hK : affineParameters a b = Icc l u := by
          ext t
          simp only [hmem, mem_Icc]
          exact ⟨fun h => ⟨h.1 _ hL.1,h.2 _ hU.1⟩,
            fun h => ⟨fun _ hx => (hL.2 hx).trans h.1, fun _ hx => h.2.trans (hU.2 hx)⟩⟩
        rcases lt_trichotomy l u with h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l,u,h,hK⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨u, by rw [hK,h,Icc_self]⟩))))
        · exact Or.inl (hK.trans (Icc_eq_empty_of_lt h))
  · refine Or.inl (eq_empty_iff_forall_notMem.mpr fun t ht => hz ?_)
    exact ((affine_mem_iff a b t).1 ht).1

/-- Finite closed affine comparisons give an empty set, the line, a closed ray, a proper closed
interval, or a singleton. Equality in a site comparison is allowed. -/
theorem edge_parameter_shapes {n : ℕ} (p : Fin n ↪ Point) (a b : Fin n) :
    let K := edgeParameters p a b
    K = ∅ ∨ K = univ ∨ (∃ l, K = Ici l) ∨ (∃ u, K = Iic u) ∨
      (∃ l u, l < u ∧ K = Icc l u) ∨ (∃ t, K = {t}) :=
  affine_parameter_shapes (fun j => (orient (p a) (p b) (p j) : ℝ))
    (fun j => edgeRhs (p a) (p b) (p j))

/-- The actual first grade of a feasible edge is attained at a parameter minimizing squared
distance to zero. The midpoint is optimal when feasible. Otherwise the optimum is an attained
finite endpoint, with either a least positive or greatest negative feasible parameter. -/
theorem edge_actual_grade_projection {n : ℕ} (p : Fin n ↪ Point) {a b : Fin n} (hab : a ≠ b)
    (hf : ({a,b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p)) :
    ∃ z ∈ edgeParameters p a b,
      (Alpha.filter (realSites p)).value ⟨{a,b},hf⟩ =
        directionSq (p a) (p b) / 4 + directionSq (p a) (p b) * z^2 ∧
      (∀ t ∈ edgeParameters p a b, z^2 ≤ t^2) ∧
      (z = 0 ↔ (0 : ℝ) ∈ edgeParameters p a b) ∧
      (z ≠ 0 → IsLeast (edgeParameters p a b) z ∨ IsGreatest (edgeParameters p a b) z) := by
  have hleast := Alpha.isLeast_sq_dist (realSites p) ⟨{a,b},hf⟩
    (show a ∈ ({a,b} : Finset (Fin n)) by simp)
  obtain ⟨x,hx,hg⟩ := hleast.1
  rw [edge_commonCells_eq_image p hab] at hx
  obtain ⟨z,hz,rfl⟩ := hx
  change dist (bisectorPoint (p a) (p b) z) (castPoint (p a)) ^ 2 = _ at hg
  rw [squared_radius_on_bisector] at hg
  have hsq {t : ℝ} (ht : t ∈ edgeParameters p a b) : z^2 ≤ t^2 := by
    have ht' := hleast.2 ⟨bisectorPoint (p a) (p b) t,
      (bisector_mem_commonCells_iff p a b t).2 ht,rfl⟩
    change _ ≤ dist (bisectorPoint (p a) (p b) t) (castPoint (p a)) ^ 2 at ht'
    rw [← hg,squared_radius_on_bisector,add_le_add_iff_left] at ht'
    exact le_of_mul_le_mul_left ht' (directionSq_pos (p.injective.ne hab))
  have hzero : z = 0 ↔ (0 : ℝ) ∈ edgeParameters p a b := by
    constructor
    · rintro rfl
      exact hz
    · intro ht
      have h := hsq ht
      nlinarith
  refine ⟨z,hz,hg.symm,fun _ => hsq,hzero,?_⟩
  · intro hnz
    have hbad : ¬ ∀ j, (0 : ℝ) ≤ (edgeRhsRat (p a) (p b) (p j) : ℝ) := by
      intro h
      exact hnz (hzero.mpr (fun j => by simpa only [mul_zero] using h j))
    push Not at hbad
    obtain ⟨j,hj⟩ := hbad
    let c : ℝ := (orient (p a) (p b) (p j) : ℝ)
    have hs {t : ℝ} (ht : t ∈ edgeParameters p a b) : c * t < 0 := (ht j).trans_lt hj
    by_cases hc : 0 < c
    · have hnonpos {t : ℝ} (ht : t ∈ edgeParameters p a b) : t ≤ 0 := by
        by_contra! H
        exact (mul_pos hc H).not_gt (hs ht)
      refine Or.inr ⟨hz,fun t ht => ?_⟩
      have h := (sq_le_sq₀ (neg_nonneg.mpr (hnonpos hz)) (neg_nonneg.mpr (hnonpos ht))).mp
        (by simpa only [neg_sq] using hsq ht)
      exact (neg_le_neg_iff.mp h)
    · have hnonneg {t : ℝ} (ht : t ∈ edgeParameters p a b) : 0 ≤ t := by
        by_contra! H
        exact (mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hc) H.le).not_gt (hs ht)
      exact Or.inl ⟨hz,fun t ht => (sq_le_sq₀ (hnonneg hz) (hnonneg ht)).mp (hsq ht)⟩

/-- The pair occurs in the actual Alpha carrier exactly when the parameter set is nonempty. -/
theorem edge_carrier_iff_parameters_nonempty {n : ℕ} (p : Fin n ↪ Point)
    {a b : Fin n} (hab : a ≠ b) :
    ({a,b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p) ↔
      (edgeParameters p a b).Nonempty := by
  rw [← Alpha.exists_mem_complex_iff]
  simp only [Alpha.mem_complex_iff (realSites p) (show a ∈ ({a,b} : Finset (Fin n)) by simp),
    edge_commonCells_eq_image p hab]
  constructor
  · rintro ⟨_,x,⟨t,ht,rfl⟩,_⟩
    exact ⟨t,ht⟩
  · rintro ⟨t,ht⟩
    exact ⟨_,_,⟨t,ht,rfl⟩,le_rfl⟩

/-- The first grade is the squared half-distance exactly when the midpoint belongs to both cells. -/
theorem edge_actual_grade_eq_midpoint_iff {n : ℕ} (p : Fin n ↪ Point)
    {a b : Fin n} (hab : a ≠ b) (hf : ({a,b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p)) :
    (Alpha.filter (realSites p)).value ⟨{a,b},hf⟩ = directionSq (p a) (p b) / 4 ↔
      castPoint (RationalAlpha.midpoint (p a) (p b)) ∈
        Alpha.commonCells (realSites p) ({a,b} : Finset (Fin n)) := by
  obtain ⟨z,_,hg,_,hz,_⟩ := edge_actual_grade_projection p hab hf
  rw [← bisectorPoint_zero, bisector_mem_commonCells_iff, ← hz, hg]
  constructor
  · intro h
    have hprod : directionSq (p a) (p b) * z^2 = 0 := by linarith
    have hzsq := (mul_eq_zero.mp hprod).resolve_left
      (directionSq_pos (p.injective.ne hab)).ne'
    nlinarith
  · rintro rfl
    ring

/-- A feasible parameter closest to zero gives the exact closed threshold at every actual
Alpha stage, including the threshold itself. -/
theorem edge_stage_of_parameter_min {n : ℕ} (p : Fin n ↪ Point) {a b : Fin n}
    (hab : a ≠ b) {z : ℝ} (hz : z ∈ edgeParameters p a b)
    (hmin : ∀ v ∈ edgeParameters p a b, z^2 ≤ v^2) (t : ℝ) :
    ({a,b} : Finset (Fin n)) ∈ Alpha.complex (realSites p) t ↔
      directionSq (p a) (p b) / 4 + directionSq (p a) (p b) * z^2 ≤ t := by
  rw [Alpha.mem_complex_iff (realSites p) (show a ∈ ({a,b} : Finset (Fin n)) by simp),
    edge_commonCells_eq_image p hab]
  constructor
  · rintro ⟨_,⟨v,hv,rfl⟩,hvt⟩
    change dist (bisectorPoint (p a) (p b) v) (castPoint (p a)) ^ 2 ≤ t at hvt
    rw [squared_radius_on_bisector] at hvt
    exact (add_le_add_right (mul_le_mul_of_nonneg_left (hmin v hv)
      (directionSq_pos (p.injective.ne hab)).le) _).trans hvt
  · intro h
    refine ⟨_,⟨z,hz,rfl⟩,?_⟩
    change dist (bisectorPoint (p a) (p b) z) (castPoint (p a)) ^ 2 ≤ t
    rwa [squared_radius_on_bisector]

/-- On a nonempty closed interval, projecting zero minimizes the squared parameter. -/
theorem interval_projection {l u : ℝ} (hlu : l ≤ u) :
    IsLeast ((fun t : ℝ => t^2) '' Icc l u) ((Set.projIcc l u hlu 0 : ℝ)^2) := by
  rw [Set.coe_projIcc, min_comm u 0]
  let z := max l (min 0 u)
  have hz : z ∈ Icc l u := ⟨le_max_left _ _,max_le hlu (min_le_right _ _)⟩
  refine ⟨⟨z,hz,rfl⟩,?_⟩
  rintro _ ⟨t,ht,rfl⟩
  rcases le_or_gt 0 u with hu | hu
  · rw [min_eq_left hu]
    rcases le_or_gt l 0 with hl | hl
    · rw [max_eq_right hl,zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · rw [max_eq_left hl.le]
      exact (sq_le_sq₀ hl.le (hl.le.trans ht.1)).2 ht.1
  · rw [min_eq_right hu.le,max_eq_right hlu]
    simpa only [neg_sq] using
      (sq_le_sq₀ (neg_nonneg.mpr hu.le) (neg_nonneg.mpr (ht.2.trans hu.le))).2
        (neg_le_neg ht.2)


/-- Reversing the edge reverses its parameter while preserving the represented point. -/
theorem bisectorPoint_swap (p q : Point) (s : ℝ) :
    bisectorPoint q p (-s) = bisectorPoint p q s := by
  ext i
  fin_cases i
  · change bisectorPoint q p (-s) 0 = bisectorPoint p q s 0
    rw [bisector_x, bisector_x]
    ring
  · change bisectorPoint q p (-s) 1 = bisectorPoint p q s 1
    rw [bisector_y, bisector_y]
    ring

/-- Reversing the edge reflects the feasible interval about zero. -/
theorem edgeParameters_swap_iff {n : ℕ} (p : Fin n ↪ Point) (a b : Fin n) (s : ℝ) :
    -s ∈ edgeParameters p b a ↔ s ∈ edgeParameters p a b := by
  rw [← bisector_mem_commonCells_iff p b a, ← bisector_mem_commonCells_iff p a b,
    bisectorPoint_swap, Finset.pair_comm b a]

/-- The squared edge length agrees with the existing rational distance calculation. -/
theorem directionSq_eq_sqDist (p q : Point) : directionSq p q = (sqDist q p : ℝ) := by
  simp [directionSq, sqDist]

end
end TDA.Filtration.RationalAlpha.EdgeGrade
