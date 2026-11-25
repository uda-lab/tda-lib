import TDA.Filtration.RationalAlpha.SignedBoundaryCoverage
import TDA.Filtration.RationalAlpha.PredicatesExamples

set_option autoImplicit false

/-!
# Exact planar signed-boundary fixtures

The trapezoid and all triangle carriers use the cast rational sites. A diagonal split
satisfies signed boundary equality and has disjoint interiors. Exact coefficients and
point witnesses detect a missing triangle and an overlapping list with the correct total
area. The triangular hull also demonstrates that coverage alone permits an unused site.
-/

namespace TDA.Filtration.RationalAlpha.SignedBoundaryExamples

open Set SignedBoundary
open scoped Matrix
open TDA.Filtration.RationalAlpha (Plane Point castPoint orient)
open TDA.Filtration.RationalAlpha.PredicatesExamples (A B C D)

/-- The four labels used in the concrete configurations. -/
abbrev Label := Fin 4

/-- The four rational sites of the trapezoid in CCW order. -/
def quad : Label → Point := ![A,B,C,D]
private abbrev Q (i : Label) : Plane := castPoint (quad i)

/-- The positively ordered hull cycle A, B, C, D. -/
def cycle : Fin 4 → Label := id
/-- The real convex hull of the four trapezoid sites. -/
abbrev trapezoidHull : Set Plane := siteHull quad cycle
/-- A directed side of the trapezoid in cycle order. -/
abbrev hullEdge (i : Fin 4) : Plane × Plane := realEdge quad (cycleEdges cycle i)

/-- The ordered triangle ABC. -/
def abc : Fin 3 → Label := ![0,1,2]
/-- The ordered triangle ACD. -/
def acd : Fin 3 → Label := ![0,2,3]
/-- The ordered triangle BCD. -/
def bcd : Fin 3 → Label := ![1,2,3]
/-- The two-triangle family split along AC. -/
def good : Fin 2 → Fin 3 → Label := ![abc,acd]
/-- The single-triangle family ABC. -/
def incomplete : Fin 1 → Fin 3 → Label := ![abc]
/-- The family ABC and BCD, which has an overlap and a gap. -/
def overlap : Fin 2 → Fin 3 → Label := ![abc,bcd]

@[simp] private theorem q00 : Q 0 0 = 0 := by change ((0 : ℚ) : ℝ) = 0; norm_num
@[simp] private theorem q01 : Q 0 1 = 0 := by change ((0 : ℚ) : ℝ) = 0; norm_num
@[simp] private theorem q10 : Q 1 0 = 4 := by change ((4 : ℚ) : ℝ) = 4; norm_num
@[simp] private theorem q11 : Q 1 1 = 0 := by change ((0 : ℚ) : ℝ) = 0; norm_num
@[simp] private theorem q20 : Q 2 0 = 3 := by change ((3 : ℚ) : ℝ) = 3; norm_num
@[simp] private theorem q21 : Q 2 1 = 2 := by change ((2 : ℚ) : ℝ) = 2; norm_num
@[simp] private theorem q30 : Q 3 0 = 0 := by change ((0 : ℚ) : ℝ) = 0; norm_num
@[simp] private theorem q31 : Q 3 1 = 2 := by change ((2 : ℚ) : ℝ) = 2; norm_num

private theorem quad_injective : Function.Injective quad := by
  change ∀ a b : Label, quad a = quad b → a = b
  decide +kernel

private theorem quad_general : ∀ a b c : Label, a ≠ b → a ≠ c → b ≠ c →
    orient (quad a) (quad b) (quad c) ≠ 0 := by decide +kernel

private theorem side_ab (x : Plane) : edgeSide (hullEdge 0) x = 4 * x 1 := by
  change edgeSide (Q 0,Q 1) x = _
  simp [edgeSide]

private theorem side_bc (x : Plane) : edgeSide (hullEdge 1) x = 8 - 2 * x 0 - x 1 := by
  change edgeSide (Q 1,Q 2) x = _
  simp [edgeSide]
  ring

private theorem side_cd (x : Plane) : edgeSide (hullEdge 2) x = 3 * (2 - x 1) := by
  change edgeSide (Q 2,Q 3) x = _
  simp [edgeSide]
  ring

private theorem side_da (x : Plane) : edgeSide (hullEdge 3) x = 2 * x 0 := by
  change edgeSide (Q 3,Q 0) x = _
  simp [edgeSide]

private theorem side_ac (x : Plane) : edgeSide (Q 0,Q 2) x = 3 * x 1 - 2 * x 0 := by
  simp [edgeSide]

private theorem side_ca (x : Plane) : edgeSide (Q 2,Q 0) x = 2 * x 0 - 3 * x 1 := by
  simp [edgeSide]
  ring

private theorem side_db (x : Plane) : edgeSide (Q 3,Q 1) x = 2 * x 0 + 4 * x 1 - 8 := by
  simp [edgeSide]
  ring

/-- The intersection of the four closed half-planes of the trapezoid. -/
def region (x : Plane) : Prop := 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 ∧ 2 * x 0 + x 1 ≤ 8

private theorem region_iff (x : Plane) : region x ↔ ∀ i, 0 ≤ edgeSide (hullEdge i) x := by
  constructor
  · rintro ⟨h₀,h₁,h₂,h₃⟩ i
    fin_cases i
    · change 0 ≤ edgeSide (hullEdge 0) x
      rw [side_ab]
      linarith
    · change 0 ≤ edgeSide (hullEdge 1) x
      rw [side_bc]
      linarith
    · change 0 ≤ edgeSide (hullEdge 2) x
      rw [side_cd]
      linarith
    · change 0 ≤ edgeSide (hullEdge 3) x
      rw [side_da]
      linarith
  · intro h
    have h₀ := h 0
    have h₁ := h 1
    have h₂ := h 2
    have h₃ := h 3
    rw [side_ab] at h₀
    rw [side_bc] at h₁
    rw [side_cd] at h₂
    rw [side_da] at h₃
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem each_site_mem_hull (i : Label) : Q i ∈ trapezoidHull :=
  subset_convexHull ℝ _ ⟨i,rfl⟩

private theorem fixture_triangle_subset (v : Fin 3 → Label) : siteTriangle quad v ⊆ trapezoidHull := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl <;> apply each_site_mem_hull

private theorem hull_left (i : Fin 4) (x : Plane) (hx : x ∈ trapezoidHull) : 0 ≤ edgeSide (hullEdge i) x := by
  have hconv : Convex ℝ {y | 0 ≤ edgeSide (hullEdge i) y} := by
    intro p hp q hq a b ha hb hab
    change 0 ≤ edgeSide (hullEdge i) (a • p + b • q)
    rw [edgeSide_combination _ _ _ _ _ hab]
    exact add_nonneg (mul_nonneg ha hp) (mul_nonneg hb hq)
  refine convexHull_min (fun y hy => ?_) hconv hx
  rcases hy with ⟨j,rfl⟩
  change 0 ≤ edgeSide (Q i, Q (i+1)) (Q j)
  rw [side_of_rational_sites]
  have h : ∀ a b : Fin 4, 0 ≤ orient (quad a) (quad (a+1)) (quad b) := by decide +kernel
  exact_mod_cast h i j

private theorem forall_fin3 {P : Fin 3 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  refine ⟨fun h => ⟨h 0,h 1,h 2⟩, fun ⟨h₀,h₁,h₂⟩ i => ?_⟩
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

/-- The three closed half-plane inequalities for the carrier of ABC. -/
theorem mem_abc_iff (x : Plane) : x ∈ siteTriangle quad abc ↔
    0 ≤ 4 * x 1 ∧ 0 ≤ 8 - 2 * x 0 - x 1 ∧ 0 ≤ 2 * x 0 - 3 * x 1 := by
  change x ∈ convexHull ℝ ({Q 0,Q 1,Q 2} : Set Plane) ↔ _
  rw [triangle_mem_iff _ _ _ _ (show 0 < edgeSide (Q 0,Q 1) (Q 2) by
    change 0 < edgeSide (hullEdge 0) (Q 2)
    rw [side_ab,q21]
    norm_num), forall_fin3]
  change (0 ≤ edgeSide (hullEdge 0) x ∧ 0 ≤ edgeSide (hullEdge 1) x ∧
    0 ≤ edgeSide (Q 2,Q 0) x) ↔ _
  rw [side_ab,side_bc,side_ca]

/-- The three closed half-plane inequalities for the carrier of ACD. -/
theorem mem_acd_iff (x : Plane) : x ∈ siteTriangle quad acd ↔
    0 ≤ 3 * x 1 - 2 * x 0 ∧ 0 ≤ 3 * (2 - x 1) ∧ 0 ≤ 2 * x 0 := by
  change x ∈ convexHull ℝ ({Q 0,Q 2,Q 3} : Set Plane) ↔ _
  rw [triangle_mem_iff _ _ _ _ (show 0 < edgeSide (Q 0,Q 2) (Q 3) by
    rw [side_ac,q30,q31]
    norm_num), forall_fin3]
  change (0 ≤ edgeSide (Q 0,Q 2) x ∧ 0 ≤ edgeSide (hullEdge 2) x ∧
    0 ≤ edgeSide (hullEdge 3) x) ↔ _
  rw [side_ac,side_cd,side_da]

/-- The three closed half-plane inequalities for the carrier of BCD. -/
theorem mem_bcd_iff (x : Plane) : x ∈ siteTriangle quad bcd ↔
    0 ≤ 8 - 2 * x 0 - x 1 ∧ 0 ≤ 3 * (2 - x 1) ∧ 0 ≤ 2 * x 0 + 4 * x 1 - 8 := by
  change x ∈ convexHull ℝ ({Q 1,Q 2,Q 3} : Set Plane) ↔ _
  rw [triangle_mem_iff _ _ _ _ (show 0 < edgeSide (Q 1,Q 2) (Q 3) by
    change 0 < edgeSide (hullEdge 1) (Q 3)
    rw [side_bc,q30,q31]
    norm_num), forall_fin3]
  change (0 ≤ edgeSide (hullEdge 1) x ∧ 0 ≤ edgeSide (hullEdge 2) x ∧
    0 ≤ edgeSide (Q 3,Q 1) x) ↔ _
  rw [side_bc,side_cd,side_db]

/-- The four coordinate half-planes describe the actual trapezoid hull. -/
theorem hull_halfplanes (x : Plane) : x ∈ trapezoidHull ↔ region x := by
  refine ⟨fun hx => (region_iff x).2 (fun i => hull_left i x hx), fun hx => ?_⟩
  obtain ⟨h₀,h₁,h₂,h₃⟩ := hx
  by_cases h : 3 * x 1 ≤ 2 * x 0
  · exact fixture_triangle_subset abc ((mem_abc_iff x).2 ⟨by linarith,by linarith,by linarith⟩)
  · exact fixture_triangle_subset acd ((mem_acd_iff x).2 ⟨by linarith,by linarith,by linarith⟩)

private theorem plane_coord_ext {p q : Plane} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  ext i
  have hi : i = 0 ∨ i = 1 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hi with rfl | rfl
  · exact h₀
  · exact h₁

private theorem hull_side_zero_mem_edge (i : Fin 4) (x : Plane) (hx : x ∈ trapezoidHull)
    (hz : edgeSide (hullEdge i) x = 0) : x ∈ segment ℝ (hullEdge i).1 (hullEdge i).2 := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := (hull_halfplanes x).1 hx
  fin_cases i
  · change edgeSide (hullEdge 0) x = 0 at hz
    rw [side_ab] at hz
    change x ∈ segment ℝ (Q 0) (Q 1)
    refine ⟨1 - x 0 / 4, x 0 / 4, by linarith, by linarith, by ring, ?_⟩
    apply plane_coord_ext <;> simp [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    all_goals linarith
  · change edgeSide (hullEdge 1) x = 0 at hz
    rw [side_bc] at hz
    change x ∈ segment ℝ (Q 1) (Q 2)
    refine ⟨1 - x 1 / 2, x 1 / 2, by linarith, by linarith, by ring, ?_⟩
    apply plane_coord_ext <;> simp [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    all_goals linarith
  · change edgeSide (hullEdge 2) x = 0 at hz
    rw [side_cd] at hz
    change x ∈ segment ℝ (Q 2) (Q 3)
    refine ⟨x 0 / 3, 1 - x 0 / 3, by linarith, by linarith, by ring, ?_⟩
    apply plane_coord_ext <;> simp [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    all_goals linarith
  · change edgeSide (hullEdge 3) x = 0 at hz
    rw [side_da] at hz
    change x ∈ segment ℝ (Q 3) (Q 0)
    refine ⟨x 1 / 2, 1 - x 1 / 2, by linarith, by linarith, by ring, ?_⟩
    apply plane_coord_ext <;> simp [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    all_goals linarith

private theorem hull_edge_slope (i : Fin 4) : sideSlope (slopeDir 1) (hullEdge i) ≠ 0 := by
  fin_cases i
  · change sideSlope (slopeDir 1) (Q 0,Q 1) ≠ 0
    norm_num [sideSlope,slopeDir]
  · change sideSlope (slopeDir 1) (Q 1,Q 2) ≠ 0
    norm_num [sideSlope,slopeDir]
  · change sideSlope (slopeDir 1) (Q 2,Q 3) ≠ 0
    norm_num [sideSlope,slopeDir]
  · change sideSlope (slopeDir 1) (Q 3,Q 0) ≠ 0
    norm_num [sideSlope,slopeDir]

private theorem strict_left_mem_interior {k : ℕ} {S : Set Plane} (e : Fin k → Plane × Plane)
    (h : ∀ x, (∀ i, 0 ≤ edgeSide (e i) x) → x ∈ S)
    {x : Plane} (hx : ∀ i, 0 < edgeSide (e i) x) : x ∈ interior S := by
  let U : Set Plane := ⋂ i, {x | 0 < edgeSide (e i) x}
  have ho : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_edgeSide (e i))
  exact interior_maximal (fun z hz => h z fun i =>
    le_of_lt (show 0 < edgeSide (e i) z from mem_iInter.1 hz i)) ho (mem_iInter.2 hx)

/-- The frontier of the trapezoid hull consists of its four closed sides. -/
theorem hull_frontier : frontier trapezoidHull = ⋃ i, segment ℝ (hullEdge i).1 (hullEdge i).2 := by
  have hc : IsClosed trapezoidHull := (Set.finite_range _).isClosed_convexHull ℝ
  ext x
  rw [frontier,hc.closure_eq]
  constructor
  · rintro ⟨hx,hi⟩
    have hz : ∃ i, edgeSide (hullEdge i) x = 0 := by
      by_contra hn
      apply hi
      apply strict_left_mem_interior hullEdge (fun y hy => (hull_halfplanes y).2 ((region_iff y).2 hy))
      intro i
      exact lt_of_le_of_ne (hull_left i x hx) (fun he => hn ⟨i,he.symm⟩)
    obtain ⟨i,hi⟩ := hz
    exact mem_iUnion.2 ⟨i,hull_side_zero_mem_edge i x hx hi⟩
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.1 hx
    have h₁ : (hullEdge i).1 ∈ trapezoidHull := each_site_mem_hull i
    have h₂ : (hullEdge i).2 ∈ trapezoidHull := each_site_mem_hull (i+1)
    refine ⟨(convex_convexHull ℝ _).segment_subset h₁ h₂ hi, fun hy => ?_⟩
    exact (interior_side_pos_of_support (hullEdge i) (hull_left i) 1 (hull_edge_slope i) hy).ne'
      (edgeSide_eq_zero_on_segment (hullEdge i) hi)

/-- The actual trapezoid hull has the certified CCW cycle A, B, C, D. -/
theorem trapezoid_certificate : PolygonCertificate trapezoidHull hullEdge := by
  apply hull_polygonCertificate quad cycle (fun _ _ h => h) quad_general
  · refine ⟨(!₂[1,1] : Plane), strict_left_mem_interior hullEdge
      (fun y hy => (hull_halfplanes y).2 ((region_iff y).2 hy)) ?_⟩
    intro i
    fin_cases i
    · change 0 < edgeSide (hullEdge 0) (!₂[1,1] : Plane)
      norm_num [side_ab]
    · change 0 < edgeSide (hullEdge 1) (!₂[1,1] : Plane)
      norm_num [side_bc]
    · change 0 < edgeSide (hullEdge 2) (!₂[1,1] : Plane)
      norm_num [side_cd]
    · change 0 < edgeSide (hullEdge 3) (!₂[1,1] : Plane)
      norm_num [side_da]
  · exact hull_frontier
  · exact hull_left


private noncomputable def chain {L : Type*} (edges : List (L × L)) : (L × L) →₀ ℤ :=
  (edges.map signedEdge).sum

/-- The signed coefficient from the two directed occurrence counts. -/
def listCoeff {L : Type*} [DecidableEq L] (es : List (L × L)) (e : L × L) : ℤ :=
  (es.count e : ℤ) - (es.count e.swap : ℤ)

private theorem chain_apply_count {L : Type*} [DecidableEq L] (es : List (L × L)) (e : L × L) :
    chain es e = listCoeff es e := by
  induction es with
  | nil => simp [chain,listCoeff]
  | cons a as ih =>
    change (signedEdge a + chain as) e = listCoeff (a :: as) e
    rw [Finsupp.add_apply, ih]
    have hs : a.swap = e ↔ a = e.swap := by
      constructor <;> intro h <;> simpa using congrArg Prod.swap h
    have he : signedEdge a e = (if a = e then 1 else 0) - (if a = e.swap then 1 else 0) := by
      simp only [signedEdge, Finsupp.sub_apply, Finsupp.single_apply, hs]
    rw [he]
    simp only [listCoeff, List.count_cons, beq_iff_eq]
    by_cases h : a = e <;> by_cases hr : a = e.swap <;> simp [h,hr] <;> omega

private theorem chain_append {L : Type*} (a b : List (L × L)) : chain (a ++ b) = chain a + chain b := by
  simp [chain, List.sum_append]

private theorem chain_flatten {L : Type*} (es : List (List (L × L))) :
    chain es.flatten = (es.map chain).sum := by
  induction es with
  | nil => rfl
  | cons a as ih => simp [List.flatten_cons, chain_append, ih]

private theorem chain_ofFn {L : Type*} {n : ℕ} (edges : Fin n → L × L) :
    chain (List.ofFn edges) = ∑ i, signedEdge (edges i) := by
  simp [chain,List.map_ofFn,List.sum_ofFn,Function.comp_def]

/-- The three ordered edge occurrences of a supplied triangle. -/
def triangleBoundaryEdges (v : Fin 3 → Label) : Fin 3 → Label × Label :=
  triangleEdges (v 0) (v 1) (v 2)

/-- The list of all edge occurrences of the supplied triangle family. -/
def suppliedEdges {n : ℕ} (v : Fin n → Fin 3 → Label) : List (Label × Label) :=
  (List.ofFn fun i => List.ofFn (triangleBoundaryEdges (v i))).flatten

/-- The list of directed occurrences in the supplied hull cycle. -/
def hullEdges {n : ℕ} (v : Fin (n+3) → Label) : List (Label × Label) :=
  List.ofFn (cycleEdges v)

/-- The integer sum of the supplied triangle boundary chains. -/
noncomputable def suppliedBoundary {n : ℕ} (v : Fin n → Fin 3 → Label) :
    (Label × Label) →₀ ℤ := ∑ i, ∑ e, signedEdge (triangleBoundaryEdges (v i) e)

/-- The integer chain of the supplied hull cycle. -/
noncomputable def hullBoundary {n : ℕ} (v : Fin (n+3) → Label) :
    (Label × Label) →₀ ℤ := ∑ e, signedEdge (cycleEdges v e)

/-- The coefficient of the triangle chain agrees with its signed list occurrence count. -/
theorem supplied_boundary_coeff {n : ℕ} (v : Fin n → Fin 3 → Label) (e : Label × Label) :
    suppliedBoundary v e = listCoeff (suppliedEdges v) e := by
  rw [← chain_apply_count]
  have h : chain (suppliedEdges v) = suppliedBoundary v := by
    simp only [suppliedEdges,suppliedBoundary,chain_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def,
      chain_ofFn]
  rw [h]

/-- The coefficient of the hull chain agrees with its signed list occurrence count. -/
theorem hull_boundary_coeff {n : ℕ} (v : Fin (n+3) → Label) (e : Label × Label) :
    hullBoundary v e = listCoeff (hullEdges v) e := by
  rw [← chain_apply_count, hullEdges, chain_ofFn, hullBoundary]

/-- All ordered-pair coefficients of the good split match those of the hull. -/
theorem good_coefficients : ∀ e : Label × Label,
    listCoeff (suppliedEdges good) e = listCoeff (hullEdges cycle) e := by decide +kernel

/-- The good split has the signed boundary of the trapezoid hull. -/
theorem good_boundary : suppliedBoundary good = hullBoundary cycle := by
  ext e
  rw [supplied_boundary_coeff,hull_boundary_coeff]
  exact good_coefficients e

/-- The incomplete list has CD coefficient zero, compared with one for the hull. -/
theorem incomplete_coefficients :
    suppliedBoundary incomplete (2,3) = 0 ∧ hullBoundary cycle (2,3) = 1 := by
  rw [supplied_boundary_coeff,hull_boundary_coeff]
  decide +kernel

/-- The incomplete list fails signed boundary equality. -/
theorem incomplete_boundary : suppliedBoundary incomplete ≠ hullBoundary cycle := by
  intro h
  have h' := congrArg (fun c : (Label × Label) →₀ ℤ => c (2,3)) h
  rw [incomplete_coefficients.1,incomplete_coefficients.2] at h'
  omega

/-- The overlapping list uses BC twice in its given direction while the hull uses it once. -/
theorem overlap_coefficients :
    suppliedBoundary overlap (1,2) = 2 ∧ hullBoundary cycle (1,2) = 1 := by
  rw [supplied_boundary_coeff,hull_boundary_coeff]
  decide +kernel

/-- The overlapping list fails signed boundary equality. -/
theorem overlap_boundary : suppliedBoundary overlap ≠ hullBoundary cycle := by
  intro h
  have h' := congrArg (fun c : (Label × Label) →₀ ℤ => c (1,2)) h
  rw [overlap_coefficients.1,overlap_coefficients.2] at h'
  omega

/-- The good and overlapping lists use all labels. The incomplete list omits a label. -/
theorem trapezoid_usage : allSitesUsed good ∧ allSitesUsed overlap ∧ ¬ allSitesUsed incomplete := by
  unfold allSitesUsed
  decide +kernel

/-- The sum of the doubled signed areas of supplied triangles, using rational orientations. -/
def area₂ {n : ℕ} (v : Fin n → Fin 3 → Label) : ℚ :=
  ∑ i, orient (quad (v i 0)) (quad (v i 1)) (quad (v i 2))

/-- The doubled signed area of the trapezoid from its cyclic shoelace sum. -/
def hullArea₂ : ℚ :=
  ∑ i : Fin 4, ((quad i).1 * (quad (i+1)).2 - (quad (i+1)).1 * (quad i).2)

/-- Both two-triangle lists have the same doubled signed area sum as the hull. -/
theorem equal_area : area₂ overlap = 14 ∧ area₂ good = 14 ∧ hullArea₂ = 14 := by decide +kernel

private theorem good_ccw : ∀ i, 0 < orient (quad (good i 0)) (quad (good i 1)) (quad (good i 2)) := by
  decide +kernel

/-- The good split has the hull's off-edge multiplicity and covers its entire closed carrier. -/
theorem trapezoid_good_cover :
    (∀ x ∈ offEdges (listedEdges quad (fun i => triangleBoundaryEdges (good i)) (cycleEdges cycle)),
      interiorMultiplicity (fun i => siteTriangle quad (good i)) x = interiorIndicator trapezoidHull x) ∧
    (⋃ i, siteTriangle quad (good i)) = trapezoidHull := by
  exact rational_cover_from_signed_boundary quad quad_injective cycle (fun _ _ h => h) good
    trapezoid_certificate each_site_mem_hull good_ccw good_boundary

private theorem mem_interior_abc_of_strict (x : Plane) :
    (0 < 4 * x 1 ∧ 0 < 8 - 2 * x 0 - x 1 ∧ 0 < 2 * x 0 - 3 * x 1) →
    x ∈ interior (siteTriangle quad abc) := by
  rintro ⟨ha,hb,hc⟩
  apply strict_left_mem_interior (triangleEdges (Q 0) (Q 1) (Q 2))
    (fun y hy => (mem_abc_iff y).2 (by
      have h₀ := hy 0; have h₁ := hy 1; have h₂ := hy 2
      change 0 ≤ edgeSide (hullEdge 0) y at h₀
      change 0 ≤ edgeSide (hullEdge 1) y at h₁
      change 0 ≤ edgeSide (Q 2,Q 0) y at h₂
      rw [side_ab] at h₀; rw [side_bc] at h₁; rw [side_ca] at h₂
      exact ⟨h₀,h₁,h₂⟩))
  intro i
  fin_cases i
  · change 0 < edgeSide (hullEdge 0) x
    rwa [side_ab]
  · change 0 < edgeSide (hullEdge 1) x
    rwa [side_bc]
  · change 0 < edgeSide (Q 2,Q 0) x
    rwa [side_ca]

private theorem mem_interior_bcd_of_strict (x : Plane) :
    (0 < 8 - 2 * x 0 - x 1 ∧ 0 < 3 * (2 - x 1) ∧ 0 < 2 * x 0 + 4 * x 1 - 8) →
    x ∈ interior (siteTriangle quad bcd) := by
  rintro ⟨ha,hb,hc⟩
  apply strict_left_mem_interior (triangleEdges (Q 1) (Q 2) (Q 3))
    (fun y hy => (mem_bcd_iff y).2 (by
      have h₀ := hy 0; have h₁ := hy 1; have h₂ := hy 2
      change 0 ≤ edgeSide (hullEdge 1) y at h₀
      change 0 ≤ edgeSide (hullEdge 2) y at h₁
      change 0 ≤ edgeSide (Q 3,Q 1) y at h₂
      rw [side_bc] at h₀; rw [side_cd] at h₁; rw [side_db] at h₂
      exact ⟨h₀,h₁,h₂⟩))
  intro i
  fin_cases i
  · change 0 < edgeSide (hullEdge 1) x
    rwa [side_bc]
  · change 0 < edgeSide (hullEdge 2) x
    rwa [side_cd]
  · change 0 < edgeSide (Q 3,Q 1) x
    rwa [side_db]

/-- The two triangles along AC have disjoint ambient interiors. -/
theorem good_disjoint_interiors :
    Disjoint (interior (siteTriangle quad abc)) (interior (siteTriangle quad acd)) := by
  rw [Set.disjoint_left]
  intro x h₀ h₁
  have ha := interior_side_pos_of_support (Q 2,Q 0)
    (fun y hy => by rw [side_ca]; exact ((mem_abc_iff y).1 hy).2.2)
    1 (by norm_num [sideSlope,slopeDir]) h₀
  have hb := interior_side_pos_of_support (Q 0,Q 2)
    (fun y hy => by rw [side_ac]; exact ((mem_acd_iff y).1 hy).1)
    1 (by norm_num [sideSlope,slopeDir]) h₁
  rw [side_ca] at ha
  rw [side_ac] at hb
  linarith

/-- A hull interior point outside both triangles of the overlapping list. -/
noncomputable def gap : Plane := !₂[1/4,1]
/-- A point in the ambient interiors of both triangles of the overlapping list. -/
def overlapPoint : Plane := !₂[3,1]

/-- The gap witness belongs to the hull interior and misses both closed triangles. -/
theorem gap_witness :
    gap ∈ interior trapezoidHull ∧ gap ∉ siteTriangle quad abc ∧ gap ∉ siteTriangle quad bcd := by
  refine ⟨?_,?_,?_⟩
  · apply strict_left_mem_interior hullEdge (fun y hy => (hull_halfplanes y).2 ((region_iff y).2 hy))
    intro i
    fin_cases i
    · change 0 < edgeSide (hullEdge 0) gap
      norm_num [side_ab,gap]
    · change 0 < edgeSide (hullEdge 1) gap
      norm_num [side_bc,gap]
    · change 0 < edgeSide (hullEdge 2) gap
      norm_num [side_cd,gap]
    · change 0 < edgeSide (hullEdge 3) gap
      norm_num [side_da,gap]
  · rw [mem_abc_iff]
    norm_num [gap]
  · rw [mem_bcd_iff]
    norm_num [gap]

/-- The overlap witness lies in both triangle interiors. -/
theorem overlap_witness :
    overlapPoint ∈ interior (siteTriangle quad abc) ∩ interior (siteTriangle quad bcd) :=
  ⟨mem_interior_abc_of_strict _ (by norm_num [overlapPoint]), mem_interior_bcd_of_strict _ (by norm_num [overlapPoint])⟩

/-- The incomplete list fails to cover the closed hull. -/
theorem incomplete_not_cover : (⋃ i, siteTriangle quad (incomplete i)) ≠ trapezoidHull := by
  intro h
  have hx : gap ∈ ⋃ i, siteTriangle quad (incomplete i) := h.symm ▸ interior_subset gap_witness.1
  obtain ⟨i,hi⟩ := mem_iUnion.1 hx
  fin_cases i
  exact gap_witness.2.1 hi

/-- The overlapping list fails to cover the closed hull. -/
theorem overlap_not_cover : (⋃ i, siteTriangle quad (overlap i)) ≠ trapezoidHull := by
  intro h
  have hx : gap ∈ ⋃ i, siteTriangle quad (overlap i) := h.symm ▸ interior_subset gap_witness.1
  obtain ⟨i,hi⟩ := mem_iUnion.1 hx
  fin_cases i
  · exact gap_witness.2.1 hi
  · exact gap_witness.2.2 hi

/-- The rational sites of a triangular hull with an additional interior site. -/
def inner : Label → Point := ![(0,0),(4,0),(0,4),(1,1)]
/-- The three hull vertices of the omitted-label fixture in CCW order. -/
def innerCycle : Fin 3 → Label := ![0,1,2]

private theorem triangle_is_inner_hull : siteTriangle inner abc = siteHull inner innerCycle := by
  change convexHull ℝ ({castPoint (inner 0), castPoint (inner 1), castPoint (inner 2)} : Set Plane) =
    convexHull ℝ (range fun i : Fin 3 => castPoint (inner (innerCycle i)))
  apply congrArg (convexHull ℝ)
  apply Set.ext
  intro x
  simp only [mem_insert_iff,mem_singleton_iff,mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  · rintro ⟨i,rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem inner_site_strict :
    castPoint (inner 3) ∈ interior (siteHull inner innerCycle) := by
  rw [← triangle_is_inner_hull]
  let A := castPoint (inner 0)
  let B := castPoint (inner 1)
  let C := castPoint (inner 2)
  have h : 0 < orient (inner 0) (inner 1) (inner 2) := by decide +kernel
  have hc : 0 < edgeSide (A,B) C := by
    dsimp only [A,B,C]
    rw [side_of_rational_sites]
    exact_mod_cast h
  apply strict_left_mem_interior (triangleEdges A B C)
    (fun y hy => (triangle_mem_iff A B C y hc).2 hy)
  intro i
  fin_cases i
  · change 0 < edgeSide (A,B) (castPoint (inner 3))
    dsimp only [A,B]
    rw [side_of_rational_sites]
    exact_mod_cast (show 0 < orient (inner 0) (inner 1) (inner 3) by decide +kernel)
  · change 0 < edgeSide (B,C) (castPoint (inner 3))
    dsimp only [B,C]
    rw [side_of_rational_sites]
    exact_mod_cast (show 0 < orient (inner 1) (inner 2) (inner 3) by decide +kernel)
  · change 0 < edgeSide (C,A) (castPoint (inner 3))
    dsimp only [C,A]
    rw [side_of_rational_sites]
    exact_mod_cast (show 0 < orient (inner 2) (inner 0) (inner 3) by decide +kernel)

private theorem omitted_boundary : suppliedBoundary incomplete = hullBoundary innerCycle := by
  ext e
  rw [supplied_boundary_coeff,hull_boundary_coeff]
  have h : ∀ e : Label × Label,
      listCoeff (suppliedEdges incomplete) e = listCoeff (hullEdges innerCycle) e := by decide +kernel
  exact h e

private theorem omitted_label_unused : ¬ ∃ i j, incomplete i j = (3 : Label) := by
  decide +kernel

/-- Covering the hull with the correct signed boundary can leave an interior site unused. -/
theorem omitted_label_fixture :
    (⋃ i, siteTriangle inner (incomplete i)) = siteHull inner innerCycle ∧
      suppliedBoundary incomplete = hullBoundary innerCycle ∧
      castPoint (inner 3) ∈ interior (siteHull inner innerCycle) ∧
      ¬ allSitesUsed incomplete := by
  refine ⟨?_, omitted_boundary, inner_site_strict, fun h => omitted_label_unused (h 3)⟩
  rw [← triangle_is_inner_hull]
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.1 hx
    fin_cases i
    exact hi
  · exact fun hx => mem_iUnion.2 ⟨0,hx⟩

/-- Three CCW triangles joining the interior site to the sides of the triangular hull. -/
def interiorFan : Fin 3 → Fin 3 → Label := ![![0,1,3],![1,2,3],![2,0,3]]

private abbrev fanEdges (i : Fin 3) := triangleBoundaryEdges (interiorFan i)

private theorem inner_edges_eq (i : Fin 3) :
    realEdge inner (cycleEdges innerCycle i) =
      triangleEdges (castPoint (inner 0)) (castPoint (inner 1)) (castPoint (inner 2)) i := by
  fin_cases i <;> rfl

/-- The outer triangle's orientation supplies the hull certificate used by the fan. -/
private theorem fan_hull_certificate :
    PolygonCertificate (siteHull inner innerCycle) (fun i => realEdge inner (cycleEdges innerCycle i)) := by
  rw [← triangle_is_inner_hull]
  simp only [siteTriangle, inner_edges_eq]
  exact rational_triangle_polygonCertificate _ _ _ (by decide +kernel)

private theorem fan_sites_contained (i : Label) : castPoint (inner i) ∈ siteHull inner innerCycle := by
  fin_cases i
  · exact subset_convexHull ℝ _ ⟨0,rfl⟩
  · exact subset_convexHull ℝ _ ⟨1,rfl⟩
  · exact subset_convexHull ℝ _ ⟨2,rfl⟩
  · exact interior_subset inner_site_strict

/-- The center lies in the hull interior, and the fan uses every site label. -/
theorem fan_uses_interior_site :
    castPoint (inner 3) ∈ interior (siteHull inner innerCycle) ∧ allSitesUsed interiorFan :=
  ⟨inner_site_strict, by unfold allSitesUsed; decide +kernel⟩

/-- The three fan triangles are counterclockwise. -/
theorem fan_ccw :
    ∀ i, 0 < orient (inner (interiorFan i 0)) (inner (interiorFan i 1)) (inner (interiorFan i 2)) := by
  decide +kernel

/-- The spoke contributions cancel and the signed boundary is the outer cycle. -/
theorem fan_signed_boundary : suppliedBoundary interiorFan = hullBoundary innerCycle := by
  ext e
  rw [supplied_boundary_coeff, hull_boundary_coeff]
  have h : ∀ e : Label × Label,
      listCoeff (suppliedEdges interiorFan) e = listCoeff (hullEdges innerCycle) e := by decide +kernel
  exact h e

/-- The signed-boundary theorem gives the closed hull coverage and the off-edge count. -/
theorem fan_coverage_and_multiplicity :
    (∀ x ∈ offEdges (listedEdges inner (fun i => triangleBoundaryEdges (interiorFan i))
        (cycleEdges innerCycle)),
      interiorMultiplicity (fun i => siteTriangle inner (interiorFan i)) x =
        interiorIndicator (siteHull inner innerCycle) x) ∧
    (⋃ i, siteTriangle inner (interiorFan i)) = siteHull inner innerCycle :=
  rational_cover_from_signed_boundary inner (by decide +kernel)
    innerCycle (by decide +kernel) interiorFan fan_hull_certificate fan_sites_contained
    fan_ccw fan_signed_boundary

private def fanSample : Point := (2,1/2)

private theorem sample_off_edges :
    castPoint fanSample ∈ offEdges (listedEdges inner fanEdges (cycleEdges innerCycle)) := by
  intro hx
  obtain ⟨j,hj⟩ := mem_iUnion.1 hx
  have hzero := edgeSide_eq_zero_on_segment _ hj
  rcases j with ⟨i,e⟩ | e
  · change edgeSide (castPoint (inner (fanEdges i e).1), castPoint (inner (fanEdges i e).2))
        (castPoint fanSample) = 0 at hzero
    rw [side_of_rational_sites] at hzero
    have hs : ∀ i e, orient (inner (fanEdges i e).1) (inner (fanEdges i e).2) fanSample ≠ 0 :=
      by decide +kernel
    exact hs i e (by exact_mod_cast hzero)
  · change edgeSide (castPoint (inner (cycleEdges innerCycle e).1),
        castPoint (inner (cycleEdges innerCycle e).2)) (castPoint fanSample) = 0 at hzero
    rw [side_of_rational_sites] at hzero
    have hs : ∀ e, orient (inner (cycleEdges innerCycle e).1)
        (inner (cycleEdges innerCycle e).2) fanSample ≠ 0 := by decide +kernel
    exact hs e (by exact_mod_cast hzero)

private theorem sample_interior : castPoint fanSample ∈ interior (siteHull inner innerCycle) := by
  rw [← triangle_is_inner_hull]
  have hccw : 0 < edgeSide (castPoint (inner 0), castPoint (inner 1)) (castPoint (inner 2)) := by
    rw [side_of_rational_sites]
    exact_mod_cast (by decide +kernel : 0 < orient (inner 0) (inner 1) (inner 2))
  apply strict_left_mem_interior
    (triangleEdges (castPoint (inner 0)) (castPoint (inner 1)) (castPoint (inner 2)))
    (fun x hx => (triangle_mem_iff _ _ _ x hccw).2 hx)
  intro i
  rw [← inner_edges_eq]
  change 0 < edgeSide (castPoint (inner (cycleEdges innerCycle i).1),
    castPoint (inner (cycleEdges innerCycle i).2)) (castPoint fanSample)
  rw [side_of_rational_sites]
  have hs : ∀ i, 0 < orient (inner (cycleEdges innerCycle i).1)
      (inner (cycleEdges innerCycle i).2) fanSample := by decide +kernel
  exact_mod_cast hs i

/-- The signed-boundary theorem gives multiplicity one at the off-edge point `(2, 1/2)`. -/
theorem fan_sample_multiplicity_one :
    interiorMultiplicity (fun i => siteTriangle inner (interiorFan i)) (castPoint (2, 1/2)) = 1 := by
  change interiorMultiplicity (fun i => siteTriangle inner (interiorFan i)) (castPoint fanSample) = 1
  rw [fan_coverage_and_multiplicity.1 _ sample_off_edges]
  simp [interiorIndicator, sample_interior]

end TDA.Filtration.RationalAlpha.SignedBoundaryExamples
