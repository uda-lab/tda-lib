import TDA.Filtration.RationalAlpha.EdgeGrade
import TDA.Filtration.RationalAlpha.IncircleGrade

set_option autoImplicit false

/-!
# Closed Voronoi regions of supplied rational planar edges

An incident triangle's all-site incircle test gives a center in its common closed cells.
Its third site makes one affine bisector bound active. Along the directed hull the
supporting half-plane leaves a single ray, while opposite interior incidences give a
closed segment. Projecting the midpoint onto that region gives the first alpha grade.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedEdgeGrade

open Set
open scoped BigOperators Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.EdgeGrade
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.IncircleGrade

noncomputable section

/-- The outward quarter-turn of a counterclockwise hull side. -/
def outward (a b : Point) : Plane :=
  !₂[((b.2 : ℝ) - a.2), -((b.1 : ℝ) - a.1)]

/-- Moving in the outward direction decreases the oriented side determinant at rate D. -/
theorem edgeSide_outward (a b : Point) (x : Plane) (r : ℝ) :
    edgeSide (castPoint a,castPoint b) (x + r • outward a b) =
      edgeSide (castPoint a,castPoint b) x - r * directionSq a b := by
  have hx (q : Point) : castPoint q 0 = (q.1 : ℝ) := rfl
  have hy (q : Point) : castPoint q 1 = (q.2 : ℝ) := rfl
  have h₀ : outward a b 0 = ((b.2 : ℝ) - a.2) := rfl
  have h₁ : outward a b 1 = -((b.1 : ℝ) - a.1) := rfl
  simp only [edgeSide, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx, hy, h₀, h₁, directionSq]
  ring

/-- The ray from a center in the direction of a vector, including the center. -/
def closedRay (center vector : Plane) : Set Plane :=
  {x | ∃ r : ℝ, 0 ≤ r ∧ center + r • vector = x}

private theorem on_bisector_outward (a b : Point) (u r : ℝ) :
    bisectorPoint a b (u - r) = bisectorPoint a b u + r • outward a b := by
  ext i
  fin_cases i
  · change ((a.1 : ℝ) + b.1) / 2 - (u-r) * ((b.2 : ℝ) - a.2) =
      ((a.1 : ℝ) + b.1) / 2 - u * ((b.2 : ℝ) - a.2) + r * ((b.2 : ℝ) - a.2)
    ring
  · change ((a.2 : ℝ) + b.2) / 2 + (u-r) * ((b.1 : ℝ) - a.1) =
      ((a.2 : ℝ) + b.2) / 2 + u * ((b.1 : ℝ) - a.1) + r * (-((b.1 : ℝ) - a.1))
    ring

private theorem image_Iic_eq_closedRay (a b : Point) (u : ℝ) :
    bisectorPoint a b '' Iic u = closedRay (bisectorPoint a b u) (outward a b) := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    have ht' : t ≤ u := ht
    exact ⟨u-t, sub_nonneg.mpr ht', by rw [← on_bisector_outward]; congr 1; ring⟩
  · rintro ⟨r,hr,rfl⟩
    exact ⟨u-r, sub_le_self _ hr, on_bisector_outward _ _ _ _⟩

private theorem image_Icc_eq_segment (a b : Point) {l u : ℝ} (hlu : l ≤ u) :
    bisectorPoint a b '' Icc l u = segment ℝ (bisectorPoint a b l) (bisectorPoint a b u) := by
  let f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap (bisectorPoint a b 0) (bisectorPoint a b 1)
  have hf : ∀ t : ℝ, f t = bisectorPoint a b t := by
    intro t
    dsimp only [f]
    rw [AffineMap.lineMap_apply_module]
    ext i
    fin_cases i
    · change (1-t) * (((a.1 : ℝ) + b.1)/2 - 0*((b.2 : ℝ) - a.2)) +
        t * (((a.1 : ℝ) + b.1)/2 - 1*((b.2 : ℝ) - a.2)) =
        ((a.1 : ℝ) + b.1)/2 - t*((b.2 : ℝ) - a.2)
      ring
    · change (1-t) * (((a.2 : ℝ) + b.2)/2 + 0*((b.1 : ℝ) - a.1)) +
        t * (((a.2 : ℝ) + b.2)/2 + 1*((b.1 : ℝ) - a.1)) =
        ((a.2 : ℝ) + b.2)/2 + t*((b.1 : ℝ) - a.1)
      ring
  simpa only [show (f : ℝ → Plane) = bisectorPoint a b from funext hf, segment_eq_Icc hlu]
    using (image_segment ℝ f l u)

private theorem edgeRhs_cast (a b d : Point) :
    (edgeRhsRat a b d : ℝ) =
      (offset a d : ℝ) - linearForm (normal a d) (castPoint (RationalAlpha.midpoint a b)) := by
  have hx (q : Point) : castPoint q 0 = (q.1 : ℝ) := rfl
  have hy (q : Point) : castPoint q 1 = (q.2 : ℝ) := rfl
  simp [edgeRhsRat, linearForm, hx, hy]

/-- An admitted common center of a triple gives an active comparison on its edge. -/
theorem active_parameter_of_center {n : ℕ} (p : Fin n ↪ Point)
    {a b c : Fin n} (hab : a ≠ b) {o : Point}
    (ho : castPoint o ∈ Alpha.commonCells (realSites p) ({a,b,c} : Finset (Fin n))) :
    ∃ s ∈ edgeParameters p a b, bisectorPoint (p a) (p b) s = castPoint o ∧
      (orient (p a) (p b) (p c) : ℝ) * s = (edgeRhsRat (p a) (p b) (p c) : ℝ) := by
  have he : castPoint o ∈ Alpha.commonCells (realSites p) ({a,b} : Finset (Fin n)) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    apply ho v
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [edge_commonCells_eq_image p hab] at he
  obtain ⟨s,hs,hcenter⟩ := he
  refine ⟨s,hs,hcenter,?_⟩
  have h := ((RationalAlpha.mem_commonCells_iff p
    (show a ∈ ({a,b,c} : Finset (Fin n)) by simp) _).1 ho).2 c (by simp)
  rw [← hcenter, linearForm_bisectorPoint] at h
  rw [edgeRhs_cast]
  linarith

private theorem active_positive {n : ℕ} (p : Fin n ↪ Point) {a b c : Fin n} {t : ℝ}
    (ht : t ∈ edgeParameters p a b) (hc : 0 < orient (p a) (p b) (p c))
    (he : (orient (p a) (p b) (p c) : ℝ) * t = (edgeRhsRat (p a) (p b) (p c) : ℝ)) :
    IsGreatest (edgeParameters p a b) t := by
  refine ⟨ht,fun s hs => ?_⟩
  exact le_of_mul_le_mul_left ((hs c).trans_eq he.symm) (by exact_mod_cast hc)

private theorem active_negative {n : ℕ} (p : Fin n ↪ Point) {a b c : Fin n} {t : ℝ}
    (ht : t ∈ edgeParameters p a b) (hc : orient (p a) (p b) (p c) < 0)
    (he : (orient (p a) (p b) (p c) : ℝ) * t = (edgeRhsRat (p a) (p b) (p c) : ℝ)) :
    IsLeast (edgeParameters p a b) t := by
  refine ⟨ht,fun s hs => ?_⟩
  have h := (hs c).trans_eq he.symm
  have hneg : (orient (p a) (p b) (p c) : ℝ) < 0 := by exact_mod_cast hc
  exact le_of_mul_le_mul_left (a := -(orient (p a) (p b) (p c) : ℝ))
    (by simpa only [neg_mul, neg_le_neg_iff] using h) (neg_pos.mpr hneg)

private theorem parameters_ray {n : ℕ} (p : Fin n ↪ Point) {a b : Fin n} {u : ℝ}
    (hu : IsGreatest (edgeParameters p a b) u)
    (hside : ∀ j, 0 ≤ orient (p a) (p b) (p j)) :
    edgeParameters p a b = Iic u := by
  ext t
  refine ⟨fun ht => hu.2 ht, fun ht j => ?_⟩
  exact (mul_le_mul_of_nonneg_left ht (by exact_mod_cast hside j)).trans (hu.1 j)

private theorem parameters_interval {n : ℕ} (p : Fin n ↪ Point) {a b : Fin n} {l u : ℝ}
    (hl : IsLeast (edgeParameters p a b) l) (hu : IsGreatest (edgeParameters p a b) u) :
    edgeParameters p a b = Icc l u := by
  ext t
  refine ⟨fun ht => ⟨hl.2 ht,hu.2 ht⟩, fun ht j => ?_⟩
  by_cases h : 0 ≤ (orient (p a) (p b) (p j) : ℝ)
  · exact (mul_le_mul_of_nonneg_left ht.2 h).trans (hu.1 j)
  · exact (mul_le_mul_of_nonpos_left ht.1 (le_of_not_ge h)).trans (hl.1 j)

private theorem zero_or_upper_projection {u : ℝ} :
    min 0 u ∈ Iic u ∧ ∀ t ∈ Iic u, (min 0 u)^2 ≤ t^2 := by
  refine ⟨mem_Iic.2 (min_le_right _ _), fun t ht => ?_⟩
  have htu : t ≤ u := ht
  by_cases hu : 0 ≤ u
  · rw [min_eq_left hu, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · rw [min_eq_right (le_of_not_ge hu)]
    simpa only [neg_sq] using
      (sq_le_sq₀ (neg_nonneg.mpr (le_of_not_ge hu))
        (neg_nonneg.mpr (htu.trans (le_of_not_ge hu)))).2 (neg_le_neg htu)

private theorem supporting_hull_side {n k : ℕ} (p : Fin n ↪ Point) (cycle : Fin (k+3) → Fin n)
    (hp : PolygonCertificate (siteHull p cycle) (fun j => realEdge p (cycleEdges cycle j)))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p cycle) (j : Fin (k+3)) :
    ∀ i, 0 ≤ orient (p (cycleEdges cycle j).1) (p (cycleEdges cycle j).2) (p i) := by
  intro i
  have h := hp.left j _ (hsite i)
  change 0 ≤ edgeSide (castPoint (p (cycleEdges cycle j).1),
    castPoint (p (cycleEdges cycle j).2)) (castPoint (p i)) at h
  rw [side_of_rational_sites] at h
  exact_mod_cast h

private theorem occurrence_third_label {n : ℕ} {I : Type*} (p : Fin n ↪ Point)
    (tri : I → Fin 3 → Fin n) (occ : I × Fin 3)
    (hccw : 0 < orient (p (tri occ.1 0)) (p (tri occ.1 1)) (p (tri occ.1 2))) :
    ∃ c, {(occurrenceEdge tri occ).1, (occurrenceEdge tri occ).2,c} =
        ({tri occ.1 0,tri occ.1 1,tri occ.1 2} : Finset (Fin n)) ∧
      0 < orient (p (occurrenceEdge tri occ).1) (p (occurrenceEdge tri occ).2) (p c) := by
  obtain ⟨i,j⟩ := occ
  let x := tri i 0
  let y := tri i 1
  let z := tri i 2
  have cyc (a b c : Point) : orient a b c = orient b c a := by
    rw [(orient_swaps b a c).2, (orient_swaps a b c).1, neg_neg]
  fin_cases j
  · exact ⟨z,rfl,hccw⟩
  · refine ⟨x,?_,?_⟩
    · change ({y,z,x} : Finset (Fin n)) = {x,y,z}
      ext i
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · change 0 < orient (p y) (p z) (p x)
      rwa [← cyc]
  · refine ⟨y,?_,?_⟩
    · change ({z,x,y} : Finset (Fin n)) = {x,y,z}
      ext i
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · change 0 < orient (p z) (p x) (p y)
      rwa [← cyc (p y), ← cyc (p x)]

/-- A directed triangle occurrence with its original computed circumcenter in the common closed
cells. The third label is read in cyclic order from the directed edge. -/
structure IncidentCenter {n : ℕ} {I : Type*} (p : Fin n ↪ Point)
    (tri : I → Fin 3 → Fin n) (i : I × Fin 3) (a b : Fin n) where
  edge : occurrenceEdge tri i = (a,b)
  third : Fin n
  ccw : 0 < orient (p a) (p b) (p third)
  sameFace : ({a,b,third} : Finset (Fin n)) = {tri i.1 0,tri i.1 1,tri i.1 2}
  center : Point
  computed : circumcenter? (p (tri i.1 0)) (p (tri i.1 1)) (p (tri i.1 2)) = some center
  feasible : castPoint center ∈ Alpha.commonCells (realSites p) ({a,b,third} : Finset (Fin n))

/-- Evaluate the all-label test in the original CCW order before transporting the label set. -/
theorem original_occurrence_center {n : ℕ} {I : Type*} (p : Fin n ↪ Point)
    (tri : I → Fin 3 → Fin n) (i : I × Fin 3) {a b : Fin n}
    (hei : occurrenceEdge tri i = (a,b))
    (hc : 0 < orient (p (tri i.1 0)) (p (tri i.1 1)) (p (tri i.1 2)))
    (htest : checkIncircle p (tri i.1 0) (tri i.1 1) (tri i.1 2) = true) :
    Nonempty (IncidentCenter p tri i a b) := by
  obtain ⟨c,hface,hpos⟩ := occurrence_third_label p tri i hc
  rw [hei] at hface hpos
  let x := tri i.1 0
  let y := tri i.1 1
  let z := tri i.1 2
  obtain ⟨o,ho,_,_⟩ := circumcenter_exists_eq_sqDist (p x) (p y) (p z) hc.ne'
  have hf := (checkIncircle_eq_true_iff_commonCells_nonempty p x y z hc ho).1 htest
  obtain ⟨q,hq⟩ := hf
  have he := commonCells_triangle_point_eq p x y z hc.ne' ho hq
  rw [he, ← hface] at hq
  exact ⟨⟨hei,c,hpos,hface,o,ho,hq⟩⟩

/-- A finite nonzero-determinant condition on four distinct labels. -/
def NoFourIncircleZeros {n : ℕ} (p : Fin n ↪ Point) : Prop :=
  ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    incircle (p a) (p b) (p c) (p d) ≠ 0

private theorem orient_pos_distinct {a b c : Point} (h : 0 < orient a b c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_,?_,?_⟩ <;> intro he <;> subst_vars <;>
    simp [orient, normal, det, mul_comm] at h

private theorem opposite_distinct_labels {n : ℕ} (p : Fin n ↪ Point)
    {a b c d : Fin n}
    (hc : 0 < orient (p a) (p b) (p c)) (hd : 0 < orient (p b) (p a) (p d)) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨hab,hac,hbc⟩ := orient_pos_distinct hc
  obtain ⟨_,hbd,had⟩ := orient_pos_distinct hd
  refine ⟨fun h => hab (congrArg p h), fun h => hac (congrArg p h),
    fun h => had (congrArg p h), fun h => hbc (congrArg p h),
    fun h => hbd (congrArg p h), ?_⟩
  intro he
  subst d
  rw [(orient_swaps (p a) (p b) (p c)).1] at hd
  linarith

/-- No real circle contains four distinct labelled sites. -/
def GeometricNoFourCocircular {n : ℕ} (p : Fin n ↪ Point) : Prop :=
  ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ o : Plane, dist o (realSites p b) = dist o (realSites p a) →
      dist o (realSites p c) = dist o (realSites p a) →
      dist o (realSites p d) = dist o (realSites p a) → False

private theorem common_sqDist_eq {n : ℕ} (p : Fin n ↪ Point)
    {s : Finset (Fin n)} {o : Point} {a b : Fin n} (ha : a ∈ s) (hb : b ∈ s)
    (h : castPoint o ∈ Alpha.commonCells (realSites p) s) :
    sqDist o (p a) = sqDist o (p b) := by
  have he := Alpha.dist_eq_of_mem_commonCells (realSites p) ha hb h
  change dist (castPoint o) (castPoint (p a)) = dist (castPoint o) (castPoint (p b)) at he
  have hs := congrArg (fun t : ℝ => t^2) he
  rw [distSq_cast, distSq_cast] at hs
  exact_mod_cast hs

/-- Equal bounds would put the two different third sites on the same circle through the edge. -/
private theorem strict_of_no_four {n : ℕ} (p : Fin n ↪ Point) (hgen : NoFourIncircleZeros p)
    {a b c d : Fin n}
    (hc : 0 < orient (p a) (p b) (p c)) (hd : 0 < orient (p b) (p a) (p d))
    {o₁ o₂ : Point}
    (h₁ : castPoint o₁ ∈ Alpha.commonCells (realSites p) ({a,b,c} : Finset (Fin n)))
    (h₂ : castPoint o₂ ∈ Alpha.commonCells (realSites p) ({b,a,d} : Finset (Fin n)))
    {l u : ℝ} (hlu : l ≤ u) (hl : bisectorPoint (p a) (p b) l = castPoint o₂)
    (hu : bisectorPoint (p a) (p b) u = castPoint o₁) : l < u := by
  apply lt_of_le_of_ne hlu
  intro h
  have heo : o₂ = o₁ := castPoint_injective (hl.symm.trans (by simpa only [h] using hu))
  rw [heo] at h₂
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := opposite_distinct_labels p hc hd
  have hb : sqDist o₁ (p b) = sqDist o₁ (p a) := common_sqDist_eq p (by simp) (by simp) h₁
  have hx : sqDist o₁ (p c) = sqDist o₁ (p a) := common_sqDist_eq p (by simp) (by simp) h₁
  have hy : sqDist o₁ (p d) = sqDist o₁ (p a) := common_sqDist_eq p (by simp) (by simp) h₂
  apply hgen a b c d hab hac had hbc hbd hcd
  rw [incircle_eq_radius_gap _ _ _ _ _ hb hx, hy, sub_self, mul_zero]

/-- The incident center, closed outward Voronoi ray, and exact stage threshold of a
directed hull edge. -/
structure HullDual {n : ℕ} {I : Type*} (p : Fin n ↪ Point) (tri : I → Fin 3 → Fin n)
    (a b : Fin n) where
  occurrence : I × Fin 3
  incident : IncidentCenter p tri occurrence a b
  unique : ∀ i, occurrenceEdge tri i = (a,b) → i = occurrence
  upper : ℝ
  upper_center : bisectorPoint (p a) (p b) upper = castPoint incident.center
  upper_active : (orient (p a) (p b) (p incident.third) : ℝ) * upper =
    (edgeRhsRat (p a) (p b) (p incident.third) : ℝ)
  parameters : edgeParameters p a b = Iic upper
  region : Alpha.commonCells (realSites p) ({a,b} : Finset (Fin n)) =
    closedRay (castPoint incident.center) (outward (p a) (p b))
  stage (t : ℝ) : ({a,b} : Finset (Fin n)) ∈ Alpha.complex (realSites p) t ↔
    directionSq (p a) (p b) / 4 + directionSq (p a) (p b) * (min 0 upper)^2 ≤ t

/-- The two incident centers, their closed Voronoi segment, and the exact stage threshold
of an interior edge. The bounds may coincide when a cocircular tie occurs. -/
structure InteriorDual {n : ℕ} {I : Type*} (p : Fin n ↪ Point)
    (tri : I → Fin 3 → Fin n) (a b : Fin n) where
  forward : I × Fin 3
  backward : I × Fin 3
  distinct : forward.1 ≠ backward.1
  left : IncidentCenter p tri forward a b
  right : IncidentCenter p tri backward b a
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper
  lower_center : bisectorPoint (p a) (p b) lower = castPoint right.center
  upper_center : bisectorPoint (p a) (p b) upper = castPoint left.center
  lower_active : (orient (p a) (p b) (p right.third) : ℝ) * lower =
    (edgeRhsRat (p a) (p b) (p right.third) : ℝ)
  upper_active : (orient (p a) (p b) (p left.third) : ℝ) * upper =
    (edgeRhsRat (p a) (p b) (p left.third) : ℝ)
  parameters : edgeParameters p a b = Icc lower upper
  region : Alpha.commonCells (realSites p) ({a,b} : Finset (Fin n)) =
    segment ℝ (castPoint right.center) (castPoint left.center)
  stage (t : ℝ) : ({a,b} : Finset (Fin n)) ∈ Alpha.complex (realSites p) t ↔
    directionSq (p a) (p b) / 4 + directionSq (p a) (p b) * (max lower (min upper 0))^2 ≤ t

section Supplied
variable {n k : ℕ} {I : Type*} [Fintype I]
    (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n) (hv : Function.Injective hull)
    (tri : I → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i,j))) =
      ∑ j, signedEdge (cycleEdges hull j))
    (hpasses : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)

include hv hh hccw hchain hpasses in
/-- A listed hull side with all sites on the supporting side gives a closed outward ray. -/
theorem supplied_hull_dual
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull) (j : Fin (k+3)) :
    Nonempty (HullDual p tri (cycleEdges hull j).1 (cycleEdges hull j).2) := by
  let a := (cycleEdges hull j).1
  let b := (cycleEdges hull j).2
  have de : (a,b) = cycleEdges hull j := Prod.eta _
  have hcounts := rational_edge_counts p p.injective hull hv tri hh hccw hchain
  have hcount := (certified_hull_face_incidence p p.injective hull hv tri hh hccw hchain j).2.1
  have hex : ∃ i, occurrenceEdge tri i = (a,b) := by
    by_contra! hn
    rw [← de] at hcount
    simp [directedMultiplicity, hn] at hcount
  obtain ⟨i,hi⟩ := hex
  obtain ⟨H⟩ := original_occurrence_center p tri i hi (hccw i.1) (hpasses i.1)
  have hab : a ≠ b := fun he => (orient_pos_distinct H.ccw).1 (congrArg p he)
  obtain ⟨u,hu,hcenter,hactive⟩ := active_parameter_of_center p hab H.feasible
  have hparam : edgeParameters p a b = Iic u :=
    parameters_ray p (active_positive p hu H.ccw hactive) (supporting_hull_side p hull hh hsite j)
  refine ⟨⟨i,H,fun j hj => hcounts.1 (hj.trans hi.symm),u,hcenter,hactive,hparam,?_,?_⟩⟩
  · rw [edge_commonCells_eq_image p hab, hparam, image_Iic_eq_closedRay, hcenter]
  · intro t
    apply edge_stage_of_parameter_min p hab
    · rw [hparam]
      exact zero_or_upper_projection.1
    · intro s hs
      rw [hparam] at hs
      exact zero_or_upper_projection.2 s hs

include hv hh hccw hchain hpasses in
/-- For a supplied non-hull pair, the reverse and forward centers bound its common cells. -/
theorem supplied_interior_dual {a b : Fin n} (hab : a ≠ b)
    (hface : ({a,b} : Finset (Fin n)) ∈ (labelComplex tri).faces)
    (hnothull : ∀ j, cycleEdges hull j ≠ (a,b) ∧ cycleEdges hull j ≠ (b,a)) :
    Nonempty (InteriorDual p tri a b) := by
  have hor := (pair_mem_iff_occurrence tri hab).1 hface
  obtain ⟨_,_,f,r,hf,hr,hdistinct⟩ :=
    (rational_edge_counts p p.injective hull hv tri hh hccw hchain).2.2 (a,b) hnothull hor
  obtain ⟨F⟩ := original_occurrence_center p tri f hf (hccw f.1) (hpasses f.1)
  obtain ⟨R⟩ := original_occurrence_center p tri r hr (hccw r.1) (hpasses r.1)
  have hd : orient (p a) (p b) (p R.third) < 0 := by
    have h := R.ccw
    rw [(orient_swaps (p a) (p b) (p R.third)).1] at h
    exact neg_pos.mp h
  have hswap : ({a,b,R.third} : Finset (Fin n)) = {b,a,R.third} := by
    ext i
    simp only [Finset.mem_insert, Finset.mem_singleton, or_left_comm]
  have hfeas : castPoint R.center ∈ Alpha.commonCells (realSites p) ({a,b,R.third} : Finset (Fin n)) :=
    hswap ▸ R.feasible
  obtain ⟨l,hl,hlc,hla⟩ := active_parameter_of_center p hab hfeas
  obtain ⟨u,hu,huc,hua⟩ := active_parameter_of_center p hab F.feasible
  have hL := active_negative p hl hd hla
  have hU := active_positive p hu F.ccw hua
  have hlu : l ≤ u := hL.2 hu
  have hparam := parameters_interval p hL hU
  refine ⟨⟨f,r,hdistinct,F,R,l,u,hlu,hlc,huc,hla,hua,hparam,?_,?_⟩⟩
  · rw [edge_commonCells_eq_image p hab, hparam, image_Icc_eq_segment _ _ hlu, hlc, huc]
  · intro t
    let z : ℝ := Set.projIcc l u hlu 0
    have hz : z ∈ edgeParameters p a b := by
      rw [hparam]
      exact (Set.projIcc l u hlu 0).property
    have hm (s : ℝ) (hs : s ∈ edgeParameters p a b) : z^2 ≤ s^2 := by
      rw [hparam] at hs
      exact (interval_projection hlu).2 ⟨s,hs,rfl⟩
    simpa only [z,Set.coe_projIcc] using edge_stage_of_parameter_min p hab hz hm t
end Supplied

private theorem actual_grade_of_stage {n : ℕ} (p : Fin n ↪ Point)
    {s : Finset (Fin n)} (hf : s ∈ Alpha.carrier (realSites p)) {g : ℝ}
    (h : ∀ t : ℝ, s ∈ Alpha.complex (realSites p) t ↔ g ≤ t) :
    (Alpha.filter (realSites p)).value ⟨s,hf⟩ = g := by
  apply (Alpha.isLeast_grade (realSites p) ⟨s,hf⟩).unique
  exact ⟨(h g).2 le_rfl,fun t ht => (h t).1 ht⟩

/-- The threshold of the supplied hull edge also witnesses membership of the actual carrier. -/
theorem HullDual.carrier {n : ℕ} {I : Type*} {p : Fin n ↪ Point}
    {tri : I → Fin 3 → Fin n} {a b : Fin n} (D : HullDual p tri a b) :
    ({a, b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p) :=
  (Alpha.exists_mem_complex_iff (realSites p) {a, b}).1 ⟨_, (D.stage _).2 le_rfl⟩

/-- The threshold of the supplied interior edge also witnesses membership of the actual carrier. -/
theorem InteriorDual.carrier {n : ℕ} {I : Type*} {p : Fin n ↪ Point}
    {tri : I → Fin 3 → Fin n} {a b : Fin n} (D : InteriorDual p tri a b) :
    ({a, b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p) :=
  (Alpha.exists_mem_complex_iff (realSites p) {a, b}).1 ⟨_, (D.stage _).2 le_rfl⟩

/-- The actual hull-edge grade is the minimum squared radius on its closed Voronoi ray. -/
theorem HullDual.grade {n : ℕ} {I : Type*} {p : Fin n ↪ Point}
    {tri : I → Fin 3 → Fin n} {a b : Fin n}
    (D : HullDual p tri a b) :
    (Alpha.filter (realSites p)).value ⟨{a, b}, D.carrier⟩ =
      directionSq (p a) (p b) / 4 + directionSq (p a) (p b) * (min 0 D.upper)^2 :=
  actual_grade_of_stage p D.carrier D.stage

/-- The actual interior-edge grade is the minimum squared radius on its closed Voronoi segment. -/
theorem InteriorDual.grade {n : ℕ} {I : Type*} {p : Fin n ↪ Point}
    {tri : I → Fin 3 → Fin n} {a b : Fin n}
    (D : InteriorDual p tri a b) :
    (Alpha.filter (realSites p)).value ⟨{a, b}, D.carrier⟩ =
      directionSq (p a) (p b) / 4 +
        directionSq (p a) (p b) * (max D.lower (min D.upper 0))^2 :=
  actual_grade_of_stage p D.carrier D.stage

/-- Nonvanishing incircle determinants on distinct four-tuples give strictly ordered endpoints. -/
theorem InteriorDual.strict {n : ℕ} {I : Type*} {p : Fin n ↪ Point}
    {tri : I → Fin 3 → Fin n} {a b : Fin n}
    (D : InteriorDual p tri a b) (hgen : NoFourIncircleZeros p) : D.lower < D.upper :=
  strict_of_no_four p hgen D.left.ccw D.right.ccw D.left.feasible D.right.feasible
    D.ordered D.lower_center D.upper_center

/-- The geometric exclusion of a circle with four distinct sites also suffices. -/
theorem InteriorDual.strict_geometric {n : ℕ} {I : Type*} {p : Fin n ↪ Point}
    {tri : I → Fin 3 → Fin n} {a b : Fin n}
    (D : InteriorDual p tri a b) (hgen : GeometricNoFourCocircular p) :
    D.lower < D.upper := by
  apply lt_of_le_of_ne D.ordered
  intro h
  have hl := D.lower_center
  rw [h] at hl
  have he := hl.symm.trans D.upper_center
  have hr := D.right.feasible
  rw [he] at hr
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := opposite_distinct_labels p D.left.ccw D.right.ccw
  apply hgen a b D.left.third D.right.third hab hac had hbc hbd hcd (castPoint D.left.center)
  · exact Alpha.dist_eq_of_mem_commonCells (realSites p) (by simp) (by simp) D.left.feasible
  · exact Alpha.dist_eq_of_mem_commonCells (realSites p) (by simp) (by simp) D.left.feasible
  · exact Alpha.dist_eq_of_mem_commonCells (realSites p) (by simp) (by simp) hr

/-- Under geometric no-four-cocircularity, the real Voronoi segment has distinct ends. -/
theorem InteriorDual.centers_ne {n : ℕ} {I : Type*} {p : Fin n ↪ Point}
    {tri : I → Fin 3 → Fin n} {a b : Fin n}
    (D : InteriorDual p tri a b) (hgen : GeometricNoFourCocircular p) :
    castPoint D.right.center ≠ castPoint D.left.center := by
  intro h
  apply (D.strict_geometric hgen).ne
  exact bisectorPoint_injective (orient_pos_distinct D.left.ccw).1
    (D.lower_center.trans (h.trans D.upper_center.symm))

end
end TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
