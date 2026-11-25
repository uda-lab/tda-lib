import TDA.Filtration.RationalAlpha.Predicates
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.GDelta.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

/-!
# Closed planar coverage from signed boundary equality

A certified polygon records a compact convex carrier, its full dimension, its boundary
segments, and the inward orientation of its sides. For a generic ray, the signed exits
and entrances of the polygon sum to its interior indicator.

Evaluating equality of integer edge chains on one such ray transfers the sum of triangle
indicators to the hull. Density away from the finitely many segments then gives equality
of the closed union with the hull. Vertex usage is a separate property of the supplied
triangle occurrences. Strict rational corner tests produce a hull certificate, and weak site
tests identify the corner hull with the hull of all sites.
-/

namespace TDA.Filtration.RationalAlpha.SignedBoundary

open TDA.Filtration.RationalAlpha (Plane Point castPoint)
open Set Module
open scoped Matrix

/-- The positive ray from `x` in direction `d` meets the open directed edge segment. -/
def rayHits (x d : Plane) (e : Plane × Plane) : Prop :=
  ∃ t : ℝ, 0 < t ∧ x + t • d ∈ openSegment ℝ e.1 e.2

/-- The determinant of the directed edge vector with the ray direction. -/
def sideSlope (d : Plane) (e : Plane × Plane) : ℝ :=
  (e.2 0 - e.1 0) * d 1 - (e.2 1 - e.1 1) * d 0

/-- The signed contribution of a transversal open-edge hit. An exit from the left half-plane
contributes `1`. An entrance contributes `-1`. -/
noncomputable def rayContribution (x d : Plane) (e : Plane × Plane) : ℤ := by
  classical
  exact if rayHits x d e then
    if sideSlope d e < 0 then 1 else if 0 < sideSlope d e then -1 else 0
  else 0

/-- Reversing a directed edge reverses its crossing contribution. -/
theorem rayContribution_swap (x d : Plane) (e : Plane × Plane) :
    rayContribution x d e.swap = -rayContribution x d e := by
  classical
  have hh : rayHits x d e.swap = rayHits x d e := by
    unfold rayHits
    simp only [Prod.fst_swap, Prod.snd_swap, openSegment_symm ℝ e.2 e.1]
  have hs : sideSlope d e.swap = -sideSlope d e := by
    simp only [sideSlope, Prod.fst_swap, Prod.snd_swap]
    ring
  unfold rayContribution
  rw [hh, hs]
  by_cases he : rayHits x d e
  · rcases lt_trichotomy (sideSlope d e) 0 with h | h | h
    · simp [he, h, h.not_gt]
    · simp [he, h]
    · simp [he, h, h.not_gt]
  · simp [he]

private theorem exists_slope_avoiding {I : Type*} [Finite I] (v : I → Plane)
    (hv : ∀ i, v i ≠ 0) :
    ∃ m : ℝ, ∀ i, v i 1 - m * v i 0 ≠ 0 := by
  obtain ⟨m, hm⟩ := (Set.finite_range (fun i => v i 1 / v i 0)).exists_notMem
  refine ⟨m, fun i hi => ?_⟩
  by_cases h : v i 0 = 0
  · have h' : v i 1 = 0 := by simpa [h] using hi
    apply hv i
    ext j
    fin_cases j
    · exact h
    · exact h'
  · apply hm
    refine ⟨i, (div_eq_iff h).2 ?_⟩
    exact sub_eq_zero.mp hi

/-- The basis vector of a directed label edge minus the basis vector for the reverse edge. -/
noncomputable def signedEdge {L : Type*} (e : L × L) : (L × L) →₀ ℤ :=
  Finsupp.single e 1 - Finsupp.single e.swap 1

private noncomputable def slopeLine (x : Plane) (m : ℝ) : ℝ →ᵃ[ℝ] Plane :=
  AffineMap.lineMap x (x + (!₂[1, m] : Plane))

private theorem compact_convex_line_slice (H : Set Plane) (hcompact : IsCompact H) (hconv : Convex ℝ H)
    (x : Plane) (m : ℝ) (hn : ((slopeLine x m) ⁻¹' H).Nonempty) :
    ∃ a b : ℝ, (slopeLine x m) ⁻¹' H = Icc a b := by
  let f := slopeLine x m
  have hform (t : ℝ) : f t = t • (!₂[1, m] : Plane) + x := by
    simp [f, slopeLine, AffineMap.lineMap_apply_module']
  have hf : Continuous f := by
    show Continuous (fun t => f t)
    simp_rw [hform]
    fun_prop
  let g (p : Plane) : ℝ := p 0 - x 0
  have hg : Continuous g := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).sub continuous_const
  have hgf (t : ℝ) : g (f t) = t := by
    simp [g, hform, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hsub : f ⁻¹' H ⊆ g '' H := fun t ht => ⟨f t, ht, hgf t⟩
  have hcomp : IsCompact (f ⁻¹' H) :=
    (hcompact.image hg).of_isClosed_subset (hcompact.isClosed.preimage hf) hsub
  exact ⟨sInf (f ⁻¹' H), sSup (f ⁻¹' H),
    eq_Icc_of_connected_compact ((hconv.affine_preimage f).isConnected hn) hcomp⟩

private theorem interval_exit_minus_entry (a b : ℝ) (hab : a ≤ b) (ha : a ≠ 0) :
    ((if 0 < b then 1 else 0) - (if 0 < a then 1 else 0) : ℤ) =
      if a < 0 ∧ 0 < b then 1 else 0 := by
  by_cases hb : 0 < b
  · rcases lt_or_gt_of_ne ha with ha' | ha'
    · simp [hb, ha', ha'.not_gt]
    · simp [hb, ha', ha'.not_gt]
  · have ha' : ¬ 0 < a := not_lt.mpr (hab.trans (le_of_not_gt hb))
    simp [hb, ha']

private theorem segment_closed (a b : Plane) : IsClosed (segment ℝ a b) := by
  rw [← convexHull_pair]
  exact ((Set.finite_singleton b).insert a).isClosed_convexHull ℝ

private theorem segment_nowhere_dense (a b : Plane) : IsNowhereDense (segment ℝ a b) := by
  apply (segment_closed a b).isNowhereDense_iff.2
  rw [← convexHull_pair, ← Set.not_nonempty_iff_eq_empty,
    interior_convexHull_nonempty_iff_affineSpan_eq_top]
  intro h
  have hs := congrArg (fun s : AffineSubspace ℝ Plane => s.direction) h
  rw [direction_affineSpan, vectorSpan_pair ℝ, AffineSubspace.direction_top] at hs
  have hdim : finrank ℝ (ℝ ∙ (a -ᵥ b)) ≤ 1 := by
    simpa using (finrank_span_le_card (R := ℝ) ({a -ᵥ b} : Set Plane))
  rw [hs, finrank_top, finrank_euclideanSpace_fin] at hdim
  omega

/-- Points outside every closed segment in the indexed edge family. -/
def offEdges {E : Type*} (p : E → Plane × Plane) : Set Plane :=
  (⋃ e, segment ℝ (p e).1 (p e).2)ᶜ

/-- Avoiding finitely many planar segments gives a dense set. -/
theorem dense_off_edges {E : Type*} [Finite E] (p : E → Plane × Plane) : Dense (offEdges p) := by
  unfold offEdges
  exact (isClosed_isNowhereDense_iff_compl.1
    ⟨isClosed_iUnion_of_finite (fun e => segment_closed (p e).1 (p e).2),
      IsNowhereDense.iUnion (fun e => segment_nowhere_dense (p e).1 (p e).2)⟩).2

/-- The integer indicator of ambient interior membership. -/
noncomputable def interiorIndicator (H : Set Plane) (x : Plane) : ℤ := by
  classical
  exact if x ∈ interior H then 1 else 0

/-- The number of indexed pieces whose ambient interiors contain the point. -/
noncomputable def interiorMultiplicity {I : Type*} [Fintype I] (T : I → Set Plane)
    (x : Plane) : ℤ :=
  ∑ i, interiorIndicator (T i) x

/-- A finite closed family contained in the hull covers it if its multiplicity is one at all off-edge
hull interior points. -/
theorem closed_cover_from_off_edge_count {I E : Type*} [Fintype I] [Finite E]
    (p : E → Plane × Plane) (H : Set Plane) (T : I → Set Plane)
    (hconv : Convex ℝ H) (hfull : (interior H).Nonempty) (hclosed : IsClosed H)
    (hT : ∀ i, IsClosed (T i)) (hsub : ∀ i, T i ⊆ H)
    (hcount : ∀ x ∈ interior H, x ∈ offEdges p → interiorMultiplicity T x = 1) :
    (⋃ i, T i) = H := by
  classical
  apply subset_antisymm (iUnion_subset hsub)
  have hz : interior H ∩ offEdges p ⊆ ⋃ i, T i := by
    rintro x ⟨hxH, hxe⟩
    by_contra hn
    have hnone (i : I) : x ∉ interior (T i) := fun h =>
      hn (mem_iUnion.2 ⟨i, interior_subset h⟩)
    have hc := hcount x hxH hxe
    simp [interiorMultiplicity, interiorIndicator, hnone] at hc
  have hTc : IsClosed (⋃ i, T i) := isClosed_iUnion_of_finite hT
  have hi : interior H ⊆ ⋃ i, T i :=
    ((dense_off_edges p).open_subset_closure_inter isOpen_interior).trans
      (closure_minimal hz hTc)
  simpa only [hconv.closure_interior_eq_closure_of_nonempty_interior hfull,
    hclosed.closure_eq] using closure_minimal hi hTc

/-- The direction vector of an affine line of finite slope. -/
noncomputable def slopeDir (m : ℝ) : Plane := !₂[1, m]

/-- The point on the line of slope `m` through `x` at parameter `t`. -/
noncomputable def rayPoint (x : Plane) (m t : ℝ) : Plane := x + t • slopeDir m

private theorem slopeLine_eq_rayPoint (x : Plane) (m t : ℝ) : slopeLine x m t = rayPoint x m t := by
  simp [slopeLine, rayPoint, slopeDir, AffineMap.lineMap_apply_module', add_comm]

private theorem continuous_rayPoint (x : Plane) (m : ℝ) : Continuous (rayPoint x m) :=
  continuous_const.add (continuous_id.smul continuous_const)

private theorem rayPoint_zero (x : Plane) (m : ℝ) : rayPoint x m 0 = x := by simp [rayPoint]

private theorem rayPoint_coord (x : Plane) (m t : ℝ) :
    rayPoint x m t 0 = x 0 + t ∧ rayPoint x m t 1 = x 1 + t * m := by
  simp [rayPoint, slopeDir, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

private theorem rayPoint_ne_vertex (x p : Plane) (m : ℝ)
    (h : (p 1 - x 1) - m * (p 0 - x 0) ≠ 0) (t : ℝ) : rayPoint x m t ≠ p := by
  intro ht
  obtain ⟨h₀, h₁⟩ := rayPoint_coord x m t
  rw [ht] at h₀ h₁
  apply h
  rw [h₀, h₁]
  ring

/-- A point off finitely many nondegenerate segments admits a slope transverse to every edge whose
entire line avoids every endpoint. -/
theorem exists_generic_slope {E : Type*} [Finite E] (edges : E → Plane × Plane) (x : Plane)
    (hedge : ∀ i, (edges i).1 ≠ (edges i).2) (hx : x ∈ offEdges edges) :
    ∃ m : ℝ, (∀ i, sideSlope (slopeDir m) (edges i) ≠ 0) ∧
      ∀ i t, rayPoint x m t ≠ (edges i).1 ∧ rayPoint x m t ≠ (edges i).2 := by
  let v (i : E × Fin 3) : Plane :=
    (![ (edges i.1).2 - (edges i.1).1, (edges i.1).1 - x, (edges i.1).2 - x ] : Fin 3 → Plane) i.2
  have hoff (i : E) : x ∉ segment ℝ (edges i).1 (edges i).2 := fun hi =>
    hx (mem_iUnion.2 ⟨i, hi⟩)
  have hv (i : E × Fin 3) : v i ≠ 0 := by
    rcases i with ⟨i, j⟩
    fin_cases j
    · simpa [v, sub_eq_zero, ne_comm] using hedge i
    · simpa [v, sub_eq_zero] using fun h : (edges i).1 = x =>
        hoff i (h ▸ left_mem_segment ℝ (edges i).1 (edges i).2)
    · simpa [v, sub_eq_zero] using fun h : (edges i).2 = x =>
        hoff i (h ▸ right_mem_segment ℝ (edges i).1 (edges i).2)
  obtain ⟨m, hm⟩ := exists_slope_avoiding v hv
  refine ⟨m, ?_, ?_⟩
  · intro i hz
    apply hm (i, 0)
    simp only [v, Matrix.cons_val_zero, PiLp.sub_apply]
    simp [sideSlope, slopeDir] at hz
    linarith
  · intro i t
    exact ⟨rayPoint_ne_vertex x (edges i).1 m (by simpa [v, PiLp.sub_apply] using hm (i, 1)) t,
      rayPoint_ne_vertex x (edges i).2 m (by simpa [v, PiLp.sub_apply] using hm (i, 2)) t⟩

/-- The signed determinant of the edge direction with the displacement from its start to `y`. -/
def edgeSide (e : Plane × Plane) (y : Plane) : ℝ :=
  (e.2 0 - e.1 0) * (y 1 - e.1 1) - (e.2 1 - e.1 1) * (y 0 - e.1 0)

/-- The side determinant is continuous as a function of the query point. -/
theorem continuous_edgeSide (e : Plane × Plane) : Continuous (edgeSide e) := by
  have h₀ := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h₁ := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  unfold edgeSide
  fun_prop

/-- The side determinant preserves affine two-point combinations. -/
theorem edgeSide_combination (e : Plane × Plane) (p q : Plane) (r s : ℝ) (h : r + s = 1) :
    edgeSide e (r • p + s • q) = r * edgeSide e p + s * edgeSide e q := by
  have hs : s = 1 - r := by linarith
  subst s
  simp only [edgeSide, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The side determinant vanishes on the associated closed segment. -/
theorem edgeSide_eq_zero_on_segment (e : Plane × Plane) {y : Plane}
    (hy : y ∈ segment ℝ e.1 e.2) : edgeSide e y = 0 := by
  obtain ⟨r, s, _, _, hrs, rfl⟩ := hy
  rw [edgeSide_combination e e.1 e.2 r s hrs]
  unfold edgeSide
  ring

private theorem edgeSide_rayPoint (e : Plane × Plane) (x : Plane) (m t : ℝ) :
    edgeSide e (rayPoint x m t) = edgeSide e x + t * sideSlope (slopeDir m) e := by
  rw [edgeSide, (rayPoint_coord x m t).1, (rayPoint_coord x m t).2]
  simp [edgeSide, sideSlope, slopeDir]
  ring

/-- A full-dimensional compact convex carrier with its certified oriented boundary.
Each side supports the carrier on its left. For any two distinct edge occurrences,
at least one endpoint of the first lies strictly left of the second. -/
structure PolygonCertificate {E : Type*} (H : Set Plane) (edges : E → Plane × Plane) : Prop where
  compact : IsCompact H
  convex : Convex ℝ H
  full : (interior H).Nonempty
  frontier_eq : frontier H = ⋃ i, segment ℝ (edges i).1 (edges i).2
  left : ∀ i y, y ∈ H → 0 ≤ edgeSide (edges i) y
  strict_endpoint : ∀ i j, i ≠ j →
    0 < edgeSide (edges j) (edges i).1 ∨ 0 < edgeSide (edges j) (edges i).2

/-- Each certified boundary segment is contained in the polygon. -/
theorem PolygonCertificate.edge_subset {E : Type*} {H : Set Plane} {edges : E → Plane × Plane}
    (P : PolygonCertificate H edges) (i : E) : segment ℝ (edges i).1 (edges i).2 ⊆ H := by
  intro y hy
  have hyf : y ∈ frontier H := P.frontier_eq.symm ▸ mem_iUnion.2 ⟨i, hy⟩
  exact P.compact.isClosed.closure_eq ▸ (frontier_subset_closure hyf)

private theorem PolygonCertificate.other_side_pos {E : Type*} {H : Set Plane} {edges : E → Plane × Plane}
    (P : PolygonCertificate H edges) {i j : E} (hij : i ≠ j) {y : Plane}
    (hy : y ∈ openSegment ℝ (edges i).1 (edges i).2) : 0 < edgeSide (edges j) y := by
  obtain ⟨r, s, hr, hs, hrs, rfl⟩ := hy
  rw [edgeSide_combination _ _ _ _ _ hrs]
  have hp := P.left j _ (P.edge_subset i (left_mem_segment ℝ (edges i).1 (edges i).2))
  have hq := P.left j _ (P.edge_subset i (right_mem_segment ℝ (edges i).1 (edges i).2))
  rcases P.strict_endpoint i j hij with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos hr h) (mul_nonneg hs.le hq)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hr.le hp) (mul_pos hs h)

/-- A nonnegative supporting determinant is positive in the interior whenever the given line direction
is transverse to that support. -/
theorem interior_side_pos_of_support {H : Set Plane} (e : Plane × Plane)
    (hleft : ∀ y ∈ H, 0 ≤ edgeSide e y) (m : ℝ)
    (hm : sideSlope (slopeDir m) e ≠ 0) {y : Plane} (hy : y ∈ interior H) :
    0 < edgeSide e y := by
  have h := hleft y (interior_subset hy)
  by_contra hn
  have hz : edgeSide e y = 0 := le_antisymm (le_of_not_gt hn) h
  have hnhds : ∀ᶠ t : ℝ in nhds 0, rayPoint y m t ∈ interior H :=
    (continuous_rayPoint y m).continuousAt (isOpen_interior.mem_nhds (by simpa [rayPoint_zero] using hy))
  rcases lt_or_gt_of_ne hm with hm | hm
  · obtain ⟨t, ht, hty⟩ := hnhds.exists_gt
    have hn := hleft _ (interior_subset hty)
    rw [edgeSide_rayPoint, hz, zero_add] at hn
    exact (not_lt_of_ge hn) (mul_neg_of_pos_of_neg ht hm)
  · obtain ⟨t, ht, hty⟩ := hnhds.exists_lt
    have hn := hleft _ (interior_subset hty)
    rw [edgeSide_rayPoint, hz, zero_add] at hn
    exact (not_lt_of_ge hn) (mul_neg_of_neg_of_pos ht hm)

/-- Membership in the polygon is equivalent to the nonnegative inward side inequalities for a family
with a transverse slope. -/
theorem PolygonCertificate.mem_iff_sides_nonneg {E : Type*}
    {H : Set Plane} {edges : E → Plane × Plane} (P : PolygonCertificate H edges) (m : ℝ)
    (hm : ∀ i, sideSlope (slopeDir m) (edges i) ≠ 0) (y : Plane) :
    y ∈ H ↔ ∀ i, 0 ≤ edgeSide (edges i) y := by
  refine ⟨fun h i => P.left i y h, fun hy => ?_⟩
  obtain ⟨z, hz⟩ := P.full
  let S : Set Plane := {p | ∀ i, 0 < edgeSide (edges i) p}
  have hzS : z ∈ S := fun i => interior_side_pos_of_support (edges i) (P.left i) m (hm i) hz
  have hc : Convex ℝ S := by
    intro p hp q hq a b ha hb hab i
    rw [edgeSide_combination _ _ _ _ _ hab]
    by_cases h : a = 0
    · have h' : b = 1 := by linarith
      simpa [h, h'] using hq i
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) (hp i))
        (mul_nonneg hb (hq i).le)
  have hsub : S ⊆ interior H := by
    apply hc.isPreconnected.subset_of_closure_inter_subset isOpen_interior ⟨z, hzS, hz⟩
    rintro p ⟨hp, hps⟩
    have hph : p ∈ H := closure_minimal interior_subset P.compact.isClosed hp
    by_contra hpi
    have hpf : p ∈ frontier H := by
      simpa [frontier, P.compact.isClosed.closure_eq] using And.intro hph hpi
    rw [P.frontier_eq] at hpf
    obtain ⟨i, hi⟩ := mem_iUnion.1 hpf
    exact (hps i).ne' (edgeSide_eq_zero_on_segment (edges i) hi)
  let f : ℝ → Plane := AffineMap.lineMap y z
  have hcont : Continuous f := by
    change Continuous (AffineMap.lineMap y z : ℝ → Plane)
    fun_prop
  have hpos : Ioc (0 : ℝ) 1 ⊆ f ⁻¹' H := by
    intro t ht
    change f t ∈ H
    apply interior_subset
    apply hsub
    intro i
    change 0 < edgeSide (edges i) (AffineMap.lineMap y z t)
    rw [AffineMap.lineMap_apply_module, edgeSide_combination _ _ _ _ _ (by ring)]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hy i))
      (mul_pos ht.1 (hzS i))
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have hf0 : (0 : ℝ) ∈ f ⁻¹' H :=
    closure_minimal hpos (P.compact.isClosed.preimage hcont) hzero
  simpa [f] using hf0


private theorem edgeSide_rayPoint_of_zero (e : Plane × Plane) (x : Plane) (m t u : ℝ)
    (ht : edgeSide e (rayPoint x m t) = 0) :
    edgeSide e (rayPoint x m u) = (u - t) * sideSlope (slopeDir m) e := by
  rw [edgeSide_rayPoint] at ht ⊢
  linear_combination ht

/-- The signed crossings of a generic positive ray sum to the interior indicator at its origin. -/
theorem PolygonCertificate.ray_sum_eq_indicator {E : Type*} [Fintype E]
    {H : Set Plane} {edges : E → Plane × Plane} (P : PolygonCertificate H edges)
    (x : Plane) (m : ℝ) (hx : x ∈ offEdges edges)
    (hm : ∀ i, sideSlope (slopeDir m) (edges i) ≠ 0)
    (hv : ∀ i t, rayPoint x m t ≠ (edges i).1 ∧ rayPoint x m t ≠ (edges i).2) :
    (∑ i, rayContribution x (slopeDir m) (edges i)) =
      interiorIndicator H x := by
  classical
  have hfront {t : ℝ} (ht : rayPoint x m t ∈ frontier H) :
      ∃ i, rayPoint x m t ∈ openSegment ℝ (edges i).1 (edges i).2 := by
    rw [P.frontier_eq] at ht
    obtain ⟨i, hi⟩ := mem_iUnion.1 ht
    exact ⟨i, mem_openSegment_of_ne_left_right (hv i t).1.symm (hv i t).2.symm hi⟩
  by_cases hn : ((slopeLine x m) ⁻¹' H).Nonempty
  · obtain ⟨a, b, hab⟩ := compact_convex_line_slice H P.compact P.convex x m hn
    have hmem (t : ℝ) : rayPoint x m t ∈ H ↔ t ∈ Icc a b := by
      rw [← slopeLine_eq_rayPoint]
      exact Set.ext_iff.mp hab t
    have hle : a ≤ b := by
      obtain ⟨t, ht⟩ := hn
      rw [hab] at ht
      exact ht.1.trans ht.2
    have hin {t : ℝ} (ht : rayPoint x m t ∈ interior H) : t ∈ Ioo a b := by
      have h := preimage_interior_subset_interior_preimage (continuous_rayPoint x m) ht
      have he : (rayPoint x m) ⁻¹' H = Icc a b := Set.ext hmem
      rwa [he, interior_Icc] at h
    have hbound {t : ℝ} (ht : t ∈ Icc a b) (h : t = a ∨ t = b) :
        rayPoint x m t ∈ frontier H := by
      have hl : rayPoint x m t ∈ H := (hmem t).2 ht
      rw [frontier, P.compact.isClosed.closure_eq]
      refine ⟨hl, fun hi => ?_⟩
      have hh := hin hi
      rcases h with he | he
      · rw [he] at hh
        exact (lt_irrefl a) hh.1
      · rw [he] at hh
        exact (lt_irrefl b) hh.2
    obtain ⟨iA, hA⟩ := hfront (hbound ⟨le_rfl, hle⟩ (Or.inl rfl))
    obtain ⟨iB, hB⟩ := hfront (hbound ⟨hle, le_rfl⟩ (Or.inr rfl))
    have hzA := edgeSide_eq_zero_on_segment (edges iA) (openSegment_subset_segment ℝ _ _ hA)
    have hzB := edgeSide_eq_zero_on_segment (edges iB) (openSegment_subset_segment ℝ _ _ hB)
    have hlt : a < b := by
      by_contra h
      have he : a = b := le_antisymm hle (le_of_not_gt h)
      let U : Set ℝ := ⋂ j : {i : E // i ≠ iA}, {t | 0 < edgeSide (edges j.1) (rayPoint x m t)}
      have hU : IsOpen U := by
        apply isOpen_iInter_of_finite
        intro j
        exact isOpen_lt continuous_const ((continuous_edgeSide (edges j.1)).comp (continuous_rayPoint x m))
      have haU : a ∈ U := mem_iInter.2 (fun j => P.other_side_pos j.2.symm hA)
      have hnear := hU.mem_nhds haU
      have impossible (t : ℝ) (ht : t ∈ U) (htn : t ≠ a)
          (hs : 0 ≤ (t - a) * sideSlope (slopeDir m) (edges iA)) : False := by
        have htH := (P.mem_iff_sides_nonneg m hm (rayPoint x m t)).2 (by
          intro j
          by_cases hj : j = iA
          · subst j
            rwa [edgeSide_rayPoint_of_zero _ _ _ a t hzA]
          · exact (mem_iInter.1 ht ⟨j, hj⟩ : 0 < edgeSide (edges j) (rayPoint x m t)).le)
        have htI := (hmem t).1 htH
        exact htn (le_antisymm (htI.2.trans_eq he.symm) htI.1)
      rcases lt_or_gt_of_ne (hm iA) with hs | hs
      · obtain ⟨t, ht, htu⟩ := Filter.Eventually.exists_lt hnear
        exact impossible t htu ht.ne (mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ht.le) hs.le)
      · obtain ⟨t, ht, htu⟩ := Filter.Eventually.exists_gt hnear
        exact impossible t htu ht.ne' (mul_nonneg (sub_nonneg.mpr ht.le) hs.le)
    have hAt : 0 < sideSlope (slopeDir m) (edges iA) := by
      have hs := P.left iA _ ((hmem b).2 ⟨hle, le_rfl⟩)
      rw [edgeSide_rayPoint_of_zero _ _ _ a b hzA] at hs
      exact lt_of_le_of_ne (nonneg_of_mul_nonneg_right hs (sub_pos.mpr hlt)) (hm iA).symm
    have hBt : sideSlope (slopeDir m) (edges iB) < 0 := by
      have hs := P.left iB _ ((hmem a).2 ⟨le_rfl, hle⟩)
      rw [edgeSide_rayPoint_of_zero _ _ _ b a hzB] at hs
      exact lt_of_le_of_ne (nonpos_of_mul_nonneg_right hs (sub_neg.mpr hlt)) (hm iB)
    have hAB : iA ≠ iB := by
      intro he
      rw [he] at hAt
      exact hAt.not_gt hBt
    have hclass {i : E} {t : ℝ} (ht : rayPoint x m t ∈ openSegment ℝ (edges i).1 (edges i).2) :
        (t = a ∧ i = iA) ∨ (t = b ∧ i = iB) := by
      have htseg := openSegment_subset_segment ℝ _ _ ht
      have hz := edgeSide_eq_zero_on_segment (edges i) htseg
      have hti := (hmem t).1 (P.edge_subset i htseg)
      rcases lt_or_gt_of_ne (hm i) with hs | hs
      · have hc := P.left i _ ((hmem b).2 ⟨hle, le_rfl⟩)
        rw [edgeSide_rayPoint_of_zero _ _ _ t b hz] at hc
        have htb : t = b := by
          by_contra hne
          exact (not_lt_of_ge hc) (mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_le_of_ne hti.2 hne)) hs)
        subst t
        refine Or.inr ⟨rfl, ?_⟩
        by_contra hne
        exact (P.other_side_pos (fun eq => hne eq.symm) hB).ne' hz
      · have hc := P.left i _ ((hmem a).2 ⟨le_rfl, hle⟩)
        rw [edgeSide_rayPoint_of_zero _ _ _ t a hz] at hc
        have hta : t = a := by
          by_contra hne
          exact (not_lt_of_ge hc) (mul_neg_of_neg_of_pos (sub_neg.mpr (lt_of_le_of_ne hti.1 (fun eq => hne eq.symm))) hs)
        subst t
        refine Or.inl ⟨rfl, ?_⟩
        by_contra hne
        exact (P.other_side_pos (fun eq => hne eq.symm) hA).ne' hz
    have hhit (i : E) : rayHits x (slopeDir m) (edges i) ↔
        (i = iA ∧ 0 < a) ∨ (i = iB ∧ 0 < b) := by
      constructor
      · rintro ⟨t, ht, hi⟩
        rcases hclass hi with ⟨rfl, h⟩ | ⟨rfl, h⟩
        · exact Or.inl ⟨h, ht⟩
        · exact Or.inr ⟨h, ht⟩
      · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
        · exact ⟨a, h, hA⟩
        · exact ⟨b, h, hB⟩
    have h0 : a ≠ 0 := by
      intro ha
      rw [ha, rayPoint_zero] at hA
      exact hx (mem_iUnion.2 ⟨iA, openSegment_subset_segment ℝ _ _ hA⟩)
    have hInt : x ∈ interior H ↔ a < 0 ∧ 0 < b := by
      constructor
      · intro h
        exact hin (t := 0) (by simpa [rayPoint_zero] using h)
      · rintro ⟨ha, hb⟩
        have hm0 : x ∈ H := by simpa [rayPoint_zero] using (hmem 0).2 ⟨ha.le, hb.le⟩
        by_contra hn0
        have hf : rayPoint x m 0 ∈ frontier H := by
          simpa [rayPoint_zero, frontier, P.compact.isClosed.closure_eq] using And.intro hm0 hn0
        obtain ⟨i, hi⟩ := hfront hf
        rcases hclass hi with ⟨he, _⟩ | ⟨he, _⟩
        · exact ha.ne he.symm
        · exact hb.ne he
    have hterm (i : E) : rayContribution x (slopeDir m) (edges i) =
        (if i = iB then if 0 < b then 1 else 0 else 0) -
          (if i = iA then if 0 < a then 1 else 0 else 0) := by
      unfold rayContribution
      rw [hhit]
      by_cases hia : i = iA
      · subst i
        by_cases h : 0 < a <;> simp [h, hAB, hAt, hAt.not_gt]
      · by_cases hib : i = iB
        · subst i
          by_cases h : 0 < b <;> simp [h, hAB.symm, hBt]
        · simp [hia, hib]
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, interiorIndicator, hInt]
    exact interval_exit_minus_entry a b hle h0
  · have hnone (i : E) : ¬ rayHits x (slopeDir m) (edges i) := by
      rintro ⟨t, _, ht⟩
      exact hn ⟨t, by
        change slopeLine x m t ∈ H
        rw [slopeLine_eq_rayPoint]
        exact P.edge_subset i (openSegment_subset_segment ℝ _ _ ht)⟩
    have hxH : x ∉ interior H := by
      intro h
      exact hn ⟨0, by
        change slopeLine x m 0 ∈ H
        rw [slopeLine_eq_rayPoint, rayPoint_zero]
        exact interior_subset h⟩
    simp [rayContribution, hnone, interiorIndicator, hxH]


/-- Embed the rational sites of a directed label edge into the real plane. -/
def realEdge {L : Type*} (site : L → Point) (e : L × L) : Plane × Plane :=
  (castPoint (site e.1), castPoint (site e.2))

/-- The real side determinant on cast sites agrees with rational orientation. -/
theorem side_of_rational_sites (a b c : Point) :
    edgeSide (castPoint a, castPoint b) (castPoint c) =
      (TDA.Filtration.RationalAlpha.orient a b c : ℝ) := by
  change ((b.1 : ℝ) - a.1) * ((c.2 : ℝ) - a.2) - ((b.2 : ℝ) - a.2) * ((c.1 : ℝ) - a.1) = _
  unfold TDA.Filtration.RationalAlpha.orient TDA.Filtration.RationalAlpha.det
    TDA.Filtration.RationalAlpha.normal
  push_cast
  rfl

/-- An antisymmetric edge weight evaluates the signed edge chain to twice its value. -/
theorem evaluate_signedEdge {L : Type*} (w : L × L → ℤ)
    (hw : ∀ e, w e.swap = -w e) (e : L × L) :
    Finsupp.linearCombination ℤ w (signedEdge e) = 2 * w e := by
  simp only [signedEdge, map_sub, Finsupp.linearCombination_single, one_smul, hw]
  ring

/-- Integer boundary equality transports sums of antisymmetric weights over edge occurrences. -/
theorem crossing_sum_of_finite_boundaries {L I E F : Type*} [Fintype I] [Fintype E] [Fintype F]
    (w : L × L → ℤ) (hw : ∀ e, w e.swap = -w e) (tri : I → E → L × L) (hull : F → L × L)
    (h : (∑ i, ∑ e, signedEdge (tri i e)) = ∑ e, signedEdge (hull e)) :
    (∑ i, ∑ e, w (tri i e)) = ∑ e, w (hull e) := by
  have he := congrArg (Finsupp.linearCombination ℤ w) h
  simp only [map_sum, evaluate_signedEdge w hw, ← Finset.mul_sum] at he
  omega

/-- The combined real triangle and hull edge families, indexed by their occurrences. -/
def listedEdges {L I E F : Type*} (site : L → Point) (tri : I → E → L × L)
    (hull : F → L × L) : Sum (I × E) F → Plane × Plane :=
  Sum.elim (fun p => realEdge site (tri p.1 p.2)) (fun e => realEdge site (hull e))

/-- Signed boundary equality gives the interior multiplicity of certified pieces at every point off
the listed edges. -/
theorem off_edge_count_from_signed_boundary {L I E F : Type*} [Fintype I] [Fintype E] [Fintype F]
    (site : L → Point) (tri : I → E → L × L) (hull : F → L × L) (T : I → Set Plane) (H : Set Plane)
    (pT : ∀ i, PolygonCertificate (T i) (fun e => realEdge site (tri i e)))
    (pH : PolygonCertificate H (fun e => realEdge site (hull e)))
    (hne : ∀ j, (listedEdges site tri hull j).1 ≠ (listedEdges site tri hull j).2)
    (hchain : (∑ i, ∑ e, signedEdge (tri i e)) = ∑ e, signedEdge (hull e))
    (x : Plane) (hx : x ∈ offEdges (listedEdges site tri hull)) :
    interiorMultiplicity T x = interiorIndicator H x := by
  classical
  obtain ⟨m, hm, hv⟩ := exists_generic_slope (listedEdges site tri hull) x hne hx
  let w (e : L × L) := rayContribution x (slopeDir m) (realEdge site e)
  have hw (e : L × L) : w e.swap = -w e :=
    rayContribution_swap x (slopeDir m) (realEdge site e)
  have he := crossing_sum_of_finite_boundaries w hw tri hull hchain
  have hT (i : I) : (∑ e, w (tri i e)) = interiorIndicator (T i) x :=
    (pT i).ray_sum_eq_indicator x m
      (fun h => hx (by
        obtain ⟨e, he⟩ := mem_iUnion.1 h
        exact mem_iUnion.2 ⟨Sum.inl (i,e), he⟩))
      (fun e => hm (Sum.inl (i,e))) (fun e t => hv (Sum.inl (i,e)) t)
  have hH : (∑ e, w (hull e)) = interiorIndicator H x :=
    pH.ray_sum_eq_indicator x m
      (fun h => hx (by
        obtain ⟨e, he⟩ := mem_iUnion.1 h
        exact mem_iUnion.2 ⟨Sum.inr e, he⟩))
      (fun e => hm (Sum.inr e)) (fun e t => hv (Sum.inr e) t)
  simp only [hT, hH] at he
  simpa only [interiorMultiplicity] using he

/-- Certified pieces contained in the hull cover its closed carrier when their signed boundary equals
its boundary. -/
theorem closed_cover_from_signed_boundary {L I E F : Type*} [Fintype I] [Fintype E] [Fintype F]
    (site : L → Point) (tri : I → E → L × L) (hull : F → L × L) (T : I → Set Plane) (H : Set Plane)
    (pT : ∀ i, PolygonCertificate (T i) (fun e => realEdge site (tri i e)))
    (pH : PolygonCertificate H (fun e => realEdge site (hull e)))
    (hne : ∀ j, (listedEdges site tri hull j).1 ≠ (listedEdges site tri hull j).2)
    (hchain : (∑ i, ∑ e, signedEdge (tri i e)) = ∑ e, signedEdge (hull e))
    (hsub : ∀ i, T i ⊆ H) :
    (⋃ i, T i) = H := by
  apply closed_cover_from_off_edge_count (listedEdges site tri hull) H T pH.convex pH.full
    pH.compact.isClosed (fun i => (pT i).compact.isClosed) hsub
  intro x hx he
  rw [off_edge_count_from_signed_boundary site tri hull T H pT pH hne hchain x he]
  simp [interiorIndicator, hx]


/-- The three directed edges of an ordered triangle. -/
def triangleEdges {A : Type*} (p q r : A) : Fin 3 → A × A :=
  ![(p,q), (q,r), (r,p)]

private theorem edgeSide_first (p q : Plane) : edgeSide (p,q) p = 0 := by
  simp [edgeSide]

private theorem edgeSide_second (p q : Plane) : edgeSide (p,q) q = 0 := by
  unfold edgeSide
  ring

private theorem edgeSide_cyclic (p q r : Plane) : edgeSide (q,r) p = edgeSide (p,q) r := by
  simp only [edgeSide]
  ring

private theorem triangle_side_endpoints {p q r : Plane} (hccw : 0 < edgeSide (p,q) r)
    (i : Fin 3) : ∀ y ∈ ({p,q,r} : Set Plane), 0 ≤ edgeSide (triangleEdges p q r i) y := by
  have hQ : 0 < edgeSide (q,r) p := edgeSide_cyclic p q r ▸ hccw
  have hR : 0 < edgeSide (r,p) q := edgeSide_cyclic q r p ▸ hQ
  intro y hy
  simp only [mem_insert_iff, mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl <;> fin_cases i <;>
    first
    | exact hccw.le
    | exact hQ.le
    | exact hR.le
    | exact (edgeSide_first _ _).ge
    | exact (edgeSide_second _ _).ge

private theorem triangle_combination (p q r y : Plane) (h : edgeSide (p,q) r ≠ 0) :
    let a := edgeSide (q,r) y / edgeSide (p,q) r
    let b := edgeSide (r,p) y / edgeSide (p,q) r
    let c := edgeSide (p,q) y / edgeSide (p,q) r
    a + b + c = 1 ∧ a • p + b • q + c • r = y := by
  dsimp only
  constructor
  · field_simp
    simp only [edgeSide]
    ring
  · ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hi : i = 0 ∨ i = 1 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hi with rfl | rfl <;> field_simp <;> simp only [edgeSide] <;> ring

/-- A real CCW triangle is the intersection of the three closed inward half-planes. -/
theorem triangle_mem_iff (p q r y : Plane) (hccw : 0 < edgeSide (p,q) r) :
    y ∈ convexHull ℝ ({p,q,r} : Set Plane) ↔
      ∀ i, 0 ≤ edgeSide (triangleEdges p q r i) y := by
  let V := ({p,q,r} : Set Plane)
  constructor
  · intro hy i
    have hcvx : Convex ℝ {z | 0 ≤ edgeSide (triangleEdges p q r i) z} := by
      intro a ha b hb s t hs ht hst
      change 0 ≤ edgeSide (triangleEdges p q r i) (s • a + t • b)
      rw [edgeSide_combination _ _ _ _ _ hst]
      exact add_nonneg (mul_nonneg hs ha) (mul_nonneg ht hb)
    exact convexHull_min (triangle_side_endpoints hccw i) hcvx hy
  · intro hy
    let w : Fin 3 → ℝ :=
      ![edgeSide (q,r) y / edgeSide (p,q) r, edgeSide (r,p) y / edgeSide (p,q) r,
        edgeSide (p,q) y / edgeSide (p,q) r]
    let pts : Fin 3 → Plane := ![p,q,r]
    obtain ⟨hs, he⟩ := triangle_combination p q r y hccw.ne'
    have hsum : ∑ i, w i = 1 := by simpa [w, Fin.sum_univ_three] using hs
    have hsumpt : ∑ i, w i • pts i = y := by simpa [w, pts, Fin.sum_univ_three] using he
    rw [← hsumpt]
    refine (convex_convexHull ℝ V).sum_mem (t := Finset.univ) (w := w) ?_ hsum ?_
    · intro i _
      fin_cases i
      · exact div_nonneg (hy 1) hccw.le
      · exact div_nonneg (hy 2) hccw.le
      · exact div_nonneg (hy 0) hccw.le
    · intro i _
      apply subset_convexHull ℝ V
      fin_cases i <;> simp [pts, V]

private theorem triangle_side_zero_mem_segment (p q r y : Plane) (hccw : 0 < edgeSide (p,q) r)
    (hy : y ∈ convexHull ℝ ({p,q,r} : Set Plane)) (i : Fin 3)
    (hz : edgeSide (triangleEdges p q r i) y = 0) :
    y ∈ segment ℝ (triangleEdges p q r i).1 (triangleEdges p q r i).2 := by
  let a := edgeSide (q,r) y / edgeSide (p,q) r
  let b := edgeSide (r,p) y / edgeSide (p,q) r
  let c := edgeSide (p,q) y / edgeSide (p,q) r
  have hn := (triangle_mem_iff p q r y hccw).1 hy
  have ha : 0 ≤ a := div_nonneg (hn 1) hccw.le
  have hb : 0 ≤ b := div_nonneg (hn 2) hccw.le
  have hc : 0 ≤ c := div_nonneg (hn 0) hccw.le
  have hr : a + b + c = 1 ∧ a • p + b • q + c • r = y := triangle_combination p q r y hccw.ne'
  fin_cases i
  · change y ∈ segment ℝ p q
    have h0 : c = 0 := by change edgeSide (p,q) y = 0 at hz; simp [c, hz]
    exact ⟨a, b, ha, hb, by simpa [h0] using hr.1, by simpa [h0] using hr.2⟩
  · change y ∈ segment ℝ q r
    have h0 : a = 0 := by change edgeSide (q,r) y = 0 at hz; simp [a, hz]
    exact ⟨b, c, hb, hc, by simpa [h0] using hr.1, by simpa [h0] using hr.2⟩
  · change y ∈ segment ℝ r p
    have h0 : b = 0 := by change edgeSide (r,p) y = 0 at hz; simp [b, hz]
    exact ⟨c, a, hc, ha, by simpa [h0, add_comm] using hr.1, by simpa [h0, add_comm] using hr.2⟩

private theorem triangle_edges_ne {p q r : Plane} (hccw : 0 < edgeSide (p,q) r) :
    ∀ i, (triangleEdges p q r i).1 ≠ (triangleEdges p q r i).2 := by
  intro i
  fin_cases i
  · change p ≠ q
    intro he
    subst q
    simp [edgeSide] at hccw
  · change q ≠ r
    intro he
    subst r
    rw [edgeSide_second] at hccw
    exact (lt_irrefl 0) hccw
  · change r ≠ p
    intro he
    subst r
    rw [edgeSide_first] at hccw
    exact (lt_irrefl 0) hccw

/-- A positively oriented real triangle carries a polygon certificate for its ordered edges. -/
theorem triangle_polygonCertificate (p q r : Plane) (hccw : 0 < edgeSide (p,q) r) :
    PolygonCertificate (convexHull ℝ ({p,q,r} : Set Plane)) (triangleEdges p q r) := by
  let V := ({p,q,r} : Set Plane)
  let H := convexHull ℝ V
  let edges := triangleEdges p q r
  have hcomp : IsCompact H := (((Set.finite_singleton r).insert q).insert p).isCompact_convexHull ℝ
  have hleft (i : Fin 3) (y : Plane) (hy : y ∈ H) : 0 ≤ edgeSide (edges i) y :=
    (triangle_mem_iff p q r y hccw).1 hy i
  let U : Set Plane := ⋂ i : Fin 3, {y | 0 < edgeSide (edges i) y}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_edgeSide (edges i))
  have hUi : U ⊆ interior H := interior_maximal (fun _ hy =>
    (triangle_mem_iff p q r _ hccw).2 fun i => (mem_iInter.1 hy i : 0 < edgeSide (edges i) _).le) hU
  have hQ : 0 < edgeSide (q,r) p := edgeSide_cyclic p q r ▸ hccw
  have hR : 0 < edgeSide (r,p) q := edgeSide_cyclic q r p ▸ hQ
  let z := (1/3 : ℝ) • (p + q + r)
  have hzU : z ∈ U := by
    apply mem_iInter.2
    intro i
    change 0 < edgeSide (edges i) z
    have hpos (a b c : Plane) (hh : 0 < edgeSide (a,b) c) :
        0 < edgeSide (a,b) ((1/3 : ℝ) • (a + b + c)) := by
      have he : edgeSide (a,b) ((1/3 : ℝ) • (a + b + c)) = (1/3 : ℝ) * edgeSide (a,b) c := by
        simp only [edgeSide, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
        ring
      rw [he]
      positivity
    fin_cases i
    · exact hpos p q r hccw
    · simpa [z, edges, triangleEdges, add_comm, add_left_comm, add_assoc] using hpos q r p hQ
    · simpa [z, edges, triangleEdges, add_comm, add_left_comm, add_assoc] using hpos r p q hR
  have hOff : z ∈ offEdges edges := by
    intro h
    obtain ⟨i, hi⟩ := mem_iUnion.1 h
    exact (mem_iInter.1 hzU i : 0 < edgeSide (edges i) z).ne'
      (edgeSide_eq_zero_on_segment (edges i) hi)
  obtain ⟨m, hm, _⟩ := exists_generic_slope edges z (triangle_edges_ne hccw) hOff
  refine ⟨hcomp, convex_convexHull ℝ V, ⟨z, hUi hzU⟩, ?_, hleft, ?_⟩
  · ext y
    rw [frontier, hcomp.isClosed.closure_eq]
    constructor
    · rintro ⟨hy, hni⟩
      have hnu : y ∉ U := fun hu => hni (hUi hu)
      have hex : ∃ i, edgeSide (edges i) y = 0 := by
        by_contra h
        apply hnu
        exact mem_iInter.2 fun i => lt_of_le_of_ne (hleft i y hy) (fun he => h ⟨i, he.symm⟩)
      obtain ⟨i, hi⟩ := hex
      exact mem_iUnion.2 ⟨i, triangle_side_zero_mem_segment p q r y hccw hy i hi⟩
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.1 hy
      have hv (j : Fin 3) : ![p,q,r] j ∈ H := by
        apply subset_convexHull ℝ V
        fin_cases j <;> simp [V]
      have hey : y ∈ H := by
        apply (convex_convexHull ℝ V).segment_subset _ _ hi <;>
          fin_cases i <;> first | exact hv 0 | exact hv 1 | exact hv 2
      refine ⟨hey, fun hyi => ?_⟩
      exact (interior_side_pos_of_support (edges i) (hleft i) m (hm i) hyi).ne'
        (edgeSide_eq_zero_on_segment (edges i) hi)
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact False.elim (hij rfl)
      | exact Or.inl hccw
      | exact Or.inr hccw
      | exact Or.inl hQ
      | exact Or.inr hQ
      | exact Or.inl hR
      | exact Or.inr hR

/-- Positive rational orientation certifies the real convex hull of the three cast vertices. -/
theorem rational_triangle_polygonCertificate (a b c : Point)
    (h : 0 < TDA.Filtration.RationalAlpha.orient a b c) :
    PolygonCertificate (convexHull ℝ ({castPoint a, castPoint b, castPoint c} : Set Plane))
      (triangleEdges (castPoint a) (castPoint b) (castPoint c)) := by
  apply triangle_polygonCertificate
  rw [side_of_rational_sites]
  exact_mod_cast h


/-- The edge joining a cycle position to its cyclic successor. -/
def cycleEdges {A : Type*} {n : ℕ} (vertices : Fin (n + 3) → A) (i : Fin (n + 3)) : A × A :=
  (vertices i, vertices (i + 1))

private theorem cycle_edges_ne {A : Type*} {n : ℕ} {vertices : Fin (n + 3) → A}
    (hv : Function.Injective vertices) (i : Fin (n + 3)) :
    (cycleEdges vertices i).1 ≠ (cycleEdges vertices i).2 := by
  intro h
  have he : i = i + 1 := hv h
  have hz : (0 : Fin (n + 3)) = 1 := add_left_cancel (by simpa only [add_zero] using he)
  have hh := congrArg Fin.val hz
  simp at hh

/-- The closed real convex hull of the vertices of a supplied label cycle. -/
def siteHull {L : Type*} (site : L → Point) {n : ℕ} (vertices : Fin (n + 3) → L) : Set Plane :=
  convexHull ℝ (range fun i => castPoint (site (vertices i)))

/-- The closed real triangle carrier determined by three supplied labels. -/
def siteTriangle {L : Type*} (site : L → Point) (vertex : Fin 3 → L) : Set Plane :=
  convexHull ℝ ({castPoint (site (vertex 0)), castPoint (site (vertex 1)),
    castPoint (site (vertex 2))} : Set Plane)

private theorem triangleEdges_cast {L : Type*} (site : L → Point) (a b c : L) (i : Fin 3) :
    realEdge site (triangleEdges a b c i) =
      triangleEdges (castPoint (site a)) (castPoint (site b)) (castPoint (site c)) i := by
  fin_cases i <;> rfl

/-- For a certified hull and a finite family of rational CCW triangles, equality of signed label
boundaries gives the off-edge multiplicity and equality of closed carriers. The hypotheses `hs`
and `hv` and the membership `hsite` of non-triangle labels are redundant:
`rational_cover_from_signed_boundary_of_triangle_sites` gives the same conclusions without them. -/
theorem rational_cover_from_signed_boundary {L I : Type*} [Fintype I] {n : ℕ}
    (site : L → Point) (hs : Function.Injective site) (hull : Fin (n + 3) → L)
    (hv : Function.Injective hull) (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hsite : ∀ v, castPoint (site v) ∈ siteHull site hull)
    (hccw : ∀ i, 0 < TDA.Filtration.RationalAlpha.orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hchain : (∑ i, ∑ e, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) e)) =
        ∑ e, signedEdge (cycleEdges hull e)) :
    (∀ x ∈ offEdges (listedEdges site (fun i => triangleEdges (tri i 0) (tri i 1) (tri i 2))
      (cycleEdges hull)), interiorMultiplicity (fun i => siteTriangle site (tri i)) x =
        interiorIndicator (siteHull site hull) x) ∧
    (⋃ i, siteTriangle site (tri i)) = siteHull site hull := by
  let ES (i : I) := triangleEdges (tri i 0) (tri i 1) (tri i 2)
  let T (i : I) := siteTriangle site (tri i)
  have pT (i : I) : PolygonCertificate (T i) (fun e => realEdge site (ES i e)) := by
    simp only [ES, triangleEdges_cast, T, siteTriangle]
    exact rational_triangle_polygonCertificate _ _ _ (hccw i)
  have hne (j : Sum (I × Fin 3) (Fin (n+3))) :
      (listedEdges site ES (cycleEdges hull) j).1 ≠ (listedEdges site ES (cycleEdges hull) j).2 := by
    rcases j with ⟨i, e⟩ | e
    · change (realEdge site (ES i e)).1 ≠ (realEdge site (ES i e)).2
      have hc : 0 < edgeSide (castPoint (site (tri i 0)), castPoint (site (tri i 1)))
          (castPoint (site (tri i 2))) := by
        rw [side_of_rational_sites]
        exact_mod_cast hccw i
      simp only [ES, triangleEdges_cast]
      exact triangle_edges_ne hc e
    · intro he
      exact cycle_edges_ne hv e (hs (TDA.Filtration.RationalAlpha.castPoint_injective he))
  have hsub (i : I) : T i ⊆ siteHull site hull := by
    apply convexHull_min _ hh.convex
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> apply hsite
  exact ⟨fun x hx => off_edge_count_from_signed_boundary site ES (cycleEdges hull) T _
    pT hh hne hchain x hx,
    closed_cover_from_signed_boundary site ES (cycleEdges hull) T _
    pT hh hne hchain hsub⟩

/-- For a distinct cyclic hull with noncollinear site triples, the certified frontier and inward
supports furnish the polygon certificate. -/
theorem hull_polygonCertificate {L : Type*} {n : ℕ}
    (site : L → Point) (hull : Fin (n+3) → L) (hv : Function.Injective hull)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      TDA.Filtration.RationalAlpha.orient (site a) (site b) (site c) ≠ 0)
    (hfull : (interior (siteHull site hull)).Nonempty)
    (hfront : frontier (siteHull site hull) =
      ⋃ i, segment ℝ (realEdge site (cycleEdges hull i)).1 (realEdge site (cycleEdges hull i)).2)
    (hleft : ∀ i y, y ∈ siteHull site hull → 0 ≤ edgeSide (realEdge site (cycleEdges hull i)) y) :
    PolygonCertificate (siteHull site hull) (fun i => realEdge site (cycleEdges hull i)) := by
  refine ⟨(Set.finite_range _).isCompact_convexHull ℝ, convex_convexHull ℝ _, hfull, hfront, hleft, ?_⟩
  have hm (j : Fin (n + 3)) : castPoint (site (hull j)) ∈ siteHull site hull :=
    subset_convexHull ℝ _ ⟨j, rfl⟩
  have hs (j t : Fin (n + 3)) (hjt : t ≠ j) (hjt' : t ≠ j+1) :
      0 < edgeSide (realEdge site (cycleEdges hull j)) (castPoint (site (hull t))) := by
    apply lt_of_le_of_ne (hleft j _ (hm t))
    intro he
    change 0 = edgeSide (castPoint (site (hull j)), castPoint (site (hull (j+1))))
      (castPoint (site (hull t))) at he
    rw [side_of_rational_sites] at he
    apply hgen _ _ _ (cycle_edges_ne hv j) (fun eq => hjt (hv eq.symm)) (fun eq => hjt' (hv eq.symm))
    exact_mod_cast he.symm
  intro i j hij
  by_cases he : i = j + 1
  · right
    apply hs j (i + 1)
    · intro hn
      have hz : j + (1 + 1) = j + 0 := by simpa only [← add_assoc, add_zero, ← he] using hn
      have htwo : (1 + 1 : Fin (n + 3)) = 0 := add_left_cancel hz
      have hval := congrArg Fin.val htwo
      have h2 : ((1 + 1 : Fin (n + 3))).val = 2 := by
        rw [Fin.val_add]
        norm_num [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
      rw [h2] at hval
      exact (by decide : (2 : ℕ) ≠ 0) hval
    · exact fun hn => hij (add_right_cancel hn)
  · exact Or.inl (hs j i hij he)

/-- Noncollinearity of distinct hull positions suffices for the supplied polygon certificate.
The real interior, frontier, and left support of the hull are supplied as hypotheses. -/
theorem hull_polygonCertificate_hullOnly {L : Type*} {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L)
    (hgen : ∀ a b c : Fin (n + 3), a ≠ b → a ≠ c → b ≠ c →
      orient (site (hull a)) (site (hull b)) (site (hull c)) ≠ 0)
    (hfull : (interior (siteHull site hull)).Nonempty)
    (hfront : frontier (siteHull site hull) =
      ⋃ i, segment ℝ (realEdge site (cycleEdges hull i)).1 (realEdge site (cycleEdges hull i)).2)
    (hleft : ∀ i y, y ∈ siteHull site hull → 0 ≤ edgeSide (realEdge site (cycleEdges hull i)) y) :
    PolygonCertificate (siteHull site hull) (fun i => realEdge site (cycleEdges hull i)) :=
  hull_polygonCertificate (site ∘ hull) id Function.injective_id hgen hfull hfront hleft

/-- Each site label occurs at some vertex position of a supplied piece. -/
def allSitesUsed {L I E : Type*} (vertices : I → E → L) : Prop :=
  ∀ label, ∃ piece vertex, vertices piece vertex = label


private theorem corner_next_ne_self {n : ℕ} (i : Fin (n + 3)) : i + 1 ≠ i := by
  intro h
  have he : (1 : Fin (n + 3)) = 0 := add_left_cancel (h.trans (add_zero i).symm)
  have hv := congrArg Fin.val he
  simp at hv

private theorem corner_next_next_ne_self {n : ℕ} (i : Fin (n + 3)) : i + 1 + 1 ≠ i := by
  intro h
  have he : (1 : Fin (n + 3)) + 1 = 0 :=
    add_left_cancel (by simpa only [← add_assoc, add_zero] using h)
  have hv := congrArg Fin.val he
  simp only [Fin.val_add, Fin.val_one, Fin.val_zero, Nat.reduceAdd] at hv
  rw [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at hv
  contradiction

private theorem corner_coordinates (p a b x : Plane) (hd : edgeSide (p, a) b ≠ 0) :
    x = a + (edgeSide (a, b) x / edgeSide (p, a) b) • (p - a) +
      (edgeSide (p, a) x / edgeSide (p, a) b) • (b - a) := by
  obtain ⟨hsum, hpoint⟩ := triangle_combination p a b x hd
  let u := edgeSide (a, b) x / edgeSide (p, a) b
  let w := edgeSide (b, p) x / edgeSide (p, a) b
  let t := edgeSide (p, a) x / edgeSide (p, a) b
  change u + w + t = 1 at hsum
  change u • p + w • a + t • b = x at hpoint
  change x = a + u • (p - a) + t • (b - a)
  rw [← hpoint, show w = 1 - u - t by linarith only [hsum]]
  module

private abbrev StrictInwardCycle {n : ℕ} (v : Fin (n + 3) → Plane) : Prop :=
  ∀ i j, j ≠ i → j ≠ i + 1 → 0 < edgeSide (cycleEdges v i) (v j)

private abbrev cycleHalfplanes {n : ℕ} (v : Fin (n + 3) → Plane) : Set Plane :=
  {x | ∀ i, 0 ≤ edgeSide (cycleEdges v i) x}

private theorem left_at_corner {n : ℕ} (v : Fin (n + 3) → Plane) (hv : StrictInwardCycle v) (i j : Fin (n + 3)) :
    0 ≤ edgeSide (cycleEdges v i) (v j) := by
  by_cases hj : j = i
  · exact le_of_eq (by rw [hj]; exact (edgeSide_first _ _).symm)
  by_cases hj' : j = i + 1
  · exact le_of_eq (by rw [hj']; exact (edgeSide_second _ _).symm)
  exact (hv i j hj hj').le

private theorem turn_pos {n : ℕ} (v : Fin (n + 3) → Plane) (hv : StrictInwardCycle v) (i : Fin (n + 3)) :
    0 < edgeSide (v i, v (i + 1)) (v (i + 1 + 1)) :=
  hv i _ (corner_next_next_ne_self i) (corner_next_ne_self (i + 1))

/-- A strictly supporting cyclic presentation cuts out the convex hull of its corners. -/
private theorem cornerHull_eq_halfplanes {n : ℕ} (v : Fin (n + 3) → Plane) (hv : StrictInwardCycle v) :
    convexHull ℝ (range v) = cycleHalfplanes v := by
  have hclosed : IsClosed (convexHull ℝ (range v)) := (finite_range v).isClosed_convexHull ℝ
  apply Subset.antisymm
  · apply convexHull_min
    · rintro x ⟨j, rfl⟩ i
      exact left_at_corner v hv i j
    · intro x hx y hy r s hr hs hrs i
      rw [edgeSide_combination _ _ _ _ _ hrs]
      exact add_nonneg (mul_nonneg hr (hx i)) (mul_nonneg hs (hy i))
  · intro x hx
    by_contra h
    obtain ⟨f, c, hc, hxc⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed h
    obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => f (v i)) Finset.univ_nonempty
    let i := j - 1
    have hij : i + 1 = j := sub_add_cancel j 1
    have hd := turn_pos v hv i
    have hp := hmax i (Finset.mem_univ i)
    have hb := hmax (i + 1 + 1) (Finset.mem_univ _)
    have hf1 : f (v i) - f (v (i + 1)) ≤ 0 := by rw [hij]; linarith
    have hf2 : f (v (i + 1 + 1)) - f (v (i + 1)) ≤ 0 := by rw [hij] at ⊢; simpa only [hij] using sub_nonpos.mpr hb
    have h1 := div_nonneg (hx (i + 1)) hd.le
    have h2 := div_nonneg (hx i) hd.le
    have he := congrArg f (corner_coordinates (v i) (v (i + 1)) (v (i + 1 + 1)) x hd.ne')
    simp only [map_add, map_smul, map_sub, smul_eq_mul] at he
    have hle : f x ≤ f (v (i + 1)) := by
      have h1' := mul_nonpos_of_nonneg_of_nonpos h1 hf1
      have h2' := mul_nonpos_of_nonneg_of_nonpos h2 hf2
      simp only [cycleEdges] at h1' h2'
      linarith only [he, h1', h2']
    exact (not_lt_of_ge hle) ((hc _ (subset_convexHull ℝ _ ⟨i + 1, rfl⟩)).trans hxc)

private theorem active_side_mem_segment {n : ℕ} (v : Fin (n + 3) → Plane) (hv : StrictInwardCycle v)
    (i : Fin (n + 3)) (x : Plane) (hx : x ∈ cycleHalfplanes v) (hzero : edgeSide (cycleEdges v i) x = 0) :
    x ∈ segment ℝ (v i) (v (i + 1)) := by
  let j := i - 1
  have hj : j + 1 = i := sub_add_cancel i 1
  have hd : 0 < edgeSide (v j, v i) (v (i + 1)) := by
    simpa only [hj] using turn_pos v hv j
  let t := edgeSide (v j, v i) x / edgeSide (v j, v i) (v (i + 1))
  have ht0 : 0 ≤ t := div_nonneg (by simpa only [cycleEdges, hj] using hx j) hd.le
  have hform : x = (1 - t) • v i + t • v (i + 1) := by
    have he := corner_coordinates (v j) (v i) (v (i + 1)) x hd.ne'
    change edgeSide (v i, v (i + 1)) x = 0 at hzero
    rw [hzero, zero_div, zero_smul, add_zero] at he
    rw [he]
    ext k
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    change v i k + t * (v (i + 1) k - v i k) =
      (1-t) * v i k + t * v (i + 1) k
    ring
  have hside : 0 ≤ edgeSide (cycleEdges v (i + 1)) x := hx (i + 1)
  rw [hform, edgeSide_combination _ _ _ _ _ (by ring)] at hside
  change 0 ≤ (1 - t) * edgeSide (v (i + 1), v (i + 1 + 1)) (v i) +
    t * edgeSide (v (i + 1), v (i + 1 + 1)) (v (i + 1)) at hside
  rw [edgeSide_first, mul_zero, add_zero, edgeSide_cyclic] at hside
  have ht1 : t ≤ 1 := sub_nonneg.mp (nonneg_of_mul_nonneg_left hside (turn_pos v hv i))
  exact ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, hform.symm⟩

private theorem corners_mem {n : ℕ} (v : Fin (n + 3) → Plane) (i : Fin (n + 3)) :
    v i ∈ convexHull ℝ (range v) := subset_convexHull ℝ _ ⟨i, rfl⟩

private theorem edge_ne {n : ℕ} (v : Fin (n + 3) → Plane) (hv : StrictInwardCycle v) (i : Fin (n + 3)) :
    (cycleEdges v i).1 ≠ (cycleEdges v i).2 := by
  change v i ≠ v (i + 1)
  intro he
  have hd := turn_pos v hv i
  rw [← he] at hd
  simp [edgeSide] at hd

/-- A supplied strict cycle produces all fields of the existing real polygon certificate. -/
private theorem cornerHull_certificate {n : ℕ} (v : Fin (n + 3) → Plane) (hv : StrictInwardCycle v) :
    PolygonCertificate (convexHull ℝ (range v)) (cycleEdges v) := by
  let H := convexHull ℝ (range v)
  have hcompact : IsCompact H := (finite_range v).isCompact_convexHull ℝ
  have hconv : Convex ℝ H := convex_convexHull ℝ _
  have hHp : H = cycleHalfplanes v := cornerHull_eq_halfplanes v hv
  have hleft (i : Fin (n + 3)) (x : Plane) (hx : x ∈ H) :
      0 ≤ edgeSide (cycleEdges v i) x := (hHp ▸ hx : x ∈ cycleHalfplanes v) i
  have hfull : (interior H).Nonempty := by
    have ht := triangle_polygonCertificate (v 0) (v (0 + 1)) (v (0 + 1 + 1)) (turn_pos v hv 0)
    apply ht.full.mono (interior_mono _)
    apply convexHull_mono
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact mem_range_self _
  have ⟨z, hz⟩ := (dense_off_edges (cycleEdges v)).nonempty
  obtain ⟨m, hm, _⟩ := exists_generic_slope (cycleEdges v) z (edge_ne v hv) hz
  refine ⟨hcompact, hconv, hfull, ?_, hleft, ?_⟩
  · let U : Set Plane := ⋂ i, {x | 0 < edgeSide (cycleEdges v i) x}
    have hUopen : IsOpen U :=
      isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_edgeSide _)
    have hUH : U ⊆ H := by
      intro x hx
      rw [hHp]
      exact fun i => (show 0 < edgeSide (cycleEdges v i) x from mem_iInter.1 hx i).le
    have hUi : U ⊆ interior H := interior_maximal hUH hUopen
    ext x
    rw [frontier, hcompact.isClosed.closure_eq]
    constructor
    · rintro ⟨hx, hn⟩
      have hex : ∃ i, edgeSide (cycleEdges v i) x = 0 := by
        by_contra h
        exact hn (hUi (mem_iInter.2 fun i =>
          lt_of_le_of_ne (hleft i x hx) (fun he => h ⟨i, he.symm⟩)))
      obtain ⟨i, hi⟩ := hex
      exact mem_iUnion.2 ⟨i, active_side_mem_segment v hv i x (hHp ▸ hx) hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      refine ⟨hconv.segment_subset (corners_mem v i) (corners_mem v (i + 1)) hi, fun hxI => ?_⟩
      exact (interior_side_pos_of_support (cycleEdges v i) (hleft i) m (hm i) hxI).ne'
        (edgeSide_eq_zero_on_segment _ hi)
  · intro i j hij
    by_cases h : i = j + 1
    · subst i
      exact Or.inr (turn_pos v hv j)
    · exact Or.inl (hv j i hij h)

/-- Every nonincident corner position is strictly left of each directed side of the supplied
cycle. The cycle has at least three positions, and successive positions are taken cyclically. -/
abbrev StrictCornerCycle {L : Type*} {n : ℕ} (site : L → Point) (hull : Fin (n + 3) → L) : Prop :=
  ∀ i j, j ≠ i → j ≠ i + 1 →
    0 < orient (site (cycleEdges hull i).1) (site (cycleEdges hull i).2) (site (hull j))

/-- Every site lies weakly left of each directed side of the supplied cycle. A site on a side
may satisfy this predicate without occurring as a strict corner. -/
abbrev HullSitesLeft {L : Type*} {n : ℕ} (site : L → Point) (hull : Fin (n + 3) → L) : Prop :=
  ∀ i l, 0 ≤ orient (site (cycleEdges hull i).1) (site (cycleEdges hull i).2) (site l)

private theorem strict_cast {L : Type*} {n : ℕ} (site : L → Point) (hull : Fin (n + 3) → L)
    (hs : StrictCornerCycle site hull) : StrictInwardCycle (fun i => castPoint (site (hull i))) := by
  intro i j hji hjs
  change 0 < edgeSide (realEdge site (cycleEdges hull i)) (castPoint (site (hull j)))
  rw [realEdge, side_of_rational_sites]
  exact_mod_cast hs i j hji hjs

/-- Strict rational corner tests certify the closed convex hull of a supplied cycle, including its
frontier and inward supports. The certificate only concerns the supplied corners. -/
theorem rational_corner_certificate {L : Type*} {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) (hs : StrictCornerCycle site hull) :
    PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)) :=
  cornerHull_certificate _ (strict_cast site hull hs)

/-- The weak rational side tests are equivalent to all-site containment for a strict corner cycle. -/
theorem rational_sites_left_iff {L : Type*} {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) (hs : StrictCornerCycle site hull) :
    HullSitesLeft site hull ↔ ∀ l, castPoint (site l) ∈ siteHull site hull := by
  have hh : siteHull site hull = cycleHalfplanes (fun i => castPoint (site (hull i))) :=
    cornerHull_eq_halfplanes _ (strict_cast site hull hs)
  rw [hh]
  constructor
  · intro hw l i
    change 0 ≤ edgeSide (realEdge site (cycleEdges hull i)) (castPoint (site l))
    rw [realEdge, side_of_rational_sites]
    exact_mod_cast hw i l
  · intro hw i l
    have h := hw l i
    change 0 ≤ edgeSide (realEdge site (cycleEdges hull i)) (castPoint (site l)) at h
    rw [realEdge, side_of_rational_sites] at h
    exact_mod_cast h

/-- The corner hull is exactly the convex hull of all cast sites under the weak side tests. -/
theorem siteHull_eq_all_sites {L : Type*} {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) (hs : StrictCornerCycle site hull)
    (hw : HullSitesLeft site hull) :
    siteHull site hull = convexHull ℝ (range fun l => castPoint (site l)) := by
  apply Subset.antisymm
  · apply convexHull_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨hull i, rfl⟩
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨l, rfl⟩
    exact (rational_sites_left_iff site hull hs).1 hw l

/-- Check a supplied strict corner cycle and weak containment of all sites using exact rational
orientation. The finite label enumeration covers corner, side-interior and other site labels. -/
def cornerHullCheck {L : Type*} [Fintype L] {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) : Bool :=
  decide (StrictCornerCycle site hull ∧ HullSitesLeft site hull)

/-- The finite check succeeds exactly for strict corner cycles containing every cast site. -/
theorem cornerHullCheck_true_iff {L : Type*} [Fintype L] {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) :
    cornerHullCheck site hull = true ↔
      StrictCornerCycle site hull ∧ (∀ l, castPoint (site l) ∈ siteHull site hull) := by
  simp only [cornerHullCheck, decide_eq_true_eq]
  constructor <;> rintro ⟨hs, h⟩
  · exact ⟨hs, (rational_sites_left_iff site hull hs).1 h⟩
  · exact ⟨hs, (rational_sites_left_iff site hull hs).2 h⟩

/-- A true exact finite check produces the existing certificate and proves equality with the full
site hull. -/
theorem cornerHullCheck_sound {L : Type*} [Fintype L] {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) (h : cornerHullCheck site hull = true) :
    PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)) ∧
      siteHull site hull = convexHull ℝ (range fun l => castPoint (site l)) := by
  have hc : StrictCornerCycle site hull ∧ HullSitesLeft site hull := of_decide_eq_true h
  exact ⟨rational_corner_certificate site hull hc.1, siteHull_eq_all_sites site hull hc.1 hc.2⟩

end TDA.Filtration.RationalAlpha.SignedBoundary
