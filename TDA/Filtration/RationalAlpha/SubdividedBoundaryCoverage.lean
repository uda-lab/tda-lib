import TDA.Filtration.RationalAlpha.SignedBoundaryCoverage

set_option autoImplicit false

/-!
# Signed coverage with subdivided hull sides

The coarse hull supplies its strict polygon certificate. The signed chain uses every directed
labelled subedge occurrence. Transverse rays avoiding the subdivision vertices give equal crossing
sums for the two hull presentations.
-/

namespace TDA.Filtration.RationalAlpha.SignedBoundary

open Set

private theorem edgeSide_add_smul (a b x d : Plane) (t : ℝ) :
    edgeSide (a,b) (x + t • d) = edgeSide (a,b) x + t * sideSlope d (a,b) := by
  simp only [edgeSide, sideSlope, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem split_slope (a b d : Plane) (u : ℝ) :
    sideSlope d (a, AffineMap.lineMap a b u) = u * sideSlope d (a,b) ∧
    sideSlope d (AffineMap.lineMap a b u, b) = (1-u) * sideSlope d (a,b) := by
  simp only [AffineMap.lineMap_apply_module', sideSlope,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> ring

private theorem left_subsegment_mem {a b y : Plane} {u : ℝ} (hu : 0 < u)
    (hy : y ∈ openSegment ℝ a (AffineMap.lineMap a b u)) :
    ∃ v ∈ Ioo 0 u, AffineMap.lineMap a b v = y := by
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨v,hv,rfl⟩ := hy
  refine ⟨v*u, ⟨mul_pos hv.1 hu, ?_⟩, ?_⟩
  · simpa using mul_lt_mul_of_pos_right hv.2 hu
  · rw [AffineMap.lineMap_lineMap_right]

private theorem right_subsegment_mem {a b y : Plane} {u : ℝ} (hu1 : u < 1)
    (hy : y ∈ openSegment ℝ (AffineMap.lineMap a b u) b) :
    ∃ v ∈ Ioo u 1, AffineMap.lineMap a b v = y := by
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨v,hv,rfl⟩ := hy
  have hpos := mul_pos hv.1 (sub_pos.mpr hu1)
  have hpos' := mul_pos (sub_pos.mpr hv.2) (sub_pos.mpr hu1)
  exact ⟨1-(1-v)*(1-u), ⟨by nlinarith, by linarith⟩,
    (AffineMap.lineMap_lineMap_left a b u v).symm⟩

private theorem long_hit_iff {a b x d : Plane} {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hvertex : ∀ t : ℝ, 0 < t → x + t • d ≠ AffineMap.lineMap a b u) :
    rayHits x d (a,b) ↔ rayHits x d (a,AffineMap.lineMap a b u) ∨
      rayHits x d (AffineMap.lineMap a b u,b) := by
  constructor
  · rintro ⟨t,ht,hh⟩
    have hm := openSegment_subset_union a b
      (show AffineMap.lineMap a b u ∈ range (AffineMap.lineMap a b : ℝ → Plane) from ⟨u,rfl⟩) hh
    rcases hm with hm | hm | hm
    · exact False.elim (hvertex t ht hm)
    · exact Or.inl ⟨t,ht,hm⟩
    · exact Or.inr ⟨t,ht,hm⟩
  · rintro (⟨t,ht,hl⟩ | ⟨t,ht,hr⟩)
    · obtain ⟨v,hv,he⟩ := left_subsegment_mem hu hl
      exact ⟨t,ht, by rw [openSegment_eq_image_lineMap]; exact ⟨v,⟨hv.1,hv.2.trans hu1⟩,he⟩⟩
    · obtain ⟨v,hv,he⟩ := right_subsegment_mem hu1 hr
      exact ⟨t,ht, by rw [openSegment_eq_image_lineMap]; exact ⟨v,⟨hu.trans hv.1,hv.2⟩,he⟩⟩

private theorem subsegment_hits_exclusive {a b x d : Plane} {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (htrans : sideSlope d (a,b) ≠ 0)
    (hl : rayHits x d (a,AffineMap.lineMap a b u))
    (hr : rayHits x d (AffineMap.lineMap a b u,b)) : False := by
  obtain ⟨t,ht,hl⟩ := hl
  obtain ⟨s,hs,hr⟩ := hr
  obtain ⟨v,hv,hev⟩ := left_subsegment_mem hu hl
  obtain ⟨w,hw,hew⟩ := right_subsegment_mem hu1 hr
  have hall (r : ℝ) (hy : x + r • d ∈ openSegment ℝ a b) :
      edgeSide (a,b) x + r * sideSlope d (a,b) = 0 := by
    rw [← edgeSide_add_smul]
    exact edgeSide_eq_zero_on_segment (a,b) (openSegment_subset_segment ℝ a b hy)
  have hlong (r q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
      (he : AffineMap.lineMap a b q = x + r • d) : x + r • d ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨q,hq,he⟩
  have h₁ := hall t (hlong t v ⟨hv.1,hv.2.trans hu1⟩ hev)
  have h₂ := hall s (hlong s w ⟨hu.trans hw.1,hw.2⟩ hew)
  have hprod : (t-s) * sideSlope d (a,b) = 0 := by linear_combination h₁-h₂
  have he : t = s := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right htrans)
  have hab : a ≠ b := by
    intro h
    exact htrans (by simp [h,sideSlope])
  have hwv : v = w := AffineMap.lineMap_injective ℝ hab
    (hev.trans (he ▸ hew.symm))
  linarith [hv.2, hw.1]

private theorem rayContribution_subdivide {a b x d : Plane} {u : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (htrans : sideSlope d (a,b) ≠ 0)
    (hvertex : ∀ t : ℝ, 0 < t → x + t • d ≠ AffineMap.lineMap a b u) :
    rayContribution x d (a,b) =
      rayContribution x d (a,AffineMap.lineMap a b u) +
        rayContribution x d (AffineMap.lineMap a b u,b) := by
  classical
  obtain ⟨hl,hr⟩ := split_slope a b d u
  have hiff := long_hit_iff hu hu1 (x := x) (d := d) hvertex
  have mul_neg {c z : ℝ} (hc : 0 < c) : c*z < 0 ↔ z < 0 := by
    constructor
    · intro h
      by_contra! hz
      exact (not_lt_of_ge (mul_nonneg hc.le hz)) h
    · exact mul_neg_of_pos_of_neg hc
  unfold rayContribution
  simp only [hiff, hl, hr, mul_pos_iff_of_pos_left hu, mul_pos_iff_of_pos_left (sub_pos.mpr hu1),
    mul_neg hu, mul_neg (sub_pos.mpr hu1)]
  by_cases h₁ : rayHits x d (a,AffineMap.lineMap a b u)
  · have h₂ : ¬ rayHits x d (AffineMap.lineMap a b u,b) :=
      fun h => subsegment_hits_exclusive hu hu1 htrans h₁ h
    simp [h₁,h₂]
  · by_cases h₂ : rayHits x d (AffineMap.lineMap a b u,b) <;> simp [h₁,h₂]

/-- The cuts lie strictly inside the remaining directed segment, in the given order. -/
def OrderedEdgeCuts {L : Type*} (site : L → Point) (b : L) : L → List L → Prop
  | _, [] => True
  | a, c :: cuts =>
    (∃ u ∈ Ioo (0 : ℝ) 1,
      castPoint (site c) = AffineMap.lineMap (castPoint (site a)) (castPoint (site b)) u) ∧
      OrderedEdgeCuts site b c cuts

/-- Rational test that `c` lies strictly between `a` and `b` on their line: it is collinear with
them and its projection onto `b - a` lies strictly inside the segment. -/
def strictlyBetween (a c b : Point) : Bool :=
  decide ((b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) = 0 ∧
    0 < (c.1 - a.1) * (b.1 - a.1) + (c.2 - a.2) * (b.2 - a.2) ∧
    (c.1 - a.1) * (b.1 - a.1) + (c.2 - a.2) * (b.2 - a.2) <
      (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2)

/-- Executable check of `OrderedEdgeCuts` from rational data. -/
def checkOrderedEdgeCuts {L : Type*} (site : L → Point) (b : L) : L → List L → Bool
  | _, [] => true
  | a, c :: cuts => strictlyBetween (site a) (site c) (site b) && checkOrderedEdgeCuts site b c cuts

/-- A passing `strictlyBetween` test gives the real parameter of the point on the segment. -/
theorem strictlyBetween_sound {a c b : Point} (h : strictlyBetween a c b = true) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      castPoint c = AffineMap.lineMap (castPoint a) (castPoint b) u := by
  simp only [strictlyBetween, decide_eq_true_eq] at h
  obtain ⟨hcol, h0, h1⟩ := h
  set N : ℚ := (c.1 - a.1) * (b.1 - a.1) + (c.2 - a.2) * (b.2 - a.2) with hN
  set D : ℚ := (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 with hD
  have hDpos : 0 < D := h0.trans h1
  have e1 : c.1 = N / D * (b.1 - a.1) + a.1 := by
    field_simp
    rw [hN, hD]
    linear_combination (-(b.2 - a.2)) * hcol
  have e2 : c.2 = N / D * (b.2 - a.2) + a.2 := by
    field_simp
    rw [hN, hD]
    linear_combination (b.1 - a.1) * hcol
  refine ⟨((N / D : ℚ) : ℝ), ⟨?_, ?_⟩, ?_⟩
  · exact_mod_cast div_pos h0 hDpos
  · exact_mod_cast (div_lt_one hDpos).2 h1
  · ext i
    simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]
    fin_cases i
    · change ((c.1 : ℚ) : ℝ) = ((N / D : ℚ) : ℝ) * (((b.1 : ℚ) : ℝ) - (a.1 : ℚ)) + (a.1 : ℚ)
      rw [e1]
      push_cast
      ring
    · change ((c.2 : ℚ) : ℝ) = ((N / D : ℚ) : ℝ) * (((b.2 : ℚ) : ℝ) - (a.2 : ℚ)) + (a.2 : ℚ)
      rw [e2]
      push_cast
      ring

/-- A passing executable check gives `OrderedEdgeCuts`. -/
theorem orderedEdgeCuts_of_check {L : Type*} (site : L → Point) (b : L) :
    ∀ (a : L) (cuts : List L), checkOrderedEdgeCuts site b a cuts = true →
      OrderedEdgeCuts site b a cuts
  | _, [], _ => trivial
  | a, c :: cuts, h => by
    rw [checkOrderedEdgeCuts, Bool.and_eq_true] at h
    exact ⟨strictlyBetween_sound h.1, orderedEdgeCuts_of_check site b c cuts h.2⟩

/-- The consecutive directed label edges from `a` through the cuts to `b`. -/
def subdivisionEdges {L : Type*} (b : L) : L → List L → List (L × L)
  | a, [] => [(a, b)]
  | a, c :: cuts => (a, c) :: subdivisionEdges b c cuts

/-- Each refined occurrence is specified by a coarse side and a position in its subdivision. -/
abbrev SubdivisionIndex {L F : Type*} (coarse : F → L × L) (cuts : F → List L) :=
  Σ e : F, Fin (subdivisionEdges (coarse e).2 (coarse e).1 (cuts e)).length

/-- The refined directed label edge at the given occurrence. -/
def subdividedEdge {L F : Type*} (coarse : F → L × L) (cuts : F → List L)
    (j : SubdivisionIndex coarse cuts) : L × L :=
  (subdivisionEdges (coarse j.1).2 (coarse j.1).1 (cuts j.1)).get j.2

/-- The triangle edges, coarse hull sides and refined hull subedges used for generic ray selection. -/
def subdividedListedEdges {L I E F : Type*} (site : L → Point) (tri : I → E → L × L)
    (coarse : F → L × L) (cuts : F → List L) :
    Sum (Sum (I × E) F) (SubdivisionIndex coarse cuts) → Plane × Plane :=
  Sum.elim (listedEdges site tri coarse) (fun j => realEdge site (subdividedEdge coarse cuts j))

private theorem edgeSide_lineMap_left (a b y : Plane) (u : ℝ) :
    edgeSide (a, AffineMap.lineMap a b u) y = u * edgeSide (a, b) y := by
  simp only [edgeSide, AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

private theorem edgeSide_lineMap_right (a b y : Plane) (u : ℝ) :
    edgeSide (AffineMap.lineMap a b u, b) y = (1 - u) * edgeSide (a, b) y := by
  simp only [edgeSide, AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-- Each directed piece of an ordered subdivision has the side form of the whole side, scaled by
a positive factor. -/
theorem subdivisionEdges_side {L : Type*} (site : L → Point) (b : L) (a : L) (cuts : List L)
    (hcuts : OrderedEdgeCuts site b a cuts) :
    ∀ e ∈ subdivisionEdges b a cuts, ∃ c : ℝ, 0 < c ∧ ∀ y : Plane,
      edgeSide (realEdge site e) y = c * edgeSide (realEdge site (a, b)) y := by
  induction cuts generalizing a with
  | nil =>
    intro e he
    simp only [subdivisionEdges, List.mem_singleton] at he
    subst he
    exact ⟨1, one_pos, fun y => (one_mul _).symm⟩
  | cons c cuts ih =>
    rcases hcuts with ⟨⟨u, hu, hc⟩, hrest⟩
    intro e he
    simp only [subdivisionEdges, List.mem_cons] at he
    rcases he with rfl | he
    · refine ⟨u, hu.1, fun y => ?_⟩
      change edgeSide (castPoint (site a), castPoint (site c)) y =
        u * edgeSide (castPoint (site a), castPoint (site b)) y
      rw [hc, edgeSide_lineMap_left]
    · obtain ⟨d, hd, hside⟩ := ih c hrest e he
      refine ⟨d * (1 - u), mul_pos hd (sub_pos.mpr hu.2), fun y => ?_⟩
      rw [hside y, mul_assoc]
      congr 1
      change edgeSide (castPoint (site c), castPoint (site b)) y =
        (1 - u) * edgeSide (castPoint (site a), castPoint (site b)) y
      rw [hc, edgeSide_lineMap_right]


private theorem subdivisionEdges_nondegenerate {L : Type*} (site : L → Point)
    (a b : L) (cuts : List L) (hcuts : OrderedEdgeCuts site b a cuts)
    (hab : castPoint (site a) ≠ castPoint (site b)) :
    ∀ e ∈ subdivisionEdges b a cuts, (realEdge site e).1 ≠ (realEdge site e).2 := by
  induction cuts generalizing a with
  | nil => simpa [subdivisionEdges, realEdge] using hab
  | cons c cuts ih =>
    rcases hcuts with ⟨⟨u, hu, hc⟩, hcuts⟩
    have hline := AffineMap.lineMap_injective ℝ hab
    have hac : castPoint (site a) ≠ castPoint (site c) := by
      intro h
      have he : (0 : ℝ) = u := hline (by simpa only [AffineMap.lineMap_apply_zero, ← hc] using h)
      exact hu.1.ne' he.symm
    have hcb : castPoint (site c) ≠ castPoint (site b) := by
      intro h
      have he : u = (1 : ℝ) := hline (by simpa only [AffineMap.lineMap_apply_one, ← hc] using h)
      exact hu.2.ne he
    intro e he
    rcases List.mem_cons.1 he with rfl | ht
    · exact hac
    · exact ih c hcuts hcb e ht

private theorem crossing_sum_subdivision {L : Type*} (site : L → Point) (x d : Plane)
    (a b : L) (cuts : List L) (hcuts : OrderedEdgeCuts site b a cuts)
    (htrans : sideSlope d (realEdge site (a, b)) ≠ 0)
    (havoid : ∀ e ∈ subdivisionEdges b a cuts, ∀ t : ℝ, 0 < t →
      x + t • d ≠ (realEdge site e).2) :
    rayContribution x d (realEdge site (a, b)) =
      ((subdivisionEdges b a cuts).map (fun e => rayContribution x d (realEdge site e))).sum := by
  induction cuts generalizing a with
  | nil => simp [subdivisionEdges]
  | cons c cuts ih =>
    rcases hcuts with ⟨⟨u, hu, hc⟩, hcuts⟩
    have hcut : ∀ t : ℝ, 0 < t →
        x + t • d ≠ AffineMap.lineMap (castPoint (site a)) (castPoint (site b)) u := by
      rw [← hc]
      exact havoid (a, c) List.mem_cons_self
    have hcb : sideSlope d (realEdge site (c, b)) ≠ 0 := by
      change sideSlope d (castPoint (site c), castPoint (site b)) ≠ 0
      rw [hc, (split_slope (castPoint (site a)) (castPoint (site b)) d u).2]
      exact mul_ne_zero (sub_pos.mpr hu.2).ne' htrans
    have hsplit := rayContribution_subdivide hu.1 hu.2 htrans hcut
    rw [← hc] at hsplit
    change rayContribution x d (realEdge site (a, b)) =
      rayContribution x d (realEdge site (a, c)) +
        ((subdivisionEdges b c cuts).map (fun e => rayContribution x d (realEdge site e))).sum
    rw [← ih c hcuts hcb (fun e he => havoid e (List.mem_cons_of_mem _ he))]
    exact hsplit

private theorem crossing_sum_subdivided_edges {L F : Type*} [Fintype F]
    (site : L → Point) (coarse : F → L × L) (cuts : F → List L) (x d : Plane)
    (hcuts : ∀ e, OrderedEdgeCuts site (coarse e).2 (coarse e).1 (cuts e))
    (htrans : ∀ e, sideSlope d (realEdge site (coarse e)) ≠ 0)
    (havoid : ∀ (j : SubdivisionIndex coarse cuts) (t : ℝ), 0 < t →
      x + t • d ≠ (realEdge site (subdividedEdge coarse cuts j)).2) :
    (∑ j, rayContribution x d (realEdge site (subdividedEdge coarse cuts j))) =
      ∑ e, rayContribution x d (realEdge site (coarse e)) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  let es := subdivisionEdges (coarse e).2 (coarse e).1 (cuts e)
  let w := fun edge => rayContribution x d (realEdge site edge)
  change (∑ j : Fin es.length, w es[(j : ℕ)]) = _
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  symm
  apply crossing_sum_subdivision site x d _ _ _ (hcuts e) (htrans e)
  intro edge he t ht
  obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
  exact havoid ⟨e, j⟩ t ht

private theorem certifiedEdge_ne {E : Type*} [Nontrivial E] {H : Set Plane}
    {edges : E → Plane × Plane} (P : PolygonCertificate H edges) (i : E) :
    (edges i).1 ≠ (edges i).2 := by
  intro he
  obtain ⟨j, hj⟩ := exists_ne i
  have hzero (x : Plane) : edgeSide (edges i) x = 0 := by simp [edgeSide, he]
  rcases P.strict_endpoint j i hj with h | h <;> simp [hzero] at h

/-- A strict coarse hull and finite rational CCW triangles determine closed coverage and off-edge
multiplicity when the triangle chain equals the ordered subdivided hull chain. The multiplicity
statement excludes the closed segments of both hull presentations and of the triangles. -/
theorem rational_cover_from_subdivided_signed_boundary {L I : Type*} [Fintype I] {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) (cuts : Fin (n + 3) → List L)
    (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hcuts : ∀ e, OrderedEdgeCuts site (cycleEdges hull e).2 (cycleEdges hull e).1 (cuts e))
    (hsite : ∀ i j, castPoint (site (tri i j)) ∈ siteHull site hull)
    (hccw : ∀ i, 0 < TDA.Filtration.RationalAlpha.orient
      (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hchain : (∑ i, ∑ e, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) e)) =
      ∑ j, signedEdge (subdividedEdge (cycleEdges hull) cuts j)) :
    (∀ x ∈ offEdges (subdividedListedEdges site
        (fun i => triangleEdges (tri i 0) (tri i 1) (tri i 2)) (cycleEdges hull) cuts),
      interiorMultiplicity (fun i => siteTriangle site (tri i)) x =
        interiorIndicator (siteHull site hull) x) ∧
    (⋃ i, siteTriangle site (tri i)) = siteHull site hull := by
  let ES (i : I) := triangleEdges (tri i 0) (tri i 1) (tri i 2)
  let T (i : I) := siteTriangle site (tri i)
  let edges := subdividedListedEdges site ES (cycleEdges hull) cuts
  have pT (i : I) : PolygonCertificate (T i) (fun e => realEdge site (ES i e)) := by
    have hcast (e : Fin 3) : realEdge site (ES i e) =
        triangleEdges (castPoint (site (tri i 0))) (castPoint (site (tri i 1)))
          (castPoint (site (tri i 2))) e := by
      fin_cases e <;> rfl
    simpa only [hcast, T, siteTriangle] using
      rational_triangle_polygonCertificate _ _ _ (hccw i)
  have hne (j : Sum (Sum (I × Fin 3) (Fin (n + 3))) (SubdivisionIndex (cycleEdges hull) cuts)) :
      (edges j).1 ≠ (edges j).2 := by
    rcases j with (⟨i, e⟩ | e) | ⟨e, j⟩
    · exact certifiedEdge_ne (pT i) e
    · exact certifiedEdge_ne hh e
    · exact subdivisionEdges_nondegenerate site _ _ _ (hcuts e) (certifiedEdge_ne hh e) _
        (List.get_mem _ j)
  have hsub (i : I) : T i ⊆ siteHull site hull := by
    apply convexHull_min _ hh.convex
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hsite i 0
    · exact hsite i 1
    · exact hsite i 2
  have hcount (x : Plane) (hx : x ∈ offEdges edges) :
      interiorMultiplicity T x = interiorIndicator (siteHull site hull) x := by
    obtain ⟨m, hm, hv⟩ := exists_generic_slope edges x hne hx
    let w (e : L × L) := rayContribution x (slopeDir m) (realEdge site e)
    have hw (e : L × L) : w e.swap = -w e :=
      rayContribution_swap x (slopeDir m) (realEdge site e)
    have he := crossing_sum_of_finite_boundaries w hw ES (subdividedEdge (cycleEdges hull) cuts) hchain
    have htransport : (∑ j, w (subdividedEdge (cycleEdges hull) cuts j)) =
        ∑ e, w (cycleEdges hull e) :=
      crossing_sum_subdivided_edges site _ cuts x (slopeDir m) hcuts
        (fun e => hm (Sum.inl (Sum.inr e))) (fun j t _ => (hv (Sum.inr j) t).2)
    have hT (i : I) : (∑ e, w (ES i e)) = interiorIndicator (T i) x :=
      (pT i).ray_sum_eq_indicator x m
        (fun h => hx (by
          obtain ⟨e, he⟩ := mem_iUnion.1 h
          exact mem_iUnion.2 ⟨Sum.inl (Sum.inl (i, e)), he⟩))
        (fun e => hm (Sum.inl (Sum.inl (i, e)))) (fun e t => hv (Sum.inl (Sum.inl (i, e))) t)
    have hH : (∑ e, w (cycleEdges hull e)) = interiorIndicator (siteHull site hull) x :=
      hh.ray_sum_eq_indicator x m
        (fun h => hx (by
          obtain ⟨e, he⟩ := mem_iUnion.1 h
          exact mem_iUnion.2 ⟨Sum.inl (Sum.inr e), he⟩))
        (fun e => hm (Sum.inl (Sum.inr e))) (fun e t => hv (Sum.inl (Sum.inr e)) t)
    rw [htransport, hH] at he
    simpa only [hT, interiorMultiplicity] using he
  refine ⟨hcount, closed_cover_from_off_edge_count edges _ T hh.convex hh.full
    hh.compact.isClosed (fun i => (pT i).compact.isClosed) hsub ?_⟩
  intro x hxH hx
  rw [hcount x hx]
  simp [interiorIndicator, hxH]

/-- The conclusions of `rational_cover_from_signed_boundary` without injectivity of the sites or
of the hull labels, and with the hull membership required only for triangle labels. The
hypotheses are a strict polygon certificate for the coarse hull, hull membership of every
triangle site, rational CCW orientation of every triangle, and equality of the triangle chain
with the coarse hull chain. -/
theorem rational_cover_from_signed_boundary_of_triangle_sites {L I : Type*} [Fintype I] {n : ℕ}
    (site : L → Point) (hull : Fin (n + 3) → L) (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hsite : ∀ i j, castPoint (site (tri i j)) ∈ siteHull site hull)
    (hccw : ∀ i, 0 < TDA.Filtration.RationalAlpha.orient
      (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hchain : (∑ i, ∑ e, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) e)) =
        ∑ e, signedEdge (cycleEdges hull e)) :
    (∀ x ∈ offEdges (listedEdges site (fun i => triangleEdges (tri i 0) (tri i 1) (tri i 2))
      (cycleEdges hull)), interiorMultiplicity (fun i => siteTriangle site (tri i)) x =
        interiorIndicator (siteHull site hull) x) ∧
    (⋃ i, siteTriangle site (tri i)) = siteHull site hull := by
  have h := rational_cover_from_subdivided_signed_boundary site hull (fun _ => []) tri hh
    (fun _ => trivial) hsite hccw (hchain.trans ?_)
  · refine ⟨fun x hx => h.1 x ?_, h.2⟩
    simp only [offEdges, mem_compl_iff, mem_iUnion, not_exists] at hx ⊢
    rintro (j | ⟨e, j⟩)
    · exact hx j
    · rcases j with ⟨_ | k, hk⟩
      · exact hx (Sum.inr e)
      · simp [subdivisionEdges] at hk
  · rw [Fintype.sum_sigma]
    refine Fintype.sum_congr _ _ (fun e => ?_)
    exact (Fin.sum_univ_one
      (fun j : Fin 1 => signedEdge (subdividedEdge (cycleEdges hull) (fun _ => []) ⟨e, j⟩))).symm

end TDA.Filtration.RationalAlpha.SignedBoundary
