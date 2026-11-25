import TDA.Filtration.RationalAlpha.TriangleIncidence

set_option autoImplicit false

/-!
# Directed edge incidence of certified rational planar triangles

Two CCW triangle occurrences with an equally directed side have overlapping interiors.
Disjoint interiors therefore bound each directed multiplicity by one. Evaluating the signed
boundary at a labelled pair then gives the forward and reverse counts on that edge.

The hull certificate and site noncollinearity also classify the actual real segments. A
listed side lies on the hull frontier, and the open segment of an unlisted pair lies in the
hull interior. All-site usage is expressed separately by `SignedBoundary.allSitesUsed`.
-/

open Set Filter
open scoped Classical
open TDA.Filtration.RationalAlpha (Plane Point castPoint castPoint_injective orient)
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence

namespace TDA.Filtration.RationalAlpha.DirectedEdgeIncidence

private theorem interior_of_positive_sides {E : Type*} [Finite E] {H : Set Plane}
    {edges : E → Plane × Plane} (P : PolygonCertificate H edges)
    (hn : ∀ e, (edges e).1 ≠ (edges e).2) {y : Plane}
    (h : ∀ e, 0 < edgeSide (edges e) y) : y ∈ interior H := by
  let U : Set Plane := ⋂ i : E, {y | 0 < edgeSide (edges i) y}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_edgeSide (edges i))
  apply interior_maximal _ hU (mem_iInter.2 h)
  intro z hz
  have hOff : z ∈ offEdges edges := by
    intro hseg
    obtain ⟨i, hi⟩ := mem_iUnion.1 hseg
    exact (mem_iInter.1 hz i : 0 < edgeSide (edges i) z).ne'
      (edgeSide_eq_zero_on_segment (edges i) hi)
  obtain ⟨m, hm, _⟩ := exists_generic_slope edges z hn hOff
  exact (P.mem_iff_sides_nonneg m hm z).2 fun i =>
    (mem_iInter.1 hz i : 0 < edgeSide (edges i) z).le

private theorem other_left_at_midpoint {G : Type*} {C : Set Plane} {D : G → Plane × Plane}
    (R : PolygonCertificate C D) {k l : G} (hkl : k ≠ l) :
    0 < edgeSide (D l) ((1/2 : ℝ) • (D k).1 + (1/2 : ℝ) • (D k).2) := by
  have h₁ := R.left l _ (R.edge_subset k (left_mem_segment ℝ (D k).1 (D k).2))
  have h₂ := R.left l _ (R.edge_subset k (right_mem_segment ℝ (D k).1 (D k).2))
  have hs := R.strict_endpoint k l hkl
  rw [edgeSide_combination _ _ _ _ _ (by norm_num)]
  rcases hs with h | h <;> linarith

/-- Two convex certified polygons sharing an equally directed side have intersecting interiors. -/
private theorem shared_directed_side_overlap {E F : Type*} [Finite E] [Finite F]
    {H K : Set Plane} {A : E → Plane × Plane} {B : F → Plane × Plane}
    (P : PolygonCertificate H A) (Q : PolygonCertificate K B)
    (hnA : ∀ e, (A e).1 ≠ (A e).2) (hnB : ∀ e, (B e).1 ≠ (B e).2)
    {i : E} {j : F} (he : A i = B j) {z : Plane} (hz : 0 < edgeSide (A i) z) :
    (interior H ∩ interior K).Nonempty := by
  let y := (1/2 : ℝ) • (A i).1 + (1/2 : ℝ) • (A i).2
  have hy : y ∈ segment ℝ (A i).1 (A i).2 :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
  let f : ℝ → Plane := AffineMap.lineMap y z
  have hc : Continuous f := by
    change Continuous (AffineMap.lineMap y z : ℝ → Plane)
    fun_prop
  have hev (D : Plane × Plane) (h : 0 < edgeSide D y) :
      ∀ᶠ t : ℝ in nhds 0, 0 < edgeSide D (f t) := by
    apply (isOpen_lt continuous_const ((continuous_edgeSide D).comp hc)).mem_nhds
    simpa [f] using h
  have hA : ∀ᶠ t : ℝ in nhds 0, ∀ k : E, i ≠ k → 0 < edgeSide (A k) (f t) := by
    rw [eventually_all]
    intro k
    by_cases hik : i ≠ k
    · exact (hev (A k) (other_left_at_midpoint P hik)).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hik h).elim
  have hB : ∀ᶠ t : ℝ in nhds 0, ∀ k : F, j ≠ k → 0 < edgeSide (B k) (f t) := by
    rw [eventually_all]
    intro k
    by_cases hjk : j ≠ k
    · have hpos := other_left_at_midpoint Q hjk
      rw [← he] at hpos
      exact (hev (B k) hpos).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hjk h).elim
  obtain ⟨t, ht, htA, htB⟩ := (hA.and hB).exists_gt
  have hmain : 0 < edgeSide (A i) (f t) := by
    change 0 < edgeSide (A i) (AffineMap.lineMap y z t)
    rw [AffineMap.lineMap_apply_module, edgeSide_combination _ _ _ _ _ (by ring),
      edgeSide_eq_zero_on_segment _ hy, mul_zero, zero_add]
    exact mul_pos ht hz
  refine ⟨f t, interior_of_positive_sides P hnA ?_, interior_of_positive_sides Q hnB ?_⟩
  · intro k
    by_cases hk : i = k
    · simpa [← hk] using hmain
    · exact htA k hk
  · intro k
    by_cases hk : j = k
    · simpa [he, ← hk] using hmain
    · exact htB k hk

private theorem edgeSide_cyclic (p q r : Plane) : edgeSide (q, r) p = edgeSide (p, q) r := by
  simp only [edgeSide]
  ring

private theorem third_left (p q r : Plane) (hccw : 0 < edgeSide (p, q) r)
    (k : Fin 3) : ∃ z : Plane, 0 < edgeSide (triangleEdges p q r k) z := by
  have hq : 0 < edgeSide (q, r) p := by rwa [edgeSide_cyclic]
  have hr : 0 < edgeSide (r, p) q := by rwa [edgeSide_cyclic]
  fin_cases k
  · exact ⟨r, hccw⟩
  · exact ⟨p, hq⟩
  · exact ⟨q, hr⟩

private theorem rational_pos (a b c : Point) (h : 0 < orient a b c) :
    0 < edgeSide (castPoint a,castPoint b) (castPoint c) := by
  rw [side_of_rational_sites]
  exact_mod_cast h

private theorem edges_cast {L : Type*} (site : L → Point) (a b c : L) (i : Fin 3) :
    realEdge site (triangleEdges a b c i) =
      triangleEdges (castPoint (site a)) (castPoint (site b)) (castPoint (site c)) i := by
  fin_cases i <;> rfl

/-- The ordered pair of labels at a side slot of a supplied triangle occurrence. -/
abbrev occurrenceEdge {L I : Type*} (tri : I → Fin 3 → L) (p : I × Fin 3) : L × L :=
  triangleEdges (tri p.1 0) (tri p.1 1) (tri p.1 2) p.2

private theorem occurrence_polygonCertificate {L I : Type*} (site : L → Point)
    (tri : I → Fin 3 → L) (i : I)
    (hccw : 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2))) :
    PolygonCertificate (siteTriangle site (tri i))
      (fun k => realEdge site (occurrenceEdge tri (i, k))) := by
  simp only [occurrenceEdge, edges_cast, siteTriangle]
  exact rational_triangle_polygonCertificate _ _ _ hccw

private theorem occurrenceEdge_left {L I : Type*} (site : L → Point) (tri : I → Fin 3 → L)
    (i : I) (hccw : 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (k : Fin 3) : ∃ z, 0 < edgeSide (realEdge site (occurrenceEdge tri (i, k))) z := by
  rw [occurrenceEdge, edges_cast]
  exact third_left _ _ _ (rational_pos _ _ _ hccw) k

private theorem occurrenceEdge_ne {L I : Type*} (site : L → Point) (tri : I → Fin 3 → L)
    (i : I) (hccw : 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (k : Fin 3) :
    (realEdge site (occurrenceEdge tri (i, k))).1 ≠ (realEdge site (occurrenceEdge tri (i, k))).2 := by
  intro h
  obtain ⟨z, hz⟩ := occurrenceEdge_left site tri i hccw k
  simp [edgeSide, h] at hz

private theorem ccw_labels_injective {L I : Type*} (site : L → Point) (tri : I → Fin 3 → L)
    (i : I) (hccw : 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2))) :
    Function.Injective (tri i) := by
  have hn := occurrenceEdge_ne site tri i hccw
  have h01 : tri i 0 ≠ tri i 1 := fun h => hn 0 (congrArg (castPoint ∘ site) h)
  have h12 : tri i 1 ≠ tri i 2 := fun h => hn 1 (congrArg (castPoint ∘ site) h)
  have h20 : tri i 2 ≠ tri i 0 := fun h => hn 2 (congrArg (castPoint ∘ site) h)
  intro k l hfirst
  fin_cases k <;> fin_cases l <;> first
    | rfl
    | exact False.elim (h01 hfirst)
    | exact False.elim (h01 hfirst.symm)
    | exact False.elim (h12 hfirst)
    | exact False.elim (h12 hfirst.symm)
    | exact False.elim (h20 hfirst)
    | exact False.elim (h20 hfirst.symm)

private theorem occurrenceEdge_eq_cycle {L I : Type*} (tri : I → Fin 3 → L) (i : I) (k : Fin 3) :
    occurrenceEdge tri (i, k) = cycleEdges (n := 0) (tri i) k := by
  fin_cases k <;> rfl

/-- Disjoint ambient interiors in a CCW family give at most one occurrence of each directed edge. -/
theorem occurrenceEdge_injective_of_disjoint_interiors {L I : Type*}
    (site : L → Point) (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hd : ∀ i j, i ≠ j → Disjoint (interior (siteTriangle site (tri i)))
      (interior (siteTriangle site (tri j)))) :
    Function.Injective (occurrenceEdge tri) := by
  intro ⟨i, k⟩ ⟨j, l⟩ he
  have hij : i = j := by
    by_contra h
    obtain ⟨z, hz⟩ := occurrenceEdge_left site tri i (hccw i) k
    exact (hd i j h).le_bot
      (shared_directed_side_overlap
        (occurrence_polygonCertificate site tri i (hccw i))
        (occurrence_polygonCertificate site tri j (hccw j))
        (occurrenceEdge_ne site tri i (hccw i)) (occurrenceEdge_ne site tri j (hccw j))
        (congrArg (realEdge site) he) hz).choose_spec
  subst j
  congr 1
  apply ccw_labels_injective site tri i (hccw i)
  have hf := congrArg Prod.fst he
  change (occurrenceEdge tri (i, k)).1 = (occurrenceEdge tri (i, l)).1 at hf
  simpa only [occurrenceEdge_eq_cycle, cycleEdges] using hf

/-- The integer count of indices carrying a given ordered pair of labels. -/
def directedMultiplicity {I L : Type*} [Fintype I] [DecidableEq L] (edges : I → L × L)
    (e : L × L) : ℤ :=
  ∑ i, if edges i = e then 1 else 0

/-- The coefficient at an ordered pair is its forward count minus its reverse count. -/
theorem chain_coefficient_eq_directed_counts {I L : Type*} [Fintype I] [DecidableEq L]
    (edges : I → L × L) (e : L × L) :
    (∑ i, signedEdge (edges i)) e =
      directedMultiplicity edges e - directedMultiplicity edges e.swap := by
  have hs (v : L × L) : v.swap = e ↔ v = e.swap := by
    constructor <;> intro h <;> simpa using congrArg Prod.swap h
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, signedEdge, Finsupp.sub_apply,
    Finsupp.single_apply, hs, Finset.sum_sub_distrib, directedMultiplicity]

/-- A pair listed by no edge has multiplicity zero. -/
theorem multiplicity_absent {I L : Type*} [Fintype I] [DecidableEq L] (es : I → L × L)
    (e : L × L) (h : ∀ i, es i ≠ e) : directedMultiplicity es e = 0 := by
  simp [directedMultiplicity, h]

private theorem exists_of_multiplicity_eq_one {I L : Type*} [Fintype I] [DecidableEq L]
    (es : I → L × L) (e : L × L) (h : directedMultiplicity es e = 1) :
    ∃ i, es i = e := by
  by_contra he
  push Not at he
  rw [multiplicity_absent es e he] at h
  omega

/-- An injective edge family lists each pair at most once. -/
theorem multiplicity_at_most_one {I L : Type*} [Fintype I] [DecidableEq L]
    (es : I → L × L) (hi : Function.Injective es) (e : L × L) :
    0 ≤ directedMultiplicity es e ∧ directedMultiplicity es e ≤ 1 := by
  rw [directedMultiplicity, Finset.sum_boole]
  constructor
  · positivity
  · have hc : (Finset.univ.filter (fun i => es i = e)).card ≤ 1 := by
      apply Finset.card_le_one_iff.2
      intro a b ha hb
      exact hi ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)
    exact_mod_cast hc

/-- An injective edge family lists each of its own edges exactly once. -/
theorem multiplicity_listed {I L : Type*} [Fintype I] [DecidableEq L]
    (es : I → L × L) (hi : Function.Injective es) (i : I) :
    directedMultiplicity es (es i) = 1 := by
  classical
  simp_rw [directedMultiplicity, show ∀ j, es j = es i ↔ j = i from
    fun j => ⟨fun h => hi h, fun h => congrArg es h⟩]
  simp

private theorem cycle_injective {L : Type*} {n : ℕ} (v : Fin (n + 3) → L)
    (hv : Function.Injective v) : Function.Injective (cycleEdges v) :=
  fun _ _ e => hv (congrArg Prod.fst e)

private theorem cycle_no_reverse {L : Type*} {n : ℕ} (v : Fin (n + 3) → L)
    (hv : Function.Injective v) (k j : Fin (n + 3)) :
    cycleEdges v k ≠ (cycleEdges v j).swap := by
  intro he
  have hk : k = j + 1 := hv (congrArg Prod.fst he)
  have hk' : k + 1 = j := hv (congrArg Prod.snd he)
  have htwo : (1 + 1 : Fin (n + 3)) = 0 := add_left_cancel (calc
    j + (1 + 1) = (j + 1) + 1 := (add_assoc _ _ _).symm
    _ = k + 1 := by rw [hk]
    _ = j + 0 := by simpa using hk')
  have hval := congrArg Fin.val htwo
  have h2 : ((1 + 1 : Fin (n + 3))).val = 2 := by
    rw [Fin.val_add]
    norm_num [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  rw [h2] at hval
  exact (by decide : (2 : ℕ) ≠ 0) hval

/-- Opposite occurrences belong to distinct triangles in a CCW family. -/
theorem opposite_edges_different_triangles {L I : Type*}
    (site : L → Point) (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    {p q : I × Fin 3} (h : occurrenceEdge tri p = (occurrenceEdge tri q).swap) :
    p.1 ≠ q.1 := by
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  intro hij
  change i = j at hij
  subst j
  simp only [occurrenceEdge_eq_cycle] at h
  exact cycle_no_reverse (n := 0) (tri i) (ccw_labels_injective site tri i (hccw i)) k l h

/-- Signed balances plus directed occurrence injectivity give the two incidence counts. -/
theorem edge_counts_of_signed_boundary {I L : Type*} [Fintype I] [DecidableEq L] {n : ℕ}
    (es : I → L × L) (hi : Function.Injective es) (v : Fin (n + 3) → L)
    (hv : Function.Injective v)
    (h : (∑ i, signedEdge (es i)) = ∑ j, signedEdge (cycleEdges v j)) :
    (∀ j, directedMultiplicity es (cycleEdges v j) = 1 ∧
      directedMultiplicity es (cycleEdges v j).swap = 0) ∧
    (∀ e : L × L, (∀ j, cycleEdges v j ≠ e ∧ cycleEdges v j ≠ e.swap) →
      (∃ i, es i = e ∨ es i = e.swap) →
      directedMultiplicity es e = 1 ∧ directedMultiplicity es e.swap = 1) := by
  have bal (e : L × L) := congrArg (fun c : (L × L) →₀ ℤ => c e) h
  simp only [chain_coefficient_eq_directed_counts] at bal
  constructor
  · intro j
    have he := bal (cycleEdges v j)
    rw [multiplicity_listed _ (cycle_injective v hv),
      multiplicity_absent _ _ (fun k => cycle_no_reverse v hv k j)] at he
    have hf := multiplicity_at_most_one es hi (cycleEdges v j)
    have hr := multiplicity_at_most_one es hi (cycleEdges v j).swap
    omega
  · intro e he ⟨i, hi'⟩
    have hb := bal e
    rw [multiplicity_absent _ _ (fun j => (he j).1),
      multiplicity_absent _ _ (fun j => (he j).2)] at hb
    have ho := multiplicity_listed es hi i
    rcases hi' with hi' | hi' <;> rw [hi'] at ho <;> omega

/-- A signed-boundary certificate gives one forward occurrence per hull side and one occurrence
in each direction at every occurring non-hull edge. The latter two occurrences have distinct
triangle indices. The off-edge multiplicity identity uses only the supplied triangle and hull
certificates. -/
theorem rational_edge_counts {L I : Type*} [DecidableEq L] [Fintype I] {n : ℕ}
    (site : L → Point) (hs : Function.Injective site) (v : Fin (n + 3) → L)
    (hv : Function.Injective v) (tri : I → Fin 3 → L)
    (P : PolygonCertificate (siteHull site v) (fun j => realEdge site (cycleEdges v j)))
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i,j))) =
      ∑ j, signedEdge (cycleEdges v j)) :
    Function.Injective (occurrenceEdge tri) ∧
    (∀ j, directedMultiplicity (occurrenceEdge tri) (cycleEdges v j) = 1 ∧
      directedMultiplicity (occurrenceEdge tri) (cycleEdges v j).swap = 0) ∧
    (∀ e : L × L, (∀ j, cycleEdges v j ≠ e ∧ cycleEdges v j ≠ e.swap) →
      (∃ i, occurrenceEdge tri i = e ∨ occurrenceEdge tri i = e.swap) →
      directedMultiplicity (occurrenceEdge tri) e = 1 ∧
      directedMultiplicity (occurrenceEdge tri) e.swap = 1 ∧
      ∃ p q : I × Fin 3, occurrenceEdge tri p = e ∧
        occurrenceEdge tri q = e.swap ∧ p.1 ≠ q.1) := by
  let edges (i : I) (j : Fin 3) := occurrenceEdge tri (i, j)
  have hne (j : Sum (I × Fin 3) (Fin (n + 3))) :
      (listedEdges site edges (cycleEdges v) j).1 ≠ (listedEdges site edges (cycleEdges v) j).2 := by
    rcases j with ⟨i, k⟩ | j
    · exact occurrenceEdge_ne site tri i (hccw i) k
    · intro he
      have hlabels : v j = v (j + 1) := hs (castPoint_injective he)
      exact cycle_no_reverse v hv j j (by simp [cycleEdges, hlabels])
  have hc := off_edge_count_from_signed_boundary site edges (cycleEdges v)
    (fun i => siteTriangle site (tri i)) (siteHull site v)
    (fun i => occurrence_polygonCertificate site tri i (hccw i)) P hne hchain
  have hd (i j : I) (h : i ≠ j) :
      Disjoint (interior (siteTriangle site (tri i))) (interior (siteTriangle site (tri j))) := by
    apply disjoint_interiors_of_off_edge_bound (listedEdges site edges (cycleEdges v)) _ _ h
    intro x hx
    rw [hc x hx]
    unfold interiorIndicator
    split <;> omega
  have hu := occurrenceEdge_injective_of_disjoint_interiors site tri hccw hd
  have hflat : (∑ p : I × Fin 3, signedEdge (occurrenceEdge tri p)) =
      ∑ j, signedEdge (cycleEdges v j) := by
    rw [Fintype.sum_prod_type]
    exact hchain
  obtain ⟨hHull, hInterior⟩ := edge_counts_of_signed_boundary _ hu v hv hflat
  refine ⟨hu, hHull, fun e he hOcc => ?_⟩
  obtain ⟨hForward, hReverse⟩ := hInterior e he hOcc
  obtain ⟨p, hp⟩ := exists_of_multiplicity_eq_one _ _ hForward
  obtain ⟨q, hq⟩ := exists_of_multiplicity_eq_one _ _ hReverse
  have hOpp : occurrenceEdge tri p = (occurrenceEdge tri q).swap := by
    rw [hp, hq, Prod.swap_swap]
  exact ⟨hForward, hReverse, p, q, hp, hq,
    opposite_edges_different_triangles site tri hccw hOpp⟩

private theorem supports_have_only_ends {L : Type*} (site : L → Point)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    {a b c : L} (hab : a ≠ b)
    (hz : edgeSide (realEdge site (a, b)) (castPoint (site c)) = 0) :
    c = a ∨ c = b := by
  by_contra hn
  push Not at hn
  have hh := hgen a b c hab hn.1.symm hn.2.symm
  apply hh
  change edgeSide (castPoint (site a), castPoint (site b)) (castPoint (site c)) = 0 at hz
  rw [side_of_rational_sites] at hz
  exact_mod_cast hz

/-- Suppose every site lies in the certified hull and no three sites with distinct labels are
collinear. A point in the open segment of two sites with distinct labels lies on the hull
frontier exactly when the pair is a certified hull side, in either orientation. -/
theorem open_site_edge_mem_frontier_iff {L : Type*} {n : ℕ}
    (site : L → Point) (v : Fin (n + 3) → L) (hv : Function.Injective v)
    (P : PolygonCertificate (siteHull site v) (fun j => realEdge site (cycleEdges v j)))
    (hsite : ∀ a, castPoint (site a) ∈ siteHull site v)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    {a b : L} (hab : a ≠ b) {x : Plane}
    (hx : x ∈ openSegment ℝ (castPoint (site a)) (castPoint (site b))) :
    x ∈ frontier (siteHull site v) ↔
      ∃ j, cycleEdges v j = (a, b) ∨ cycleEdges v j = (b, a) := by
  constructor
  · intro hf
    rw [P.frontier_eq] at hf
    obtain ⟨j, hj⟩ := mem_iUnion.1 hf
    let e := realEdge site (cycleEdges v j)
    have hz : edgeSide e x = 0 := edgeSide_eq_zero_on_segment e hj
    have ha := P.left j _ (hsite a)
    have hb := P.left j _ (hsite b)
    obtain ⟨r, s, hr, hs, hrs, rfl⟩ := hx
    rw [edgeSide_combination _ _ _ _ _ hrs] at hz
    have ha0 : edgeSide e (castPoint (site a)) = 0 := by
      symm
      apply (eq_or_lt_of_le ha).resolve_right
      intro hp
      exact (add_pos_of_pos_of_nonneg (mul_pos hr hp) (mul_nonneg hs.le hb)).ne' hz
    have hb0 : edgeSide e (castPoint (site b)) = 0 := by
      symm
      apply (eq_or_lt_of_le hb).resolve_right
      intro hp
      exact (add_pos_of_nonneg_of_pos (mul_nonneg hr.le ha) (mul_pos hs hp)).ne' hz
    have hvne : v j ≠ v (j + 1) := by
      intro he
      exact cycle_no_reverse v hv j j (by simp [cycleEdges, he])
    have ⟨ha', hb'⟩ :=
      And.intro (supports_have_only_ends site hgen hvne ha0)
        (supports_have_only_ends site hgen hvne hb0)
    refine ⟨j, ?_⟩
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact (hab (ha'.trans hb'.symm)).elim
    · exact Or.inl (by simp [cycleEdges, ha', hb'])
    · exact Or.inr (by simp [cycleEdges, ha', hb'])
    · exact (hab (ha'.trans hb'.symm)).elim
  · rintro ⟨j, hj | hj⟩
    · apply P.frontier_eq.symm ▸ mem_iUnion.2 ⟨j, ?_⟩
      simpa [hj, realEdge] using openSegment_subset_segment ℝ _ _ hx
    · apply P.frontier_eq.symm ▸ mem_iUnion.2 ⟨j, ?_⟩
      simpa [hj, realEdge, segment_symm ℝ (castPoint (site b)) (castPoint (site a))] using
        openSegment_subset_segment ℝ _ _ hx

/-- In either orientation the whole closed segment of a listed hull side is on the frontier. -/
theorem closed_site_edge_subset_frontier_of_hull_pair {L : Type*} {n : ℕ}
    (site : L → Point) (v : Fin (n + 3) → L)
    (P : PolygonCertificate (siteHull site v) (fun j => realEdge site (cycleEdges v j)))
    {a b : L} (h : ∃ j, cycleEdges v j = (a, b) ∨ cycleEdges v j = (b, a)) :
    segment ℝ (castPoint (site a)) (castPoint (site b)) ⊆ frontier (siteHull site v) := by
  intro x hx
  rw [P.frontier_eq]
  rcases h with ⟨j, hj | hj⟩
  · exact mem_iUnion.2 ⟨j, by simpa [hj, realEdge] using hx⟩
  · exact mem_iUnion.2 ⟨j, by
      simpa [hj, realEdge, segment_symm ℝ (castPoint (site b)) (castPoint (site a))] using hx⟩

/-- Suppose every site lies in the certified hull and no three sites with distinct labels are
collinear. The open segment of a pair of distinct labels is in the hull interior when the pair
is unlisted in both orientations. -/
theorem nonhull_open_site_edge_subset_interior {L : Type*} {n : ℕ}
    (site : L → Point) (v : Fin (n + 3) → L) (hv : Function.Injective v)
    (P : PolygonCertificate (siteHull site v) (fun j => realEdge site (cycleEdges v j)))
    (hsite : ∀ a, castPoint (site a) ∈ siteHull site v)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    {a b : L} (hab : a ≠ b) (h : ∀ j, cycleEdges v j ≠ (a, b) ∧ cycleEdges v j ≠ (b, a)) :
    openSegment ℝ (castPoint (site a)) (castPoint (site b)) ⊆ interior (siteHull site v) := by
  intro x hx
  have hm := P.convex.segment_subset (hsite a) (hsite b) (openSegment_subset_segment ℝ _ _ hx)
  by_contra hn
  have hf : x ∈ frontier (siteHull site v) := by
    simpa [frontier, P.compact.isClosed.closure_eq] using And.intro hm hn
  obtain ⟨j, hj | hj⟩ := (open_site_edge_mem_frontier_iff site v hv P hsite hgen hab hx).mp hf
  · exact (h j).1 hj
  · exact (h j).2 hj

end TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
