import TDA.Filtration.RationalAlpha.SignedBoundaryCoverage
import Mathlib.Analysis.LocallyConvex.Separation

set_option autoImplicit false

/-!
# Pairwise incidence of certified rational planar triangles

Positive orientation gives full-dimensional triangle carriers. The signed-boundary
certificate bounds ambient-interior multiplicity away from the listed segments.
Density then gives disjoint interiors for distinct occurrences.

A separating line reduces each closed carrier to the convex hull of the vertices
on that line. The site noncollinearity hypothesis makes the union of those contact
vertices affinely independent. The intersection is therefore the convex hull of
the shared labelled vertices.

The family is indexed by occurrences. The multiplicity bound rules out equal
carriers at different indices, including repeated occurrences of a triangle.
All-site usage is expressed separately by `SignedBoundary.allSitesUsed`.
-/

namespace TDA.Filtration.RationalAlpha.TriangleIncidence

open Set
open scoped Matrix Classical
open TDA.Filtration.RationalAlpha (Plane Point castPoint orient orient_swaps)
open TDA.Filtration.RationalAlpha.SignedBoundary

/-- A finite family with off-edge multiplicity at most one has disjoint interiors at distinct indices. -/
theorem disjoint_interiors_of_off_edge_bound {I E : Type*} [Fintype I] [Finite E]
    (edges : E → Plane × Plane) (T : I → Set Plane)
    (hcount : ∀ x ∈ offEdges edges, interiorMultiplicity T x ≤ 1)
    {i j : I} (hij : i ≠ j) : Disjoint (interior (T i)) (interior (T j)) := by
  classical
  rw [Set.disjoint_left]
  intro x hxi hxj
  obtain ⟨z, hz⟩ := (dense_off_edges edges).inter_open_nonempty
    (interior (T i) ∩ interior (T j)) (isOpen_interior.inter isOpen_interior) ⟨x, hxi, hxj⟩
  have hpair : (∑ k ∈ ({i,j} : Finset I), interiorIndicator (T k) z) = 2 := by
    have hn : i ∉ ({j} : Finset I) := by simpa using hij
    rw [Finset.sum_insert hn, Finset.sum_singleton]
    simp [interiorIndicator, hz.1.1, hz.1.2]
  have low : (∑ k ∈ ({i,j} : Finset I), interiorIndicator (T k) z) ≤
      ∑ k, interiorIndicator (T k) z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro k _ _
      unfold interiorIndicator
      split <;> omega)
  have high := hcount z hz.2
  unfold interiorMultiplicity at high
  omega

/-- Distinct certified pieces have disjoint interiors when their signed boundary sum
equals that of the certified hull. The listed segments are nondegenerate. -/
theorem disjoint_interiors_of_signed_boundary {L I E F : Type*}
    [Fintype I] [Fintype E] [Fintype F]
    (site : L → Point) (tri : I → E → L × L) (hull : F → L × L)
    (T : I → Set Plane) (H : Set Plane)
    (pT : ∀ i, PolygonCertificate (T i) (fun e => realEdge site (tri i e)))
    (pH : PolygonCertificate H (fun e => realEdge site (hull e)))
    (hne : ∀ j, (listedEdges site tri hull j).1 ≠ (listedEdges site tri hull j).2)
    (hchain : (∑ i, ∑ e, signedEdge (tri i e)) = ∑ e, signedEdge (hull e))
    {i j : I} (hij : i ≠ j) : Disjoint (interior (T i)) (interior (T j)) := by
  apply disjoint_interiors_of_off_edge_bound (listedEdges site tri hull) T _ hij
  intro x hx
  rw [off_edge_count_from_signed_boundary site tri hull T H pT pH hne hchain x hx]
  unfold interiorIndicator
  split <;> omega

private theorem weak_separation_of_disjoint_interiors {A B : Set Plane}
    (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hneA : (interior A).Nonempty) (hneB : (interior B).Nonempty)
    (hdisj : Disjoint (interior A) (interior B)) :
    ∃ (f : Plane →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
      (∀ x ∈ A, f x ≤ c) ∧ ∀ y ∈ B, c ≤ f y := by
  obtain ⟨f,c,hlo,hhi⟩ := geometric_hahn_banach_open_open hA.interior isOpen_interior
    hB.interior isOpen_interior hdisj
  have hne : f ≠ 0 := by
    intro hf
    obtain ⟨x,hx⟩ := hneA
    obtain ⟨y,hy⟩ := hneB
    have h₀ : 0 < c := by simpa [hf] using hlo x hx
    have h₁ : c < 0 := by simpa [hf] using hhi y hy
    linarith
  refine ⟨f,c,hne,?_,?_⟩
  · intro x hx
    have h := closure_minimal (fun z hz => (hlo z hz).le :
        interior A ⊆ f ⁻¹' Iic c) (isClosed_Iic.preimage f.continuous)
    exact h (by simpa [hA.closure_interior_eq_closure_of_nonempty_interior hneA] using
      (subset_closure hx : x ∈ closure A))
  · intro x hx
    have h := closure_minimal (fun z hz => (hhi z hz).le :
        interior B ⊆ f ⁻¹' Ici c) (isClosed_Ici.preimage f.continuous)
    exact h (by simpa [hB.closure_interior_eq_closure_of_nonempty_interior hneB] using
      (subset_closure hx : x ∈ closure B))

private noncomputable def contact (V : Finset Plane) (f : Plane →L[ℝ] ℝ) (c : ℝ) : Finset Plane := by
  classical exact V.filter (fun p => f p = c)

private theorem mem_contact {V : Finset Plane} {f : Plane →L[ℝ] ℝ} {c : ℝ} {x : Plane} :
    x ∈ contact V f c ↔ x ∈ V ∧ f x = c := by
  classical simp [contact]

private theorem convexHull_contact_le (V : Finset Plane) (f : Plane →L[ℝ] ℝ) (c : ℝ)
    (h : ∀ p ∈ V, f p ≤ c) :
    convexHull ℝ (V : Set Plane) ∩ (f ⁻¹' {c}) = convexHull ℝ (contact V f c : Set Plane) := by
  classical
  refine subset_antisymm ?_ (subset_inter
    (convexHull_mono (fun p hp => (mem_contact.1 hp).1))
    (convexHull_min (fun p hp => (mem_contact.1 hp).2)
      ((convex_singleton c).linear_preimage f.toLinearMap)))
  rintro x ⟨hx,hc⟩
  have he : f x = c := hc
  obtain ⟨w,hw,hs,hx⟩ := (Finset.mem_convexHull' (R := ℝ)).1 hx
  have hval : (∑ p ∈ V, w p * f p) = c := by
    rw [← he, ← hx, map_sum]
    simp [smul_eq_mul]
  have hzero : (∑ p ∈ V, w p * (c - f p)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, hval, one_mul, sub_self]
  have hwzero (p : Plane) (hp : p ∈ V) (hp' : p ∉ contact V f c) : w p = 0 := by
    have hprod := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q hq => mul_nonneg (hw q hq) (sub_nonneg.mpr (h q hq)))).1 hzero p hp
    exact (mul_eq_zero.mp hprod).resolve_right (fun hh => hp' (mem_contact.2 ⟨hp, by linarith⟩))
  have hsub : contact V f c ⊆ V := fun _ hp => (mem_contact.1 hp).1
  apply (Finset.mem_convexHull' (R := ℝ)).2
  refine ⟨w, fun p hp => hw p (hsub hp), ?_, ?_⟩
  · rw [Finset.sum_subset hsub hwzero, hs]
  · rw [Finset.sum_subset hsub (fun p hp hp' => by rw [hwzero p hp hp', zero_smul]), hx]

private theorem convexHull_contact_ge (V : Finset Plane) (f : Plane →L[ℝ] ℝ) (c : ℝ)
    (h : ∀ p ∈ V, c ≤ f p) :
    convexHull ℝ (V : Set Plane) ∩ (f ⁻¹' {c}) = convexHull ℝ (contact V f c : Set Plane) := by
  classical
  have hlevel : ((-f) ⁻¹' {-c} : Set Plane) = f ⁻¹' {c} := by
    ext x
    simp
  have hcontact : contact V (-f) (-c) = contact V f c := by
    ext x
    simp [mem_contact]
  have hh := convexHull_contact_le V (-f) (-c) (fun p hp => by simpa using neg_le_neg (h p hp))
  rwa [hlevel,hcontact] at hh

private theorem full_of_nonzero_orient (a b c : Point) (h : orient a b c ≠ 0) :
    (interior (convexHull ℝ ({castPoint a,castPoint b,castPoint c} : Set Plane))).Nonempty := by
  rcases lt_or_gt_of_ne h with hn | hp
  · have hp : 0 < orient b a c := by rw [(orient_swaps a b c).1]; linarith
    simpa only [Set.insert_comm (castPoint b) (castPoint a)] using
      (rational_triangle_polygonCertificate b a c hp).full
  · exact (rational_triangle_polygonCertificate a b c hp).full

private theorem no_three_on_level {L : Type*} (site : L → Point)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    (f : Plane →L[ℝ] ℝ) (hf : f ≠ 0) (s : ℝ)
    {a b c : L} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : f (castPoint (site a)) = s) (hb : f (castPoint (site b)) = s)
    (hc : f (castPoint (site c)) = s) : False := by
  have hsubset : convexHull ℝ ({castPoint (site a),castPoint (site b),castPoint (site c)} : Set Plane)
      ⊆ f ⁻¹' {s} := by
    apply convexHull_min _ ((convex_singleton s).linear_preimage f.toLinearMap)
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hopen : IsOpenMap f := f.isOpenMap_of_ne_zero hf
  have hempty : interior (f ⁻¹' ({s} : Set ℝ)) = ∅ := by
    rw [← hopen.preimage_interior_eq_interior_preimage f.continuous, interior_singleton, preimage_empty]
  obtain ⟨x,hx⟩ := full_of_nonzero_orient (site a) (site b) (site c) (hgen a b c hab hac hbc)
  have hx' := interior_mono hsubset hx
  rw [hempty] at hx'
  exact hx'

private theorem affineIndepOn_of_at_most_two (S : Set Plane)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → False) :
    AffineIndepOn ℝ id S := by
  classical
  by_cases hpair : ∃ a ∈ S, ∃ b ∈ S, a ≠ b
  · obtain ⟨a,ha,b,hb,hab⟩ := hpair
    apply (affineIndepOn_of_ne ℝ hab).mono
    intro c hc
    by_cases hac : a = c
    · exact Or.inl hac.symm
    · exact Or.inr (mem_singleton_iff.2 ((not_ne_iff.mp (h a ha b hb c hc hab hac)).symm))
  · have : Subsingleton S := ⟨fun a b => Subtype.ext (by
      by_contra hn
      exact hpair ⟨a,a.2,b,b.2,hn⟩)⟩
    exact affineIndependent_of_subsingleton ℝ _

private theorem contact_union_independent {L : Type*} (site : L → Point)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    (V W : Finset Plane)
    (hV : (V : Set Plane) ⊆ range (castPoint ∘ site))
    (hW : (W : Set Plane) ⊆ range (castPoint ∘ site))
    (f : Plane →L[ℝ] ℝ) (hf : f ≠ 0) (r : ℝ) :
    AffineIndependent ℝ (Subtype.val : (↑(contact V f r ∪ contact W f r) : Set Plane) → Plane) := by
  classical
  have hmem {p : Plane} (h : p ∈ contact V f r ∪ contact W f r) :
      p ∈ range (castPoint ∘ site) ∧ f p = r := by
    rcases Finset.mem_union.1 h with h' | h'
    · exact ⟨hV (mem_contact.1 h').1,(mem_contact.1 h').2⟩
    · exact ⟨hW (mem_contact.1 h').1,(mem_contact.1 h').2⟩
  apply affineIndepOn_of_at_most_two
  intro a ha b hb c hc hab hac hbc
  obtain ⟨⟨ia,rfl⟩,ha'⟩ := hmem ha
  obtain ⟨⟨ib,rfl⟩,hb'⟩ := hmem hb
  obtain ⟨⟨ic,rfl⟩,hc'⟩ := hmem hc
  exact no_three_on_level site hgen f hf r
    (fun e => hab (congrArg (castPoint ∘ site) e))
    (fun e => hac (congrArg (castPoint ∘ site) e))
    (fun e => hbc (congrArg (castPoint ∘ site) e)) ha' hb' hc'

private theorem face_to_face_of_disjoint_interiors {L : Type*} (site : L → Point)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    (V W : Finset Plane)
    (hV : (V : Set Plane) ⊆ range (castPoint ∘ site))
    (hW : (W : Set Plane) ⊆ range (castPoint ∘ site))
    (hv : (interior (convexHull ℝ (V : Set Plane))).Nonempty)
    (hw : (interior (convexHull ℝ (W : Set Plane))).Nonempty)
    (hd : Disjoint (interior (convexHull ℝ (V : Set Plane))) (interior (convexHull ℝ (W : Set Plane)))) :
    convexHull ℝ (V : Set Plane) ∩ convexHull ℝ (W : Set Plane) =
      convexHull ℝ (↑(V ∩ W) : Set Plane) := by
  classical
  obtain ⟨f,r,hf,hA,hB⟩ := weak_separation_of_disjoint_interiors
    (convex_convexHull ℝ _) (convex_convexHull ℝ _) hv hw hd
  have hV' : convexHull ℝ (V : Set Plane) ∩ (f ⁻¹' {r}) =
      convexHull ℝ (contact V f r : Set Plane) :=
    convexHull_contact_le V f r (fun p hp => hA p (subset_convexHull ℝ _ hp))
  have hW' : convexHull ℝ (W : Set Plane) ∩ (f ⁻¹' {r}) =
      convexHull ℝ (contact W f r : Set Plane) :=
    convexHull_contact_ge W f r (fun p hp => hB p (subset_convexHull ℝ _ hp))
  have hi := (contact_union_independent site hgen V W hV hW f hf r).convexHull_inter'
  refine subset_antisymm ?_ ?_
  · rintro p ⟨hp,hq⟩
    have hp' : p ∈ f ⁻¹' ({r} : Set ℝ) := le_antisymm (hA p hp) (hB p hq)
    have hcontact : p ∈ convexHull ℝ (↑(contact V f r ∩ contact W f r) : Set Plane) := by
      rw [Finset.coe_inter, hi]
      exact ⟨hV' ▸ ⟨hp,hp'⟩,hW' ▸ ⟨hq,hp'⟩⟩
    exact convexHull_mono (fun x hx => Finset.mem_inter.2
      ⟨(mem_contact.1 (Finset.mem_inter.1 hx).1).1,(mem_contact.1 (Finset.mem_inter.1 hx).2).1⟩) hcontact
  · exact subset_inter (convexHull_mono fun p hp => (Finset.mem_inter.1 hp).1)
      (convexHull_mono fun p hp => (Finset.mem_inter.1 hp).2)


/-- The set of labels at the three vertex positions of a supplied triangle. -/
def labelVertices {L : Type*} [DecidableEq L] (v : Fin 3 → L) : Finset L :=
  Finset.univ.image v

/-- A label belongs to a triangle's vertex set exactly when it occurs at a vertex position. -/
@[simp] theorem mem_labelVertices {L : Type*} [DecidableEq L] {v : Fin 3 → L} {label : L} :
    label ∈ labelVertices v ↔ ∃ i, v i = label := by
  simp [labelVertices]

private noncomputable def pointVertices {L : Type*} [DecidableEq L]
    (site : L → Point) (v : Fin 3 → L) : Finset Plane :=
  (labelVertices v).image (castPoint ∘ site)

private theorem siteTriangle_eq_hull_points {L : Type*} [DecidableEq L] (site : L → Point)
    (v : Fin 3 → L) : siteTriangle site v = convexHull ℝ (pointVertices site v : Set Plane) := by
  unfold siteTriangle
  apply congrArg (convexHull ℝ)
  ext x
  simp only [pointVertices, labelVertices, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
    true_and, mem_insert_iff, mem_singleton_iff, Function.comp_apply]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨v 0,⟨0,rfl⟩,rfl⟩
    · exact ⟨v 1,⟨1,rfl⟩,rfl⟩
    · exact ⟨v 2,⟨2,rfl⟩,rfl⟩
  · rintro ⟨l,⟨i,rfl⟩,rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- The closed carriers of distinct CCW occurrences intersect in the convex hull of their shared
cast labels when no three sites with distinct labels are collinear and off-edge
ambient-interior multiplicity is at most one. -/
theorem triangle_inter_eq_shared_labels {L I E : Type*} [DecidableEq L] [Fintype I] [Finite E]
    (site : L → Point) (hsite : Function.Injective site)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    (edges : E → Plane × Plane) (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hcount : ∀ x ∈ offEdges edges, interiorMultiplicity (fun i => siteTriangle site (tri i)) x ≤ 1)
    {i j : I} (hij : i ≠ j) :
    siteTriangle site (tri i) ∩ siteTriangle site (tri j) =
      convexHull ℝ (↑((labelVertices (tri i) ∩ labelVertices (tri j)).image (castPoint ∘ site)) :
        Set Plane) := by
  classical
  have hp (k : I) : (pointVertices site (tri k) : Set Plane) ⊆ range (castPoint ∘ site) := by
    intro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.1 hx
    exact ⟨v,rfl⟩
  have hn (k : I) : (interior (convexHull ℝ (pointVertices site (tri k) : Set Plane))).Nonempty := by
    rw [← siteTriangle_eq_hull_points]
    exact (rational_triangle_polygonCertificate _ _ _ (hccw k)).full
  have hh := disjoint_interiors_of_off_edge_bound edges (fun i => siteTriangle site (tri i)) hcount hij
  rw [siteTriangle_eq_hull_points site (tri i), siteTriangle_eq_hull_points site (tri j)] at hh ⊢
  rw [Finset.image_inter _ _ (TDA.Filtration.RationalAlpha.castPoint_injective.comp hsite)]
  exact face_to_face_of_disjoint_interiors site hgen _ _ (hp i) (hp j) (hn i) (hn j) hh

/-- Distinct CCW occurrences under the off-edge bound have distinct closed carriers. -/
theorem siteTriangle_injective_of_off_edge_bound {L I E : Type*} [Fintype I] [Finite E]
    (site : L → Point) (edges : E → Plane × Plane) (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hcount : ∀ x ∈ offEdges edges, interiorMultiplicity (fun i => siteTriangle site (tri i)) x ≤ 1) :
    Function.Injective (fun i => siteTriangle site (tri i)) := by
  classical
  intro i j he
  by_contra hij
  have hd := disjoint_interiors_of_off_edge_bound edges (fun k => siteTriangle site (tri k)) hcount hij
  obtain ⟨x, hx⟩ := (rational_triangle_polygonCertificate _ _ _ (hccw i)).full
  change x ∈ interior (siteTriangle site (tri i)) at hx
  exact Set.disjoint_left.1 hd hx (by simpa only [he] using hx)

/-- Under the off-edge bound, and when no three sites with distinct labels are collinear, two CCW
occurrences without a common label have disjoint carriers. -/
theorem triangle_inter_eq_empty_of_disjoint_labels {L I E : Type*}
    [DecidableEq L] [Fintype I] [Finite E]
    (site : L → Point) (hsite : Function.Injective site)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    (edges : E → Plane × Plane) (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hcount : ∀ x ∈ offEdges edges, interiorMultiplicity (fun i => siteTriangle site (tri i)) x ≤ 1)
    {i j : I} (hij : i ≠ j) (hlabels : Disjoint (labelVertices (tri i)) (labelVertices (tri j))) :
    siteTriangle site (tri i) ∩ siteTriangle site (tri j) = ∅ := by
  rw [triangle_inter_eq_shared_labels site hsite hgen edges tri hccw hcount hij,
    Finset.disjoint_iff_inter_eq_empty.mp hlabels]
  simp

/-- For a certified hull containing every site and its signed-boundary triangle family, when no
three sites with distinct labels are collinear, each distinct pair of closed triangle carriers
meets in exactly the convex hull of the shared cast labels. -/
theorem triangle_inter_eq_shared_labels_of_signed_boundary {L I : Type*}
    [DecidableEq L] [Fintype I] {n : ℕ}
    (site : L → Point) (hs : Function.Injective site) (hull : Fin (n + 3) → L)
    (hv : Function.Injective hull) (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hsite : ∀ v, castPoint (site v) ∈ siteHull site hull)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c →
      orient (site a) (site b) (site c) ≠ 0)
    (hchain : (∑ i, ∑ e, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) e)) =
        ∑ e, signedEdge (cycleEdges hull e)) {i j : I} (hij : i ≠ j) :
    siteTriangle site (tri i) ∩ siteTriangle site (tri j) =
      convexHull ℝ (↑((labelVertices (tri i) ∩ labelVertices (tri j)).image (castPoint ∘ site)) :
        Set Plane) := by
  have hcover := (rational_cover_from_signed_boundary site hs hull hv tri hh hsite hccw hchain).1
  refine triangle_inter_eq_shared_labels site hs hgen
    (listedEdges site (fun k => triangleEdges (tri k 0) (tri k 1) (tri k 2)) (cycleEdges hull))
    tri hccw ?_ hij
  intro x hx
  rw [hcover x hx]
  unfold interiorIndicator
  split <;> omega

end TDA.Filtration.RationalAlpha.TriangleIncidence
