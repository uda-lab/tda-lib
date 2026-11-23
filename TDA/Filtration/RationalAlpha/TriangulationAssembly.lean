import TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

set_option autoImplicit false

/-!
# Assembly of certified rational planar triangles

The labelled faces are the nonempty subfaces of the supplied triangles. Their images form
a geometric simplicial complex. Positive orientation gives affine independence in each
triangle, and the parent intersection identity then yields intersection on all subfaces.

The signed boundary certificate gives the parent intersections and the closed hull carrier.
Full vertex support is equivalent to the separate `SignedBoundary.allSitesUsed` check.
-/

open Set
open scoped Classical Matrix
open TDA.Filtration.RationalAlpha (Plane Point castPoint castPoint_injective orient orient_zero_iff_collinear)
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence

namespace TDA.Filtration.RationalAlpha.TriangulationAssembly

/-- The labelled faces are precisely the nonempty subfaces of supplied triangles. -/
def labelComplex {L I : Type*} [DecidableEq L] (tri : I → Fin 3 → L) :
    PreAbstractSimplicialComplex L where
  faces := {s | s.Nonempty ∧ ∃ i, s ⊆ labelVertices (tri i)}
  isRelLowerSet_faces := fun {_} ⟨hn, i, h⟩ => ⟨hn, fun _ hst ht => ⟨ht, i, hst.trans h⟩⟩

/-- Enumerate the nonempty subfaces of the finite family by their label sets. -/
def faceFinset {L I : Type*} [DecidableEq L] [Fintype I] (tri : I → Fin 3 → L) :
    Finset (Finset L) :=
  Finset.univ.biUnion fun i => (labelVertices (tri i)).powerset.erase ∅

/-- The labelled face set agrees with its finite enumeration. -/
theorem faces_eq_finset {L I : Type*} [DecidableEq L] [Fintype I] (tri : I → Fin 3 → L) :
    (labelComplex tri).faces = (faceFinset tri : Set (Finset L)) := by
  ext s
  simp only [labelComplex, Set.mem_ofPred_eq, faceFinset, Finset.mem_coe, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_erase, Finset.mem_powerset, Finset.nonempty_iff_ne_empty]
  exact ⟨fun ⟨hn, i, hi⟩ => ⟨i, hn, hi⟩, fun ⟨i, hn, hi⟩ => ⟨hn, i, hi⟩⟩

/-- A label is a vertex exactly when it is used by a supplied triangle. -/
theorem singleton_mem_iff_used {L I : Type*} [DecidableEq L] (tri : I → Fin 3 → L) (a : L) :
    {a} ∈ (labelComplex tri).faces ↔ ∃ i j, tri i j = a := by
  simp [labelComplex, Finset.singleton_subset_iff, mem_labelVertices]

/-- The labelled complex has every singleton exactly when every site is used. -/
theorem full_label_support_iff {L I : Type*} [DecidableEq L] (tri : I → Fin 3 → L) :
    (∀ a : L, {a} ∈ (labelComplex tri).faces) ↔ allSitesUsed tri := by
  simp only [singleton_mem_iff_used, allSitesUsed]

/-- Embed a rational site in the real Euclidean plane. -/
def embedSite {L : Type*} (site : L → Point) (a : L) : Plane := castPoint (site a)

/-- Embed a finite set of labels in the real Euclidean plane. -/
noncomputable def pointVertices {L : Type*} [DecidableEq L] (site : L → Point)
    (s : Finset L) : Finset Plane := s.image (embedSite site)

private theorem triangle_affineIndependent {L : Type*} (site : L → Point) (v : Fin 3 → L)
    (h : 0 < orient (site (v 0)) (site (v 1)) (site (v 2))) :
    AffineIndependent ℝ (embedSite site ∘ v) := by
  have ha : AffineIndependent ℝ ![castPoint (site (v 0)), castPoint (site (v 1)),
      castPoint (site (v 2))] := by
    rw [affineIndependent_iff_not_collinear_set, ← orient_zero_iff_collinear]
    exact h.ne'
  convert ha using 1
  ext i
  fin_cases i <;> rfl

private theorem triangle_pointVertices_range {L : Type*} [DecidableEq L] (site : L → Point)
    (v : Fin 3 → L) : (pointVertices site (labelVertices v) : Set Plane) =
      range (embedSite site ∘ v) := by
  ext x
  simp only [pointVertices, Finset.mem_coe, Finset.mem_image, mem_labelVertices, mem_range,
    Function.comp_apply]
  constructor
  · rintro ⟨a,⟨j, rfl⟩,rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨v j,⟨j, rfl⟩,rfl⟩

private theorem triangle_eq_convexHull {L : Type*} [DecidableEq L] (site : L → Point)
    (v : Fin 3 → L) : siteTriangle site v =
      convexHull ℝ (pointVertices site (labelVertices v) : Set Plane) := by
  rw [triangle_pointVertices_range]
  unfold siteTriangle
  congr 1
  ext x
  simp only [mem_range, Function.comp_apply, embedSite, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp

private theorem triangle_points_independent {L : Type*} [DecidableEq L] (site : L → Point)
    (v : Fin 3 → L) (h : 0 < orient (site (v 0)) (site (v 1)) (site (v 2))) :
    AffineIndependent ℝ ((↑) : pointVertices site (labelVertices v) → Plane) := by
  have ha := (triangle_affineIndependent site v h).range
  rw [← triangle_pointVertices_range site v] at ha
  exact ha

private theorem labelVertices_card {L : Type*} [DecidableEq L] (site : L → Point)
    (v : Fin 3 → L) (h : 0 < orient (site (v 0)) (site (v 1)) (site (v 2))) :
    (labelVertices v).card = 3 := by
  have hv : Function.Injective v :=
    fun _ _ he => (triangle_affineIndependent site v h).injective (congrArg (embedSite site) he)
  change (Finset.univ.image v).card = 3
  rw [Finset.card_image_of_injective _ hv]
  simp

/-- The faces maximal under inclusion in a pre-abstract simplicial complex. -/
def maximalFaces {α : Type*} (K : PreAbstractSimplicialComplex α) : Set (Finset α) :=
  {s | s ∈ K.faces ∧ ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t}

/-- The maximal labelled faces of a CCW family are its supplied triangles. -/
theorem maximal_label_faces {L I : Type*} [DecidableEq L] (site : L → Point)
    (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2))) :
    maximalFaces (labelComplex tri) = range (fun i => labelVertices (tri i)) := by
  have hc (i : I) : (labelVertices (tri i)).card = 3 :=
    labelVertices_card site (tri i) (hccw i)
  have hface (i : I) : labelVertices (tri i) ∈ (labelComplex tri).faces :=
    ⟨Finset.card_pos.mp (by simp [hc]), i, Finset.Subset.rfl⟩
  ext s
  constructor
  · rintro ⟨⟨_, i, hsi⟩, hm⟩
    exact ⟨i, (hm (hface i) hsi).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨hface i, ?_⟩
    rintro t ⟨_, j, ht⟩ hit
    apply Finset.eq_of_subset_of_card_le hit
    exact (Finset.card_le_card ht).trans (by rw [hc, hc])

/-- Each maximal labelled face has three vertices. -/
theorem maximal_label_faces_card_three {L I : Type*} [DecidableEq L] (site : L → Point)
    (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    {s : Finset L} (hs : s ∈ maximalFaces (labelComplex tri)) : s.card = 3 := by
  rw [maximal_label_faces site tri hccw] at hs
  obtain ⟨i, rfl⟩ := hs
  exact labelVertices_card site _ (hccw i)

private theorem lower_overlap {s t S T : Finset Plane}
    (hs : s ⊆ S) (ht : t ⊆ T)
    (hS : AffineIndependent ℝ ((↑) : S → Plane))
    (hT : AffineIndependent ℝ ((↑) : T → Plane))
    (hParent : convexHull ℝ (S : Set Plane) ∩ convexHull ℝ (T : Set Plane) =
      convexHull ℝ (S ∩ T : Set Plane)) :
    convexHull ℝ (s : Set Plane) ∩ convexHull ℝ (t : Set Plane) ⊆
      convexHull ℝ (s ∩ t : Set Plane) := by
  intro x hx
  have hp : x ∈ convexHull ℝ (S ∩ T : Set Plane) := hParent ▸
    ⟨convexHull_mono (Finset.coe_subset.mpr hs) hx.1,
      convexHull_mono (Finset.coe_subset.mpr ht) hx.2⟩
  have haux : x ∈ convexHull ℝ (s ∩ (S ∩ T) : Set Plane) := by
    have he := hS.convexHull_inter hs (Finset.inter_subset_left : S ∩ T ⊆ S)
    simp only [Finset.coe_inter] at he
    exact he.symm ▸ ⟨hx.1, hp⟩
  have hsub : s ∩ (S ∩ T) ⊆ T := Finset.inter_subset_right.trans Finset.inter_subset_right
  have hlast : x ∈ convexHull ℝ ((s ∩ (S ∩ T)) ∩ t : Set Plane) := by
    have he := hT.convexHull_inter hsub ht
    simp only [Finset.coe_inter] at he
    exact he.symm ▸ ⟨haux, hx.2⟩
  have hm : ((s : Set Plane) ∩ (S ∩ T : Set Plane)) ∩ (t : Set Plane) ⊆ (s ∩ t : Set Plane) :=
    fun _ hz => ⟨hz.1.1, hz.2⟩
  exact convexHull_mono hm hlast

/-- The geometric complex obtained from the cast labelled faces and their parent intersections. -/
noncomputable def geometricComplex {L I : Type*} [DecidableEq L] (site : L → Point)
    (hs : Function.Injective site) (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hParent : ∀ i j, i ≠ j → siteTriangle site (tri i) ∩ siteTriangle site (tri j) =
      convexHull ℝ (pointVertices site (labelVertices (tri i) ∩ labelVertices (tri j)) : Set Plane)) :
    Geometry.SimplicialComplex ℝ Plane where
  toPreAbstractSimplicialComplex := (labelComplex tri).map (embedSite site)
  indep := by
    rintro _ ⟨s,⟨_, i, hi⟩,rfl⟩
    exact (triangle_points_independent site _ (hccw i)).mono
      (Finset.image_subset_image hi)
  inter_subset_convexHull := by
    rintro _ _ ⟨s,⟨_, i, hi⟩,rfl⟩ ⟨t,⟨_, j, hj⟩,rfl⟩
    have hp :
        convexHull ℝ (pointVertices site (labelVertices (tri i)) : Set Plane) ∩
          convexHull ℝ (pointVertices site (labelVertices (tri j)) : Set Plane) =
        convexHull ℝ (pointVertices site (labelVertices (tri i)) ∩
          pointVertices site (labelVertices (tri j)) : Set Plane) := by
      by_cases hij : i = j
      · subst j
        simp
      · rw [← triangle_eq_convexHull, ← triangle_eq_convexHull, hParent i j hij]
        unfold pointVertices
        have hEmbed : Function.Injective (embedSite site) := castPoint_injective.comp hs
        rw [Finset.image_inter _ _ hEmbed, Finset.coe_inter]
    exact lower_overlap (Finset.image_subset_image hi) (Finset.image_subset_image hj)
      (triangle_points_independent site _ (hccw i))
      (triangle_points_independent site _ (hccw j)) hp

/-- The geometric space is the union of the supplied closed triangle carriers. -/
theorem geometric_space_eq_union {L I : Type*} [DecidableEq L] (site : L → Point)
    (hs : Function.Injective site) (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hParent : ∀ i j, i ≠ j → siteTriangle site (tri i) ∩ siteTriangle site (tri j) =
      convexHull ℝ (pointVertices site (labelVertices (tri i) ∩ labelVertices (tri j)) : Set Plane)) :
    (geometricComplex site hs tri hccw hParent).space = ⋃ i, siteTriangle site (tri i) := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨_,⟨s,⟨_, i, hi⟩,rfl⟩,hx⟩
    apply mem_iUnion.2 ⟨i, ?_⟩
    rw [triangle_eq_convexHull]
    exact convexHull_mono (Finset.coe_subset.mpr (Finset.image_subset_image hi)) hx
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    refine ⟨pointVertices site (labelVertices (tri i)), ⟨labelVertices (tri i),?_, rfl⟩,?_⟩
    · exact ⟨⟨tri i 0, (mem_labelVertices).2 ⟨0, rfl⟩⟩, i, Finset.Subset.rfl⟩
    · rwa [← triangle_eq_convexHull]

/-- Assemble the geometric complex using the certified pairwise triangle intersections. -/
noncomputable def certifiedComplex {L I : Type*} [DecidableEq L] [Fintype I] {n : ℕ}
    (site : L → Point) (hs : Function.Injective site) (hull : Fin (n + 3) → L)
    (hv : Function.Injective hull) (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hsite : ∀ v, castPoint (site v) ∈ siteHull site hull)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c → orient (site a) (site b) (site c) ≠ 0)
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i, j))) =
      ∑ j, signedEdge (cycleEdges hull j)) : Geometry.SimplicialComplex ℝ Plane :=
  geometricComplex site hs tri hccw fun _ _ hij =>
    triangle_inter_eq_shared_labels_of_signed_boundary site hs hull hv tri hh hsite hccw hgen hchain hij

/-- The geometric space of a certified assembly is the closed hull carrier. -/
theorem certified_space_eq_siteHull {L I : Type*} [DecidableEq L] [Fintype I] {n : ℕ}
    (site : L → Point) (hs : Function.Injective site) (hull : Fin (n + 3) → L)
    (hv : Function.Injective hull) (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hsite : ∀ v, castPoint (site v) ∈ siteHull site hull)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c → orient (site a) (site b) (site c) ≠ 0)
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i, j))) =
      ∑ j, signedEdge (cycleEdges hull j)) :
    (certifiedComplex site hs hull hv tri hh hsite hccw hgen hchain).space = siteHull site hull := by
  exact (geometric_space_eq_union site hs tri hccw _).trans
    (rational_cover_from_signed_boundary site hs hull hv tri hh hsite hccw hchain).2

section Realized

variable {L I : Type*} [DecidableEq L] (site : L → Point) (hs : Function.Injective site)
    (tri : I → Fin 3 → L)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hParent : ∀ i j, i ≠ j → siteTriangle site (tri i) ∩ siteTriangle site (tri j) =
      convexHull ℝ (pointVertices site (labelVertices (tri i) ∩ labelVertices (tri j)) : Set Plane))

local notation "G" => geometricComplex site hs tri hccw hParent

/-- Enumerate the geometric faces by embedding the finite labelled face family. -/
theorem geometric_faces_finite [Fintype I] :
    (G).faces = ((faceFinset tri).image (pointVertices site) : Set (Finset Plane)) := by
  change (labelComplex tri).faces.image (pointVertices site) = _
  rw [faces_eq_finset, Finset.coe_image]

/-- The geometric vertex set is the full cast site range exactly when all sites are used. -/
theorem geometric_full_support_iff : (G).vertices = range (embedSite site) ↔ allSitesUsed tri := by
  have he : Function.Injective (embedSite site) := castPoint_injective.comp hs
  have hmem (a : L) :
      embedSite site a ∈ (G).vertices ↔ {a} ∈ (labelComplex tri).faces := by
    change {embedSite site a} ∈ (G).faces ↔ _
    constructor
    · rintro ⟨s, hs', himg⟩
      have h' : s.image (embedSite site) = ({a} : Finset L).image (embedSite site) := by
        simpa using himg
      have heq := Finset.image_injective he h'
      exact heq ▸ hs'
    · intro ha
      exact ⟨{a}, ha, by simp⟩
  rw [← full_label_support_iff]
  constructor
  · intro h a
    exact (hmem a).1 (h.symm ▸ mem_range_self a)
  · intro h
    ext x
    constructor
    · intro hx
      change {x} ∈ (G).faces at hx
      obtain ⟨s, _, heq⟩ := hx
      change s.image (embedSite site) = {x} at heq
      have hx' : x ∈ s.image (embedSite site) := by
        rw [heq]
        exact Finset.mem_singleton_self x
      obtain ⟨a, _, hax⟩ := Finset.mem_image.1 hx'
      exact ⟨a, hax⟩
    · rintro ⟨a, rfl⟩
      exact (hmem a).2 (h a)

/-- The geometric facets are exactly the embedded supplied triangles. -/
theorem geometric_facets_exact :
    (G).facets = range (fun i => pointVertices site (labelVertices (tri i))) := by
  have he : Function.Injective (embedSite site) := castPoint_injective.comp hs
  have hTransfer : (G).facets = (maximalFaces (labelComplex tri)).image (pointVertices site) := by
    ext p
    rw [Geometry.SimplicialComplex.mem_facets]
    constructor
    · rintro ⟨⟨s, hs', rfl⟩, hm⟩
      refine ⟨s, ⟨hs', ?_⟩, rfl⟩
      intro t ht hst
      apply Finset.image_injective he
      exact hm (pointVertices site t) ⟨t, ht, rfl⟩ (Finset.image_subset_image hst)
    · rintro ⟨s, ⟨hs', hm⟩, rfl⟩
      refine ⟨⟨s, hs',rfl⟩, ?_⟩
      rintro _ ⟨t, ht, rfl⟩ hst
      have hst' : s ⊆ t := (Finset.image_subset_image_iff he).mp hst
      exact congrArg (pointVertices site) (hm ht hst')
  rw [hTransfer, maximal_label_faces site tri hccw]
  ext p
  constructor
  · rintro ⟨_, ⟨i, rfl⟩,rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨labelVertices (tri i), ⟨i, rfl⟩, rfl⟩

/-- Every geometric facet of the CCW family has three vertices. -/
theorem geometric_facets_card_three {s : Finset Plane} (hf : s ∈ (G).facets) : s.card = 3 := by
  rw [geometric_facets_exact] at hf
  obtain ⟨i, rfl⟩ := hf
  have he : Function.Injective (embedSite site) := castPoint_injective.comp hs
  exact (Finset.card_image_of_injective _ he).trans (labelVertices_card site _ (hccw i))

include hs hccw hParent in
/-- The hulls of two labelled faces intersect in the hull of their common labels. -/
theorem label_face_hulls_inter {s t : Finset L} (hS : s ∈ (labelComplex tri).faces)
    (hT : t ∈ (labelComplex tri).faces) :
    convexHull ℝ (pointVertices site s : Set Plane) ∩
      convexHull ℝ (pointVertices site t : Set Plane) =
      convexHull ℝ (pointVertices site (s ∩ t) : Set Plane) := by
  have hS' : pointVertices site s ∈ (G).faces := ⟨s, hS, rfl⟩
  have hT' : pointVertices site t ∈ (G).faces := ⟨t, hT, rfl⟩
  have he : Function.Injective (embedSite site) := castPoint_injective.comp hs
  have h := (G).convexHull_inter_convexHull hS' hT'
  simpa only [pointVertices, Finset.image_inter _ _ he, Finset.coe_inter] using h

end Realized

/-- A two-label face is exactly an unordered side of some supplied occurrence. -/
theorem pair_mem_iff_occurrence {L I : Type*} [DecidableEq L]
    (tri : I → Fin 3 → L) {a b : L} (hab : a ≠ b) :
    ({a, b} : Finset L) ∈ (labelComplex tri).faces ↔
      ∃ p : I × Fin 3, occurrenceEdge tri p = (a, b) ∨ occurrenceEdge tri p = (b, a) := by
  constructor
  · rintro ⟨_, i, hi⟩
    obtain ⟨k, hka⟩ := mem_labelVertices.1 (hi (by simp : a ∈ ({a, b} : Finset L)))
    obtain ⟨l, hlb⟩ := mem_labelVertices.1 (hi (by simp : b ∈ ({a, b} : Finset L)))
    have hkl : k ≠ l := by
      intro he
      subst l
      exact hab (hka.symm.trans hlb)
    have hpos : ∀ k l : Fin 3, k ≠ l → ∃ e : Fin 3,
        triangleEdges (0 : Fin 3) 1 2 e = (k, l) ∨
          triangleEdges (0 : Fin 3) 1 2 e = (l, k) := by decide +kernel
    obtain ⟨j, hj⟩ := hpos k l hkl
    have hm : occurrenceEdge tri (i, j) =
        Prod.map (tri i) (tri i) (triangleEdges (0 : Fin 3) 1 2 j) := by
      fin_cases j <;> rfl
    refine ⟨(i, j), ?_⟩
    rcases hj with hj | hj
    · exact Or.inl (by rw [hm, hj]; simp [hka, hlb])
    · exact Or.inr (by rw [hm, hj]; simp [hka, hlb])
  · rintro ⟨⟨i, j⟩,h⟩
    have he : (occurrenceEdge tri (i, j)).1 ∈ labelVertices (tri i) ∧
        (occurrenceEdge tri (i, j)).2 ∈ labelVertices (tri i) := by
      fin_cases j
      · exact ⟨mem_labelVertices.2 ⟨0, rfl⟩, mem_labelVertices.2 ⟨1, rfl⟩⟩
      · exact ⟨mem_labelVertices.2 ⟨1, rfl⟩, mem_labelVertices.2 ⟨2, rfl⟩⟩
      · exact ⟨mem_labelVertices.2 ⟨2, rfl⟩, mem_labelVertices.2 ⟨0, rfl⟩⟩
    refine ⟨by simp, i, ?_⟩
    rcases h with h | h <;> rw [h] at he
    · exact Finset.insert_subset_iff.2 ⟨he.1, Finset.singleton_subset_iff.2 he.2⟩
    · exact Finset.insert_subset_iff.2 ⟨he.2, Finset.singleton_subset_iff.2 he.1⟩

/-- A hull cycle containing all sites spans the convex hull of their full cast range. -/
theorem siteHull_eq_full_site_hull {L : Type*} {n : ℕ} (site : L → Point)
    (hull : Fin (n + 3) → L) (hsite : ∀ v, castPoint (site v) ∈ siteHull site hull) :
    siteHull site hull = convexHull ℝ (range (embedSite site)) := by
  apply Subset.antisymm
  · exact convexHull_mono (by rintro _ ⟨j, rfl⟩; exact ⟨hull j, rfl⟩)
  · exact convexHull_min (by rintro _ ⟨a, rfl⟩; exact hsite a) (convex_convexHull ℝ _)

section CertifiedAssembly

variable {L I : Type*} [DecidableEq L] [Fintype I] {n : ℕ}
    (site : L → Point) (hs : Function.Injective site) (hull : Fin (n + 3) → L)
    (hv : Function.Injective hull) (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hsite : ∀ v, castPoint (site v) ∈ siteHull site hull)
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c → orient (site a) (site b) (site c) ≠ 0)
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i, j))) =
      ∑ j, signedEdge (cycleEdges hull j))

local notation "C" => certifiedComplex site hs hull hv tri hh hsite hccw hgen hchain

/-- The certified geometric space is the convex hull of the full real site range. -/
theorem certified_space_eq_full_site_hull :
    (C).space = convexHull ℝ (range (embedSite site)) :=
  (certified_space_eq_siteHull site hs hull hv tri hh hsite hccw hgen hchain).trans
    (siteHull_eq_full_site_hull site hull hsite)

/-- A certified assembly has a facet, and every facet has three vertices. -/
theorem certified_facets_pure_two :
    (C).facets.Nonempty ∧ ∀ s ∈ (C).facets, Finset.card s = 3 := by
  have hFacets : (C).facets = range (fun i => pointVertices site (labelVertices (tri i))) :=
    geometric_facets_exact site hs tri hccw _
  obtain ⟨x, hx⟩ := hh.full
  have hxHull : x ∈ siteHull site hull := interior_subset hx
  rw [← (rational_cover_from_signed_boundary site hs hull hv tri hh hsite hccw hchain).2] at hxHull
  obtain ⟨i, _⟩ := mem_iUnion.1 hxHull
  refine ⟨?_, fun s hf => geometric_facets_card_three site hs tri hccw _ hf⟩
  rw [hFacets]
  exact ⟨_, ⟨i, rfl⟩⟩

end CertifiedAssembly

section CertifiedEdges

variable {L I : Type*} [DecidableEq L] [Fintype I] {n : ℕ}
    (site : L → Point) (hs : Function.Injective site) (hull : Fin (n + 3) → L)
    (hv : Function.Injective hull) (tri : I → Fin 3 → L)
    (hh : PolygonCertificate (siteHull site hull) (fun e => realEdge site (cycleEdges hull e)))
    (hccw : ∀ i, 0 < orient (site (tri i 0)) (site (tri i 1)) (site (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i, j))) =
      ∑ j, signedEdge (cycleEdges hull j))

include site hs hv hh hccw hchain in
/-- Each listed hull side belongs to the labelled assembly. -/
theorem certified_hull_pair_face (j : Fin (n + 3)) :
    ({(cycleEdges hull j).1, (cycleEdges hull j).2} : Finset L) ∈
      (labelComplex tri).faces := by
  let e := cycleEdges hull j
  obtain ⟨hf, hr⟩ := (rational_edge_counts site hs hull hv tri hh hccw hchain).2.1 j
  have he : e.1 ≠ e.2 := by
    intro h
    have heSwap : e.swap = e := Prod.ext h.symm h
    change directedMultiplicity (occurrenceEdge tri) e = 1 at hf
    change directedMultiplicity (occurrenceEdge tri) e.swap = 0 at hr
    rw [heSwap, hf] at hr
    omega
  apply (pair_mem_iff_occurrence tri he).2
  by_contra hn
  have habs : ∀ p, occurrenceEdge tri p ≠ e := fun p heq => hn ⟨p, Or.inl heq⟩
  change directedMultiplicity (occurrenceEdge tri) e = 1 at hf
  simp [directedMultiplicity, habs] at hf

include site hs hv hh hccw hchain in
/-- A listed hull side is a face with one forward occurrence and its closed segment on the
frontier. -/
theorem certified_hull_face_incidence (j : Fin (n + 3)) :
    let e := cycleEdges hull j
    ({e.1, e.2} : Finset L) ∈ (labelComplex tri).faces ∧
    directedMultiplicity (occurrenceEdge tri) e = 1 ∧
    directedMultiplicity (occurrenceEdge tri) e.swap = 0 ∧
    segment ℝ (embedSite site e.1) (embedSite site e.2) ⊆ frontier (siteHull site hull) := by
  dsimp only
  obtain ⟨hf, hr⟩ := (rational_edge_counts site hs hull hv tri hh hccw hchain).2.1 j
  refine ⟨certified_hull_pair_face site hs hull hv tri hh hccw hchain j, hf, hr, ?_⟩
  exact closed_site_edge_subset_frontier_of_hull_pair site hull hh ⟨j, Or.inl rfl⟩

include hs hv hh hccw hchain in
/-- An assembled non-hull edge has two opposite incidences and its open segment lies inside the hull. -/
theorem certified_nonhull_face_incidence
    (hsite : ∀ a, castPoint (site a) ∈ siteHull site hull)
    (hgen : ∀ a b c : L, a ≠ b → a ≠ c → b ≠ c → orient (site a) (site b) (site c) ≠ 0)
    {a b : L} (hab : a ≠ b) (hFace : ({a, b} : Finset L) ∈ (labelComplex tri).faces)
    (hNotHull : ∀ j, cycleEdges hull j ≠ (a, b) ∧ cycleEdges hull j ≠ (b, a)) :
    directedMultiplicity (occurrenceEdge tri) (a, b) = 1 ∧
    directedMultiplicity (occurrenceEdge tri) (b, a) = 1 ∧
    (∃ p q : I × Fin 3, occurrenceEdge tri p = (a, b) ∧
      occurrenceEdge tri q = (b, a) ∧ p.1 ≠ q.1) ∧
    openSegment ℝ (castPoint (site a)) (castPoint (site b)) ⊆ interior (siteHull site hull) := by
  obtain ⟨hf, hr, he⟩ := (rational_edge_counts site hs hull hv tri hh hccw hchain).2.2 (a, b)
    hNotHull ((pair_mem_iff_occurrence tri hab).1 hFace)
  exact ⟨hf, hr, he, nonhull_open_site_edge_subset_interior site hull hv hh hsite hgen hab hNotHull⟩

end CertifiedEdges

end TDA.Filtration.RationalAlpha.TriangulationAssembly
