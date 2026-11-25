import TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
import TDA.Filtration.RationalAlpha.SubdividedBoundaryCoverage
import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false

/-!
# The Alpha carrier of a certified supplied triangulation

The squared-norm affine supports of an actual Alpha face and a supplied
triangle agree at the face barycenter. The positive face weights force every
face site onto the triangle circle. With no fourth circle contact, all the
labels lie in that triangle. Restricting the triangle witnesses gives the
other inclusion.

Both carriers use nonempty faces. The signed polygon theorem concerns
full-dimensional hulls and requires at least three labels. The
common-cell inclusion is independent of polygon coverage.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedCarrier

open Set
open scoped BigOperators Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade

noncomputable section

private def height (z : Plane) : ℝ := (z 0)^2 + (z 1)^2

private def supportLinear (x : Plane) : Plane →ₗ[ℝ] ℝ :=
  (2 * x 0) • PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 0 +
    (2 * x 1) • PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) 1

/-- Squared-height lower support associated to a center and a squared radius. -/
private def support (x : Plane) (r : ℝ) (z : Plane) : ℝ :=
  supportLinear x z + (r - height x)

private theorem support_gap (x z : Plane) (r : ℝ) :
    height z - support x r z = dist x z ^ 2 - r := by
  rw [distSq_coordinates]
  simp only [support, height, supportLinear, LinearMap.add_apply, LinearMap.smul_apply,
    PiLp.projₗ_apply, smul_eq_mul]
  ring

private theorem support_average {ι : Type*} (s : Finset ι) (w : ι → ℝ) (v : ι → Plane)
    (hw : ∑ i ∈ s, w i = 1) (x : Plane) (r : ℝ) :
    support x r (∑ i ∈ s, w i • v i) = ∑ i ∈ s, w i * support x r (v i) := by
  have hlin : supportLinear x (∑ i ∈ s, w i • v i) =
      ∑ i ∈ s, w i * supportLinear x (v i) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [support]
  rw [hlin]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]

private theorem support_le_site {n : ℕ} (p : Fin n ↪ Point)
    {s : Finset (Fin n)} {a : Fin n} (ha : a ∈ s) {x : Plane}
    (hx : x ∈ Alpha.commonCells (realSites p) s) (i : Fin n) :
    support x (dist x (realSites p a)^2) (realSites p i) ≤ height (realSites p i) := by
  have h := (sq_le_sq₀ dist_nonneg dist_nonneg).2 (hx a ha i)
  have hg := support_gap x (realSites p i) (dist x (realSites p a)^2)
  linarith only [h,hg]

private theorem support_tight_iff {n : ℕ} (p : Fin n ↪ Point) (x : Plane) (a i : Fin n) :
    support x (dist x (realSites p a)^2) (realSites p i) = height (realSites p i) ↔
      dist x (realSites p i) = dist x (realSites p a) := by
  have hg := support_gap x (realSites p i) (dist x (realSites p a)^2)
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg]
  constructor <;> intro h <;> linarith only [hg,h]

private theorem support_tight_on_face {n : ℕ} (p : Fin n ↪ Point)
    {s : Finset (Fin n)} {a i : Fin n} (ha : a ∈ s) (hi : i ∈ s) {x : Plane}
    (hx : x ∈ Alpha.commonCells (realSites p) s) :
    support x (dist x (realSites p a)^2) (realSites p i) = height (realSites p i) :=
  (support_tight_iff p x a i).2
    (Alpha.dist_eq_of_mem_commonCells (realSites p) hi ha hx)

private def faceBarycenter {n : ℕ} (p : Fin n ↪ Point) (s : Finset (Fin n)) : Plane :=
  ∑ j ∈ s, s.centroidWeights ℝ j • realSites p j

private theorem uniformWeight_pos {n : ℕ} {s : Finset (Fin n)} (hs : s.Nonempty) (j : Fin n) :
    0 < s.centroidWeights ℝ j := by
  rw [Finset.centroidWeights_apply]
  exact inv_pos.mpr (Nat.cast_pos.mpr hs.card_pos)

private theorem barycenter_mem_of_contained {n : ℕ} (p : Fin n ↪ Point)
    {s : Finset (Fin n)} (hs : s.Nonempty) {H : Set Plane}
    (hc : Convex ℝ H) (hsite : ∀ i, realSites p i ∈ H) :
    faceBarycenter p s ∈ H :=
  hc.sum_mem (fun i _ => (uniformWeight_pos hs i).le)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) (fun i _ => hsite i)

private theorem triangle_weights {n : ℕ} (p : Fin n ↪ Point) (v : Fin 3 → Fin n)
    {z : Plane} (hz : z ∈ siteTriangle p v) :
    ∃ (js : Finset (Fin 3)) (w : Fin 3 → ℝ), (∀ j ∈ js, 0 ≤ w j) ∧
      (∑ j ∈ js, w j = 1) ∧ (∑ j ∈ js, w j • realSites p (v j)) = z := by
  have he : ({castPoint (p (v 0)), castPoint (p (v 1)), castPoint (p (v 2))} : Set Plane) =
      range (fun j => realSites p (v j)) := by
    ext x
    constructor
    · simp only [mem_insert_iff, mem_singleton_iff]
      rintro (rfl | rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    · rintro ⟨j,rfl⟩
      fin_cases j <;> simp [realSites, castSites]
  change z ∈ convexHull ℝ _ at hz
  rw [he,convexHull_range_eq_exists_affineCombination] at hz
  obtain ⟨js,w,h₀,h₁,hw⟩ := hz
  rw [Finset.affineCombination_eq_linear_combination _ _ _ h₁] at hw
  exact ⟨js,w,h₀,h₁,hw⟩

/-- An admitted triangle covering the uniform positive barycenter has every face site on its
circle. The triangle weights in this proof are allowed to vanish. -/
private theorem face_circle_tight_of_barycenter {n : ℕ} (p : Fin n ↪ Point)
    {s : Finset (Fin n)} {a : Fin n} (ha : a ∈ s) (v : Fin 3 → Fin n)
    (hz : faceBarycenter p s ∈ siteTriangle p v)
    {x y : Plane} (hx : x ∈ Alpha.commonCells (realSites p) s)
    (hy : y ∈ Alpha.commonCells (realSites p) (labelVertices v)) :
    ∀ j ∈ s, dist y (realSites p j) = dist y (realSites p (v 0)) := by
  let w := s.centroidWeights ℝ
  let r := dist x (realSites p a)^2
  let q := dist y (realSites p (v 0))^2
  let z := faceBarycenter p s
  let A := support x r
  let B := support y q
  let h := fun j => height (realSites p j)
  have hw : ∑ j ∈ s, w j = 1 := s.sum_centroidWeights_eq_one_of_nonempty ℝ ⟨a,ha⟩
  have hwpos (j : Fin n) : 0 < w j := uniformWeight_pos ⟨a,ha⟩ j
  have hv (j : Fin 3) : v j ∈ labelVertices v := mem_labelVertices.2 ⟨j,rfl⟩
  obtain ⟨js,k,hk₀,hk₁,hzb⟩ := triangle_weights p v hz
  change (∑ j ∈ js, k j • realSites p (v j)) = z at hzb
  have hfaceA : A z = ∑ j ∈ s, w j * h j := by
    calc
      A z = ∑ j ∈ s, w j * A (realSites p j) := support_average s w (realSites p) hw x r
      _ = ∑ j ∈ s, w j * h j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [show A (realSites p j) = h j from support_tight_on_face p ha hj hx]
  have hfaceB : B z = ∑ j ∈ s, w j * B (realSites p j) :=
    support_average s w (realSites p) hw y q
  have hBA : B z ≤ A z := by
    rw [hfaceA,hfaceB]
    exact Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (support_le_site p (hv 0) hy j) (hwpos j).le
  have hAB : A z ≤ B z := by
    rw [← hzb]
    change support x r (∑ j ∈ js, k j • realSites p (v j)) ≤
      support y q (∑ j ∈ js, k j • realSites p (v j))
    rw [support_average js k _ hk₁, support_average js k _ hk₁]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left
      ((support_le_site p ha hx (v j)).trans_eq
        (support_tight_on_face p (hv 0) (hv j) hy).symm) (hk₀ j hj)
  have he : A z = B z := le_antisymm hAB hBA
  have hg : (∑ j ∈ s, w j * (h j - B (realSites p j))) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← hfaceA, ← hfaceB, he, sub_self]
  intro j hj
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    mul_nonneg (hwpos i).le (sub_nonneg.mpr (support_le_site p (hv 0) hy i)))).1 hg j hj
  apply (support_tight_iff p y (v 0) j).1
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (hwpos j).ne')).symm

private theorem label_tri_eq_triple {n : ℕ} (v : Fin 3 → Fin n) :
    labelVertices v = {v 0,v 1,v 2} := by
  ext j
  rw [mem_labelVertices]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

private theorem tri_distinct {a b c : Point} (h : 0 < orient a b c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_,?_,?_⟩ <;> intro he <;> subst_vars <;>
    simp [orient, normal, det, mul_comm] at h

private theorem rational_sq_eq_of_real_dist_eq (o a b : Point)
    (h : dist (castPoint o) (castPoint a) = dist (castPoint o) (castPoint b)) :
    sqDist o a = sqDist o b := by
  have hs := congrArg (fun r : ℝ => r^2) h
  rw [distSq_cast,distSq_cast] at hs
  exact_mod_cast hs

private theorem admitted_triangle_center {n : ℕ} (p : Fin n ↪ Point) (v : Fin 3 → Fin n)
    (hccw : 0 < orient (p (v 0)) (p (v 1)) (p (v 2)))
    (hpass : checkIncircle p (v 0) (v 1) (v 2) = true) :
    ∃ o : Point, sqDist o (p (v 1)) = sqDist o (p (v 0)) ∧
      sqDist o (p (v 2)) = sqDist o (p (v 0)) ∧
      castPoint o ∈ Alpha.commonCells (realSites p) (labelVertices v) := by
  obtain ⟨o,ho,hob,hoc⟩ := circumcenter_exists_eq_sqDist _ _ _ hccw.ne'
  obtain ⟨x,hx⟩ := (checkIncircle_eq_true_iff_commonCells_nonempty
    p (v 0) (v 1) (v 2) hccw ho).1 hpass
  have hcenter := commonCells_triangle_point_eq p (v 0) (v 1) (v 2) hccw.ne' ho hx
  rw [hcenter, ← label_tri_eq_triple] at hx
  exact ⟨o,hob,hoc,hx⟩

/-- The original CCW finite test gives a center whose contacts are exactly the three labels
when either no-four condition holds. This is the `hcontact` input of
`alphaCarrier_le_labelComplex_of_closed_cover` for a client with its own closed cover. -/
theorem admitted_triangle_contact {n : ℕ} (p : Fin n ↪ Point) (v : Fin 3 → Fin n)
    (hccw : 0 < orient (p (v 0)) (p (v 1)) (p (v 2)))
    (hpass : checkIncircle p (v 0) (v 1) (v 2) = true)
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p) :
    ∃ y ∈ Alpha.commonCells (realSites p) (labelVertices v),
      ∀ j, dist y (realSites p j) = dist y (realSites p (v 0)) → j ∈ labelVertices v := by
  obtain ⟨o,hob,hoc,hx⟩ := admitted_triangle_center p v hccw hpass
  refine ⟨castPoint o,hx,fun j hj => ?_⟩
  by_contra hn
  have hv (i : Fin 3) : v i ∈ labelVertices v := mem_labelVertices.2 ⟨i,rfl⟩
  have hd (i : Fin 3) : v i ≠ j := fun he => hn (he ▸ hv i)
  obtain ⟨hab,hac,hbc⟩ := tri_distinct hccw
  have hab' : v 0 ≠ v 1 := fun he => hab (congrArg p he)
  have hac' : v 0 ≠ v 2 := fun he => hac (congrArg p he)
  have hbc' : v 1 ≠ v 2 := fun he => hbc (congrArg p he)
  rcases hno with hg | hf
  · exact hg (v 0) (v 1) (v 2) j hab' hac' (hd 0) hbc' (hd 1) (hd 2) (castPoint o)
      (Alpha.dist_eq_of_mem_commonCells (realSites p) (hv 1) (hv 0) hx)
      (Alpha.dist_eq_of_mem_commonCells (realSites p) (hv 2) (hv 0) hx) hj
  · apply hf (v 0) (v 1) (v 2) j hab' hac' (hd 0) hbc' (hd 1) (hd 2)
    have hsq := rational_sq_eq_of_real_dist_eq o (p j) (p (v 0)) hj
    rw [incircle_eq_radius_gap _ _ _ _ _ hob hoc, hsq, sub_self, mul_zero]

/-- Every nonempty subface of a supplied triangle with a real common-cell witness belongs
to the actual all-scales Alpha carrier. -/
theorem labelComplex_le_alphaCarrier_of_commonCells {n : ℕ} {I : Type*}
    (p : Fin n ↪ Point) (tri : I → Fin 3 → Fin n)
    (h : ∀ i, (Alpha.commonCells (realSites p) (labelVertices (tri i))).Nonempty) :
    labelComplex tri ≤ Alpha.carrier (realSites p) := by
  intro s hs
  obtain ⟨hn,i,hsub⟩ := hs
  obtain ⟨y,hy⟩ := h i
  change s ∈ TDA.Topology.nerve (Alpha.voronoiFamily (realSites p))
  exact (TDA.Topology.mem_nerve_iff _ _).2 ⟨hn,y,fun j hj => hy j (hsub hj)⟩

/-- Original-order CCW empty-circumdisk tests put the supplied labelled faces in the actual
carrier, including when another site ties at a circumcenter. -/
theorem labelComplex_le_alphaCarrier {n : ℕ} {I : Type*} (p : Fin n ↪ Point)
    (tri : I → Fin 3 → Fin n)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true) :
    labelComplex tri ≤ Alpha.carrier (realSites p) := by
  apply labelComplex_le_alphaCarrier_of_commonCells p tri
  intro i
  obtain ⟨o, _, _, ho⟩ := admitted_triangle_center p (tri i) (hccw i) (hpass i)
  exact ⟨castPoint o, ho⟩

/-- Every actual Alpha face lies in one supplied triangle when the triangles cover a convex
region `H` that contains every site and each triangle has a circle contact center whose only
contacts are its three labels. The hypotheses are `hc` (convexity of `H`), `hsite` (all sites
lie in `H`), `hcover` (the closed triangles cover `H`) and `hcontact` (the exact contact
condition of `admitted_triangle_contact`). The hull-specific carrier theorems use this with
`H` a site hull, and a client with another certified cover may use it directly. -/
theorem alphaCarrier_le_labelComplex_of_closed_cover {n : ℕ} {I : Type*}
    (p : Fin n ↪ Point) (tri : I → Fin 3 → Fin n)
    {H : Set Plane} (hc : Convex ℝ H) (hsite : ∀ i, realSites p i ∈ H)
    (hcover : (⋃ i, siteTriangle p (tri i)) = H)
    (hcontact : ∀ i, ∃ y ∈ Alpha.commonCells (realSites p) (labelVertices (tri i)),
      ∀ j, dist y (realSites p j) = dist y (realSites p (tri i 0)) → j ∈ labelVertices (tri i)) :
    Alpha.carrier (realSites p) ≤ labelComplex tri := by
  intro s hs
  change s ∈ TDA.Topology.nerve (Alpha.voronoiFamily (realSites p)) at hs
  obtain ⟨hs,x,hx⟩ := (TDA.Topology.mem_nerve_iff _ _).1 hs
  obtain ⟨a,ha⟩ := hs
  have hb := barycenter_mem_of_contained p (show s.Nonempty from ⟨a,ha⟩) hc hsite
  rw [← hcover] at hb
  obtain ⟨i,hi⟩ := mem_iUnion.1 hb
  obtain ⟨y,hy,htight⟩ := hcontact i
  refine ⟨⟨a,ha⟩,i,fun j hj => htight j ?_⟩
  exact face_circle_tight_of_barycenter p ha (tri i) hi hx hy j hj

/-- Closed signed coverage and exact triangle contacts put every actual Alpha face into one
supplied triangle. Geometric no-four-cocircularity or nonvanishing four-site determinants
suffice for the contact condition. -/
theorem alphaCarrier_le_labelComplex_of_signed_boundary {n k : ℕ} {I : Type*} [Fintype I]
    (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n) (hv : Function.Injective hull)
    (tri : I → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) j)) =
      ∑ j, signedEdge (cycleEdges hull j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p) :
    Alpha.carrier (realSites p) ≤ labelComplex tri := by
  apply alphaCarrier_le_labelComplex_of_closed_cover p tri hh.convex hsite
    (rational_cover_from_signed_boundary p p.injective hull hv tri hh hsite hccw hchain).2
  intro i
  exact admitted_triangle_contact p (tri i) (hccw i) (hpass i) hno

/-- The actual all-scales Alpha carrier equals the nonempty labelled downward closure
of the certified supplied triangles. -/
theorem carrier_eq_of_signed_boundary {n k : ℕ} {I : Type*} [Fintype I]
    (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n) (hv : Function.Injective hull)
    (tri : I → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) j)) =
      ∑ j, signedEdge (cycleEdges hull j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p) :
    Alpha.carrier (realSites p) = labelComplex tri :=
  le_antisymm
    (alphaCarrier_le_labelComplex_of_signed_boundary p hull hv tri hh hsite hccw hchain hpass hno)
    (labelComplex_le_alphaCarrier p tri hccw hpass)

/-- Closed subdivided-boundary coverage and exact triangle contacts put every actual Alpha
face into one supplied triangle. The coarse hull has a strict polygon certificate, and the
triangle chain equals the chain of the ordered subdivided hull sides, so a hull side may carry
site labels in its interior. Hull labels need not be injective. Geometric no-four-cocircularity
or nonvanishing four-site determinants suffice for the contact condition. -/
theorem alphaCarrier_le_labelComplex_of_subdivided_boundary {n k : ℕ} {I : Type*} [Fintype I]
    (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n) (cuts : Fin (k+3) → List (Fin n))
    (tri : I → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hcuts : ∀ e, OrderedEdgeCuts p (cycleEdges hull e).2 (cycleEdges hull e).1 (cuts e))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) j)) =
      ∑ j, signedEdge (subdividedEdge (cycleEdges hull) cuts j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p) :
    Alpha.carrier (realSites p) ≤ labelComplex tri := by
  apply alphaCarrier_le_labelComplex_of_closed_cover p tri hh.convex hsite
    (rational_cover_from_subdivided_signed_boundary p hull cuts tri hh hcuts
      (fun i j => hsite (tri i j)) hccw hchain).2
  intro i
  exact admitted_triangle_contact p (tri i) (hccw i) (hpass i) hno

/-- The actual all-scales Alpha carrier equals the nonempty labelled downward closure of the
certified supplied triangles when a hull side of the coarse strict polygon carries subdivision
labels. See `alphaCarrier_le_labelComplex_of_subdivided_boundary`. Grades and stages are not
part of this carrier statement. -/
theorem carrier_eq_of_subdivided_boundary {n k : ℕ} {I : Type*} [Fintype I]
    (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n) (cuts : Fin (k+3) → List (Fin n))
    (tri : I → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hcuts : ∀ e, OrderedEdgeCuts p (cycleEdges hull e).2 (cycleEdges hull e).1 (cuts e))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) j)) =
      ∑ j, signedEdge (subdividedEdge (cycleEdges hull) cuts j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p) :
    Alpha.carrier (realSites p) = labelComplex tri :=
  le_antisymm
    (alphaCarrier_le_labelComplex_of_subdivided_boundary p hull cuts tri hh hcuts hsite hccw
      hchain hpass hno)
    (labelComplex_le_alphaCarrier p tri hccw hpass)

/-- All-site usage is a consequence of this carrier equality, using the actual singletons. -/
theorem allSitesUsed_of_carrier_eq {n : ℕ} {I : Type*} (p : Fin n ↪ Point) (tri : I → Fin 3 → Fin n)
    (he : Alpha.carrier (realSites p) = labelComplex tri) :
    allSitesUsed tri := by
  intro j
  apply (singleton_mem_iff_used tri j).1
  rw [← he]
  exact (Alpha.exists_mem_complex_iff (realSites p) {j}).1
    ⟨0, (Alpha.singleton_mem_complex_iff (realSites p) j 0).2 le_rfl⟩

/-- Both ordinary face APIs exclude the empty set of labels. -/
theorem empty_excluded {n : ℕ} {I : Type*} (p : Fin n ↪ Point) (tri : I → Fin 3 → Fin n) :
    (∅ : Finset (Fin n)) ∉ Alpha.carrier (realSites p) ∧
    (∅ : Finset (Fin n)) ∉ labelComplex tri := by
  constructor
  · intro h
    exact Finset.not_nonempty_empty ((TDA.Topology.mem_nerve_iff _ _).1 h).1
  · intro h
    exact Finset.not_nonempty_empty h.1

/-- The injective cycle required for signed polygon coverage has at least three labels. -/
theorem hull_requires_three {n k : ℕ} {hull : Fin (k+3) → Fin n} (hv : Function.Injective hull) :
    3 ≤ n := by
  have h := Fintype.card_le_of_injective hull hv
  simp only [Fintype.card_fin] at h
  omega

end
end TDA.Filtration.RationalAlpha.SuppliedCarrier
