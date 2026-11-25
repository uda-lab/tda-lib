import TDA.Topology.Nerve
import TDA.Topology.SubdivisionLastVertex
import TDA.Topology.SubdivisionMesh
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Closed-star labels for nested convex covers

Realize the flags of both nerves with compatible intersection witnesses. A compact patch and the
closed-star mesh bound give one labeling on their common subdivision.
-/

namespace TDA.Topology.ConvexNerve

open CategoryTheory Convexity TDA.Simplicial TDA.Topology.SubdivisionRealization
noncomputable section
universe u

variable {I : Type u}
variable {E : Type*}
variable {K L : PreAbstractSimplicialComplex I}

/-- A nonempty flag has a least face. -/
theorem exists_least_face [Fintype I] {F : Finset (Finset I)} (hF : F ∈ barycentricSubdivision K) :
    ∃ J ∈ F, ∀ A ∈ F, J ⊆ A := by
  obtain ⟨J, hJ, _, _, h⟩ := exists_flag_extrema hF
  exact ⟨J, hJ, fun A hA => (h A hA).1⟩

/-- Use the smaller intersection witness on every face of the smaller nerve. -/
theorem exists_compatibleWitnesses [Zero E] (C D : I → Set E) (h : ∀ i, C i ⊆ D i) :
    ∃ p : Finset I → E,
      (∀ J ∈ nerve C, ∀ i ∈ J, p J ∈ C i) ∧
      (∀ J ∈ nerve D, ∀ i ∈ J, p J ∈ D i) := by
  classical
  let p (J : Finset I) : E := if hC : J ∈ nerve C then Classical.choose hC.2
    else if hD : J ∈ nerve D then Classical.choose hD.2 else 0
  refine ⟨p, ?_, ?_⟩
  · intro J hC i hi
    simpa [p, hC] using Classical.choose_spec hC.2 i hi
  · intro J hD i hi
    by_cases hC : J ∈ nerve C
    · simpa [p, hC] using h i (Classical.choose_spec hC.2 i hi)
    · simpa [p, hC, hD] using Classical.choose_spec hD.2 i hi

/-- A vertex whose position belongs to all labels of a face witnesses its nerve image. -/
theorem exists_vertexMap_of_subordinate {W : Type*} {Q : PreAbstractSimplicialComplex W}
    (p : W → E) (C : I → Set E) (a : W → I)
    (ha : ∀ T ∈ Q, ∀ v ∈ T, ∀ w ∈ T, p w ∈ C (a v)) :
    ∃ f : VertexMap Q (nerve C), (f : W → I) = a := by
  classical
  let : DecidableEq I := Classical.decEq I
  refine ⟨⟨a, fun T hT => ?_⟩, rfl⟩
  obtain ⟨w, hw⟩ := (Q.isRelLowerSet_faces hT).1
  refine ⟨((Q.isRelLowerSet_faces hT).1.image a), p w, fun i hi => ?_⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  exact ha T hT v hv w hw

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The convex hulls of compatible witnesses over flags form a compact subset of the union. -/
theorem exists_compact_witness_patch [Fintype I] (D : I → Set E) (p : Finset I → E) (hc : ∀ i, Convex ℝ (D i))
    (hp : ∀ J ∈ nerve D, ∀ i ∈ J, p J ∈ D i) :
    ∃ H : Set E, IsCompact H ∧ H ⊆ ⋃ i, D i ∧
      ∀ F ∈ barycentricSubdivision (nerve D), convexHull ℝ (p '' (F : Set (Finset I))) ⊆ H := by
  classical
  let Q := barycentricSubdivision (nerve D)
  let B (F : Q.faces) := convexHull ℝ (p '' (F.val : Set (Finset I)))
  refine ⟨⋃ F, B F, isCompact_iUnion (fun F => (F.val.finite_toSet.image p).isCompact_convexHull ℝ), ?_, ?_⟩
  · intro x hx
    obtain ⟨F, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨J, hJ, hsmall⟩ := exists_least_face F.property
    obtain ⟨i, hi⟩ := ((nerve D).isRelLowerSet_faces (F.property.2.1 J hJ).1).1
    refine Set.mem_iUnion.mpr ⟨i, convexHull_min ?_ (hc i) hx⟩
    rintro _ ⟨A, hA, rfl⟩
    exact hp A (F.property.2.1 A hA).1 i (hsmall A hA hi)
  · intro F hF
    exact Set.subset_iUnion B ⟨F, hF⟩

section Geometry
variable {V : Type u} [Fintype V]

/-- A refined vertex stays in any convex set containing the positions of the original face. -/
theorem vertexPosition_mem_convex (K : PreAbstractSimplicialComplex V) (p : V → E) (S : Set E)
    (hc : Convex ℝ S) (n : ℕ) (F : Finset (Vertex V n)) (hf : F ∈ complex K n)
    (hp : ∀ v ∈ originalFace n F, p v ∈ S) (w : Vertex V n) (hw : w ∈ F) : vertexPosition p n w ∈ S := by
  classical
  have hs := ((complex K n).isRelLowerSet_faces hf).2 (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty _)
  let x := vertexPoint _ w hs
  let y := barycentricProjection K n x
  have hy : y.val.weights.support ⊆ originalFace n F := by
    rw [show y.val.weights.support = originalFace n x.val.weights.support from projection_support K n x]
    apply originalFace_mono
    simpa [x, vertexPoint] using (Finset.singleton_subset_iff.mpr hw : ({w} : Finset _) ⊆ F)
  rw [← realize_vertexPoint K p n w hs]
  change realize p K n x ∈ S
  rw [realize_eq_comp_projection]
  change (∑ v, y.val.weights v • p v) ∈ S
  rw [← Finset.sum_subset (Finset.subset_univ y.val.weights.support)
    (fun v _ hv => by simp [Finsupp.notMem_support_iff.mp hv])]
  exact hc.sum_mem (fun _ _ => y.val.weights_nonneg _) y.val.total (fun i hi => hp i (hy hi))

/-- The original face bounds the convex hull containing each refined vertex. -/
theorem vertexPosition_mem_convexHull (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ)
    (F : Finset (Vertex V n)) (hF : F ∈ complex K n) (w) (hw : w ∈ F) :
    vertexPosition p n w ∈ convexHull ℝ (p '' (originalFace n F : Set V)) :=
  vertexPosition_mem_convex K p _ (convex_convexHull ℝ _) n F hF
    (fun _ hv => subset_convexHull ℝ (p '' (originalFace n F : Set V)) (Set.mem_image_of_mem p hv)) w hw

/-- The closed star of a vertex contains every other vertex of a coface. -/
theorem vertexPosition_mem_closedStarImage (K : PreAbstractSimplicialComplex V) (p : V → E) (n : ℕ)
    {F : Finset (Vertex V n)} (hf : F ∈ complex K n) {v w : Vertex V n} (hv : v ∈ F) (hw : w ∈ F) :
    vertexPosition p n w ∈ closedStarImage K p n v := by
  classical
  have hs := ((complex K n).isRelLowerSet_faces hf).2 (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty _)
  exact ⟨F, hf, hv, vertexPoint _ w hs, by simpa [vertexPoint] using (Finset.singleton_subset_iff.mpr hw : ({w} : Finset _) ⊆ F),
    realize_vertexPoint K p n w hs⟩

/-- A common subdivision makes every closed star subordinate to the open cover of the patch. -/
theorem exists_subordinate_closedStars (K : PreAbstractSimplicialComplex V) (p : V → E)
    {I : Type*} [Nonempty I] (C : I → Set E) (hc : ∀ i, IsOpen (C i))
    (H : Set E) (hh : IsCompact H) (hcover : H ⊆ ⋃ i, C i)
    (hhull : ∀ F ∈ K, convexHull ℝ (p '' (F : Set V)) ⊆ H) :
    ∃ (n : ℕ) (a : Vertex V n → I), ∀ v, closedStarImage K p n v ⊆ C (a v) := by
  classical
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hh hc hcover
  obtain ⟨n, hN⟩ := eventually_diam_lt K p (Fintype.card V) (M := Metric.diam (Set.range p)) Metric.diam_nonneg
    (fun F _ => (Finset.card_le_univ F).trans (Nat.le_succ _))
    (fun _ _ v _ w _ => Metric.dist_le_diam_of_mem (Set.finite_range p).isBounded
      (Set.mem_range_self v) (Set.mem_range_self w)) hδ
  have hin (v : Vertex V n) (hv : ({v} : Finset _) ∈ complex K n) : vertexPosition p n v ∈ H :=
    hhull _ (originalFace_mem K n _ hv) (vertexPosition_mem_convexHull K p n _ hv v (Finset.mem_singleton_self _))
  let a (v : Vertex V n) := if hv : ({v} : Finset _) ∈ complex K n then
    Classical.choose (hball _ (hin v hv)) else Classical.choice ‹Nonempty I›
  refine ⟨n, a, fun v x hx => ?_⟩
  have hx0 := hx
  obtain ⟨F, hf, hv, _⟩ := hx0
  have hs := ((complex K n).isRelLowerSet_faces hf).2 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty _)
  have hdist := (Metric.dist_le_diam_of_mem (isBounded_closedStarImage K p n v) hx (vertexPosition_mem_closedStarImage K p n hf hv hv)).trans_lt ((hN n le_rfl).2 v)
  dsimp only [a]
  split
  · exact Classical.choose_spec (hball _ (hin v hs)) hdist
  · contradiction

end Geometry

variable [Fintype I] [Nonempty I]

/-- Choose one witness realization and one subordinate labeling, including on the smaller nerve. -/
theorem exists_common_labeling (C D : I → Set E) (hc : ∀ i, IsOpen (C i))
    (hd : ∀ i, Convex ℝ (D i)) (hle : ∀ i, C i ⊆ D i) (hu : (⋃ i, C i) = ⋃ i, D i) :
    ∃ (p : Finset I → E), (∀ J ∈ nerve C, ∀ i ∈ J, p J ∈ C i) ∧
      (∀ J ∈ nerve D, ∀ i ∈ J, p J ∈ D i) ∧
      ∃ (n : ℕ) (a : VertexMap (complex (barycentricSubdivision (nerve D)) n) (nerve C)),
        (∀ T ∈ complex (barycentricSubdivision (nerve D)) n, ∀ v ∈ T, ∀ w ∈ T,
          vertexPosition p n w ∈ C (a v)) ∧
        (∀ v, closedStarImage (barycentricSubdivision (nerve D)) p n v ⊆ C (a v)) ∧
        (∀ v, closedStarImage (barycentricSubdivision (nerve C)) p n v ⊆ C (a v)) := by
  classical
  obtain ⟨p, hp, hp'⟩ := exists_compatibleWitnesses C D hle
  obtain ⟨H, hH, hHD, hpatch⟩ := exists_compact_witness_patch D p hd hp'
  obtain ⟨n, b, hb⟩ := exists_subordinate_closedStars _ p C hc H hH (hu.symm ▸ hHD) hpatch
  have hv (T) (ht : T ∈ complex (barycentricSubdivision (nerve D)) n) (v) (hv : v ∈ T) (w) (hw : w ∈ T) :=
    hb v (vertexPosition_mem_closedStarImage _ p n ht hv hw)
  obtain ⟨a, ha⟩ := exists_vertexMap_of_subordinate _ C b hv
  refine ⟨p, hp, hp', n, a, ?_, ?_, ?_⟩
  · simpa only [ha] using hv
  · simpa only [ha] using hb
  · simpa only [ha] using closedStarImage_subset_of_labels (subdivision_mono (nerve_mono hle)) p n C b hb

end
end TDA.Topology.ConvexNerve
