import TDA.Filtration.SparseRips.Relaxed
import TDA.Simplicial.ContiguityHomotopy

/-!
# Homology equivalence for a single deletion scale

The geometric deletion projection decreases relaxed dissimilarities. Each face
and its projected face span a relaxed face, giving contiguity to the identity.
The same union lies in the closed active complex when the original face does.
The existing signed prism homotopy therefore proves that the closed active
inclusion induces an isomorphism in every degree, over every coefficient ring.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial CategoryTheory

noncomputable section

variable {V : Type*} [MetricSpace V]

local instance deletionHomologyDecidableEq : DecidableEq V := Classical.decEq V

theorem relaxedDistance_comm (η : ℝ) (time : V → Option ℝ) (r : ℝ) (x y : V) :
    relaxedDistance η time r x y = relaxedDistance η time r y x := by
  simp only [relaxedDistance, dist_comm]
  ring

/-- Weighted domination of one endpoint decreases the dissimilarity. -/
theorem relaxedDistance_left_le {η r : ℝ} {time : V → Option ℝ} {x q y : V}
    (hq : dist x q ≤ weight η (time x) r - weight η (time q) r) :
    relaxedDistance η time r q y ≤ relaxedDistance η time r x y := by
  have htri : dist q y ≤ dist x q + dist x y := by
    simpa only [dist_comm q x] using dist_triangle q x y
  dsimp [relaxedDistance]
  linarith

/-- A face together with all of its projected vertices is still a relaxed face. -/
theorem image_union_mem_relaxedComplex {η r : ℝ} (time : V → Option ℝ) (f : V → V)
    (hf : ∀ x, dist x (f x) ≤ weight η (time x) r - weight η (time (f x)) r)
    {σ : Finset V} (hσ : σ ∈ relaxedComplex η time r) :
    σ.image f ∪ σ ∈ relaxedComplex η time r := by
  refine ⟨hσ.1.mono Finset.subset_union_right, hσ.2.1, ?_⟩
  intro x hx y hy
  simp only [Finset.mem_union, Finset.mem_image] at hx hy
  rcases hx with ⟨a, ha, rfl⟩ | hx <;> rcases hy with ⟨b, hb, rfl⟩ | hy
  · exact (relaxedDistance_left_le (y := f b) (hf a)).trans
      (by rw [relaxedDistance_comm η time r a (f b)]
          exact (relaxedDistance_left_le (y := a) (hf b)).trans (hσ.2.2 b hb a ha))
  · exact (relaxedDistance_left_le (hf a)).trans (hσ.2.2 a ha y hy)
  · rw [relaxedDistance_comm]
    exact (relaxedDistance_left_le (hf b)).trans (hσ.2.2 b hb x hx)
  · exact hσ.2.2 x hx y hy

variable [Fintype V]

/-- The geometric projection is simplicial into the closed active complex. -/
def deletionVertexMap (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) :
    VertexMap (relaxedComplex η (deletionTime seed η) r) (closedActiveComplex seed η r) where
  toFun := deletionMap seed η r hη.le hr
  map_face := by
    intro σ hσ
    have hunion := image_union_mem_relaxedComplex (deletionTime seed η)
      (deletionMap seed η r hη.le hr) (deletionMap_domination seed hη hη' hr) hσ
    refine ⟨(relaxedComplex η (deletionTime seed η) r).isRelLowerSet_faces hunion |>.2
      Finset.subset_union_left (hσ.1.image _), ?_⟩
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    have hactive := deletionMap_active seed hη hη' hr a
    cases ht : deletionTime seed η (deletionMap seed η r hη.le hr a) with
    | none => trivial
    | some t => exact (show r < t by simpa [ht, OpenActive] using hactive).le

/-- Closed active faces are relaxed faces on the same ambient vertices. -/
theorem closedActiveComplex_le_relaxedComplex (seed : V) (η r : ℝ) :
    closedActiveComplex seed η r ≤ relaxedComplex η (deletionTime seed η) r :=
  fun _ h => h.1

/-- Projection followed by inclusion is contiguous to the relaxed identity. -/
theorem deletion_inclusion_contiguous (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) :
    Contiguous (VertexMap.comp (deletionVertexMap seed hη hη' hr)
      (inclusionVertexMap (closedActiveComplex_le_relaxedComplex seed η r)))
      (VertexMap.id (relaxedComplex η (deletionTime seed η) r)) := by
  intro σ hσ
  change σ.image (deletionMap seed η r hη.le hr) ∪ σ.image id ∈
    relaxedComplex η (deletionTime seed η) r
  simpa only [Finset.image_id] using image_union_mem_relaxedComplex (deletionTime seed η)
      (deletionMap seed η r hη.le hr) (deletionMap_domination seed hη hη' hr) hσ

/-- Inclusion followed by projection is contiguous to the closed-active identity,
including vertices exactly at the deletion boundary. -/
theorem inclusion_deletion_contiguous (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) :
    Contiguous (VertexMap.comp
      (inclusionVertexMap (closedActiveComplex_le_relaxedComplex seed η r))
      (deletionVertexMap seed hη hη' hr))
      (VertexMap.id (closedActiveComplex seed η r)) := by
  intro σ hσ
  change σ.image (deletionMap seed η r hη.le hr) ∪ σ.image id ∈ closedActiveComplex seed η r
  rw [Finset.image_id]
  refine ⟨image_union_mem_relaxedComplex (deletionTime seed η)
    (deletionMap seed η r hη.le hr) (deletionMap_domination seed hη hη' hr) hσ.1, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (deletionVertexMap seed hη hη' hr).map_face σ hσ.1 |>.2 x hx
  · exact hσ.2 x hx

variable [LinearOrder V]

/-- The isomorphism's forward map is the actual closed-active inclusion on homology. -/
def closedActiveHomologyIso (R : Type*) [Ring R] (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (n : ℕ) :
    simplicialHomology (closedActiveComplex seed η r) R n ≅
      simplicialHomology (relaxedComplex η (deletionTime seed η) r) R n where
  hom := simplicialHomologyMap R
    (inclusionVertexMap (closedActiveComplex_le_relaxedComplex seed η r)) n
  inv := simplicialHomologyMap R (deletionVertexMap seed hη hη' hr) n
  hom_inv_id := by
    rw [← simplicialHomologyMap_comp,
      Contiguous.simplicialHomologyMap_eq R (inclusion_deletion_contiguous seed hη hη' hr),
      simplicialHomologyMap_id]
  inv_hom_id := by
    rw [← simplicialHomologyMap_comp,
      Contiguous.simplicialHomologyMap_eq R (deletion_inclusion_contiguous seed hη hη' hr),
      simplicialHomologyMap_id]

@[simp] theorem closedActiveHomologyIso_hom (R : Type*) [Ring R] (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (n : ℕ) :
    (closedActiveHomologyIso R seed hη hη' hr n).hom =
      simplicialHomologyIncl R (closedActiveComplex_le_relaxedComplex seed η r) n :=
  simplicialHomologyMap_inclusion R _ n

/-- The canonical inclusion map itself is invertible; no choice of a levelwise abstract
isomorphism is required when constructing a natural comparison. -/
theorem isIso_closedActiveHomologyIncl (R : Type*) [Ring R] (seed : V) {η r : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (n : ℕ) :
    IsIso (simplicialHomologyIncl R (closedActiveComplex_le_relaxedComplex seed η r) n) := by
  have hi : IsIso (closedActiveHomologyIso R seed hη hη' hr n).hom := inferInstance
  rwa [closedActiveHomologyIso_hom] at hi

end

end TDA.Filtration.SparseRips
