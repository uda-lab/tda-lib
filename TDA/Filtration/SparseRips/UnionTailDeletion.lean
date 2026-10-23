import TDA.Filtration.SparseRips.DeletionGrid

/-!
# Retraction of an earliest closed-active stage from a finite union

The deletion projection at a scale `d` fixes every vertex belonging to a
later closed-active stage. If there is no deletion time between `d` and the
next scale `s`, it sends the `d` stage into the `s` stage. Consequently the
entire tail union is a homology retract of the union including `d`.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial CategoryTheory

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V]

local instance unionTailDecidableEq : DecidableEq V := Classical.decEq V

theorem activeUnion_mono (seed : V) (η : ℝ) {G H : Finset ℝ}
    (hGH : G ⊆ H) : activeUnion seed η G ≤ activeUnion seed η H := by
  intro σ hσ
  obtain ⟨a, ha, hσa⟩ := hσ
  exact ⟨a, hGH ha, hσa⟩

theorem closedActiveComplex_le_activeUnion (seed : V) (η : ℝ) {G : Finset ℝ}
    {a : ℝ} (ha : a ∈ G) : closedActiveComplex seed η a ≤ activeUnion seed η G := by
  intro σ hσ
  exact ⟨a, ha, hσ⟩

/-- Hypotheses needed to remove the first scale of a finite union. -/
structure TailDeletionData (seed : V) (η : ℝ) (G H : Finset ℝ) (d s : ℝ) : Prop where
  first_mem : d ∈ G
  next_mem : s ∈ H
  tail_subset : H ⊆ G
  first_or_tail : ∀ a ∈ G, a = d ∨ a ∈ H
  first_nonneg : 0 ≤ d
  first_lt_tail : ∀ a ∈ H, d < a
  no_deletion : NoDeletionBetween seed η d s

def tailDeletionVertexMap (seed : V) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 3) {G H : Finset ℝ} {d s : ℝ}
    (data : TailDeletionData seed η G H d s) :
    VertexMap (activeUnion seed η G) (activeUnion seed η H) where
  toFun := deletionMap seed η d hη.le data.first_nonneg
  map_face := by
    intro σ hσ
    obtain ⟨a, ha, hσa⟩ := hσ
    rcases data.first_or_tail a ha with rfl | haH
    · refine ⟨s, data.next_mem, ?_⟩
      exact image_mem_later_of_noDeletion seed hη hη' data.first_nonneg
        (le_of_lt (data.first_lt_tail s data.next_mem)) data.no_deletion hσa
    · refine ⟨a, haH, ?_⟩
      simpa only [deletionMap_image_later seed hη.le data.first_nonneg
        (data.first_lt_tail a haH) hσa] using hσa

theorem tailDeletion_inclusion_contiguous (seed : V) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 3) {G H : Finset ℝ} {d s : ℝ}
    (data : TailDeletionData seed η G H d s) :
    Contiguous
      (VertexMap.comp (tailDeletionVertexMap seed hη hη' data)
        (inclusionVertexMap (activeUnion_mono seed η data.tail_subset)))
      (VertexMap.id (activeUnion seed η G)) := by
  intro σ hσ
  change σ.image (deletionMap seed η d hη.le data.first_nonneg) ∪ σ.image id ∈
    activeUnion seed η G
  rw [Finset.image_id]
  obtain ⟨a, ha, hσa⟩ := hσ
  rcases data.first_or_tail a ha with had | haH
  · subst a
    refine ⟨d, data.first_mem, ?_⟩
    have hcont := inclusion_deletion_contiguous seed hη hη' data.first_nonneg σ hσa
    change σ.image (deletionMap seed η d hη.le data.first_nonneg) ∪ σ.image id ∈
      closedActiveComplex seed η d at hcont
    simpa only [Finset.image_id] using hcont
  · rw [deletionMap_image_later seed hη.le data.first_nonneg
      (data.first_lt_tail a haH) hσa, Finset.union_self]
    exact ⟨a, ha, hσa⟩

theorem inclusion_tailDeletion_contiguous (seed : V) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 3) {G H : Finset ℝ} {d s : ℝ}
    (data : TailDeletionData seed η G H d s) :
    Contiguous
      (VertexMap.comp (inclusionVertexMap (activeUnion_mono seed η data.tail_subset))
        (tailDeletionVertexMap seed hη hη' data))
      (VertexMap.id (activeUnion seed η H)) := by
  intro σ hσ
  change σ.image (deletionMap seed η d hη.le data.first_nonneg) ∪ σ.image id ∈
    activeUnion seed η H
  rw [Finset.image_id]
  obtain ⟨a, ha, hσa⟩ := hσ
  rw [deletionMap_image_later seed hη.le data.first_nonneg
    (data.first_lt_tail a ha) hσa, Finset.union_self]
  exact ⟨a, ha, hσa⟩

variable [LinearOrder V]

/-- The inclusion of the tail union induces a homology isomorphism. -/
def tailDeletionHomologyIso (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) {G H : Finset ℝ} {d s : ℝ}
    (data : TailDeletionData seed η G H d s) (n : ℕ) :
    simplicialHomology (activeUnion seed η H) R n ≅
      simplicialHomology (activeUnion seed η G) R n where
  hom := simplicialHomologyMap R
    (inclusionVertexMap (activeUnion_mono seed η data.tail_subset)) n
  inv := simplicialHomologyMap R (tailDeletionVertexMap seed hη hη' data) n
  hom_inv_id := by
    rw [← simplicialHomologyMap_comp,
      Contiguous.simplicialHomologyMap_eq R
        (inclusion_tailDeletion_contiguous seed hη hη' data), simplicialHomologyMap_id]
  inv_hom_id := by
    rw [← simplicialHomologyMap_comp,
      Contiguous.simplicialHomologyMap_eq R
        (tailDeletion_inclusion_contiguous seed hη hη' data), simplicialHomologyMap_id]

@[simp] theorem tailDeletionHomologyIso_hom (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) {G H : Finset ℝ} {d s : ℝ}
    (data : TailDeletionData seed η G H d s) (n : ℕ) :
    (tailDeletionHomologyIso R seed hη hη' data n).hom =
      simplicialHomologyIncl R (activeUnion_mono seed η data.tail_subset) n :=
  simplicialHomologyMap_inclusion R _ n

end

end TDA.Filtration.SparseRips
