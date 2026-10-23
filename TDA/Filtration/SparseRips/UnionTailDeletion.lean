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

/-- Completeness of a grid above its earliest retained stage. -/
def DeletionComplete (seed : V) (η : ℝ) (F : Finset ℝ) (r : ℝ) : Prop :=
  ∀ x t, deletionTime seed η x = some t →
    (∃ a ∈ F, a ≤ t) → t ≤ r → t ∈ F

theorem deletionGrid_complete (seed : V) (η r : ℝ) :
    DeletionComplete seed η (deletionGrid seed η r) r := by
  intro x t ht _ htr
  exact (mem_deletionGrid seed η r t).mpr (Or.inr ⟨htr, x, ht⟩)

theorem deletionGrid_nonneg_le (seed : V) {η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 3) {r a : ℝ} (hr : 0 ≤ r)
    (ha : a ∈ deletionGrid seed η r) : 0 ≤ a ∧ a ≤ r := by
  rcases (mem_deletionGrid seed η r a).mp ha with rfl | ⟨har, x, hx⟩
  · exact ⟨hr, le_rfl⟩
  · exact ⟨deletionTime_nonneg seed hη hη' x a hx, har⟩

/-- Removing the minimum from a complete grid preserves completeness. -/
theorem deletionComplete_erase_min (seed : V) (η : ℝ) {F : Finset ℝ} {r : ℝ}
    (hF : F.Nonempty) (hcomplete : DeletionComplete seed η F r) :
    DeletionComplete seed η (F.erase (F.min' hF)) r := by
  intro x t ht hbefore htr
  obtain ⟨a, ha, hat⟩ := hbefore
  have htF : t ∈ F := hcomplete x t ht ⟨a, Finset.mem_of_mem_erase ha, hat⟩ htr
  have hdt : F.min' hF < t :=
    (Finset.min'_lt_of_mem_erase_min' F hF ha).trans_le hat
  exact Finset.mem_erase.mpr ⟨ne_of_gt hdt, htF⟩

/-- The minimum and its next successor in a complete grid satisfy the tail
retraction hypotheses, including simultaneous vertex deletions. -/
theorem tailDeletionData_of_complete (seed : V) {η : ℝ}
    {F : Finset ℝ} {r : ℝ} (hF : F.Nonempty)
    (hbound : ∀ a ∈ F, 0 ≤ a ∧ a ≤ r)
    (hcomplete : DeletionComplete seed η F r)
    (hH : (F.erase (F.min' hF)).Nonempty) :
    TailDeletionData seed η F (F.erase (F.min' hF))
      (F.min' hF) ((F.erase (F.min' hF)).min' hH) where
  first_mem := Finset.min'_mem F hF
  next_mem := Finset.min'_mem _ hH
  tail_subset := Finset.erase_subset _ _
  first_or_tail := by
    intro a ha
    by_cases had : a = F.min' hF
    · exact Or.inl had
    · exact Or.inr (Finset.mem_erase.mpr ⟨had, ha⟩)
  first_nonneg := (hbound _ (Finset.min'_mem F hF)).1
  first_lt_tail := by
    intro a ha
    exact Finset.min'_lt_of_mem_erase_min' F hF ha
  no_deletion := by
    intro x t ht hdt
    let H := F.erase (F.min' hF)
    let s := H.min' hH
    have hsr : s ≤ r := (hbound s (Finset.mem_of_mem_erase (Finset.min'_mem H hH))).2
    by_contra hst
    have htr : t ≤ r := (le_of_lt (lt_of_not_ge hst)).trans hsr
    have htF : t ∈ F := hcomplete x t ht
      ⟨F.min' hF, Finset.min'_mem F hF, hdt.le⟩ htr
    have htH : t ∈ H := Finset.mem_erase.mpr ⟨ne_of_gt hdt, htF⟩
    exact (not_lt_of_ge (Finset.min'_le H t htH)) (lt_of_not_ge hst)

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
