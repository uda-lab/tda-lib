import TDA.Filtration.SparseRips.DeletionHomology

/-!
# Removing the earliest stage from a sparse union

Between two scales with no deletion time in the open gap, the earlier closed
active complex can be absorbed into the later one without changing homology.
The projection at the earlier scale fixes all later active vertices. This is the
successive-union step needed to compare the sparse filtration with relaxed Rips.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial CategoryTheory

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V]

local instance unionDeletionDecidableEq : DecidableEq V := Classical.decEq V

/-- Every vertex surviving strictly past `r` remains closed-active at `s`. -/
def NoDeletionBetween (seed : V) (η r s : ℝ) : Prop :=
  ∀ x t, t ∈ deletionTime seed η x → r < t → s ≤ t

theorem closedActive_of_openActive_of_noDeletion (seed : V) {η r s : ℝ}
    (hgap : NoDeletionBetween seed η r s) {x : V}
    (hx : OpenActive (deletionTime seed η x) r) :
    ClosedActive (deletionTime seed η x) s := by
  cases ht : deletionTime seed η x with
  | none => trivial
  | some t => exact hgap x t (by simp [ht]) (by simpa [ht, OpenActive] using hx)

theorem deletionMap_fixes_later (seed : V) {η r s : ℝ}
    (hη : 0 ≤ η) (hr : 0 ≤ r) (hrs : r < s) {x : V}
    (hx : ClosedActive (deletionTime seed η x) s) : deletionMap seed η r hη hr x = x := by
  apply deletionMap_of_active
  cases ht : deletionTime seed η x with
  | none => trivial
  | some t => exact hrs.trans_le (show s ≤ t by simpa [ht, ClosedActive] using hx)

theorem deletionMap_image_later (seed : V) {η r s : ℝ}
    (hη : 0 ≤ η) (hr : 0 ≤ r) (hrs : r < s) {σ : Finset V}
    (hσ : σ ∈ closedActiveComplex seed η s) :
    σ.image (deletionMap seed η r hη hr) = σ := by
  have heq : σ.image (deletionMap seed η r hη hr) = σ.image id :=
    Finset.image_congr (fun x hx => deletionMap_fixes_later seed hη hr hrs (hσ.2 x hx))
  simpa only [Finset.image_id] using heq

/-- The earlier projection maps each earlier active face into the next active complex. -/
theorem image_mem_later_of_noDeletion (seed : V) {η r s : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hgap : NoDeletionBetween seed η r s) {σ : Finset V}
    (hσ : σ ∈ closedActiveComplex seed η r) :
    σ.image (deletionMap seed η r hη.le hr) ∈ closedActiveComplex seed η s := by
  have hproject := (deletionVertexMap seed hη hη' hr).map_face σ hσ.1
  refine ⟨relaxedComplex_mono hη.le (by linarith) (deletionTime seed η)
    (deletionTime_nonneg seed hη hη') hrs hproject.1, ?_⟩
  intro x hx
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  exact closedActive_of_openActive_of_noDeletion seed hgap (deletionMap_active seed hη hη' hr a)

/-- Retraction from the two-stage union to the later stage. -/
def unionDeletionVertexMap (seed : V) {η r s : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (hrs : r < s)
    (hgap : NoDeletionBetween seed η r s) :
    VertexMap (closedActiveComplex seed η r ⊔ closedActiveComplex seed η s)
      (closedActiveComplex seed η s) where
  toFun := deletionMap seed η r hη.le hr
  map_face := by
    intro σ hσ
    rcases (show σ ∈ closedActiveComplex seed η r ∨ σ ∈ closedActiveComplex seed η s from hσ)
      with hσ | hσ
    · exact image_mem_later_of_noDeletion seed hη hη' hr hrs.le hgap hσ
    · simpa only [deletionMap_image_later seed hη.le hr hrs hσ] using hσ

/-- The union retraction is contiguous to the identity after inclusion. -/
theorem unionDeletion_inclusion_contiguous (seed : V) {η r s : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (hrs : r < s)
    (hgap : NoDeletionBetween seed η r s) :
    Contiguous (VertexMap.comp (unionDeletionVertexMap seed hη hη' hr hrs hgap)
      (inclusionVertexMap (show closedActiveComplex seed η s ≤
        closedActiveComplex seed η r ⊔ closedActiveComplex seed η s from le_sup_right)))
      (VertexMap.id (closedActiveComplex seed η r ⊔ closedActiveComplex seed η s)) := by
  intro σ hσ
  change σ.image (deletionMap seed η r hη.le hr) ∪ σ.image id ∈
    closedActiveComplex seed η r ⊔ closedActiveComplex seed η s
  rw [Finset.image_id]
  rcases (show σ ∈ closedActiveComplex seed η r ∨ σ ∈ closedActiveComplex seed η s from hσ)
    with hσ | hσ
  · apply (show closedActiveComplex seed η r ≤
      closedActiveComplex seed η r ⊔ closedActiveComplex seed η s from le_sup_left)
    change σ.image (deletionMap seed η r hη.le hr) ∪ σ ∈ closedActiveComplex seed η r
    have hcont := inclusion_deletion_contiguous seed hη hη' hr σ hσ
    change σ.image (deletionMap seed η r hη.le hr) ∪ σ.image id ∈
      closedActiveComplex seed η r at hcont
    simpa only [Finset.image_id] using hcont
  · rw [deletionMap_image_later seed hη.le hr hrs hσ, Finset.union_self]
    exact Or.inr hσ

/-- The reverse composite fixes all later active faces. -/
theorem inclusion_unionDeletion_contiguous (seed : V) {η r s : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (hrs : r < s)
    (hgap : NoDeletionBetween seed η r s) :
    Contiguous (VertexMap.comp
      (inclusionVertexMap (show closedActiveComplex seed η s ≤
        closedActiveComplex seed η r ⊔ closedActiveComplex seed η s from le_sup_right))
      (unionDeletionVertexMap seed hη hη' hr hrs hgap))
      (VertexMap.id (closedActiveComplex seed η s)) := by
  intro σ hσ
  change σ.image (deletionMap seed η r hη.le hr) ∪ σ.image id ∈ closedActiveComplex seed η s
  rw [Finset.image_id]
  simpa only [deletionMap_image_later seed hη.le hr hrs hσ, Finset.union_self] using hσ

variable [LinearOrder V]

/-- A proved two-stage union homology equivalence, with the actual inclusion as forward map. -/
def unionDeletionHomologyIso (R : Type*) [Ring R] (seed : V) {η r s : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (hrs : r < s)
    (hgap : NoDeletionBetween seed η r s) (n : ℕ) :
    simplicialHomology (closedActiveComplex seed η s) R n ≅
      simplicialHomology (closedActiveComplex seed η r ⊔ closedActiveComplex seed η s) R n where
  hom := simplicialHomologyMap R (inclusionVertexMap le_sup_right) n
  inv := simplicialHomologyMap R (unionDeletionVertexMap seed hη hη' hr hrs hgap) n
  hom_inv_id := by
    rw [← simplicialHomologyMap_comp,
      Contiguous.simplicialHomologyMap_eq R
        (inclusion_unionDeletion_contiguous seed hη hη' hr hrs hgap), simplicialHomologyMap_id]
  inv_hom_id := by
    rw [← simplicialHomologyMap_comp,
      Contiguous.simplicialHomologyMap_eq R
        (unionDeletion_inclusion_contiguous seed hη hη' hr hrs hgap), simplicialHomologyMap_id]

@[simp] theorem unionDeletionHomologyIso_hom (R : Type*) [Ring R] (seed : V) {η r s : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (hr : 0 ≤ r) (hrs : r < s)
    (hgap : NoDeletionBetween seed η r s) (n : ℕ) :
    (unionDeletionHomologyIso R seed hη hη' hr hrs hgap n).hom =
      simplicialHomologyIncl R (show closedActiveComplex seed η s ≤
        closedActiveComplex seed η r ⊔ closedActiveComplex seed η s from le_sup_right) n :=
  simplicialHomologyMap_inclusion R _ n

end

end TDA.Filtration.SparseRips
