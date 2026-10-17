import TDA.Topology.MultiNerve

/-!
# Multinerve fixtures

Generic negative controls for `TDA.Topology.MultiNerve`, on the discrete spaces `Bool` and
`Unit`:

* **Disjoint members.** The singletons `{false}` and `{true}` have empty intersection, so the
  pair of their labels carries no multinerve cell and is not a nerve face.
* **Duplicate labels.** Two labels for the same full member give two distinct vertex cells,
  mirroring the label-retaining convention of the ordinary nerve, and the pair carries a cell.
-/

namespace TDA.Topology.MultiNerveExamples

open Finset Set
open TDA.Topology.MultiNerveCell

noncomputable section

/-! ## Disjoint members -/

/-- The family of singletons on the discrete Boolean space. -/
def singletonFamily : CoverFamily Bool Bool := fun b => {b}

/-- The two singleton members have empty intersection. -/
theorem singletonFamily_interMember_pair :
    interMember singletonFamily {false, true} = ∅ := by
  rw [interMember_insert, interMember_singleton]
  ext x
  cases x <;> simp [singletonFamily]

/-- A pair of indices with disjoint members has no path component of its intersection, no
multinerve cell over it, and is not a nerve face. -/
theorem singletonFamily_no_cell_over_pair :
    IsEmpty (ZerothHomotopy (interMember singletonFamily {false, true})) ∧
      (¬ ∃ a : MultiNerveCell singletonFamily, a.support = {false, true}) ∧
      ({false, true} : Finset Bool) ∉ nerve singletonFamily := by
  have hempty := (isEmpty_cellsOver_iff singletonFamily _).2 singletonFamily_interMember_pair
  refine ⟨hempty, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    exact hempty.false (cellsOverEquiv singletonFamily _ (by simp) ⟨a, ha⟩)
  · intro hσ
    obtain ⟨a, ha⟩ := exists_cell_of_mem_nerve hσ
    exact hempty.false (cellsOverEquiv singletonFamily _ (by simp) ⟨a, ha⟩)

/-! ## Duplicate labels -/

/-- Two labels for the full member of the one-point space. -/
def duplicateFamily : CoverFamily Unit Bool := fun _ => Set.univ

private theorem unit_mem_duplicate (σ : Finset Bool) : () ∈ interMember duplicateFamily σ :=
  (mem_interMember_iff duplicateFamily).2 fun _ _ => Set.mem_univ ()

/-- The cell over a label set represented by the unique point. -/
def duplicateCell (σ : Finset Bool) (hσ : σ.Nonempty) : MultiNerveCell duplicateFamily :=
  mk σ hσ (ZerothHomotopy.mk ⟨(), unit_mem_duplicate σ⟩)

/-- The two labels give two distinct vertex cells, both faces of the cell over the pair, while
their supports are distinct nerve vertices. -/
theorem duplicate_labels_distinct_vertex_cells :
    duplicateCell {false} (by simp) ≠ duplicateCell {true} (by simp) ∧
      duplicateCell {false} (by simp) ≤ duplicateCell {false, true} (by simp) ∧
      duplicateCell {true} (by simp) ≤ duplicateCell {false, true} (by simp) ∧
      ({false} : Finset Bool) ∈ nerve duplicateFamily ∧
      ({true} : Finset Bool) ∈ nerve duplicateFamily := by
  refine ⟨fun h => ?_, ⟨by simp [duplicateCell], rfl⟩, ⟨by simp [duplicateCell], rfl⟩,
    support_mem_nerve (duplicateCell {false} (by simp)),
    support_mem_nerve (duplicateCell {true} (by simp))⟩
  have hs := congrArg MultiNerveCell.support h
  simp [duplicateCell] at hs

end

end TDA.Topology.MultiNerveExamples
