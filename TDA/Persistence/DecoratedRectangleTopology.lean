import TDA.Persistence.DecoratedRectangleCells
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness and separation of decorated rectangles

The map to pairs of bundled lower sets puts every source rectangle in the native complete
cut-line topology. Its image is compact and open. Shrinking coordinate cells separates
any two distinct cut pairs while preserving the strict separation from the diagonal.
-/

universe v

namespace TDA.Persistence.RectangleMeasure

open Set

variable {α : Type v} [LinearOrder α]

/-- The existing two-cut representation, in the native ordered lower-set space. -/
def rectangleLowerSetEquiv : (Cut α × Cut α) ≃ (LowerSet α × LowerSet α) :=
  cutLowerSetEquiv.prodCongr cutLowerSetEquiv

/-- Each rectangle maps to the product of its two decorated coordinate images. -/
theorem image_rectangleCell (a b c d : α) :
    rectangleLowerSetEquiv '' rectangleCell a b c d =
      (cutLowerSet '' cutCell a b) ×ˢ (cutLowerSet '' cutCell c d) :=
  Set.prodMap_image_prod cutLowerSet cutLowerSet _ _

/-- Decorated rectangles are compact, with all four boundary decorations retained. -/
theorem isCompact_image_rectangleCell [TopologicalSpace (LowerSet α)]
    [OrderTopology (LowerSet α)] (a b c d : α) :
    IsCompact (rectangleLowerSetEquiv '' rectangleCell a b c d) := by
  rw [image_rectangleCell]
  exact (isCompact_image_cutCell a b).prod (isCompact_image_cutCell c d)

/-- Decorated rectangles are open, so containing zero-content cells give open covers. -/
theorem isOpen_image_rectangleCell [TopologicalSpace (LowerSet α)]
    [OrderTopology (LowerSet α)] (a b c d : α) :
    IsOpen (rectangleLowerSetEquiv '' rectangleCell a b c d) := by
  rw [image_rectangleCell]
  exact (isOpen_image_cutCell a b).prod (isOpen_image_cutCell c d)

/-- An inward endpoint refinement separates distinct cuts in a containing cell. -/
theorem exists_subcell_separating_cuts {x y : Cut α} (hxy : x ≠ y) {a b : α}
    (hx : x ∈ cutCell a b) :
    ∃ a' b', a ≤ a' ∧ b' ≤ b ∧ x ∈ cutCell a' b' ∧ y ∉ cutCell a' b' := by
  classical
  have hex : ∃ t, (t ∈ x.lower ∧ t ∉ y.lower) ∨ (t ∈ y.lower ∧ t ∉ x.lower) := by
    by_contra hn
    apply hxy
    apply cut_eq_of_lower_eq
    ext t
    constructor
    · intro ht
      by_contra ht'
      exact hn ⟨t, Or.inl ⟨ht, ht'⟩⟩
    · intro ht
      by_contra ht'
      exact hn ⟨t, Or.inr ⟨ht, ht'⟩⟩
  obtain ⟨t, ht | ht⟩ := hex
  · refine ⟨max a t, b, le_max_left _ _, le_rfl, ⟨?_, hx.2⟩, ?_⟩
    · rcases le_total a t with hat | hta
      · simpa only [max_eq_right hat] using ht.1
      · simpa only [max_eq_left hta] using hx.1
    · exact fun hy => ht.2 (Cut.lower_of_le (le_max_right _ _) hy.1)
  · have htx : t ∈ x.upper := (x.mem_lower_or_upper t).resolve_left ht.2
    refine ⟨a, min b t, le_rfl, min_le_left _ _, ⟨hx.1, ?_⟩, ?_⟩
    · rcases le_total b t with hbt | htb
      · simpa only [min_eq_left hbt] using hx.2
      · simpa only [min_eq_right htb] using htx
    · exact fun hy => Cut.not_mem_upper ht.1 (Cut.upper_of_le (min_le_right _ _) hy.2)

/-- A source rectangle containing one cut pair can be refined to exclude any distinct pair. -/
theorem exists_rectangleCell_separating {p q : Cut α × Cut α} (hpq : p ≠ q)
    {a b c d : α} (hbc : b < c) (hp : p ∈ rectangleCell a b c d) :
    ∃ U ∈ separatedRectangleCells, p ∈ U ∧ q ∉ U := by
  classical
  by_cases hfst : p.1 = q.1
  · have hsnd : p.2 ≠ q.2 := fun h => hpq (Prod.ext hfst h)
    obtain ⟨c', d', hcc', _, hp', hq'⟩ := exists_subcell_separating_cuts hsnd hp.2
    refine ⟨rectangleCell a b c' d', rectangleCell_mem_separatedRectangleCells _ _ _ _
      (hbc.trans_le hcc'), ⟨hp.1, hp'⟩, ?_⟩
    exact fun hq => hq' hq.2
  · obtain ⟨a', b', _, hb'b, hp', hq'⟩ := exists_subcell_separating_cuts hfst hp.1
    refine ⟨rectangleCell a' b' c d, rectangleCell_mem_separatedRectangleCells _ _ _ _
      (hb'b.trans_lt hbc), ⟨hp', hp.2⟩, ?_⟩
    exact fun hq => hq' hq.1

end TDA.Persistence.RectangleMeasure
