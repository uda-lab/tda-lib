import TDA.Persistence.DecoratedMeasureCuts
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic

/-!
# Finite decorated cells as a semiring

The cut-membership convention preserves endpoints under intersections, differences and
splitting. The resulting one-dimensional cells form a set semiring. These are the actual
coordinate cells of persistence rectangles, rather than intervals with forgotten ticks.
-/

universe v

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory

variable {α : Type v} [LinearOrder α]

private theorem max_mem_lower (q : Cut α) (a b : α) :
    max a b ∈ q.lower ↔ a ∈ q.lower ∧ b ∈ q.lower := by
  constructor
  · exact fun h => ⟨Cut.lower_of_le (le_max_left _ _) h,
      Cut.lower_of_le (le_max_right _ _) h⟩
  · rintro ⟨ha, hb⟩
    rcases le_total a b with hab | hba
    · simpa only [max_eq_right hab] using hb
    · simpa only [max_eq_left hba] using ha

private theorem min_mem_upper (q : Cut α) (a b : α) :
    min a b ∈ q.upper ↔ a ∈ q.upper ∧ b ∈ q.upper := by
  constructor
  · exact fun h => ⟨Cut.upper_of_le (min_le_left _ _) h,
      Cut.upper_of_le (min_le_right _ _) h⟩
  · rintro ⟨ha, hb⟩
    rcases le_total a b with hab | hba
    · simpa only [min_eq_left hab] using ha
    · simpa only [min_eq_right hba] using hb

/-- Cells whose endpoint order is reversed are empty. -/
theorem cutCell_eq_empty {a b : α} (h : b ≤ a) : cutCell a b = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun q hq => (not_lt_of_ge h) (lt_of_mem_cutCell hq)

/-- Intersecting cells retains the larger lower endpoint and smaller upper endpoint. -/
theorem cutCell_inter (a b c d : α) :
    cutCell a b ∩ cutCell c d = cutCell (max a c) (min b d) := by
  ext q
  change ((a ∈ q.lower ∧ b ∈ q.upper) ∧ (c ∈ q.lower ∧ d ∈ q.upper)) ↔ _
  rw [show q ∈ cutCell (max a c) (min b d) ↔
    (a ∈ q.lower ∧ c ∈ q.lower) ∧ (b ∈ q.upper ∧ d ∈ q.upper) by
      exact and_congr (max_mem_lower q a c) (min_mem_upper q b d)]
  tauto

/-- Subtracting a cell gives the two remaining endpoint strips. -/
theorem cutCell_sdiff (a b c d : α) :
    cutCell a b \ cutCell c d =
      cutCell a (min b c) ∪ cutCell (max a d) b := by
  ext q
  change ((a ∈ q.lower ∧ b ∈ q.upper) ∧ ¬ (c ∈ q.lower ∧ d ∈ q.upper)) ↔ _
  change _ ↔ (a ∈ q.lower ∧ min b c ∈ q.upper) ∨
    (max a d ∈ q.lower ∧ b ∈ q.upper)
  rw [min_mem_upper, max_mem_lower, cut_upper_eq_compl q]
  simp only [mem_compl_iff]
  tauto

/-- The two difference strips are disjoint when the removed cell has ordered endpoints. -/
theorem disjoint_cutCell_sdiff_strips (a b : α) {c d : α} (hcd : c ≤ d) :
    Disjoint (cutCell a (min b c)) (cutCell (max a d) b) := by
  apply Set.disjoint_left.mpr
  intro q hq hq'
  have hc : c ∈ q.upper := Cut.upper_of_le (min_le_right _ _) hq.2
  have hd : d ∈ q.lower := Cut.lower_of_le (le_max_right _ _) hq'.1
  exact (not_lt_of_ge hcd) (q.lower_lt_upper hd hc)

/-- A split assigns each decorated cut to exactly one child cell. -/
theorem cutCell_split {a e b : α} (hae : a ≤ e) (heb : e ≤ b) :
    cutCell a b = cutCell a e ∪ cutCell e b := by
  ext q
  constructor
  · intro hq
    rcases q.mem_lower_or_upper e with he | he
    · exact Or.inr ⟨he, hq.2⟩
    · exact Or.inl ⟨hq.1, he⟩
  · rintro (hq | hq)
    · exact ⟨hq.1, Cut.upper_of_le heb hq.2⟩
    · exact ⟨Cut.lower_of_le hae hq.1, hq.2⟩

/-- The two cells of a split are disjoint, including at the decorated boundary. -/
theorem disjoint_cutCell_split (a e b : α) : Disjoint (cutCell a e) (cutCell e b) := by
  apply Set.disjoint_left.mpr
  intro q hl hr
  exact Cut.not_mem_upper hr.1 hl.2

/-- Finite decorated cells, including the empty cell. -/
def cutCells : Set (Set (Cut α)) :=
  {U | ∃ a b, a ≤ b ∧ U = cutCell a b}

/-- Every endpoint pair defines a member, after normalizing an empty cell if necessary. -/
theorem cutCell_mem_cutCells (a b : α) : cutCell a b ∈ cutCells := by
  refine ⟨a, max a b, le_max_left _ _, ?_⟩
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
  · rw [cutCell_eq_empty hba, max_eq_left hba, cutCell_eq_empty le_rfl]

/-- Decorated coordinate cells satisfy the finite disjoint-difference semiring laws. -/
theorem isSetSemiring_cutCells [Nonempty α] : IsSetSemiring (cutCells (α := α)) where
  empty_mem := by
    inhabit α
    exact ⟨default, default, le_rfl, (cutCell_eq_empty le_rfl).symm⟩
  inter_mem := by
    rintro U ⟨a, b, _, rfl⟩ V ⟨c, d, _, rfl⟩
    rw [cutCell_inter]
    exact cutCell_mem_cutCells _ _
  sdiff_eq_sUnion' := by
    classical
    rintro U ⟨a, b, _, rfl⟩ V ⟨c, d, hcd, rfl⟩
    refine ⟨{cutCell a (min b c), cutCell (max a d) b}, ?_, ?_, ?_⟩
    · intro W hW
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl <;> exact cutCell_mem_cutCells _ _
    · intro W hW Z hZ hWZ
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hW hZ
      rcases hW with rfl | rfl <;> rcases hZ with rfl | rfl
      · exact (hWZ rfl).elim
      · exact disjoint_cutCell_sdiff_strips a b hcd
      · exact (disjoint_cutCell_sdiff_strips a b hcd).symm
      · exact (hWZ rfl).elim
    · simpa only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton]
        using cutCell_sdiff a b c d

/-- A finite persistence rectangle consists of two decorated coordinate cells. -/
def rectangleCell (a b c d : α) : Set (Cut α × Cut α) :=
  cutCell a b ×ˢ cutCell c d

/-- The finite rectangles lying strictly above the persistence diagonal, and the empty set. -/
def separatedRectangleCells : Set (Set (Cut α × Cut α)) :=
  {U | U = ∅ ∨ ∃ a b c d, a < b ∧ b < c ∧ c < d ∧ U = rectangleCell a b c d}

/-- Separated endpoint pairs define a rectangle cell even if one coordinate is empty. -/
theorem rectangleCell_mem_separatedRectangleCells (a b c d : α) (hbc : b < c) :
    rectangleCell a b c d ∈ separatedRectangleCells := by
  by_cases hab : a < b
  · by_cases hcd : c < d
    · exact Or.inr ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
    · exact Or.inl (by simp [rectangleCell, cutCell_eq_empty (le_of_not_gt hcd)])
  · exact Or.inl (by simp [rectangleCell, cutCell_eq_empty (le_of_not_gt hab)])

/-- Rectangle intersection retains the four inward-facing endpoints. -/
theorem rectangleCell_inter (a b c d e f g h : α) :
    rectangleCell a b c d ∩ rectangleCell e f g h =
      rectangleCell (max a e) (min b f) (max c g) (min d h) := by
  simp only [rectangleCell, prod_inter_prod, cutCell_inter]

/-- The disjoint strips in a rectangle difference retain all boundary decorations. -/
theorem rectangleCell_sdiff (a b c d e f g h : α) :
    rectangleCell a b c d \ rectangleCell e f g h =
      (rectangleCell a (min b e) c d ∪ rectangleCell (max a f) b c d) ∪
      (rectangleCell (max a e) (min b f) c (min d g) ∪
       rectangleCell (max a e) (min b f) (max c h) d) := by
  have hprod : (cutCell a b ×ˢ cutCell c d) \ (cutCell e f ×ˢ cutCell g h) =
      ((cutCell a b \ cutCell e f) ×ˢ cutCell c d) ∪
      ((cutCell a b ∩ cutCell e f) ×ˢ (cutCell c d \ cutCell g h)) := by
    ext p
    simp only [mem_sdiff, mem_prod, mem_union, mem_inter_iff]
    tauto
  simp only [rectangleCell, hprod, cutCell_sdiff, cutCell_inter, union_prod, prod_union]

/-- Separated decorated rectangles form a semiring, with finite disjoint strip differences. -/
theorem isSetSemiring_separatedRectangleCells :
    IsSetSemiring (separatedRectangleCells (α := α)) where
  empty_mem := Or.inl rfl
  inter_mem := by
    rintro U (rfl | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩)
      V (rfl | ⟨e, f, g, h, hef, hfg, hgh, rfl⟩)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · rw [rectangleCell_inter]
      exact rectangleCell_mem_separatedRectangleCells _ _ _ _
        ((min_le_left _ _).trans_lt (hbc.trans_le (le_max_left _ _)))
  sdiff_eq_sUnion' := by
    classical
    rintro U (rfl | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩)
      V (rfl | ⟨e, f, g, h, hef, hfg, hgh, rfl⟩)
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    · exact ⟨{rectangleCell a b c d}, by simpa using
        rectangleCell_mem_separatedRectangleCells a b c d hbc, by simp, by simp⟩
    · let R₁ := rectangleCell a (min b e) c d
      let R₂ := rectangleCell (max a f) b c d
      let R₃ := rectangleCell (max a e) (min b f) c (min d g)
      let R₄ := rectangleCell (max a e) (min b f) (max c h) d
      have hL : Disjoint (cutCell a (min b e)) (cutCell (max a e) (min b f)) := by
        apply Set.disjoint_left.mpr
        intro q hq hq'
        exact Cut.not_mem_upper (Cut.lower_of_le (le_max_right _ _) hq'.1)
          (Cut.upper_of_le (min_le_right _ _) hq.2)
      have hR : Disjoint (cutCell (max a f) b) (cutCell (max a e) (min b f)) := by
        apply Set.disjoint_left.mpr
        intro q hq hq'
        exact Cut.not_mem_upper (Cut.lower_of_le (le_max_right _ _) hq.1)
          (Cut.upper_of_le (min_le_right _ _) hq'.2)
      have h12 : Disjoint R₁ R₂ := disjoint_prod.mpr
        (Or.inl (disjoint_cutCell_sdiff_strips a b hef.le))
      have h13 : Disjoint R₁ R₃ := disjoint_prod.mpr (Or.inl hL)
      have h14 : Disjoint R₁ R₄ := disjoint_prod.mpr (Or.inl hL)
      have h23 : Disjoint R₂ R₃ := disjoint_prod.mpr (Or.inl hR)
      have h24 : Disjoint R₂ R₄ := disjoint_prod.mpr (Or.inl hR)
      have h34 : Disjoint R₃ R₄ := disjoint_prod.mpr
        (Or.inr (disjoint_cutCell_sdiff_strips c d hgh.le))
      refine ⟨{R₁, R₂, R₃, R₄}, ?_, ?_, ?_⟩
      · intro W hW
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hW
        rcases hW with rfl | rfl | rfl | rfl
        · exact rectangleCell_mem_separatedRectangleCells _ _ _ _ ((min_le_left _ _).trans_lt hbc)
        · exact rectangleCell_mem_separatedRectangleCells _ _ _ _ hbc
        · exact rectangleCell_mem_separatedRectangleCells _ _ _ _ ((min_le_left _ _).trans_lt hbc)
        · exact rectangleCell_mem_separatedRectangleCells _ _ _ _
            ((min_le_left _ _).trans_lt (hbc.trans_le (le_max_left _ _)))
      · intro W hW Z hZ hWZ
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hW hZ
        rcases hW with rfl | rfl | rfl | rfl <;>
          rcases hZ with rfl | rfl | rfl | rfl
        all_goals first
          | exact (hWZ rfl).elim
          | exact h12
          | exact h13
          | exact h14
          | exact h23
          | exact h24
          | exact h34
          | exact h12.symm
          | exact h13.symm
          | exact h14.symm
          | exact h23.symm
          | exact h24.symm
          | exact h34.symm
      · simpa only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton,
          union_assoc] using rectangleCell_sdiff a b c d e f g h

end TDA.Persistence.RectangleMeasure
