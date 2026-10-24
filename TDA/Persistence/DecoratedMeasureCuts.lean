import TDA.Persistence.CutSubspaces
import Mathlib.Order.UpperLower.Principal
import Mathlib.Topology.Order.Compact

/-!
# Decorated cuts and compact rectangle cells

The existing persistence cut is equivalent to mathlib's bundled lower set. The latter
already carries a complete linear order. A decorated interval cell, expressed by
membership of its two real endpoints in the two parts of a cut, becomes both a closed
and an open interval of that complete order. Its compactness preserves the boundary
decorations needed by the persistence-measure representation theorem.
-/

universe v

namespace TDA.Persistence.RectangleMeasure

open Set

variable {α : Type v} [LinearOrder α]

/-- The initial part of a persistence cut, as a bundled lower set. -/
def cutLowerSet (c : Cut α) : LowerSet α :=
  ⟨c.lower, fun _ _ h ht => Cut.lower_of_le h ht⟩

/-- A lower set determines the complementary final part of a cut. -/
def cutOfLowerSet (s : LowerSet α) : Cut α where
  lower := s
  upper := (s : Set α)ᶜ
  mem_lower_or_upper t := Classical.em (t ∈ s)
  lower_lt_upper := by
    intro a b ha hb
    exact lt_of_not_ge fun hba => hb (s.lower hba ha)

/-- The final part of a cut is determined by its initial part. -/
theorem cut_upper_eq_compl (c : Cut α) : c.upper = c.lowerᶜ := by
  ext t
  constructor
  · exact fun ht hl => Cut.not_mem_upper hl ht
  · exact fun ht => (c.mem_lower_or_upper t).resolve_left ht

/-- Equality of initial parts determines equality of cuts. -/
theorem cut_eq_of_lower_eq {c d : Cut α} (h : c.lower = d.lower) : c = d := by
  have hu : c.upper = d.upper := by
    rw [cut_upper_eq_compl, cut_upper_eq_compl, h]
  rcases c with ⟨cl, cu, cp, co⟩
  rcases d with ⟨dl, du, dp, do'⟩
  cases h
  cases hu
  rfl

/-- Bundling and unbundling an initial part preserves it. -/
@[simp] theorem cutLowerSet_cutOfLowerSet (s : LowerSet α) :
    cutLowerSet (cutOfLowerSet s) = s := by
  apply LowerSet.ext
  rfl

/-- A cut is recovered from its bundled initial part. -/
@[simp] theorem cutOfLowerSet_cutLowerSet (c : Cut α) :
    cutOfLowerSet (cutLowerSet c) = c :=
  cut_eq_of_lower_eq rfl

/-- Persistence cuts use the existing complete lower-set order without a competing cut type. -/
def cutLowerSetEquiv : Cut α ≃ LowerSet α where
  toFun := cutLowerSet
  invFun := cutOfLowerSet
  left_inv := cutOfLowerSet_cutLowerSet
  right_inv := cutLowerSet_cutOfLowerSet

/-- The minus decoration: a closed birth or open death at the parameter. -/
def minusCut (a : α) : Cut α where
  lower := Iio a
  upper := Ici a
  mem_lower_or_upper t := lt_or_ge t a
  lower_lt_upper := fun hs ht => hs.trans_le ht

/-- The plus decoration: an open birth or closed death at the parameter. -/
def plusCut (a : α) : Cut α where
  lower := Iic a
  upper := Ioi a
  mem_lower_or_upper t := le_or_gt t a
  lower_lt_upper := fun hs ht => hs.trans_lt ht

/-- The initial part of the minus cut is the open principal lower set. -/
@[simp] theorem cutLowerSet_minusCut (a : α) :
    cutLowerSet (minusCut a) = LowerSet.Iio a := by
  apply LowerSet.ext
  rfl

/-- The initial part of the plus cut is the closed principal lower set. -/
@[simp] theorem cutLowerSet_plusCut (a : α) :
    cutLowerSet (plusCut a) = LowerSet.Iic a := by
  apply LowerSet.ext
  rfl

/-- A decorated cell uses the same cut-membership convention in either coordinate. -/
def cutCell (a b : α) : Set (Cut α) :=
  {c | a ∈ c.lower ∧ b ∈ c.upper}

/-- The two endpoint memberships of a cut force a nondegenerate underlying interval. -/
theorem lt_of_mem_cutCell {a b : α} {c : Cut α} (hc : c ∈ cutCell a b) : a < b :=
  c.lower_lt_upper hc.1 hc.2

/-- A decorated cell is a closed interval in the complete cut line. -/
theorem image_cutCell_eq_Icc (a b : α) :
    cutLowerSet '' cutCell a b = Icc (LowerSet.Iic a) (LowerSet.Iio b) := by
  ext s
  constructor
  · rintro ⟨c, hc, rfl⟩
    constructor
    · exact LowerSet.Iic_le.mpr hc.1
    · intro t ht
      exact c.lower_lt_upper ht hc.2
  · intro hs
    refine ⟨cutOfLowerSet s, ⟨?_, ?_⟩, cutLowerSet_cutOfLowerSet s⟩
    · exact LowerSet.Iic_le.mp hs.1
    · intro hb
      exact lt_irrefl b (hs.2 hb)

private theorem iio_lt_iic (a : α) : LowerSet.Iio a < LowerSet.Iic a := by
  apply lt_of_le_not_ge
  · intro t ht
    exact ht.le
  · intro h
    have ha : a < a := h (show a ∈ LowerSet.Iic a from le_rfl)
    exact lt_irrefl a ha

/-- Membership is also a strict interval between the adjacent principal cuts. -/
theorem image_cutCell_eq_Ioo (a b : α) :
    cutLowerSet '' cutCell a b = Ioo (LowerSet.Iio a) (LowerSet.Iic b) := by
  rw [image_cutCell_eq_Icc]
  ext s
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · exact (iio_lt_iic a).trans_le ha
    · exact hb.trans_lt (iio_lt_iic b)
  · rintro ⟨ha, hb⟩
    constructor
    · apply LowerSet.Iic_le.mpr
      by_contra h
      have hs : s ≤ LowerSet.Iio a := by
        intro t ht
        exact lt_of_not_ge fun hat => h (s.lower hat ht)
      exact (not_le_of_gt ha) hs
    · intro t ht
      by_contra h
      have hbt : b ≤ t := le_of_not_gt h
      have hb' : b ∈ s := s.lower hbt ht
      exact (not_le_of_gt hb) (LowerSet.Iic_le.mpr hb')

/-- Decorated cells are compact in the complete cut-line order topology. -/
theorem isCompact_image_cutCell [TopologicalSpace (LowerSet α)]
    [OrderTopology (LowerSet α)] (a b : α) :
    IsCompact (cutLowerSet '' cutCell a b) := by
  rw [image_cutCell_eq_Icc]
  exact isCompact_Icc

/-- Decorated cells are open as well, so compactness applies to zero-mass cell covers. -/
theorem isOpen_image_cutCell [TopologicalSpace (LowerSet α)]
    [OrderTopology (LowerSet α)] (a b : α) :
    IsOpen (cutLowerSet '' cutCell a b) := by
  rw [image_cutCell_eq_Ioo]
  exact isOpen_Ioo

end TDA.Persistence.RectangleMeasure
