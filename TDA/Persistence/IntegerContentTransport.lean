import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.Tactic

/-!
# Transport of additive contents

Taking preimages transports finite disjoint covers. An integer-valued content which is
nonnegative on its cells also gives a natural-valued content. These constructions will be
applied to the signed primitive of the module's essential birth-strip measure.
-/

universe v w

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory

/-- Preimages along a function transport actual additive contents between cell families. -/
noncomputable def preimageContent {X : Type v} {Y : Type w} {G : Type*} [AddCommMonoid G]
    {C : Set (Set Y)} {D : Set (Set X)} (m : AddContent G C) (g : Y → X)
    (hD : ∀ U ∈ D, g ⁻¹' U ∈ C) : AddContent G D where
  toFun U := m (g ⁻¹' U)
  empty' := by simp
  sUnion' S hSC hdis hUnion := by
    rw [preimage_sUnion]
    apply addContent_biUnion
    · exact fun U hU => hD U (hSC hU)
    · intro U hU V hV hUV
      exact (hdis hU hV hUV).preimage g
    · simpa only [preimage_sUnion, Finset.mem_coe] using hD _ hUnion

/-- Transported values are the original content of the preimage. -/
theorem preimageContent_apply {X : Type v} {Y : Type w} {G : Type*} [AddCommMonoid G]
    {C : Set (Set Y)} {D : Set (Set X)} (m : AddContent G C) (g : Y → X)
    (hD : ∀ U ∈ D, g ⁻¹' U ∈ C) (U : Set X) :
    preimageContent m g hD U = m (g ⁻¹' U) := rfl

/-- A cellwise nonnegative integer content is an actual natural-valued additive content. -/
noncomputable def naturalContentOfNonnegative {X : Type v} {C : Set (Set X)}
    (m : AddContent ℤ C) (hm : ∀ U ∈ C, 0 ≤ m U) : AddContent ℕ C where
  toFun U := (m U).toNat
  empty' := by simp
  sUnion' S hSC hdis hUnion := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg (hm _ hUnion)]
    simp only [Nat.cast_sum]
    rw [addContent_sUnion hSC hdis hUnion]
    exact Finset.sum_congr rfl fun U hU => (Int.toNat_of_nonneg (hm U (hSC hU))).symm

/-- Converting a nonnegative integer content keeps its natural value. -/
theorem naturalContentOfNonnegative_apply {X : Type v} {C : Set (Set X)}
    (m : AddContent ℤ C) (hm : ∀ U ∈ C, 0 ≤ m U) (U : Set X) :
    naturalContentOfNonnegative m hm U = (m U).toNat := rfl

end TDA.Persistence.RectangleMeasure
