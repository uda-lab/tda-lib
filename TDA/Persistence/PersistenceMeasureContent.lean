import TDA.Persistence.PersistenceMeasureBoxContent
import TDA.Persistence.DecoratedRectangleBox
import Mathlib.MeasureTheory.Measure.AddContent

/-!
# The additive content constructed from a q-tame module

The value on a nonempty decorated rectangle is its actual module quotient dimension.
Every finite disjoint rectangle cover induces an ordinary box partition by taking
preimages along the two minus cuts. The proved box-partition theorem then establishes
mathlib's full additive-content law, without assuming a finite-tiling certificate.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open BoxIntegral Set MeasureTheory
open scoped Classical

/-- Choose the unique ordinary box of a nonempty rectangle; other sets get a default. -/
noncomputable def rectangleCellBox (U : Set (Cut ℝ × Cut ℝ)) : Box (Fin 2) :=
  if h : ∃ I : Box (Fin 2), U = boxRectangleCell I then h.choose else default

/-- Choosing a box from its decorated rectangle recovers that box. -/
theorem rectangleCellBox_boxRectangleCell (I : Box (Fin 2)) :
    rectangleCellBox (boxRectangleCell I) = I := by
  have h : ∃ J : Box (Fin 2), boxRectangleCell I = boxRectangleCell J := ⟨I, rfl⟩
  simp only [rectangleCellBox, h, dif_pos]
  exact (boxRectangleCell_injective h.choose_spec).symm

/-- The chosen box recovers every nonempty source rectangle exactly. -/
theorem boxRectangleCell_rectangleCellBox {U : Set (Cut ℝ × Cut ℝ)}
    (hU : U ∈ separatedRectangleCells) (hne : U ≠ ∅) :
    U = boxRectangleCell (rectangleCellBox U) := by
  obtain ⟨I, _, rfl⟩ := exists_boxRectangleCell hU hne
  rw [rectangleCellBox_boxRectangleCell]

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- The actual module quotient dimension on nonempty rectangles, with zero at the empty set. -/
noncomputable def moduleRectangleValue (U : Set (Cut ℝ × Cut ℝ)) : ℕ :=
  if U = ∅ then 0 else persistenceBoxValue M (rectangleCellBox U)

/-- The empty rectangle has zero content. -/
theorem moduleRectangleValue_empty : moduleRectangleValue M ∅ = 0 := by
  simp [moduleRectangleValue]

/-- A nonempty rectangle's value is the actual persistence box value. -/
theorem moduleRectangleValue_boxRectangleCell (I : Box (Fin 2)) :
    moduleRectangleValue M (boxRectangleCell I) = persistenceBoxValue M I := by
  rw [moduleRectangleValue, if_neg (boxRectangleCell_nonempty I).ne_empty,
    rectangleCellBox_boxRectangleCell]

/-- Q-tameness constructs an actual natural-valued additive content on decorated rectangles. -/
noncomputable def moduleRectangleContent (hM : M.QTame) :
    AddContent ℕ (separatedRectangleCells (α := ℝ)) where
  toFun := moduleRectangleValue M
  empty' := moduleRectangleValue_empty M
  sUnion' S hSC hdis hUnion := by
    classical
    by_cases hzero : ⋃₀ (S : Set (Set (Cut ℝ × Cut ℝ))) = ∅
    · rw [hzero, moduleRectangleValue_empty]
      symm
      apply Finset.sum_eq_zero
      intro U hU
      have hUzero : U = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        have hx' := mem_sUnion.mpr ⟨U, hU, hx⟩
        rw [hzero] at hx'
        exact hx')
      rw [hUzero, moduleRectangleValue_empty]
    · obtain ⟨I, hIgap, hI⟩ := exists_boxRectangleCell hUnion hzero
      let S' := S.erase ∅
      have hsource : ∀ U ∈ S', U = boxRectangleCell (rectangleCellBox U) := by
        intro U hU
        have hh := Finset.mem_erase.mp hU
        exact boxRectangleCell_rectangleCellBox (hSC hh.2) hh.1
      let π : Prepartition I := {
        boxes := S'.image rectangleCellBox
        le_of_mem' := by
          intro J hJ
          obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hJ
          change (rectangleCellBox U : Set (Fin 2 → ℝ)) ⊆ (I : Set (Fin 2 → ℝ))
          rw [← preimage_boxRectangleCell, ← preimage_boxRectangleCell,
            ← hsource U hU, ← hI]
          exact preimage_mono (subset_sUnion_of_mem (Finset.mem_erase.mp hU).2)
        pairwiseDisjoint := by
          intro J hJ L hL hJL
          obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hJ
          obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hL
          have hUV : U ≠ V := fun h => hJL (congrArg rectangleCellBox h)
          have hd := hdis (Finset.mem_erase.mp hU).2 (Finset.mem_erase.mp hV).2 hUV
          change Disjoint (rectangleCellBox U : Set (Fin 2 → ℝ))
            (rectangleCellBox V : Set (Fin 2 → ℝ))
          rw [← preimage_boxRectangleCell, ← preimage_boxRectangleCell,
            ← hsource U hU, ← hsource V hV]
          exact hd.preimage minusCutPair }
      have hπ : π.IsPartition := by
        intro x hx
        change x ∈ (I : Set (Fin 2 → ℝ)) at hx
        rw [← preimage_boxRectangleCell I, ← hI] at hx
        obtain ⟨U, hUS, hxU⟩ := mem_sUnion.mp hx
        have hUne : U ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨minusCutPair x, hxU⟩
        have hU : U ∈ S' := Finset.mem_erase.mpr ⟨hUne, hUS⟩
        refine ⟨rectangleCellBox U, Finset.mem_image.mpr ⟨U, hU, rfl⟩, ?_⟩
        change x ∈ (rectangleCellBox U : Set (Fin 2 → ℝ))
        rw [← preimage_boxRectangleCell, ← hsource U hU]
        exact hxU
      have hInject : Set.InjOn rectangleCellBox (S' : Set (Set (Cut ℝ × Cut ℝ))) := by
        intro U hU V hV hUV
        rw [hsource U hU, hsource V hV, hUV]
      have hsumBoxes : ∑ J ∈ π.boxes, persistenceBoxValue M J =
          ∑ U ∈ S', moduleRectangleValue M U := by
        change ∑ J ∈ S'.image rectangleCellBox, persistenceBoxValue M J = _
        rw [Finset.sum_image hInject]
        apply Finset.sum_congr rfl
        intro U hU
        rw [hsource U hU, moduleRectangleValue_boxRectangleCell,
          rectangleCellBox_boxRectangleCell]
      have hsumErase : ∑ U ∈ S', moduleRectangleValue M U =
          ∑ U ∈ S, moduleRectangleValue M U := by
        apply Finset.sum_subset (Finset.erase_subset _ _)
        intro U hUS hUnot
        have hUzero : U = ∅ := by
          by_contra hne
          exact hUnot (Finset.mem_erase.mpr ⟨hne, hUS⟩)
        rw [hUzero, moduleRectangleValue_empty]
      calc moduleRectangleValue M (⋃₀ (S : Set (Set (Cut ℝ × Cut ℝ)))) =
              persistenceBoxValue M I := by rw [hI, moduleRectangleValue_boxRectangleCell]
        _ = ∑ J ∈ π.boxes, persistenceBoxValue M J :=
          (persistenceBoxValue_sum_partition M hM I hIgap π hπ).symm
        _ = ∑ U ∈ S', moduleRectangleValue M U := hsumBoxes
        _ = ∑ U ∈ S, moduleRectangleValue M U := hsumErase

/-- The constructed content evaluates to the module's quotient dimension on every strict
separated rectangle. -/
theorem moduleRectangleContent_apply (hM : M.QTame) (a b c d : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    moduleRectangleContent M hM (rectangleCell a b c d) =
      persistenceMeasureValue M hab.le hbc.le hcd.le := by
  change moduleRectangleValue M (boxRectangleCell (rectangleBox a b c d hab hcd)) = _
  rw [moduleRectangleValue_boxRectangleCell, persistenceBoxValue_of_separated _ _ hbc]
  rfl

end TDA.Persistence.RectangleMeasure
