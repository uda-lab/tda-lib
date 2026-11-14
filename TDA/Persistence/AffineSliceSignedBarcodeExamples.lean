import TDA.Persistence.AffineSliceExamples
import TDA.Persistence.AffineSliceSignedBarcode
import TDA.Persistence.RankSignedNontriangle
import Mathlib.Tactic

/-!
# Cancellation examples for positive affine slices

The actual finitely presented staircase supplies a nonempty cancellation:
different principal hooks restrict to repeated essential intervals. The
remaining examples retain finite intervals, omitted nonzero hooks, and the
empty original presentation. Cancellation here concerns endpoint multisets.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.AffineSliceSignedBarcodeExamples

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence

private def diagonalLine : PositiveAffineLine 2 where
  offset _ := 0
  slope _ := 1
  slope_pos _ := by norm_num

private theorem diagonal_entrance (p : Fin 2 → ℝ) :
    diagonalLine.entrance p = max (p 0) (p 1) := by
  apply le_antisymm
  · apply (diagonalLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i
    · simp [PositiveAffineLine.orderHom_apply, diagonalLine]
    · simp [PositiveAffineLine.orderHom_apply, diagonalLine]
  · apply max_le
    · simpa only [diagonalLine, sub_zero, div_one] using diagonalLine.normalizedDifference_le_entrance p 0
    · simpa only [diagonalLine, sub_zero, div_one] using diagonalLine.normalizedDifference_le_entrance p 1

private def tiltedLine : PositiveAffineLine 2 where
  offset _ := 0
  slope i := if i = 0 then 1 else 2
  slope_pos i := by fin_cases i <;> norm_num

private theorem tilted_entrance (p : Fin 2 → ℝ) :
    tiltedLine.entrance p = max (p 0) (p 1 / 2) := by
  apply le_antisymm
  · apply (tiltedLine.entrance_le_iff _ _).mpr
    intro i
    fin_cases i
    · simp [PositiveAffineLine.orderHom_apply, tiltedLine]
    · have h := le_max_right (p 0) (p 1 / 2)
      norm_num [PositiveAffineLine.orderHom_apply, tiltedLine]
      linarith
  · apply max_le
    · simpa [tiltedLine] using tiltedLine.normalizedDifference_le_entrance p 0
    · simpa [tiltedLine] using tiltedLine.normalizedDifference_le_entrance p 1

private abbrev essential (b : ℝ) : ℝ × WithTop ℝ := (b, ⊤)

private theorem diagonal_even :
    diagonalLine.sliceHookMultiset signedStaircaseCenter.positive =
      {essential 3} + {essential 2} + {essential 2} + {essential 3} := by
  classical
  simp only [signedStaircaseCenter, hookTagMultiset,
    PositiveAffineLine.sliceHookMultiset_add, PositiveAffineLine.sliceHookMultiset_singleton,
    PositiveAffineLine.sliceHookMultiset_zero, PositiveAffineLine.hookEndpoints_principal,
    Option.toList_some]
  norm_num [diagonal_entrance, signedStaircaseVertices, essential]
  all_goals
    ext p
    simp only [Multiset.count_cons, Multiset.count_singleton]
    omega

private theorem diagonal_odd :
    diagonalLine.sliceHookMultiset signedStaircaseCenter.negative =
      {essential 3} + {essential 2} + {essential 3} := by
  classical
  simp only [signedStaircaseCenter, hookTagMultiset,
    PositiveAffineLine.sliceHookMultiset_add, PositiveAffineLine.sliceHookMultiset_singleton,
    PositiveAffineLine.sliceHookMultiset_zero, PositiveAffineLine.hookEndpoints_principal,
    Option.toList_some]
  norm_num [diagonal_entrance, signedStaircaseJoins, essential]
  all_goals
    ext p
    simp only [Multiset.count_cons, Multiset.count_singleton]
    omega

private theorem tilted_even :
    tiltedLine.sliceHookMultiset signedStaircaseCenter.positive =
      {essential (3 / 2)} + {essential 1} + {essential 2} + {essential 3} := by
  classical
  simp only [signedStaircaseCenter, hookTagMultiset,
    PositiveAffineLine.sliceHookMultiset_add, PositiveAffineLine.sliceHookMultiset_singleton,
    PositiveAffineLine.sliceHookMultiset_zero, PositiveAffineLine.hookEndpoints_principal,
    Option.toList_some]
  norm_num [tilted_entrance, signedStaircaseVertices, essential]
  all_goals
    ext p
    simp only [Multiset.count_cons, Multiset.count_singleton]
    omega

private theorem tilted_odd :
    tiltedLine.sliceHookMultiset signedStaircaseCenter.negative =
      {essential (3 / 2)} + {essential 2} + {essential 3} := by
  classical
  simp only [signedStaircaseCenter, hookTagMultiset,
    PositiveAffineLine.sliceHookMultiset_add, PositiveAffineLine.sliceHookMultiset_singleton,
    PositiveAffineLine.sliceHookMultiset_zero, PositiveAffineLine.hookEndpoints_principal,
    Option.toList_some]
  norm_num [tilted_entrance, signedStaircaseJoins, essential]
  all_goals
    ext p
    simp only [Multiset.count_cons, Multiset.count_singleton]
    omega

/-- The nonempty odd part shares two copies of `[3,∞)` with the even part;
the repeated even interval `[2,∞)` also retains its multiplicity. -/
theorem staircase_shared_essential_multiplicities :
    (diagonalLine.sliceHookMultiset signedStaircaseCenter.positive).count (3, ⊤) = 2 ∧
    (diagonalLine.sliceHookMultiset signedStaircaseCenter.negative).count (3, ⊤) = 2 ∧
    (diagonalLine.sliceHookMultiset signedStaircaseCenter.positive).count (2, ⊤) = 2 := by
  classical
  rw [diagonal_even, diagonal_odd]
  norm_num [essential]

/-- The capstone consumes the staircase's original finite presentation:
three nonempty odd intervals cancel against four even intervals. -/
theorem staircase_diagonal_cancellation (k : Type u) [Field k] :
    (finitelyPresentedOneDimensionalBarcodeDiagram
      (reindex diagonalLine.orderHom (signedStaircaseModule (k := k)))
      (diagonalLine.finitelyPresented_fromReal_slice
        (signedStaircaseModule_finitelyPresented (k := k)))).points +
        ({essential 3} + {essential 2} + {essential 3}) =
      {essential 3} + {essential 2} + {essential 2} + {essential 3} := by
  have h := diagonalLine.finitelyPresented_sliceSignedHookBarcode_cancel
    (signedStaircaseModule (k := k)) (signedStaircaseModule_finitelyPresented (k := k))
  rw [signedStaircaseModule_barcode, diagonal_even, diagonal_odd] at h
  exact h

/-- The ordinary barcode of the actual diagonal staircase slice is `[2,∞)`;
the shared odd intervals have all been cancelled with their multiplicities. -/
theorem staircase_diagonal_ordinary_barcode (k : Type u) [Field k] :
    (finitelyPresentedOneDimensionalBarcodeDiagram
      (reindex diagonalLine.orderHom (signedStaircaseModule (k := k)))
      (diagonalLine.finitelyPresented_fromReal_slice
        (signedStaircaseModule_finitelyPresented (k := k)))).points = {(2, ⊤)} := by
  classical
  apply add_right_cancel (b := {essential 3} + {essential 2} + {essential 3})
  rw [staircase_diagonal_cancellation]
  ext p
  simp only [Multiset.count_add, Multiset.count_singleton, essential]
  omega

/-- Unequal slopes change the surviving ordinary interval to `[1,∞)`.
The ordinary barcode still comes directly from the original presentation. -/
theorem staircase_unequal_slopes_ordinary_barcode (k : Type u) [Field k] :
    tiltedLine.slope 0 ≠ tiltedLine.slope 1 ∧
      (finitelyPresentedOneDimensionalBarcodeDiagram
        (reindex tiltedLine.orderHom (signedStaircaseModule (k := k)))
        (tiltedLine.finitelyPresented_fromReal_slice
          (signedStaircaseModule_finitelyPresented (k := k)))).points = {(1, ⊤)} := by
  classical
  refine ⟨by norm_num [tiltedLine], ?_⟩
  have h := tiltedLine.finitelyPresented_sliceSignedHookBarcode_cancel
    (signedStaircaseModule (k := k)) (signedStaircaseModule_finitelyPresented (k := k))
  rw [signedStaircaseModule_barcode, tilted_even, tilted_odd] at h
  apply add_right_cancel (b := {essential (3 / 2)} + {essential 2} + {essential 3})
  rw [h]
  ext p
  simp only [Multiset.count_add, Multiset.count_singleton, essential]
  omega

private theorem diagonal_staircase_support (t : ℝ) :
    diagonalLine.orderHom t ∈ signedStaircaseSupport ↔ 2 ≤ t := by
  change (∃ i : Fin 4, signedStaircaseVertices i ≤ diagonalLine.orderHom t) ↔ _
  simp only [← diagonalLine.entrance_le_iff, diagonal_entrance]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> norm_num [signedStaircaseVertices] at hi ⊢ <;> linarith
  · intro ht
    exact ⟨1, by norm_num [signedStaircaseVertices]; exact ht⟩

/-- The actual diagonal restriction of the staircase has the fibres and
structure maps of the single surviving essential interval `[2,∞)`. -/
theorem staircase_diagonal_actual_interval (k : Type u) [Field k] :
    reindex diagonalLine.orderHom (signedStaircaseModule (k := k)) =
      RealBarcode.intervalModule (k := k) (2, ⊤) := by
  let S : Set ℝ := {t | diagonalLine.orderHom t ∈ signedStaircaseSupport}
  have hS : S.OrdConnected := by
    constructor
    intro s hs t ht v hv
    apply (diagonal_staircase_support v).mpr
    exact ((diagonal_staircase_support s).mp hs).trans hv.1
  have he : S = IntervalCompatibility.support (2, ⊤) := by
    ext t
    simp only [S, Set.mem_ofPred_eq, diagonal_staircase_support,
      IntervalCompatibility.support, RealBarcode.alive, WithTop.coe_lt_top, and_true]
  change SupportInterval.module (k := k) S hS = _
  simp only [he]
  rfl

/-- A nonzero planar hook over any field can disappear on a positive affine
slice; the assertion concerns the actual original and restricted modules. -/
theorem nonzero_hook_can_collapse (k : Type u) [Field k] :
    ∃ (L : PositiveAffineLine 2) (p q : Fin 2 → ℝ),
      p < q ∧ (∃ x : (Hook.module (k := k) p q).obj p, x ≠ 0) ∧
        IsZero (reindex L.orderHom (Hook.module (k := k) p q)) := by
  refine ⟨_, _, _, ?_, AffineSliceExamples.collapse_original_nonzero k,
    AffineSliceExamples.collapse_slice_zero k⟩
  change (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) <
    (fun i : Fin 2 => if i = 0 then (2 : ℝ) else 0)
  apply lt_iff_le_not_ge.mpr
  constructor
  · intro i
    fin_cases i <;> norm_num
  · intro h
    have h0 := h 0
    norm_num at h0

/-- Finite nonzero intervals retain two occurrences after unequal-slope
restriction, even in a family that also contains a collapsed nonzero hook. -/
theorem repeated_finite_intervals_survive :
    ∃ (L : PositiveAffineLine 2) (B : Multiset (RealHookTag (n := 2))),
      L.slope 0 ≠ L.slope 1 ∧ B.card = 3 ∧
        (L.sliceHookMultiset B).count (0, (2 : WithTop ℝ)) = 2 := by
  refine ⟨_, _, ?_, ?_, AffineSliceExamples.repeated_retained_endpoints_count⟩
  · change (2 : ℝ) ≠ 1
    norm_num
  · simp only [Multiset.card_add, Multiset.card_singleton]

/-- In dimension one, a slope of two changes the actual finite interval
`[7,11)` at offset three to `[2,4)`. -/
theorem one_coordinate_nonunit_actual_interval (k : Type u) [Field k] :
    ∃ (L : PositiveAffineLine 1) (p q : Fin 1 → ℝ),
      L.offset 0 = 3 ∧ L.slope 0 = 2 ∧ p 0 = 7 ∧ q 0 = 11 ∧
        reindex L.orderHom (Hook.module (k := k) p q) =
          RealBarcode.intervalModule (k := k) (2, (4 : WithTop ℝ)) :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, AffineSliceExamples.nonunit_slope_hook_interval k⟩

private abbrev noGenerators : GradedFree.GradedGenerators.{0,0} (Fin 2 → ℝ) where
  Carrier := Fin 0
  grade := Fin.elim0

private theorem noGenerators_slice_isZero (k : Type u) [Field k] :
    IsZero (reindex tiltedLine.orderHom (GradedFree.module (R := k) noGenerators)) := by
  apply Functor.isZero
  intro t
  have : Subsingleton ((reindex tiltedLine.orderHom
      (GradedFree.module (R := k) noGenerators)).obj t) := by
    constructor
    intro x y
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact Fin.elim0 i
  exact ModuleCat.isZero_of_subsingleton _

/-- The actual empty original generator family gives an empty ordinary
slice barcode; no interval is introduced by the finite-presentation bridge. -/
theorem empty_original_ordinary_barcode (k : Type u) [Field k] :
    (finitelyPresentedOneDimensionalBarcodeDiagram
      (reindex tiltedLine.orderHom (GradedFree.module (R := k) noGenerators))
      (tiltedLine.finitelyPresented_fromReal_slice
        (GradedFree.free_finitelyPresented noGenerators))).points = 0 := by
  classical
  let B := finitelyPresentedOneDimensionalBarcodeDiagram
    (reindex tiltedLine.orderHom (GradedFree.module (R := k) noGenerators))
    (tiltedLine.finitelyPresented_fromReal_slice (GradedFree.free_finitelyPresented noGenerators))
  have e := finitelyPresentedOneDimensionalBarcodeRealizationIso
    (reindex tiltedLine.orderHom (GradedFree.module (R := k) noGenerators))
    (tiltedLine.finitelyPresented_fromReal_slice (GradedFree.free_finitelyPresented noGenerators))
  apply RealBarcode.multiset_eq_of_rankCounts_eq B.points 0
    (finitelyPresentedOneDimensionalBarcodeDiagram_isPositive _ _)
    (by simp)
  intro s t hst
  rw [← RealBarcode.rank_realize (k := k) B s t hst,
    ← rankOfStructureMap_iso hst e,
    rankOfStructureMap_iso hst (noGenerators_slice_isZero k).isoZero,
    rankOfStructureMap_zero]
  simp

end TDA.Persistence.AffineSliceSignedBarcodeExamples
