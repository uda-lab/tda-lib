import TDA.Persistence.AffineSliceMatching
import TDA.Persistence.AffineSliceHooks
import Mathlib.Tactic

/-!
# Ordinary affine-slice matching examples

These examples use actual interleaving maps and original finite presentations.
They distinguish diagonal components from required padding, preserve repeated
essential intervals, and include empty barcodes and infinite extended distances.
-/

set_option autoImplicit false
universe u

namespace TDA.Persistence.AffineSliceMatchingExamples
open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence NNReal ENNReal ZeroObject

private def line : PositiveAffineLine 2 where
  offset j := if j = 0 then 1 else -1
  slope j := if j = 0 then 2 else 1
  slope_pos j := by fin_cases j <;> norm_num

private theorem minimum : line.minSlope = 1 := by
  apply le_antisymm
  · exact_mod_cast (show (line.minSlope : ℝ) ≤ 1 by
      simpa [line] using line.minSlope_le_slope 1)
  · apply NNReal.coe_le_coe.mp
    apply (line.le_minSlope_iff 1).mpr
    intro j
    fin_cases j <;> norm_num [line]

private def birth : Fin 2 → ℝ := fun j => if j = 0 then 1 else -1
private def death : Fin 2 → ℝ := fun j => if j = 0 then 3 else 0

private theorem source_support : line.orderHom 0 ∈ Hook.support birth death := by
  constructor
  · intro j
    fin_cases j <;> norm_num [PositiveAffineLine.orderHom_apply, line, birth]
  · intro h
    have h0 := h 0
    norm_num [PositiveAffineLine.orderHom_apply, line, death] at h0

private theorem middle_support :
    CoordinateShift.translation (1 : ℝ≥0) (line.orderHom 0) ∈ Hook.support birth death := by
  constructor
  · intro j
    fin_cases j <;> norm_num [CoordinateShift.translation_apply,
      PositiveAffineLine.orderHom_apply, line, birth]
  · intro h
    have h0 := h 0
    norm_num [CoordinateShift.translation_apply,
      PositiveAffineLine.orderHom_apply, line, death] at h0

private theorem target_not_support :
    line.orderHom (0 + (((1 : ℝ≥0) / line.minSlope : ℝ≥0) : ℝ)) ∉
      Hook.support birth death := by
  intro h
  apply h.2
  intro j
  rw [minimum]
  fin_cases j <;> norm_num [PositiveAffineLine.orderHom_apply, line, death]

private noncomputable def unit (k : Type u) [Field k] :
    (Hook.module (k := k) birth death).obj (line.orderHom 0) :=
  SupportInterval.one (Hook.support birth death) source_support

/-- The raw diagonal transition remains nonzero, but the correctly padded
restriction kills the same source class at the line's finite death. -/
theorem diagonal_transition_survives_but_padded_slice_dies (k : Type u) [Field k] :
    let i := CoordinateInterleaving.refl (1 : ℝ≥0) (Hook.module (k := k) birth death)
    (i.φ.app (line.orderHom 0)).hom (unit k) ≠ 0 ∧
      ((i.restrictPositiveAffineLine line).φ.app 0).hom (unit k) = 0 := by
  dsimp only
  constructor
  · change structureMapLinear (Hook.module (k := k) birth death)
      (show line.orderHom 0 ≤ CoordinateShift.translation (1 : ℝ≥0) (line.orderHom 0)
        from fun j => le_add_of_nonneg_right (by norm_num)) (unit k) ≠ 0
    intro hz
    have hc := SupportInterval.structureMap_val (k := k) (Hook.support birth death)
      (Hook.support_ordConnected birth death)
      (show line.orderHom 0 ≤ CoordinateShift.translation (1 : ℝ≥0) (line.orderHom 0)
        from fun j => le_add_of_nonneg_right (by norm_num)) (unit k)
    rw [if_pos middle_support] at hc
    have hv := congrArg Subtype.val hz
    exact (one_ne_zero : (1 : k) ≠ 0) (hc.symm.trans hv)
  · rw [CoordinateInterleaving.restrictPositiveAffineLine_φ_app]
    apply Subtype.ext
    exact SupportInterval.val_eq_zero (Hook.support birth death) target_not_support _

/-- Unequal slopes make the padding inequality strict in the first coordinate. -/
theorem shifted_grade_ne_line_next :
    CoordinateShift.translation (1 : ℝ≥0) (line.orderHom 0) ≠
      line.orderHom (0 + (((1 : ℝ≥0) / line.minSlope : ℝ≥0) : ℝ)) := by
  intro he
  have h0 := congrFun he 0
  rw [minimum] at h0
  norm_num [CoordinateShift.translation_apply,
    PositiveAffineLine.orderHom_apply, line] at h0


private abbrev repeatedGenerators (r : ℕ) : GradedFree.GradedGenerators.{0,0} (Fin 1 → ℝ) where
  Carrier := Fin r
  grade _ := 0

private noncomputable abbrev repeatedModule (k : Type u) [Field k] (r : ℕ) :
    PModule.{u,0,u} k (Fin 1 → ℝ) :=
  GradedFree.module (R := k) (repeatedGenerators r)

private theorem repeated_original_fp (k : Type u) [Field k] (r : ℕ) :
    GradedFree.FinitelyPresented.{u,0,0} (repeatedModule k r) :=
  GradedFree.free_finitelyPresented (repeatedGenerators r)

private noncomputable def repeatedHookPresentation (k : Type u) [Field k] (r : ℕ) :
    FiniteHookSumPresentation (k := k) (n := 1) (repeatedModule k r) := by
  let F : Fin r → PModule.{u,0,u} k (Fin 1 → ℝ) :=
    fun _ => HookInfinity.module (R := k) (0 : Fin 1 → ℝ)
  let forward : repeatedModule k r ⟶ ⨁ F :=
    GradedFree.lift (repeatedGenerators r) (⨁ F) (fun j =>
      ((biproduct.ι F j).app 0).hom (HookInfinity.birth (R := k) 0))
  let backward : (⨁ F) ⟶ repeatedModule k r :=
    biproduct.desc (fun j => HookInfinity.fromBirth 0 (repeatedModule k r)
      (GradedFree.birth (repeatedGenerators r) j))
  refine ⟨r, (fun _ => .inr 0), ?_⟩
  refine ⟨forward, backward, ?_, ?_⟩
  · apply GradedFree.hom_ext_birth (repeatedGenerators r)
    intro j
    change (backward.app 0).hom
      ((forward.app 0).hom (GradedFree.birth (repeatedGenerators r) j)) =
        GradedFree.birth (repeatedGenerators r) j
    have hf : (forward.app 0).hom (GradedFree.birth (repeatedGenerators r) j) =
        ((biproduct.ι F j).app 0).hom (HookInfinity.birth (R := k) 0) :=
      GradedFree.lift_birth (repeatedGenerators r) (⨁ F) _ j
    rw [hf]
    change ((biproduct.ι F j ≫ backward).app 0).hom (HookInfinity.birth (R := k) 0) = _
    dsimp only [backward]
    rw [biproduct.ι_desc]
    exact HookInfinity.fromBirth_birth 0 _ _
  · apply biproduct.hom_ext'
    intro j
    apply HookInfinity.hom_ext
    change (forward.app 0).hom
      (((biproduct.ι F j ≫ backward).app 0).hom (HookInfinity.birth (R := k) 0)) =
        ((biproduct.ι F j).app 0).hom (HookInfinity.birth (R := k) 0)
    dsimp only [backward]
    rw [biproduct.ι_desc, HookInfinity.fromBirth_birth]
    exact GradedFree.lift_birth (repeatedGenerators r) (⨁ F) _ j

private noncomputable def repeatedDiagram (r : ℕ) : Diagram ℝ :=
  oneDimensionalHookDiagram (fun _ : Fin r => Sum.inr (0 : Fin 1 → ℝ))

private noncomputable def diagonalFromRealIso (k : Type u) [Field k]
    (M : PModule.{u,0,u} k ℝ) :
    reindex (PositiveAffineLine.diagonal 1).orderHom (CoordinateRealBridge.fromReal M) ≅ M := by
  apply eqToIso
  rw [CoordinateRealBridge.fromReal, reindex_comp]
  have he : CoordinateRealBridge.evaluate.comp (PositiveAffineLine.diagonal 1).orderHom =
      (OrderHom.id : ℝ →o ℝ) := by
    ext t
    change (PositiveAffineLine.diagonal 1).orderHom t 0 = t
    exact PositiveAffineLine.diagonal_orderHom 1 t 0
  rw [he, reindex_id]

private noncomputable def repeatedSliceIso (k : Type u) [Field k] (r : ℕ) :
    reindex (PositiveAffineLine.diagonal 1).orderHom (repeatedModule k r) ≅
      RealBarcode.realize (k := k) (repeatedDiagram r) := by
  have e := finiteHookSum_realizationIso (repeatedHookPresentation k r)
  change repeatedModule k r ≅ CoordinateRealBridge.fromReal
    (RealBarcode.realize (k := k) (repeatedDiagram r)) at e
  exact Functor.isoWhiskerLeft (PositiveAffineLine.diagonal 1).orderHom.toFunctor e ≪≫
    diagonalFromRealIso k _

private theorem repeated_ordinary_barcode (k : Type u) [Field k] (r : ℕ) :
    (PositiveAffineLine.diagonal 1).ordinarySliceBarcode (repeatedModule k r)
      (repeated_original_fp k r) = repeatedDiagram r :=
  (PositiveAffineLine.diagonal 1).ordinarySliceBarcode_eq_of_realizationIso
    (repeatedModule k r) (repeated_original_fp k r) (repeatedDiagram r)
    (oneDimensionalHookDiagram_isPositive _) (repeatedSliceIso k r)

/-- An empty original free presentation has an empty actual ordinary slice barcode. -/
theorem empty_ordinary_barcode (k : Type u) [Field k] :
    ((PositiveAffineLine.diagonal 1).ordinarySliceBarcode (repeatedModule k 0)
      (repeated_original_fp k 0)).points = 0 := by
  rw [repeated_ordinary_barcode]
  simp [repeatedDiagram, oneDimensionalHookDiagram_points, hookTagMultiset]

/-- A single free generator contributes one essential interval, with death infinity. -/
theorem essential_ordinary_barcode (k : Type u) [Field k] :
    ((PositiveAffineLine.diagonal 1).ordinarySliceBarcode (repeatedModule k 1)
      (repeated_original_fp k 1)).points = {(0, (⊤ : WithTop ℝ))} := by
  rw [repeated_ordinary_barcode]
  simp [repeatedDiagram, oneDimensionalHookDiagram_points, hookTagMultiset,
    oneDimensionalHookEndpoints]

/-- Two original generators at the same grade remain two separate ordinary
barcode occurrences, even though their essential endpoints coincide. -/
theorem repeated_essential_ordinary_barcode (k : Type u) [Field k] :
    ((PositiveAffineLine.diagonal 1).ordinarySliceBarcode (repeatedModule k 2)
      (repeated_original_fp k 2)).points.count (0, (⊤ : WithTop ℝ)) = 2 := by
  classical
  rw [repeated_ordinary_barcode]
  simp [repeatedDiagram, oneDimensionalHookDiagram_points, hookTagMultiset,
    oneDimensionalHookEndpoints]

private theorem diagonal_minimum : (PositiveAffineLine.diagonal 1).minSlope = 1 := by
  apply le_antisymm
  · exact_mod_cast (show ((PositiveAffineLine.diagonal 1).minSlope : ℝ) ≤ 1 by
      simpa using (PositiveAffineLine.diagonal 1).minSlope_le_slope 0)
  · apply NNReal.coe_le_coe.mp
    apply ((PositiveAffineLine.diagonal 1).le_minSlope_iff 1).mpr
    intro j
    simp

private theorem essential_empty_bottleneck (k : Type u) [Field k] :
    bottleneck
      ((PositiveAffineLine.diagonal 1).ordinarySliceBarcode (repeatedModule k 1)
        (repeated_original_fp k 1))
      ((PositiveAffineLine.diagonal 1).ordinarySliceBarcode (repeatedModule k 0)
        (repeated_original_fp k 0)) = ⊤ := by
  apply (bottleneck_eq_top_iff _ _).mpr
  rw [essential_ordinary_barcode, empty_ordinary_barcode]
  change (1 : ℕ) ≠ 0
  norm_num

/-- Essential-cardinality mismatch produces an infinite weighted ordinary
slice bottleneck on the normalized diagonal. -/
theorem infinite_weighted_slice_bottleneck (k : Type u) [Field k] :
    (PositiveAffineLine.diagonal 1).weightedSliceBottleneck
      (repeatedModule k 1) (repeatedModule k 0)
      (repeated_original_fp k 1) (repeated_original_fp k 0) = ⊤ := by
  unfold PositiveAffineLine.weightedSliceBottleneck
  rw [diagonal_minimum, essential_empty_bottleneck]
  simp

/-- The normalized supremum can be infinite for originally finitely presented modules. -/
theorem infinite_matching_distance (k : Type u) [Field k] :
    sliceMatchingDistance (repeatedModule k 1) (repeatedModule k 0)
      (repeated_original_fp k 1) (repeated_original_fp k 0) = ⊤ := by
  apply top_unique
  have h := weightedSliceBottleneck_le_sliceMatchingDistance
    (repeatedModule k 1) (repeatedModule k 0)
    (repeated_original_fp k 1) (repeated_original_fp k 0) (NormalizedAffineLine.diagonal 1)
  change (PositiveAffineLine.diagonal 1).weightedSliceBottleneck _ _ _ _ ≤ _ at h
  rw [infinite_weighted_slice_bottleneck] at h
  exact h

/-- The upper-bound theorem also applies when the coordinate distance is infinite. -/
theorem infinite_coordinate_distance (k : Type u) [Field k] :
    coordinateInterleavingDistance (repeatedModule k 1) (repeatedModule k 0) = ⊤ := by
  apply top_unique
  have h := sliceMatchingDistance_le_coordinateInterleavingDistance
    (repeatedModule k 1) (repeatedModule k 0)
    (repeated_original_fp k 1) (repeated_original_fp k 0)
  rw [infinite_matching_distance] at h
  exact h

private def nonunitLine : PositiveAffineLine 1 where
  offset _ := 3
  slope _ := 2
  slope_pos _ := by norm_num

private theorem nonunit_minimum : nonunitLine.minSlope = 2 := by
  apply le_antisymm
  · exact_mod_cast (show (nonunitLine.minSlope : ℝ) ≤ 2 by
      simpa [nonunitLine] using nonunitLine.minSlope_le_slope 0)
  · apply NNReal.coe_le_coe.mp
    apply (nonunitLine.le_minSlope_iff 2).mpr
    intro j
    exact le_rfl

private noncomputable def closePrincipalInterleaving (k : Type u) [Field k] :
    CoordinateInterleaving 1 (HookInfinity.module (R := k) (0 : Fin 1 → ℝ))
      (HookInfinity.module (R := k) (1 : Fin 1 → ℝ)) :=
  HookMatching.principalHookInterleavingOfBirthClose (k := k) 1
    (fun _ => by norm_num) (fun _ => by norm_num)

/-- A nonunit slope halves the parameter of an actual interleaving between
distinct principal births; the nonzero offset is allowed. -/
theorem nonunit_line_interleaving (k : Type u) [Field k] :
    Nonempty (RealInterleaving (1 / 2)
      (reindex nonunitLine.orderHom (HookInfinity.module (R := k) (0 : Fin 1 → ℝ)))
      (reindex nonunitLine.orderHom (HookInfinity.module (R := k) (1 : Fin 1 → ℝ)))) := by
  have i := (closePrincipalInterleaving k).restrictPositiveAffineLine nonunitLine
  rw [nonunit_minimum] at i
  exact ⟨i⟩

/-- The ordinary-barcode bound consumes original finite presentations of both
principal modules on this nonunit, nonzero-offset line. -/
theorem nonunit_weighted_bottleneck_le_one (k : Type u) [Field k] :
    nonunitLine.weightedSliceBottleneck
      (HookInfinity.module (R := k) (0 : Fin 1 → ℝ))
      (HookInfinity.module (R := k) (1 : Fin 1 → ℝ))
      (GradedFree.free_finitelyPresented (HookInfinity.generators 0))
      (GradedFree.free_finitelyPresented (HookInfinity.generators 1)) ≤ 1 :=
  (nonunitLine.weightedSliceBottleneck_le_coordinateInterleavingDistance _ _ _ _).trans
    (closePrincipalInterleaving k).distance_le

end TDA.Persistence.AffineSliceMatchingExamples
