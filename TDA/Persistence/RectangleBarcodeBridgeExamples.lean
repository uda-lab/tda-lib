import TDA.Persistence.RectangleBarcodeBridge
import TDA.Persistence.RectangleMatchingDistanceExamples

/-!
# Consumers of the rectangle and real barcode bridge

The examples distinguish endpoint cost from actual short-pair interleavings,
retain repeated occurrences, and compare exact positive distances and deletion
thresholds through the original real barcode realization.
-/

set_option autoImplicit false

namespace TDA.Persistence.RectangleBarcodeBridge.Examples

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence NNReal ENNReal Classical ZeroObject

private def source : Bool → ℝ × ℝ
  | false => (0, 6)
  | true => (10, 16)

private def target (b : Bool) : ℝ × ℝ := ((source (!b)).1 + 1, (source (!b)).2 + 1)
private theorem source_pos (b : Bool) : (source b).1 < (source b).2 := by cases b <;> norm_num [source]
private theorem target_pos (b : Bool) : (target b).1 < (target b).2 := by cases b <;> norm_num [target, source]

private def swap : OccurrenceMatching Bool Bool PEmpty.{1} PEmpty.{1} where
  finite b := some (!b)
  finite_injective := by decide
  essential := Equiv.refl _

private theorem swap_cost : swap.cost source target PEmpty.elim PEmpty.elim ≤ 1 := by
  apply swap.cost_le_of
  · intro i
    cases i <;> norm_num [swap, source, target, finitePairCost]
  · intro j
    have hj : ∃ i, swap.finite i = some j := ⟨!j, by cases j <;> rfl⟩
    simp [hj]
  · intro i
    exact i.elim

/-- A nontrivial occurrence permutation and endpoint shift give actual real maps. -/
noncomputable def shiftedRealInterleaving :
    RealInterleaving 1 (RealBarcode.realize (k := ℚ) (diagram source source_pos))
      (RealBarcode.realize (diagram target target_pos)) :=
  toRealInterleaving source target source_pos target_pos
    (isMatching_of_cost source target source_pos target_pos 1 swap swap_cost).interleaving

private theorem diagram_numeric_eq {I J : Type} [Fintype I] [Fintype J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (hx : ∀ i, (x i).1 < (x i).2) (hy : ∀ j, (y j).1 < (y j).2) :
    bottleneck (diagram x hx) (diagram y hy) =
      presentationBottleneck x y (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) := by
  apply TDA.Persistence.bottleneck_eq_presentation
  · exact (diagram_finitePart x hx).symm
  · exact (diagram_finitePart y hy).symm
  · simp [diagram_essentialPart]
  · simp [diagram_essentialPart]

/-- All three existing values are exactly one for the shifted, permuted long bars. -/
theorem shifted_exact_distances :
    bottleneck (diagram source source_pos) (diagram target target_pos) = 1 ∧
    realInterleavingDistance (RealBarcode.realize (k := ℚ) (diagram source source_pos))
      (RealBarcode.realize (diagram target target_pos)) = 1 ∧
    RectangleMatching.bottleneckDistance (k := ℚ)
      (fun i => halfOpenRectangle (source i) (source_pos i))
      (fun j => halfOpenRectangle (target j) (target_pos j)) = 1 := by
  have hl : (1 : ℝ≥0∞) ≤ bottleneck (diagram source source_pos) (diagram target target_pos) := by
    rw [diagram_numeric_eq]
    apply le_iInf
    intro M
    have hs := M.source_le_cost source target Fin.elim0 Fin.elim0 false
    apply le_trans _ hs
    cases hi : M.finite false with
    | none => norm_num [hi, diagonalCost, source]
    | some j => cases j <;> norm_num [hi, finitePairCost, source, target]
  have hu : bottleneck (diagram source source_pos) (diagram target target_pos) ≤ 1 := by
    rw [← rectangle_bottleneck_eq_diagram (k := ℚ)]
    exact RectangleMatching.bottleneckDistance_le_of_matching
      (isMatching_of_cost (k := ℚ) source target source_pos target_pos 1 swap swap_cost)
  have hd := le_antisymm hu hl
  refine ⟨hd, ?_, ?_⟩
  · rw [← diagram_bottleneck_eq_real_distance, hd]
  · rw [rectangle_bottleneck_eq_diagram, hd]

private def copies : Bool → ℝ × ℝ := fun _ => (0, 2)
private theorem copies_pos (b : Bool) : (copies b).1 < (copies b).2 := by norm_num [copies]
private def empty : Fin 0 → ℝ × ℝ := Fin.elim0
private theorem empty_pos (i : Fin 0) : (empty i).1 < (empty i).2 := Fin.elim0 i

/-- Two equal endpoint values remain two occurrences in the original diagram domain. -/
theorem repeated_occurrences :
    (diagram copies copies_pos).points.count (0, (2 : WithTop ℝ)) = 2 := by
  norm_num [diagram, copies, Multiset.map_const]

private def eraseCopies : OccurrenceMatching Bool (Fin 0) PEmpty.{1} PEmpty.{1} where
  finite _ := none
  finite_injective := by simp
  essential := Equiv.refl _

private theorem eraseCopies_cost : eraseCopies.cost copies empty PEmpty.elim PEmpty.elim ≤ 1 := by
  apply eraseCopies.cost_le_of
  · intro i
    norm_num [eraseCopies, copies, diagonalCost]
  · intro i
    exact Fin.elim0 i
  · intro i
    exact i.elim

/-- Both copies can be deleted at the exact half-open threshold. -/
noncomputable def copiesDeletion :
    RealInterleaving 1 (RealBarcode.realize (k := ℚ) (diagram copies copies_pos))
      (RealBarcode.realize (diagram empty empty_pos)) :=
  toRealInterleaving copies empty copies_pos empty_pos
    (isMatching_of_cost copies empty copies_pos empty_pos 1 eraseCopies eraseCopies_cost).interleaving

/-- The threshold is the actual original real-module distance, rather than just a bound. -/
theorem copies_exact_distance :
    realInterleavingDistance (RealBarcode.realize (k := ℚ) (diagram copies copies_pos))
      (RealBarcode.realize (diagram empty empty_pos)) = 1 := by
  rw [← diagram_bottleneck_eq_real_distance, diagram_numeric_eq]
  change presentationBottleneck (fun _ : Bool => ((0, 2) : ℝ × ℝ))
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) = 1
  rw [presentationBottleneck_constant_empty]
  norm_num [diagonalCost]

/-- The exact parameter set here is closed, in contrast to the closed-point fixture. -/
theorem copies_interleaving_iff (ε : ℝ≥0) :
    Nonempty (RealInterleaving ε
      (RealBarcode.realize (k := ℚ) (diagram copies copies_pos))
      (RealBarcode.realize (diagram empty empty_pos))) ↔ 1 ≤ ε := by
  constructor
  · rintro ⟨I⟩
    have h := I.distance_le
    rw [copies_exact_distance] at h
    exact ENNReal.coe_le_coe.mp h
  · intro h
    exact ⟨copiesDeletion.mono h⟩

/-- The witness conversions include parameter zero and repeated occurrences. -/
noncomputable def zero_parameter_roundTrip :
    CoordinateInterleaving 0
      (RectangleFamily.module (k := ℚ) (fun i => halfOpenRectangle (copies i) (copies_pos i)))
      (RectangleFamily.module (fun i => halfOpenRectangle (copies i) (copies_pos i))) :=
  ofRealInterleaving copies copies copies_pos copies_pos
    (toRealInterleaving copies copies copies_pos copies_pos (CoordinateInterleaving.refl 0 _))

/-- Empty occurrence families also pass through the actual realization bridge. -/
noncomputable def empty_real_interleaving :
    RealInterleaving 0 (RealBarcode.realize (k := ℚ) (diagram empty empty_pos))
      (RealBarcode.realize (diagram empty empty_pos)) :=
  toRealInterleaving empty empty empty_pos empty_pos (CoordinateInterleaving.refl 0 _)

private def farSource : Unit → ℝ × ℝ := fun _ => (0, 1)
private def farTarget : Unit → ℝ × ℝ := fun _ => (100, 101)
private theorem farSource_pos (i : Unit) : (farSource i).1 < (farSource i).2 := by norm_num [farSource]
private theorem farTarget_pos (i : Unit) : (farTarget i).1 < (farTarget i).2 := by norm_num [farTarget]

private noncomputable def farPair :
    CoordinateInterleaving 1 ((halfOpenRectangle (0, 1) (by norm_num)).module (k := ℚ))
      (halfOpenRectangle (100, 101) (by norm_num)).module := by
  have hx := (RealBarcode.transition_eq_zero_iff (k := ℚ) 1 0 1).mpr (by norm_num)
  have hy := (RealBarcode.transition_eq_zero_iff (k := ℚ) 1 100 101).mpr (by norm_num)
  let I : RealInterleaving 1 (RealBarcode.intervalModule (k := ℚ) (0, ((1 : ℝ) : WithTop ℝ)))
      (RealBarcode.intervalModule (100, ((101 : ℝ) : WithTop ℝ))) :=
    ⟨0, 0, by simpa only [zero_comp] using hx.symm,
      by simpa only [zero_comp] using hy.symm⟩
  exact (CoordinateRealBridge.toCoordinate I).congr
    (intervalIso (0, 1) (by norm_num)).symm (intervalIso (100, 101) (by norm_num)).symm

private def farMatching : OccurrenceMatching Unit Unit PEmpty.{1} PEmpty.{1} where
  finite _ := some ()
  finite_injective _ _ _ _ _ := Subsingleton.elim _ _
  essential := Equiv.refl _

private theorem farMatching_actual : RectangleMatching.IsMatching (k := ℚ) 1
    (fun i => halfOpenRectangle (farSource i) (farSource_pos i))
    (fun j => halfOpenRectangle (farTarget j) (farTarget_pos j)) farMatching := by
  refine ⟨fun _ _ _ => ⟨farPair⟩, ?_, ?_⟩
  · intro i hi
    simp [farMatching] at hi
  · intro j hj
    have h := hj ()
    cases j
    simp [farMatching] at h

/-- A valid short-pair matching can have cost 100 at radius one. The bridge
produces another matching which deletes the pair and has cost at most one. -/
theorem short_far_pruning :
    ∃ M : OccurrenceMatching Unit Unit PEmpty.{1} PEmpty.{1},
      RectangleMatching.IsMatching (k := ℚ) 1
        (fun i => halfOpenRectangle (farSource i) (farSource_pos i))
        (fun j => halfOpenRectangle (farTarget j) (farTarget_pos j)) M ∧
      M.cost farSource farTarget PEmpty.elim PEmpty.elim = 100 ∧
      ∃ A : OccurrenceMatching Unit Unit PEmpty.{1} PEmpty.{1},
        A.cost farSource farTarget PEmpty.elim PEmpty.elim ≤ 1 ∧ A.finite () = none := by
  refine ⟨farMatching, farMatching_actual, ?_, ?_⟩
  · norm_num [OccurrenceMatching.cost, farMatching, farSource, farTarget, finitePairCost]
  · obtain ⟨A, hA⟩ := exists_cost_matching farSource farTarget farSource_pos farTarget_pos
      1 farMatching farMatching_actual
    refine ⟨A, hA, ?_⟩
    cases ha : A.finite () with
    | none => rfl
    | some j =>
      have h := (A.source_le_cost farSource farTarget PEmpty.elim PEmpty.elim ()).trans hA
      norm_num [ha, farSource, farTarget, finitePairCost] at h

/-- Raw half-open constructors with empty or reversed support are genuinely zero. -/
theorem empty_and_reversed_zero :
    IsZero (RealBarcode.intervalModule (k := ℚ) (0, (0 : WithTop ℝ))) ∧
    IsZero (RealBarcode.intervalModule (k := ℚ) (2, (1 : WithTop ℝ))) :=
  ⟨empty_interval_isZero (0, 0) le_rfl, empty_interval_isZero (2, 1) (by norm_num)⟩

private def closedPoint : Rectangle 1 := fun _ => ⟨0, 0, true, true, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- A closed singleton is retained by rectangles, unlike an empty half-open
interval. Its zero distance still has no parameter-zero family interleaving. -/
theorem decorated_singleton_boundary :
    IsZero (RealBarcode.intervalModule (k := ℚ) (0, (0 : WithTop ℝ))) ∧
    RectangleMatching.bottleneckDistance (k := ℚ) (fun _ : Unit => closedPoint)
      (Fin.elim0 : Fin 0 → Rectangle 1) = 0 ∧
    ¬ Nonempty (CoordinateInterleaving 0
      (RectangleFamily.module (k := ℚ) (fun _ : Unit => closedPoint))
      (RectangleFamily.module (Fin.elim0 : Fin 0 → Rectangle 1))) :=
  ⟨empty_interval_isZero (0, 0) le_rfl,
    RectangleMatching.DistanceExamples.point_bottleneck_zero,
    RectangleMatching.DistanceExamples.point_no_zero_interleaving⟩

end TDA.Persistence.RectangleBarcodeBridge.Examples
