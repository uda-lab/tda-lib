import TDA.Persistence.RankSignedBarcodeOneDimensional
import TDA.Persistence.FinitePresentationHookKernel
import Mathlib.Tactic

/-!
# One-dimensional signed barcode and endpoint examples

These examples retain negative births and repeated occurrences, keep finite
deaths separate from essential tails, check empty output, and exercise the
exact diagonal-deletion threshold.  A nonzero interval with an actual original
finite presentation also consumes the module-level barcode stability theorem,
both against itself and, for two distinct essential intervals born at `0` and
`1`, through an explicit radius-one interleaving.
-/

set_option autoImplicit false

namespace TDA.Persistence.RankSignedBarcodeOneDimensionalExamples

open CategoryTheory CategoryTheory.Limits GradedFree RealBarcode
open scoped Classical ENNReal ZeroObject

private noncomputable def negativeFiniteTag : RealHookTag (n := 1) :=
  .inl ⟨(fun _ : Fin 1 => (-2 : ℝ), fun _ : Fin 1 => (1 : ℝ)), by
    apply lt_of_le_of_ne
    · intro i
      fin_cases i
      norm_num
    · intro h
      have h0 := congrArg (fun p : Fin 1 → ℝ => p 0) h
      norm_num at h0⟩

private noncomputable def essentialTag : RealHookTag (n := 1) :=
  .inr (fun _ : Fin 1 => (-2 : ℝ))

private noncomputable def repeatedFiniteTags : Fin 2 → RealHookTag (n := 1) :=
  fun _ => negativeFiniteTag

/-- Negative births are preserved, and repeated finite hooks contribute two
separate endpoint occurrences. -/
theorem repeated_negative_hooks_keep_multiplicity :
    (oneDimensionalHookDiagram repeatedFiniteTags).points.count (-2, (1 : WithTop ℝ)) = 2 := by
  simp [oneDimensionalHookDiagram_points, repeatedFiniteTags, hookTagMultiset,
    oneDimensionalHookEndpoints, negativeFiniteTag]

/-- The same endpoint convention distinguishes a finite death from an
essential principal hook born at the same negative value. -/
theorem finite_and_essential_endpoints :
    oneDimensionalHookEndpoints negativeFiniteTag = (-2, (1 : WithTop ℝ)) ∧
      oneDimensionalHookEndpoints essentialTag = (-2, (⊤ : WithTop ℝ)) := by
  constructor <;> simp [oneDimensionalHookEndpoints, negativeFiniteTag, essentialTag]

private noncomputable def mixedDiagram : Diagram ℝ :=
  orderedQ 1 1 (fun _ => (-2, 1), fun _ => -2)

private theorem mixedDiagram_positive : mixedDiagram.IsPositive := by
  rw [mixedDiagram, orderedQ_isPositive_iff]
  intro i
  norm_num

/-- The finite-death and principal occurrences of a mixed diagram both return
through the actual occurrence-indexed hook presentation. -/
theorem mixed_finite_and_essential_roundtrip :
    oneDimensionalHookDiagram
      (positiveDiagram_hookPresentation (k := ℚ) mixedDiagram mixedDiagram_positive).tag =
        mixedDiagram :=
  positiveDiagram_hookPresentation_diagram (k := ℚ) mixedDiagram mixedDiagram_positive

private noncomputable def emptyDiagram : Diagram ℝ :=
  orderedQ 0 0 (Fin.elim0, Fin.elim0)

private theorem emptyDiagram_positive : emptyDiagram.IsPositive := by
  intro p hp
  simp [emptyDiagram, orderedQ] at hp

/-- The zero barcode has the empty hook presentation and no spurious endpoint. -/
theorem empty_diagram_roundtrip :
    oneDimensionalHookDiagram
      (positiveDiagram_hookPresentation (k := ℚ) emptyDiagram emptyDiagram_positive).tag =
        emptyDiagram :=
  positiveDiagram_hookPresentation_diagram (k := ℚ) emptyDiagram emptyDiagram_positive

private noncomputable def deletionBoundaryDiagram : Diagram ℝ :=
  orderedQ 1 0 (fun _ => (-2, 0), Fin.elim0)

private theorem deletionBoundaryDiagram_positive : deletionBoundaryDiagram.IsPositive := by
  rw [deletionBoundaryDiagram, orderedQ_isPositive_iff]
  intro i
  norm_num

/-- The length-two diagram also returns through the actual finite-hook
presentation, preserving its negative birth and finite death. -/
theorem finite_death_deletion_boundary_roundtrip :
    oneDimensionalHookDiagram
      (positiveDiagram_hookPresentation (k := ℚ) deletionBoundaryDiagram
        deletionBoundaryDiagram_positive).tag = deletionBoundaryDiagram :=
  positiveDiagram_hookPresentation_diagram (k := ℚ) deletionBoundaryDiagram
    deletionBoundaryDiagram_positive

/-- A length-two negative-birth bar has diagonal deletion cost exactly one,
including at the equality boundary. -/
theorem finite_death_deletion_boundary :
    bottleneck
      (oneDimensionalHookDiagram
        (positiveDiagram_hookPresentation (k := ℚ) deletionBoundaryDiagram
          deletionBoundaryDiagram_positive).tag)
      emptyDiagram = 1 := by
  rw [finite_death_deletion_boundary_roundtrip]
  rw [bottleneck_eq_presentation deletionBoundaryDiagram emptyDiagram
    (fun _ : Fin 1 => (-2, 0)) (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)]
  · rw [presentationBottleneck_constant_empty]
    norm_num [diagonalCost]
  · simp [deletionBoundaryDiagram, finitePart_orderedQ]
  · simp [emptyDiagram, finitePart_orderedQ]
  · simp [deletionBoundaryDiagram, essentialPart_orderedQ]
  · simp [emptyDiagram, essentialPart_orderedQ]

private noncomputable def intervalGrid : CoordinateGrid 1 := fun _ => {-2, 1}

private noncomputable def intervalGridBirth : intervalGrid.Point := fun _ =>
  ⟨-2, by simp [intervalGrid]
  ⟩

private noncomputable def intervalGridDeath : intervalGrid.Point := fun _ =>
  ⟨1, by simp [intervalGrid]
  ⟩

private theorem intervalGridBirth_lt_death : intervalGridBirth < intervalGridDeath := by
  apply lt_of_le_of_ne
  · change ∀ i : Fin 1, (intervalGridBirth i).val ≤ (intervalGridDeath i).val
    intro i
    fin_cases i
    norm_num [intervalGridBirth, intervalGridDeath, intervalGrid]
  · intro h
    have h0 := congrArg (fun p : intervalGrid.Point => (p 0).val) h
    norm_num [intervalGridBirth, intervalGridDeath] at h0

private noncomputable def intervalHookBirth : Fin 1 → ℝ :=
  intervalGrid.embedding intervalGridBirth

private noncomputable def intervalHookDeath : Fin 1 → ℝ :=
  intervalGrid.embedding intervalGridDeath

private theorem intervalHook_finitelyPresented :
    FinitelyPresented.{0,0,0} (R := ℚ) (P := Fin 1 → ℝ)
      (Hook.module (k := ℚ) intervalHookBirth intervalHookDeath) := by
  let A : PModule ℚ intervalGrid.Point :=
    Hook.module (k := ℚ) intervalGridBirth intervalGridDeath
  have hA : FinitelyPresented (R := ℚ) (P := intervalGrid.Point) A :=
    GradedFree.pfd_finitelyPresented_of_finite_poset A (by
      intro p
      infer_instance)
  have hLan : FinitelyPresented (R := ℚ) (P := Fin 1 → ℝ) (intervalGrid.lan.obj A) :=
    GradedFree.finitelyPresented_lan_of_finiteGrid intervalGrid hA
  have e := intervalGrid.hookLanIso (k := ℚ) intervalGridBirth intervalGridDeath
  exact GradedFree.finitelyPresented_of_iso hLan e

private noncomputable def negativeInterval : PModule.{0,0,0} ℚ ℝ :=
  RealBarcode.intervalModule (k := ℚ) (-2, (1 : WithTop ℝ))

private theorem negativeInterval_nonzero :
    ∃ x : negativeInterval.obj (-2), x ≠ 0 := by
  let x : negativeInterval.obj (-2) := ⟨1, by
    change (1 : ℚ) ∈ RealBarcode.fiber (k := ℚ) (-2, (1 : WithTop ℝ)) (-2)
    have ha : RealBarcode.alive (-2, (1 : WithTop ℝ)) (-2) := by
      refine ⟨by norm_num, ?_⟩
      exact WithTop.coe_lt_coe.mpr (by norm_num)
    simp only [RealBarcode.fiber, if_pos ha, Submodule.mem_top]
    ⟩
  refine ⟨x, ?_⟩
  intro hx
  have hval := congrArg Subtype.val hx
  change (1 : ℚ) = 0 at hval
  norm_num at hval

private theorem negativeInterval_original_finitePresentation :
    FinitelyPresented.{0,0,0} (R := ℚ) (P := Fin 1 → ℝ)
      (CoordinateRealBridge.fromReal negativeInterval) := by
  have e := finiteHook_intervalIso (k := ℚ) intervalHookBirth intervalHookDeath
    intervalGridBirth_lt_death
  exact GradedFree.finitelyPresented_of_iso intervalHook_finitelyPresented e

/-- The original small finite presentation is consumed by the public
module-level capstone on a nonzero negative-birth interval. -/
theorem nonzero_original_fp_barcode_self_distance :
    (∃ x : negativeInterval.obj (-2), x ≠ 0) ∧
    bottleneck
        (finitelyPresentedOneDimensionalBarcodeDiagram negativeInterval
          negativeInterval_original_finitePresentation)
        (finitelyPresentedOneDimensionalBarcodeDiagram negativeInterval
          negativeInterval_original_finitePresentation) = 0 := by
  constructor
  · exact negativeInterval_nonzero
  · rw [finitelyPresentedOneDimensionalBarcode_bottleneck_eq_distance
      (k := ℚ) negativeInterval negativeInterval
      negativeInterval_original_finitePresentation negativeInterval_original_finitePresentation]
    exact realInterleavingDistance_self _

/-- The essential half-open interval born at `b`. -/
private noncomputable def essentialInterval (b : ℝ) : PModule.{0,0,0} ℚ ℝ :=
  RealBarcode.intervalModule (k := ℚ) (b, (⊤ : WithTop ℝ))

private theorem essentialInterval_original_finitePresentation (b : ℝ) :
    FinitelyPresented.{0,0,0} (R := ℚ) (P := Fin 1 → ℝ)
      (CoordinateRealBridge.fromReal (essentialInterval b)) :=
  GradedFree.finitelyPresented_of_iso
    (GradedFree.free_finitelyPresented (R := ℚ) (P := Fin 1 → ℝ)
      (HookInfinity.generators (P := Fin 1 → ℝ) (fun _ : Fin 1 => b)))
    (principalHook_intervalIso (k := ℚ) (fun _ : Fin 1 => b))

/-- The explicit radius-one interleaving of the essential intervals born at `0`
and `1`, transported from the principal hooks. -/
private noncomputable def essentialIntervalInterleaving :
    CoordinateInterleaving 1 (CoordinateRealBridge.fromReal (essentialInterval 0))
      (CoordinateRealBridge.fromReal (essentialInterval 1)) :=
  (HookMatching.principalHookInterleavingOfBirthClose (k := ℚ)
    (a := fun _ : Fin 1 => (0 : ℝ)) (c := fun _ : Fin 1 => (1 : ℝ)) 1
    (fun _ => by norm_num) (fun _ => by norm_num)).congr
    (principalHook_intervalIso (k := ℚ) (fun _ : Fin 1 => (0 : ℝ)))
    (principalHook_intervalIso (k := ℚ) (fun _ : Fin 1 => (1 : ℝ)))

/-- The module-level isometry compares two distinct essential intervals, born
at `0` and `1`: the first has a nonzero fiber at `0`, where the second
vanishes, and their barcode bottleneck distance is at most the radius of the
explicit interleaving. -/
theorem distinct_essential_intervals_bottleneck_le_one :
    (∃ x : (essentialInterval 0).obj 0, x ≠ 0) ∧
    (∀ y : (essentialInterval 1).obj 0, y = 0) ∧
    bottleneck
        (finitelyPresentedOneDimensionalBarcodeDiagram (essentialInterval 0)
          (essentialInterval_original_finitePresentation 0))
        (finitelyPresentedOneDimensionalBarcodeDiagram (essentialInterval 1)
          (essentialInterval_original_finitePresentation 1)) ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · let x : (essentialInterval 0).obj 0 := ⟨1, by
      have ha : RealBarcode.alive (0, (⊤ : WithTop ℝ)) 0 :=
        ⟨le_rfl, WithTop.coe_lt_top 0⟩
      simp only [RealBarcode.fiber, if_pos ha, Submodule.mem_top]⟩
    refine ⟨x, ?_⟩
    intro hx
    have hval := congrArg Subtype.val hx
    change (1 : ℚ) = 0 at hval
    norm_num at hval
  · intro y
    have hna : ¬ RealBarcode.alive (1, (⊤ : WithTop ℝ)) 0 := fun h =>
      absurd h.1 (by norm_num)
    have hy : y.val ∈ RealBarcode.fiber (k := ℚ) (1, (⊤ : WithTop ℝ)) 0 := y.property
    simp only [RealBarcode.fiber, if_neg hna, Submodule.mem_bot] at hy
    exact Subtype.ext hy
  · rw [finitelyPresentedOneDimensionalBarcode_bottleneck_eq_coordinateDistance (k := ℚ)]
    simpa using essentialIntervalInterleaving.distance_le

end TDA.Persistence.RankSignedBarcodeOneDimensionalExamples
