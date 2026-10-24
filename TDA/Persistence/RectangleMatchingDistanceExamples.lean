import TDA.Persistence.RectangleMatchingDistance
import TDA.Persistence.RectangleMatchingExamples

/-!
# Consumers of rectangle matching assembly and distance bounds

A partial matching swaps two distinct long intervals and deletes a singleton
on each side. Its assembled component maps detect the swap and the zero
deletion paths. Closed and half-open endpoint thresholds are retained.
A singleton versus the empty family has both distances zero but neither a
zero-radius matching nor a zero-radius interleaving, so the infimum is not attained.
-/

set_option autoImplicit false

namespace TDA.Persistence.RectangleMatching.DistanceExamples

open CategoryTheory CategoryTheory.Limits CoordinateShift RectangleFamily RectangleHall
  RectangleStabilityGeometry
open scoped TDA.Persistence NNReal ENNReal Classical ZeroObject

private def point (a : ℝ) : Rectangle 1 := fun _ =>
  { lower := a, upper := a, lowerClosed := true, upperClosed := true
    nonempty := Or.inr ⟨rfl, rfl, rfl⟩ }

private theorem point_mem_iff (a : ℝ) (p : Fin 1 → ℝ) :
    p ∈ (point a).support ↔ ∀ j, p j = a := by
  constructor
  · intro hp j
    have h := hp j
    change (a < p j ∨ (a = p j ∧ true = true)) ∧
      (p j < a ∨ (p j = a ∧ true = true)) at h
    have hu := h.2
    rcases h.1 with h | ⟨h, _⟩ <;>
      (rcases hu with h' | ⟨h', _⟩ <;> linarith)
  · intro h j
    simp [point, BoundedInterval.support, h j]

private theorem point_zero (a : ℝ) (ε : ℝ≥0) (hε : 0 < ε) :
    Nonempty (CoordinateInterleaving ε ((point a).module (k := ℚ)) 0) := by
  apply (interleaved_zero_iff _ _).mpr
  rintro ⟨p, hp, hq⟩
  have hp' := (point_mem_iff a p).mp hp 0
  have hq' := (point_mem_iff a (translation (ε + ε) p)).mp hq 0
  change p 0 + ((ε + ε : ℝ≥0) : ℝ) = a at hq'
  rw [NNReal.coe_add] at hq'
  have he : 0 < (ε : ℝ) := hε
  linarith

/-- A closed singleton cannot be deleted at parameter zero. -/
theorem point_not_zero (a : ℝ) :
    ¬ Nonempty (CoordinateInterleaving 0 ((point a).module (k := ℚ)) 0) := by
  rw [interleaved_zero_iff, not_not]
  refine ⟨fun _ => a, ?_, ?_⟩ <;> intro j <;>
    norm_num [point, Rectangle.support, BoundedInterval.support, translation_apply]

private def longBar (a : ℝ) : Rectangle 1 := fun _ =>
  { lower := a, upper := a + 6, lowerClosed := true, upperClosed := true
    nonempty := Or.inl (by linarith) }

private def source : Option Bool → Rectangle 1
  | none => point 0
  | some false => longBar 0
  | some true => longBar 10

private def target : Option Bool → Rectangle 1
  | none => point 20
  | some false => longBar 10
  | some true => longBar 0

private def swapDelete : OccurrenceMatching (Option Bool) (Option Bool) PEmpty.{1} PEmpty.{1} where
  finite i := match i with
    | none => none
    | some b => some (some (!b))
  finite_injective := by decide
  essential := Equiv.refl _

private theorem mixed_matching : IsMatching (k := ℚ) 1 source target swapDelete := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (_ | b) j h
    · simp [swapDelete] at h
    · cases b <;> simp [swapDelete] at h <;> subst j <;>
        exact ⟨CoordinateInterleaving.refl 1 _⟩
  · rintro (_ | b) h
    · exact point_zero 0 1 (by norm_num)
    · simp [swapDelete] at h
  · rintro (_ | b) h
    · exact point_zero 20 1 (by norm_num)
    · exact False.elim (h (some (!b)) (by cases b <;> rfl))

/-- An actual interleaving assembled from a nontrivial permutation with
unmatched summands on both sides. -/
noncomputable def mixedInterleaving :
    CoordinateInterleaving 1 (module (k := ℚ) source) (module target) :=
  mixed_matching.interleaving

/-- The swapped long interval gives a nonzero component, while both deletion
directions give zero components. These use the public component interface. -/
theorem mixed_components :
    component source target 1 mixedInterleaving.φ (some false) (some true) ≠ 0 ∧
    component source target 1 mixedInterleaving.φ none (some false) = 0 ∧
    component target source 1 mixedInterleaving.ψ none (some false) = 0 := by
  constructor
  · obtain ⟨I, hφ, _⟩ := mixed_matching.interleaving_components (some false) (some true) rfl
    change component source target 1 mixed_matching.interleaving.φ _ _ ≠ 0
    rw [hφ]
    intro hz
    have hs : Significant (1 + 1) (source (some false)) := by
      refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro j <;>
        norm_num [source, longBar, Rectangle.support, BoundedInterval.support, translation_apply]
    have hn := (significant_iff_transition_ne_zero (k := ℚ) _ _).mp hs
    have he := I.φ_ψ
    rw [hz, zero_comp] at he
    exact hn he.symm
  · exact ⟨mixed_matching.interleaving_component_zero none (some false) (by decide),
      mixed_matching.interleaving_reverse_component_zero (some false) none (by decide)⟩

/-- The assembled positive-radius witness bounds both infima. -/
theorem mixed_distance_bounds :
    coordinateInterleavingDistance (module (k := ℚ) source) (module target) ≤ 1 ∧
    bottleneckDistance (k := ℚ) source target ≤ 1 :=
  ⟨mixedInterleaving.distance_le, bottleneckDistance_le_of_matching mixed_matching⟩

private def eraseAll (I J : Type) : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} where
  finite _ := none
  finite_injective := by intros; contradiction
  essential := Equiv.refl _

private def empty : Fin 0 → Rectangle 1 := Fin.elim0

private theorem point_matching (ε : ℝ≥0) (hε : 0 < ε) :
    IsMatching (k := ℚ) ε (fun _ : Unit => point 0) empty (eraseAll Unit (Fin 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; exact Fin.elim0 j
  · intro i _; exact point_zero 0 ε hε
  · intro j; exact Fin.elim0 j

/-- There are matching witnesses at every positive radius, but the infimum is zero. -/
theorem point_bottleneck_zero :
    bottleneckDistance (k := ℚ) (fun _ : Unit => point 0) empty = 0 := by
  apply nonpos_iff_eq_zero.mp
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  simpa using bottleneckDistance_le_of_matching (point_matching ε hε)

/-- The corresponding actual family interleaving distance is also zero. -/
theorem point_interleavingDistance_zero :
    coordinateInterleavingDistance (module (k := ℚ) (fun _ : Unit => point 0))
      (module empty) = 0 := by
  apply nonpos_iff_eq_zero.mp
  simpa [point_bottleneck_zero] using
    interleavingDistance_le_bottleneckDistance (k := ℚ) (fun _ : Unit => point 0) empty

/-- No zero-radius matching exists, although its bottleneck infimum is zero. -/
theorem point_no_zero_matching :
    ¬ ∃ M : OccurrenceMatching Unit (Fin 0) PEmpty.{1} PEmpty.{1},
      IsMatching (k := ℚ) 0 (fun _ => point 0) empty M := by
  rintro ⟨M, hM⟩
  have hm : M.finite () = none := by
    cases h : M.finite () with
    | none => rfl
    | some j => exact Fin.elim0 j
  exact point_not_zero 0 (hM.source_zero () hm)

/-- Zero interleaving distance here has no actual parameter-zero witness. -/
theorem point_no_zero_interleaving :
    ¬ Nonempty (CoordinateInterleaving 0
      (module (k := ℚ) (fun _ : Unit => point 0)) (module empty)) := by
  rintro ⟨I⟩
  obtain ⟨M, hM⟩ := exists_matching (by decide : 0 < 1) _ _ 0 I
  apply point_no_zero_matching
  exact ⟨M, by simpa [stabilityRadius] using hM⟩

private def halfOpen : Rectangle 1 := fun _ =>
  { lower := 0, upper := 2, lowerClosed := true, upperClosed := false
    nonempty := Or.inl (by norm_num) }

private theorem halfOpen_matching : IsMatching (k := ℚ) 1
    (fun _ : Unit => halfOpen) empty (eraseAll Unit (Fin 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; exact Fin.elim0 j
  · intro i _; exact RectangleMatching.Examples.halfOpen_zero
  · intro j; exact Fin.elim0 j

/-- The exact-width half-open deletion assembles in both orientations. -/
noncomputable def critical_halfOpen_assemblies :
    CoordinateInterleaving 1 (module (k := ℚ) (fun _ : Unit => halfOpen)) (module empty) ×
      CoordinateInterleaving 1 (module (k := ℚ) empty) (module (fun _ : Unit => halfOpen)) :=
  ⟨halfOpen_matching.interleaving, halfOpen_matching.reverse.interleaving⟩

private def criticalClosed : Rectangle 1 := fun _ =>
  { lower := 0, upper := 2, lowerClosed := true, upperClosed := true
    nonempty := Or.inl (by norm_num) }

/-- Closing the upper endpoint excludes deletion at that exact same radius. -/
theorem critical_closed_no_matching :
    ¬ ∃ M : OccurrenceMatching Unit (Fin 0) PEmpty.{1} PEmpty.{1},
      IsMatching (k := ℚ) 1 (fun _ => criticalClosed) empty M := by
  rintro ⟨M, hM⟩
  have hm : M.finite () = none := by
    cases h : M.finite () with
    | none => rfl
    | some j => exact Fin.elim0 j
  exact RectangleMatching.Examples.closed_not_zero (hM.source_zero () hm)

/-- Repeated occurrences remain present when a zero-radius matching is assembled. -/
noncomputable def repeated_zero_assembly : CoordinateInterleaving 0
    (module (k := ℚ) (fun _ : Bool => longBar 0)) (module (fun _ : Bool => longBar 0)) := by
  let h := exists_matching (k := ℚ) (by decide : 0 < 1)
    (fun _ : Bool => longBar 0) (fun _ : Bool => longBar 0) 0
    (CoordinateInterleaving.refl 0 _)
  let M := h.choose
  have hMraw : IsMatching (k := ℚ) (stabilityRadius 1 0)
      (fun _ : Bool => longBar 0) (fun _ : Bool => longBar 0) M := h.choose_spec
  have he : stabilityRadius 1 0 = 0 := by norm_num [stabilityRadius]
  have hM : IsMatching (k := ℚ) 0 (fun _ : Bool => longBar 0) (fun _ : Bool => longBar 0) M :=
    he ▸ hMraw
  exact hM.interleaving

/-- Empty two-coordinate families satisfy the same distance capstone. -/
theorem empty_bottleneck_zero : bottleneckDistance (k := ℚ) (n := 2)
    (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) = 0 := by
  apply nonpos_iff_eq_zero.mp
  simpa [coordinateInterleavingDistance_self] using
    bottleneckDistance_le_interleavingDistance (k := ℚ) (by decide : 0 < 2)
      (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)

end TDA.Persistence.RectangleMatching.DistanceExamples
