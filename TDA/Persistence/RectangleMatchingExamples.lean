import TDA.Persistence.RectangleMatching

/-!
# Consumers of two-sided rectangle matching

Repeated long rectangles force coverage of both occurrence sets by the same
matching. Half-open and closed intervals behave differently at their exact
double-shift width. Singleton-to-empty interleavings exercise actual unmatched
module witnesses on both sides; zero parameter and empty families are included.
-/

set_option autoImplicit false

namespace TDA.Persistence.RectangleMatching.Examples

open CategoryTheory CategoryTheory.Limits CoordinateShift RectangleHall
open scoped TDA.Persistence NNReal ZeroObject Classical

private def closedBox (n : ℕ) : Rectangle n := fun _ =>
  { lower := 0, upper := 6, lowerClosed := true, upperClosed := true
    nonempty := Or.inl (by norm_num) }

private theorem box_significant (n : ℕ) : Significant 6 (closedBox n) := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro j <;>
    norm_num [Rectangle.support, BoundedInterval.support, closedBox, translation_apply]

/-- The same matching covers all two source and two target occurrences,
although every rectangle has the same value. The radius in dimension two is 3. -/
theorem repeated_two_sided :
    ∃ M : OccurrenceMatching Bool Bool PEmpty.{1} PEmpty.{1},
      IsMatching (k := ℚ) 3 (fun _ => closedBox 2) (fun _ => closedBox 2) M ∧
      (∀ i, ∃ j, M.finite i = some j) ∧ (∀ j, ∃ i, M.finite i = some j) := by
  obtain ⟨M, hM⟩ := exists_matching (k := ℚ) (by decide : 0 < 2)
    (fun _ : Bool => closedBox 2) (fun _ : Bool => closedBox 2) 1
    (CoordinateInterleaving.refl 1 _)
  have hM' : IsMatching (k := ℚ) 3 (fun _ => closedBox 2) (fun _ => closedBox 2) M := by
    simpa [RectangleStabilityGeometry.stabilityRadius] using hM
  have hs : Significant (3 + 3) (closedBox 2) := by
    norm_num
    exact box_significant 2
  exact ⟨M, hM', fun i => hM'.source_covered i hs,
    fun j => hM'.target_covered j hs⟩

private def singleton : Rectangle 1 := fun _ =>
  { lower := 0, upper := 0, lowerClosed := true, upperClosed := true
    nonempty := Or.inr ⟨rfl, rfl, rfl⟩ }

private theorem singleton_significant_zero : Significant 0 singleton := by
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro j <;>
    norm_num [Rectangle.support, BoundedInterval.support, singleton, translation_apply]

/-- At ε=0 even repeated singleton rectangles must all be paired on both sides. -/
theorem zero_parameter_coverage :
    ∃ M : OccurrenceMatching Bool Bool PEmpty.{1} PEmpty.{1},
      IsMatching (k := ℚ) 0 (fun _ => singleton) (fun _ => singleton) M ∧
      (∀ i, ∃ j, M.finite i = some j) ∧ (∀ j, ∃ i, M.finite i = some j) := by
  obtain ⟨M, hM⟩ := exists_matching (k := ℚ) (by decide : 0 < 1)
    (fun _ : Bool => singleton) (fun _ : Bool => singleton) 0
    (CoordinateInterleaving.refl 0 _)
  have hM' : IsMatching (k := ℚ) 0 (fun _ => singleton) (fun _ => singleton) M := by
    simpa [RectangleStabilityGeometry.stabilityRadius] using hM
  have hs : Significant (0 + 0) singleton := by simpa using singleton_significant_zero
  exact ⟨M, hM', fun i => hM'.source_covered i hs,
    fun j => hM'.target_covered j hs⟩

private def bar (closed : Bool) : Rectangle 1 := fun _ =>
  { lower := 0, upper := 2, lowerClosed := true, upperClosed := closed
    nonempty := Or.inl (by norm_num) }

/-- A half-open bar at its exact double-shift width can be deleted. -/
theorem halfOpen_zero :
    Nonempty (CoordinateInterleaving 1 ((bar false).module (k := ℚ)) 0) := by
  apply (interleaved_zero_iff _ _).mpr
  rintro ⟨p, hp, hp'⟩
  have h := hp 0
  have h' := hp' 0
  norm_num only [show (1 + 1 : ℝ≥0) = 2 by norm_num] at h'
  change (0 < p 0 ∨ (0 = p 0 ∧ true = true)) ∧ _ at h
  change _ ∧ (p 0 + 2 < 2 ∨ (p 0 + 2 = 2 ∧ false = true)) at h'
  rcases h.1 with h | ⟨h, _⟩ <;>
    (rcases h'.2 with h' | ⟨_, h'⟩ <;> simp_all <;> linarith)

/-- Including the final endpoint prevents deletion at that same parameter. -/
theorem closed_not_zero :
    ¬ Nonempty (CoordinateInterleaving 1 ((bar true).module (k := ℚ)) 0) := by
  rw [interleaved_zero_iff, not_not]
  refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro j <;>
    norm_num [Rectangle.support, BoundedInterval.support, bar, translation_apply]

private instance : HasFiniteBiproducts (PModule.{0,0,0} ℚ (Fin 1 → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def singleIso :
    RectangleFamily.module (k := ℚ) (fun _ : Unit => bar false) ≅ (bar false).module :=
  biproductUniqueIso (fun _ : Unit => (bar false).module (k := ℚ))

private noncomputable def emptyIso :
    RectangleFamily.module (k := ℚ) (fun i : Fin 0 => Fin.elim0 i) ≅
      (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) := by
  apply IsZero.isoZero
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro i
  exact Fin.elim0 i

private noncomputable def deleteBar : CoordinateInterleaving 1
    (RectangleFamily.module (k := ℚ) (fun _ : Unit => bar false))
    (RectangleFamily.module (fun i : Fin 0 => Fin.elim0 i)) :=
  halfOpen_zero.some.congr singleIso.symm emptyIso.symm

/-- The capstone supplies an actual source deletion when the target is empty. -/
theorem empty_target_deletion :
    ∃ M : OccurrenceMatching Unit (Fin 0) PEmpty.{1} PEmpty.{1},
      IsMatching (k := ℚ) 1 (fun _ => bar false) (fun i => Fin.elim0 i) M ∧
      M.finite () = none := by
  obtain ⟨M, hM⟩ := exists_matching (by decide : 0 < 1) _ _ 1 deleteBar
  refine ⟨M, ?_, ?_⟩
  · simpa [RectangleStabilityGeometry.stabilityRadius] using hM
  · cases h : M.finite () with
    | none => rfl
    | some j => exact Fin.elim0 j

/-- Reversing that actual interleaving exercises target deletion in the same API. -/
theorem empty_source_deletion :
    ∃ M : OccurrenceMatching (Fin 0) Unit PEmpty.{1} PEmpty.{1},
      IsMatching (k := ℚ) 1 (fun i => Fin.elim0 i) (fun _ => bar false) M ∧
      Nonempty (CoordinateInterleaving 1 ((bar false).module (k := ℚ)) 0) := by
  obtain ⟨M, hM⟩ := exists_matching (by decide : 0 < 1) _ _ 1 deleteBar.symm
  have hM' : IsMatching (k := ℚ) 1 (fun i => Fin.elim0 i) (fun _ => bar false) M := by
    simpa [RectangleStabilityGeometry.stabilityRadius] using hM
  exact ⟨M, hM', hM'.target_zero () (fun i => Fin.elim0 i)⟩

/-- Empty occurrence types are admitted by the actual matching capstone. -/
theorem empty_families :
    ∃ M : OccurrenceMatching (Fin 0) (Fin 0) PEmpty.{1} PEmpty.{1},
      IsMatching (k := ℚ) (n := 1) 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) M := by
  simpa [RectangleStabilityGeometry.stabilityRadius] using
    (exists_matching (k := ℚ) (by decide : 0 < 1)
      (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i) 0
      (CoordinateInterleaving.refl 0 _))

end TDA.Persistence.RectangleMatching.Examples
