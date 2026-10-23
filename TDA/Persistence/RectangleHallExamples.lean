import TDA.Persistence.RectangleHall

/-!
# Consumers of the finite rectangle Hall inequality

The examples retain occurrences of the same rectangle separately, test the
critical closed-endpoint case of composition, and compare it with a half-open
interval that dies at its width. The empty selection and zero parameter are
included.
-/

set_option autoImplicit false

namespace TDA.Persistence.RectangleHall.Examples

open CategoryTheory CoordinateShift RectangleStabilityGeometry
open scoped TDA.Persistence NNReal

private def closedBar (a : ℝ) : Rectangle 1 := fun _ =>
  { lower := a, upper := a + 2, lowerClosed := true, upperClosed := true
    nonempty := Or.inl (by linarith) }

private theorem closedBar_significant (a : ℝ) : Significant 2 (closedBar a) := by
  refine ⟨fun _ => a, ?_, ?_⟩ <;> intro j <;>
    norm_num [Rectangle.support, BoundedInterval.support, closedBar, translation_apply]

private theorem forward_bounds (a : ℝ) : ∀ j,
    decoratedLE (endpoint (closedBar a) j)
      (endpoint (closedBar a) j + (1 : ℝ))
      (plus (closedBar a) j) (plus (closedBar a) j) := by
  rintro ⟨j, b⟩
  cases b <;> norm_num [decoratedLE, endpoint, plus, closedBar, add_assoc]

private noncomputable def forward (a : ℝ) :
    (closedBar a).module (k := ℚ) ⟶ (shift 1).obj (closedBar a).module :=
  comparison _ _ 1 (forward_bounds a)

private theorem forward_coefficient (a : ℝ) :
    shiftedCoefficient (closedBar a) (closedBar a) 1 (forward a) = 1 := by
  apply shiftedCoefficient_comparison (p := fun _ => a)
  · intro j
    norm_num [Rectangle.support, BoundedInterval.support, closedBar]
  · intro j
    norm_num [Rectangle.support, BoundedInterval.support, closedBar, translation_apply]

/-- A bar of width two overlaps its twice-shifted copy at just its lower
endpoint; this certifies the critical support geometry of the next example. -/
theorem closed_double_overlap (a : ℝ) :
    {p : Fin 1 → ℝ | p ∈ (closedBar a).support ∧
      translation 2 p ∈ (closedBar a).support} = {fun _ => a} := by
  ext p
  constructor
  · rintro ⟨hp, hp'⟩
    apply Set.mem_singleton_iff.mpr
    funext j
    have h := hp j
    have h' := hp' j
    change (a < p j ∨ (a = p j ∧ true = true)) ∧ _ at h
    change _ ∧ (p j + 2 < a + 2 ∨ (p j + 2 = a + 2 ∧ true = true)) at h'
    rcases h.1 with h | ⟨h, _⟩ <;>
      (rcases h'.2 with h' | ⟨h', _⟩ <;> linarith)
  · intro hp
    have he := Set.mem_singleton_iff.mp hp
    subst p
    constructor <;> intro j <;>
      norm_num [Rectangle.support, BoundedInterval.support, closedBar, translation_apply]

/-- The twice-shifted overlap is a single closed endpoint. The composition
law still gives one, so the path is nonzero at the critical significance bound. -/
theorem closed_boundary_composite (a : ℝ) :
    shiftedCoefficient (closedBar a) (closedBar a) (1 + 1)
      (forward a ≫ (shift 1).map (forward a) ≫
        (compIso 1 1 ((closedBar a).module (k := ℚ))).hom) = 1 := by
  have hα : alphaLE (closedBar a) (closedBar a) := Or.inr ⟨rfl, le_rfl⟩
  have he := shiftedCoefficient_composite (k := ℚ) (by decide : 0 < 1)
    (closedBar a) (closedBar a) (closedBar a) 1 hα
    (by
      convert closedBar_significant a using 1
      norm_num [stabilityRadius, Significant])
    (by
      convert closedBar_significant a using 1
      norm_num [stabilityRadius, Significant])
    (forward a) (forward a)
  simpa only [forward_coefficient, one_mul] using he

private def halfOpenBar : Rectangle 1 := fun _ =>
  { lower := 0, upper := 2, lowerClosed := true, upperClosed := false
    nonempty := Or.inl (by norm_num) }

/-- Excluding the final endpoint kills the transition at exactly the width. -/
theorem halfOpen_dies_at_width : ¬ Significant 2 halfOpenBar := by
  rintro ⟨p, hp, hp'⟩
  have h := hp 0
  have h' := hp' 0
  change (0 < p 0 ∨ (0 = p 0 ∧ true = true)) ∧ _ at h
  change _ ∧ (p 0 + 2 < 2 ∨ (p 0 + 2 = 2 ∧ false = true)) at h'
  rcases h.1 with h | ⟨h, _⟩ <;>
    (rcases h'.2 with h' | ⟨_, h'⟩ <;> simp_all <;> linarith)

/-- Two equal occurrences still require two target occurrences at positive
width; the proof consumes the actual family interleaving. -/
theorem repeated_occurrences :
    2 ≤ (neighbors (k := ℚ)
      (fun _ : Bool => closedBar 0) (fun _ : Bool => closedBar 0)
      Finset.univ (stabilityRadius 1 1)).card := by
  have h := card_le_neighbors (k := ℚ) (by decide : 0 < 1)
    (fun _ : Bool => closedBar 0) (fun _ : Bool => closedBar 0) 1
    (CoordinateInterleaving.refl 1 _) Finset.univ
    (fun i hi => by convert closedBar_significant 0 using 1; norm_num [stabilityRadius])
  simpa using h

private def closedSquare : Rectangle 2 := fun _ =>
  { lower := 0, upper := 6, lowerClosed := true, upperClosed := true
    nonempty := Or.inl (by norm_num) }

/-- The two-coordinate coefficient is three; closed squares of width six
remain significant at its doubled threshold. -/
theorem two_parameter_occurrences :
    2 ≤ (neighbors (k := ℚ)
      (fun _ : Bool => closedSquare) (fun _ : Bool => closedSquare)
      Finset.univ 3).card := by
  have hp : Significant 6 closedSquare := by
    refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro j <;>
      norm_num [Rectangle.support, BoundedInterval.support, closedSquare, translation_apply]
  have h := card_le_neighbors (k := ℚ) (by decide : 0 < 2)
    (fun _ : Bool => closedSquare) (fun _ : Bool => closedSquare) 1
    (CoordinateInterleaving.refl 1 _) Finset.univ
    (fun i hi => by convert hp using 1; norm_num [stabilityRadius])
  norm_num [stabilityRadius] at h
  exact h

private def closedPoint : Rectangle 1 := fun _ =>
  { lower := 0, upper := 0, lowerClosed := true, upperClosed := true
    nonempty := Or.inr ⟨rfl, rfl, rfl⟩ }

/-- Closed singletons survive at zero and count as significant occurrences. -/
theorem zero_parameter_singleton :
    1 ≤ (neighbors (k := ℚ)
      (fun _ : Unit => closedPoint) (fun _ : Unit => closedPoint)
      Finset.univ (stabilityRadius 1 0)).card := by
  have hp : Significant 0 closedPoint := by
    refine ⟨fun _ => 0, ?_, ?_⟩ <;> intro j <;>
      norm_num [Rectangle.support, BoundedInterval.support, closedPoint, translation_apply]
  have h := card_le_neighbors (k := ℚ) (by decide : 0 < 1)
    (fun _ : Unit => closedPoint) (fun _ : Unit => closedPoint) 0
    (CoordinateInterleaving.refl 0 _) Finset.univ
    (fun i hi => by simpa [stabilityRadius] using hp)
  exact h

/-- Both empty family indices are accepted by the same matrix argument. -/
theorem empty_families (ε : ℝ≥0) :
    (Finset.univ : Finset (Fin 0)).card ≤
      (neighbors (n := 1) (k := ℚ) (fun i : Fin 0 => i.elim0)
        (fun i : Fin 0 => i.elim0) Finset.univ (stabilityRadius 1 ε)).card := by
  exact card_le_neighbors (k := ℚ) (by decide : 0 < 1)
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) ε
    (CoordinateInterleaving.refl ε _) Finset.univ (fun i _ => i.elim0)

/-- An empty selection uses the same public Hall theorem. -/
theorem empty_selection (ε : ℝ≥0) :
    0 ≤ (neighbors (k := ℚ) (fun _ : Bool => closedBar 0)
      (fun _ : Bool => closedBar 0) ∅ (stabilityRadius 1 ε)).card := by
  have h := card_le_neighbors (k := ℚ) (by decide : 0 < 1)
    (fun _ : Bool => closedBar 0) (fun _ : Bool => closedBar 0) ε
    (CoordinateInterleaving.refl ε _) ∅ (by simp)
  exact h

end TDA.Persistence.RectangleHall.Examples
