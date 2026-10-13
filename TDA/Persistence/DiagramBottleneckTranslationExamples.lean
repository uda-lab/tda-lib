import TDA.Persistence.DiagramBottleneckTranslation
import TDA.Persistence.FiniteFilterStabilitySingletonExamples

namespace TDA.Persistence.TranslationExamples

open TDA.Persistence
open scoped ENNReal

private def essentialInput (b : ℝ) : (Fin 0 → ℝ × ℝ) × (Fin 1 → ℝ) :=
  (Fin.elim0, fun _ => b)

/-- A single essential birth moves by exactly `|c|` for either sign of `c`,
including zero. -/
theorem essential_singleton_translation (b c : ℝ) :
    bottleneck (orderedQ 0 1 (essentialInput b))
      (translateDiagram (orderedQ 0 1 (essentialInput b)) c) =
        ENNReal.ofReal |c| := by
  apply bottleneck_translate_eq_of_essential
  simp [essentialPart_orderedQ, essentialInput]

private def repeatedReversedInput : (Fin 2 → ℝ × ℝ) × (Fin 2 → ℝ) :=
  (fun _ => (3, 1), fun _ => 4)

/-- Repeated reversed finite pairs and repeated essential births retain their
multiplicity under translation; the exact distance is still `|c|`. -/
theorem repeated_reversed_translation (c : ℝ) :
    bottleneck (orderedQ 2 2 repeatedReversedInput)
      (translateDiagram (orderedQ 2 2 repeatedReversedInput) c) =
        ENNReal.ofReal |c| := by
  apply bottleneck_translate_eq_of_essential
  simp [essentialPart_orderedQ, repeatedReversedInput]

private def emptyInput : (Fin 0 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (Fin.elim0, Fin.elim0)

/-- The empty diagram is fixed by translation and has distance zero, so essential
nonemptiness is necessary for the general equality. -/
theorem empty_translation_distance_zero (c : ℝ) :
    bottleneck (orderedQ 0 0 emptyInput)
      (translateDiagram (orderedQ 0 0 emptyInput) c) = 0 := by
  have h : translateDiagram (orderedQ 0 0 emptyInput) c = orderedQ 0 0 emptyInput := by
    apply Diagram.ext
    simp [translateDiagram, translateDiagramPoint, emptyInput, orderedQ]
  rw [h]
  exact bottleneck_self _

private def finiteSource : (Fin 1 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (fun _ => (0, 2), Fin.elim0)

private def finiteTarget : (Fin 1 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (fun _ => (3, 5), Fin.elim0)

/-- A finite-only singleton `(0,2)` shifted by `3` has bottleneck distance `1`:
deleting both points costs `1`, while matching them costs `3`. -/
theorem finite_only_translation_counterexample :
    bottleneck (orderedQ 1 0 finiteSource) (orderedQ 1 0 finiteTarget) =
      ENNReal.ofReal 1 := by
  let x : Fin 1 → ℝ × ℝ := fun _ => (0, 2)
  let y : Fin 1 → ℝ × ℝ := fun _ => (3, 5)
  have hx : (Finset.univ : Finset (Fin 1)).val.map x =
      finitePart (orderedQ 1 0 finiteSource).points := by
    rw [finitePart_orderedQ]
    simp [finiteSource, x]
  have hy : (Finset.univ : Finset (Fin 1)).val.map y =
      finitePart (orderedQ 1 0 finiteTarget).points := by
    rw [finitePart_orderedQ]
    simp [finiteTarget, y]
  have hb : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) = essentialPart (orderedQ 1 0 finiteSource).points := by
    rw [essentialPart_orderedQ]
    simp [finiteSource]
  have hc : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) = essentialPart (orderedQ 1 0 finiteTarget).points := by
    rw [essentialPart_orderedQ]
    simp [finiteTarget]
  rw [bottleneck_eq_presentation (orderedQ 1 0 finiteSource)
    (orderedQ 1 0 finiteTarget) x y (Fin.elim0 : Fin 0 → ℝ)
    (Fin.elim0 : Fin 0 → ℝ) hx hy hb hc]
  apply le_antisymm
  · let M₀ : OccurrenceMatching (Fin 1) (Fin 1) (Fin 0) (Fin 0) :=
      ⟨fun _ => none, by simp, Equiv.refl _⟩
    have hcost : M₀.cost x y Fin.elim0 Fin.elim0 = ENNReal.ofReal 1 := by
      simp [OccurrenceMatching.cost, M₀, x, y, diagonalCost]
      norm_num
    exact (presentationBottleneck_le_cost x y Fin.elim0 Fin.elim0 M₀).trans_eq hcost
  · unfold presentationBottleneck
    apply le_iInf
    intro M
    have hsource := M.source_le_cost x y Fin.elim0 Fin.elim0 0
    cases h : M.finite 0 with
    | none =>
      calc
        ENNReal.ofReal 1 = diagonalCost (x 0) := by norm_num [x, diagonalCost]
        _ ≤ M.cost x y Fin.elim0 Fin.elim0 := by simpa [h] using hsource
    | some j =>
      calc
        ENNReal.ofReal 1 ≤ finitePairCost (x 0) (y j) := by
          norm_num [x, y, finitePairCost]
        _ ≤ M.cost x y Fin.elim0 Fin.elim0 := by simpa [h] using hsource

/-- The preceding finite-only pair really is the pointwise translate by `3`,
yet its bottleneck distance is strictly smaller than `3`. -/
theorem finite_only_shift_three_distance :
    bottleneck (orderedQ 1 0 finiteSource)
      (translateDiagram (orderedQ 1 0 finiteSource) 3) = ENNReal.ofReal 1 := by
  have hshift : translateDiagram (orderedQ 1 0 finiteSource) 3 =
      orderedQ 1 0 finiteTarget := by
    apply Diagram.ext
    norm_num [translateDiagram, translateDiagramPoint, orderedQ, finiteSource, finiteTarget]
  rw [hshift]
  exact finite_only_translation_counterexample

/-- The actual one-vertex degree-zero diagram is essential, and translating its
face value by `c` moves it by exactly `|c|`. -/
theorem isolated_vertex_translation_exact (a c : ℝ) :
    bottleneck
      (dgm (ZMod 2) (StabilityExamples.vertexFilter a) 0)
      (dgm (ZMod 2)
        (translateFilterFunction (StabilityExamples.vertexFilter a) c) 0) =
      ENNReal.ofReal |c| := by
  have hfilter :
      translateFilterFunction (StabilityExamples.vertexFilter a) c =
        StabilityExamples.vertexFilter (a + c) := by
    rfl
  rw [hfilter, StabilityExamples.vertex_bottleneck_sharp]
  simp [show a - (a + c) = -c by ring]

end TDA.Persistence.TranslationExamples
