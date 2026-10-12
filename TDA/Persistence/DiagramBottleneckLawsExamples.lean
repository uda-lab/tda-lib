import TDA.Persistence.DiagramBottleneckLaws

namespace TDA.Persistence

private def singletonMatch : OccurrenceMatching (Fin 1) (Fin 1) (Fin 0) (Fin 0) where
  finite _ := some 0
  finite_injective := by intro i i' _ _ _; exact Subsingleton.elim i i'
  essential := Equiv.refl _

private def singletonDelete : OccurrenceMatching (Fin 1) (Fin 0) (Fin 0) (Fin 0) where
  finite _ := none
  finite_injective := by intro _ _ j; exact Fin.elim0 j
  essential := Equiv.refl _

private def singletonInsert : OccurrenceMatching (Fin 0) (Fin 1) (Fin 0) (Fin 0) where
  finite := Fin.elim0
  finite_injective := by intro i; exact Fin.elim0 i
  essential := Equiv.refl _

/-- A reversed pair can match a middle point that is deleted toward the last diagram. -/
example : (singletonMatch.compose singletonDelete).finite 0 = none ∧
    diagonalCost ((3 : ℝ), 1) ≤
      finitePairCost ((3 : ℝ), 1) ((4 : ℝ), 1) + diagonalCost ((4 : ℝ), 1) := by
  exact ⟨rfl, diagonalCost_le_pair_add _ _⟩

/-- The reverse unmatched-middle branch leaves the final occurrence on the diagonal. -/
example : (singletonInsert.compose singletonMatch).cost
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (fun _ => ((4 : ℝ), 1))
    (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) ≤
      singletonInsert.cost (Fin.elim0 : Fin 0 → ℝ × ℝ)
        (fun _ => ((3 : ℝ), 1)) Fin.elim0 Fin.elim0 +
      singletonMatch.cost (fun _ => ((3 : ℝ), 1))
        (fun _ => ((4 : ℝ), 1)) Fin.elim0 Fin.elim0 := by
  exact OccurrenceMatching.cost_compose_le _ _ _ _ _ _ _ _

/-- A middle occurrence unmatched on both sides introduces no endpoint cost. -/
example : (singletonInsert.compose singletonDelete).cost
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) = 0 := by
  simp [OccurrenceMatching.cost]

/-- A complete path composes to a match and obeys the coordinate triangle bound. -/
example : (singletonMatch.compose singletonMatch).finite 0 = some 0 ∧
    finitePairCost ((0 : ℝ), 2) ((2 : ℝ), 4) ≤
      finitePairCost ((0 : ℝ), 2) ((1 : ℝ), 3) +
        finitePairCost ((1 : ℝ), 3) ((2 : ℝ), 4) := by
  exact ⟨rfl, finitePairCost_triangle _ _ _⟩

/-- Reindexing both finite and essential occurrences, even with repeated values,
does not change the diagram or its zero self-distance. -/
theorem bottleneck_permuted_presentations (m n : ℕ)
    (x : Fin m → ℝ × ℝ) (b : Fin n → ℝ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    bottleneck (orderedQ m n (x ∘ σ, b ∘ τ)) (orderedQ m n (x, b)) = 0 := by
  rw [orderedQ_perm]
  exact bottleneck_self _

/-- Deleting one of two identical finite occurrences has positive cost. -/
theorem bottleneck_repeated_pair_ne_zero :
    bottleneck (orderedQ 2 0 (fun _ => ((0 : ℝ), 2), Fin.elim0))
      (orderedQ 1 0 (fun _ => ((0 : ℝ), 2), Fin.elim0)) ≠ 0 := by
  intro hz
  have heq := (bottleneck_eq_zero_iff _ _).mp hz
  have hc := congrArg (fun D : Diagram ℝ => (finitePart D.points).card) heq
  simp [finitePart_orderedQ] at hc

/-- The unconditional triangle includes unequal essential cardinalities. -/
example (D : Diagram ℝ) :
    bottleneck (orderedQ 0 0 (Fin.elim0, Fin.elim0)) D ≤
      bottleneck (orderedQ 0 0 (Fin.elim0, Fin.elim0))
        (orderedQ 0 1 (Fin.elim0, fun _ => (1 : ℝ))) +
      bottleneck (orderedQ 0 1 (Fin.elim0, fun _ => (1 : ℝ))) D :=
  bottleneck_triangle _ _ _

end TDA.Persistence
