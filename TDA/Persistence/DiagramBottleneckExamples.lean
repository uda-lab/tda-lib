import TDA.Persistence.DiagramBottleneck

namespace TDA.Persistence

private def emptyRealInput : (Fin 0 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (Fin.elim0, Fin.elim0)

private def reversedInput : (Fin 1 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (fun _ => (3, 1), Fin.elim0)

private def essentialInput (b : ℝ) : (Fin 0 → ℝ × ℝ) × (Fin 1 → ℝ) :=
  (Fin.elim0, fun _ => b)

private def duplicatedInput : (Fin 2 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (fun _ => (0, 2), Fin.elim0)

private def singleInput : (Fin 1 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (fun _ => (0, 2), Fin.elim0)

private def diagonalInput : (Fin 1 → ℝ × ℝ) × (Fin 0 → ℝ) :=
  (fun _ => (7, 7), Fin.elim0)

theorem bottleneck_empty_empty :
    bottleneck (orderedQ 0 0 emptyRealInput) (orderedQ 0 0 emptyRealInput) = 0 := by
  have h := bottleneck_orderedQ_le_norm 0 0 emptyRealInput emptyRealInput
  have hz : bottleneck (orderedQ 0 0 emptyRealInput)
      (orderedQ 0 0 emptyRealInput) ≤ 0 := by simpa using h
  exact le_antisymm hz bot_le

theorem bottleneck_reversed_singleton_empty :
    bottleneck (orderedQ 1 0 reversedInput) (orderedQ 0 0 emptyRealInput) = 1 := by
  have hx := orderedQ_finite_occurrences 1 0 reversedInput
  have hy : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        finitePart (orderedQ 0 0 emptyRealInput).points := by
    simp [finitePart_orderedQ]
  have hb : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) =
        essentialPart (orderedQ 1 0 reversedInput).points := by
    simp [essentialPart_orderedQ]
  have hc : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) =
        essentialPart (orderedQ 0 0 emptyRealInput).points := by
    simp [essentialPart_orderedQ]
  rw [bottleneck_eq_presentation (orderedQ 1 0 reversedInput)
    (orderedQ 0 0 emptyRealInput)
    (fun i : NonDiagonalIndices 1 reversedInput.1 => reversedInput.1 i.1)
    (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) hx hy hb hc]
  haveI : Nonempty (NonDiagonalIndices 1 reversedInput.1) :=
    ⟨⟨0, by norm_num [reversedInput]⟩⟩
  change presentationBottleneck
    (fun _ : NonDiagonalIndices 1 reversedInput.1 => ((3 : ℝ), (1 : ℝ)))
    Fin.elim0 Fin.elim0 Fin.elim0 = 1
  rw [presentationBottleneck_constant_empty]
  norm_num [diagonalCost]

theorem bottleneck_one_sided_diagonal :
    bottleneck (orderedQ 1 0 reversedInput) (orderedQ 1 0 diagonalInput) = 1 := by
  have hd : orderedQ 1 0 diagonalInput = orderedQ 0 0 emptyRealInput := by
    apply (orderedQ_eq_iff 1 0 0 0 diagonalInput emptyRealInput).mpr
    constructor <;> simp [diagonalInput, emptyRealInput]
  rw [hd]
  exact bottleneck_reversed_singleton_empty

theorem bottleneck_essential_singletons :
    bottleneck (orderedQ 0 1 (essentialInput 1))
      (orderedQ 0 1 (essentialInput 4)) = 3 := by
  have hf₁ : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        finitePart (orderedQ 0 1 (essentialInput 1)).points := by
    simp [finitePart_orderedQ]
  have hf₂ : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ × ℝ) =
        finitePart (orderedQ 0 1 (essentialInput 4)).points := by
    simp [finitePart_orderedQ]
  have he₁ := orderedQ_essential_occurrences 0 1 (essentialInput 1)
  have he₂ := orderedQ_essential_occurrences 0 1 (essentialInput 4)
  rw [bottleneck_eq_presentation _ _
    (Fin.elim0 : Fin 0 → ℝ × ℝ) (Fin.elim0 : Fin 0 → ℝ × ℝ)
    (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (4 : ℝ))
    hf₁ hf₂ (by simpa [essentialInput] using he₁)
      (by simpa [essentialInput] using he₂)]
  rw [presentationBottleneck_essential_singletons]
  norm_num [essentialPairCost]

theorem bottleneck_unequal_essential_counts :
    bottleneck (orderedQ 0 0 emptyRealInput)
      (orderedQ 0 1 (essentialInput 1)) = ⊤ := by
  apply (bottleneck_eq_top_iff _ _).mpr
  simp [essentialPart_orderedQ, emptyRealInput, essentialInput]

theorem bottleneck_repeated_pair_detected :
    bottleneck (orderedQ 2 0 duplicatedInput) (orderedQ 1 0 singleInput) = 1 := by
  have hf₁ : (Finset.univ : Finset (Fin 2)).val.map (fun _ => ((0 : ℝ), (2 : ℝ))) =
      finitePart (orderedQ 2 0 duplicatedInput).points := by
    rw [finitePart_orderedQ]
    simp [duplicatedInput, List.ofFn_eq_map, ← Finset.val_univ_fin]
    rfl
  have hf₂ : (Finset.univ : Finset (Fin 1)).val.map (fun _ => ((0 : ℝ), (2 : ℝ))) =
      finitePart (orderedQ 1 0 singleInput).points := by
    rw [finitePart_orderedQ]
    simp [singleInput, List.ofFn_eq_map, ← Finset.val_univ_fin]
  have he₁ : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) = essentialPart (orderedQ 2 0 duplicatedInput).points := by
    simp [essentialPart_orderedQ]
  have he₂ : (Finset.univ : Finset (Fin 0)).val.map
      (Fin.elim0 : Fin 0 → ℝ) = essentialPart (orderedQ 1 0 singleInput).points := by
    simp [essentialPart_orderedQ]
  rw [bottleneck_eq_presentation _ _
    (fun _ : Fin 2 => ((0 : ℝ), (2 : ℝ)))
    (fun _ : Fin 1 => ((0 : ℝ), (2 : ℝ)))
    (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)
    hf₁ hf₂ he₁ he₂]
  rw [presentationBottleneck_two_equal_vs_one]
  norm_num [diagonalCost]

end TDA.Persistence
