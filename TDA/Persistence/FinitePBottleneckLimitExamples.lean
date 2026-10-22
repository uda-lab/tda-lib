import TDA.Persistence.FinitePBottleneckLimit
import TDA.Persistence.DiagramBottleneckExamples

/-!
# Bottleneck limits on finite diagrams

Unit-height bars test empty inputs, occurrence multiplicity and a pair-and-delete matching. Essential singleton births show the necessity of
excluding essential bars from the finite-part limit theorem.
-/

noncomputable section
namespace TDA.Persistence.FinitePBottleneckLimitExamples
open Filter
open scoped Classical Topology

/-- A diagram with `n` copies of the positive bar `(0,2)`. -/
def unitBars (n : ℕ) : Diagram ℝ :=
  orderedQ n 0 (fun _ => (0, 2), Fin.elim0)

private theorem unitBars_finitePart (n : ℕ) :
    finitePart (unitBars n).points = Multiset.replicate n ((0, 2) : ℝ × ℝ) := by
  simp [unitBars, finitePart_orderedQ, List.ofFn_const, Multiset.coe_replicate]

private theorem unitBars_essentialPart (n : ℕ) : essentialPart (unitBars n).points = 0 := by
  simp [unitBars, essentialPart_orderedQ]

private theorem unitBars_card (n : ℕ) : Fintype.card (unitBars n).finiteOccurrences = n := by
  simp only [Multiset.card_coe, unitBars_finitePart, Multiset.card_replicate]

private theorem unitBars_coordinates (n : ℕ) (q : (unitBars n).finiteOccurrences) :
    q.1 = ((0, 2) : ℝ × ℝ) := by
  have h := Multiset.coe_mem (x := q)
  exact Multiset.eq_of_mem_replicate (by simpa only [unitBars_finitePart] using h)

/-- Every retained finite occurrence has strictly positive lifetime. -/
theorem unitBars_positive (n : ℕ) : (unitBars n).IsPositive := by
  apply (orderedQ_isPositive_iff _ _ _).mpr
  intro i
  norm_num

private instance empty_occurrences : IsEmpty (unitBars 0).finiteOccurrences :=
  Fintype.card_eq_zero_iff.mp (unitBars_card 0)

theorem empty_occurrence_count :
    Fintype.card (unitBars 0).finiteOccurrences +
      Fintype.card (unitBars 0).finiteOccurrences = 0 := by
  rw [unitBars_card]

private theorem unitBars_to_empty (n : ℕ) (p : ℝ) :
    finitePMatchingCost p (fun q : (unitBars n).finiteOccurrences => q.1)
      (fun q : (unitBars 0).finiteOccurrences => q.1) = (n : ℝ) ^ p⁻¹ := by
  rw [finitePMatchingCost_of_isEmpty_right]
  have hd : (diagonalCost ((0, 2) : ℝ × ℝ)).toReal = 1 := by norm_num [diagonalCost]
  simp only [unitBars_coordinates, hd, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    unitBars_card, nsmul_eq_mul, mul_one]

private theorem unitBars_bottleneck_empty (n : ℕ) (hn : 0 < n) :
    bottleneck (unitBars n) (unitBars 0) = 1 := by
  have : Nonempty (unitBars n).finiteOccurrences :=
    Fintype.card_pos_iff.mp (by rw [unitBars_card]; exact hn)
  have hz : unitBars 0 = orderedQ 0 0
      ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ)) := by
    apply Diagram.ext
    simp [unitBars, orderedQ]
  rw [hz]
  rw [bottleneck_finite_only_empty _ (unitBars_essentialPart n)]
  simp only [unitBars_coordinates]
  norm_num [diagonalCost]
  exact Finset.sup_const Finset.univ_nonempty 1

/-- Empty finite occurrence families exercise the zero-cardinality branch. -/
theorem empty_costs_eventually_zero :
    (∀ᶠ p : ℝ in atTop,
      finitePMatchingCost p (fun q : (unitBars 0).finiteOccurrences => q.1)
        (fun q : (unitBars 0).finiteOccurrences => q.1) = 0 ∧
      finitePBoundaryTransportCost p (fun q : (unitBars 0).finiteOccurrences => q.1)
        (fun q : (unitBars 0).finiteOccurrences => q.1) = 0) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with p hp
  exact ⟨finitePMatchingCost_empty hp _ _, finitePBoundaryTransportCost_empty hp _ _⟩

theorem empty_bottleneck_zero : bottleneck (unitBars 0) (unitBars 0) = 0 :=
  bottleneck_empty_empty

theorem empty_costs_tendsto_zero :
    Tendsto (fun p : ℝ => finitePMatchingCost p
      (fun q : (unitBars 0).finiteOccurrences => q.1)
      (fun q : (unitBars 0).finiteOccurrences => q.1)) atTop (𝓝 0) ∧
    Tendsto (fun p : ℝ => finitePBoundaryTransportCost p
      (fun q : (unitBars 0).finiteOccurrences => q.1)
      (fun q : (unitBars 0).finiteOccurrences => q.1)) atTop (𝓝 0) := by
  constructor
  · simpa only [empty_bottleneck_zero, ENNReal.toReal_zero] using
      finitePMatchingCost_tendsto_bottleneck _ _ (unitBars_essentialPart 0)
        (unitBars_essentialPart 0)
  · simpa only [empty_bottleneck_zero, ENNReal.toReal_zero] using
      finitePBoundaryTransportCost_tendsto_bottleneck _ _ (unitBars_essentialPart 0)
        (unitBars_essentialPart 0)

/-- One unit-height bar has matching and real-plan distance one from empty. -/
theorem singleton_empty_costs {p : ℝ} (_hp : 1 ≤ p) :
    finitePMatchingCost p (fun q : (unitBars 1).finiteOccurrences => q.1)
        (fun q : (unitBars 0).finiteOccurrences => q.1) = 1 ∧
      finitePBoundaryTransportCost p (fun q : (unitBars 1).finiteOccurrences => q.1)
        (fun q : (unitBars 0).finiteOccurrences => q.1) = 1 := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost, unitBars_to_empty,
    Nat.cast_one, Real.one_rpow, and_self]

theorem singleton_empty_bottleneck : bottleneck (unitBars 1) (unitBars 0) = 1 :=
  unitBars_bottleneck_empty 1 (by norm_num)

/-- Both copies contribute separately to the unnormalized powered sum. -/
theorem duplicate_empty_costs (p : ℝ) :
    finitePMatchingCost p (fun q : (unitBars 2).finiteOccurrences => q.1)
        (fun q : (unitBars 0).finiteOccurrences => q.1) = (2 : ℝ) ^ p⁻¹ ∧
      finitePBoundaryTransportCost p (fun q : (unitBars 2).finiteOccurrences => q.1)
        (fun q : (unitBars 0).finiteOccurrences => q.1) = (2 : ℝ) ^ p⁻¹ := by
  simp only [finitePBoundaryTransportCost_eq_matchingCost, unitBars_to_empty,
    Nat.cast_ofNat, and_self]

theorem duplicate_empty_first_order :
    finitePMatchingCost 1 (fun q : (unitBars 2).finiteOccurrences => q.1)
      (fun q : (unitBars 0).finiteOccurrences => q.1) = 2 := by
  simpa using (duplicate_empty_costs 1).1

theorem duplicate_empty_three_halves :
    finitePMatchingCost ((3 : ℝ) / 2) (fun q : (unitBars 2).finiteOccurrences => q.1)
      (fun q : (unitBars 0).finiteOccurrences => q.1) = (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  simpa using (duplicate_empty_costs ((3 : ℝ) / 2)).1

theorem duplicate_empty_bottleneck : bottleneck (unitBars 2) (unitBars 0) = 1 :=
  unitBars_bottleneck_empty 2 (by norm_num)

theorem duplicate_empty_costs_tendsto_one :
    Tendsto (fun p : ℝ => finitePMatchingCost p
      (fun q : (unitBars 2).finiteOccurrences => q.1)
      (fun q : (unitBars 0).finiteOccurrences => q.1)) atTop (𝓝 1) ∧
    Tendsto (fun p : ℝ => finitePBoundaryTransportCost p
      (fun q : (unitBars 2).finiteOccurrences => q.1)
      (fun q : (unitBars 0).finiteOccurrences => q.1)) atTop (𝓝 1) := by
  constructor
  · simpa only [duplicate_empty_bottleneck, ENNReal.toReal_one] using
      finitePMatchingCost_tendsto_bottleneck _ _ (unitBars_essentialPart 2)
        (unitBars_essentialPart 0)
  · simpa only [duplicate_empty_bottleneck, ENNReal.toReal_one] using
      finitePBoundaryTransportCost_tendsto_bottleneck _ _ (unitBars_essentialPart 2)
        (unitBars_essentialPart 0)

private def pairAndDelete : OccurrenceMatching (Fin 2) (Fin 1) PEmpty.{1} PEmpty.{1} where
  finite i := if i = 0 then some 0 else none
  finite_injective := by
    intro i i' j hi hi'
    fin_cases i <;> fin_cases i' <;> simp_all
  essential := Equiv.refl _

theorem duplicate_singleton_bottleneck : bottleneck (unitBars 2) (unitBars 1) = 1 :=
  bottleneck_repeated_pair_detected

/-- Pair one occurrence and delete the other, then compare with the full bottleneck. -/
theorem duplicate_singleton_costs {p : ℝ} (hp : 1 ≤ p) :
    finitePMatchingCost p (fun q : (unitBars 2).finiteOccurrences => q.1)
        (fun q : (unitBars 1).finiteOccurrences => q.1) = 1 ∧
      finitePBoundaryTransportCost p (fun q : (unitBars 2).finiteOccurrences => q.1)
        (fun q : (unitBars 1).finiteOccurrences => q.1) = 1 := by
  let u := (Fintype.equivFinOfCardEq (unitBars_card 2)).symm
  let v := (Fintype.equivFinOfCardEq (unitBars_card 1)).symm
  have hcost : pairAndDelete.totalFinitePowerCost p (fun _ => (0, 2)) (fun _ => (0, 2)) = 1 := by
    have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
    norm_num [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
      pairAndDelete, Fin.sum_univ_two, finitePairCost, diagonalCost, Real.zero_rpow hp0,
      Fin.exists_fin_two]
  have hu := finitePMatchingCost_le_matching hp (fun _ : Fin 2 => (0, 2))
    (fun _ : Fin 1 => (0, 2)) pairAndDelete
  rw [hcost, Real.one_rpow] at hu
  have hreindex := finitePMatchingCost_reindex u v p
    (fun q : (unitBars 2).finiteOccurrences => q.1)
    (fun q : (unitBars 1).finiteOccurrences => q.1)
  simp only [Function.comp_def, unitBars_coordinates] at hreindex
  rw [hreindex] at hu
  have hl := bottleneck_toReal_le_finitePMatchingCost hp _ _
    (unitBars_essentialPart 2) (unitBars_essentialPart 1)
  rw [duplicate_singleton_bottleneck, ENNReal.toReal_one] at hl
  simp only [unitBars_coordinates] at hl ⊢
  have heq := le_antisymm hu hl
  exact ⟨heq, by rw [finitePBoundaryTransportCost_eq_matchingCost]; exact heq⟩

theorem duplicate_singleton_costs_tendsto_one :
    Tendsto (fun p : ℝ => finitePMatchingCost p
      (fun q : (unitBars 2).finiteOccurrences => q.1)
      (fun q : (unitBars 1).finiteOccurrences => q.1)) atTop (𝓝 1) ∧
    Tendsto (fun p : ℝ => finitePBoundaryTransportCost p
      (fun q : (unitBars 2).finiteOccurrences => q.1)
      (fun q : (unitBars 1).finiteOccurrences => q.1)) atTop (𝓝 1) := by
  constructor
  · simpa only [duplicate_singleton_bottleneck, ENNReal.toReal_one] using
      finitePMatchingCost_tendsto_bottleneck _ _ (unitBars_essentialPart 2)
        (unitBars_essentialPart 1)
  · simpa only [duplicate_singleton_bottleneck, ENNReal.toReal_one] using
      finitePBoundaryTransportCost_tendsto_bottleneck _ _ (unitBars_essentialPart 2)
        (unitBars_essentialPart 1)

/-- A diagram consisting of one essential birth. -/
def essentialBirth (b : ℝ) : Diagram ℝ := orderedQ 0 1 (Fin.elim0, fun _ => b)

theorem essentialBirth_positive (b : ℝ) : (essentialBirth b).IsPositive := by
  apply (orderedQ_isPositive_iff _ _ _).mpr
  intro i
  exact Fin.elim0 i

theorem essential_births_zero_one {p : ℝ} (hp : 1 ≤ p) :
    finitePMatchingCost p (fun q : (essentialBirth 0).finiteOccurrences => q.1)
        (fun q : (essentialBirth 1).finiteOccurrences => q.1) = 0 ∧
      bottleneck (essentialBirth 0) (essentialBirth 1) = 1 := by
  have hempty (b : ℝ) : IsEmpty (essentialBirth b).finiteOccurrences := by
    apply Fintype.card_eq_zero_iff.mp
    change Fintype.card (finitePart (essentialBirth b).points) = 0
    rw [Multiset.card_coe]
    simp [essentialBirth, finitePart_orderedQ]
  let := hempty 0
  let := hempty 1
  constructor
  · exact finitePMatchingCost_empty hp _ _
  · have hf (b : ℝ) : (Finset.univ : Finset (Fin 0)).val.map
        (Fin.elim0 : Fin 0 → ℝ × ℝ) = finitePart (essentialBirth b).points := by
      simp [essentialBirth, finitePart_orderedQ]
    rw [bottleneck_eq_presentation _ _ _ _ _ _ (hf 0) (hf 1)
      (orderedQ_essential_occurrences 0 1 (Fin.elim0, fun _ => (0 : ℝ)))
      (orderedQ_essential_occurrences 0 1 (Fin.elim0, fun _ => (1 : ℝ)))]
    rw [presentationBottleneck_essential_singletons]
    norm_num [essentialPairCost]

end TDA.Persistence.FinitePBottleneckLimitExamples
