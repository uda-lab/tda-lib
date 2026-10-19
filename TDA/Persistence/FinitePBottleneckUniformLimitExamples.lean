import TDA.Persistence.FinitePBottleneckUniformLimit
import TDA.Persistence.FinitePBottleneckLimitExamples
import TDA.Persistence.FinitePBoundaryTransportExamples
import TDA.Persistence.FinitePBoundaryTransportLaws
import TDA.Persistence.DiagramBottleneckLaws

/-!
# Count and radius controls for uniform bottleneck recovery

The fixtures use actual canonical diagram occurrences and both optimized costs.
Repeated bars attain the error bound; changing the count or radius gives error
one without the corresponding budget. Essential bars test the excluded domain.
-/

noncomputable section

namespace TDA.Persistence.FinitePBottleneckUniformLimitExamples

open Filter
open scoped Classical Topology ENNReal

private abbrev matching (p : ℝ) (D E : Diagram ℝ) : ℝ :=
  finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
    (fun q : E.finiteOccurrences => q.1)

private abbrev transport (p : ℝ) (D E : Diagram ℝ) : ℝ :=
  finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
    (fun q : E.finiteOccurrences => q.1)

private abbrev budgetSet (m : ℕ) (R : ℝ) : Set (Diagram ℝ × Diagram ℝ) :=
  {z | essentialPart z.1.points = 0 ∧ essentialPart z.2.points = 0 ∧
    Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤ m ∧
    bottleneck z.1 z.2 ≤ ENNReal.ofReal R}

private abbrev uniformLimits (m : ℕ) (R : ℝ) : Prop :=
  TendstoUniformlyOn (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ => matching p z.1 z.2)
    (fun z => (bottleneck z.1 z.2).toReal) atTop (budgetSet m R) ∧
  TendstoUniformlyOn (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ => transport p z.1 z.2)
    (fun z => (bottleneck z.1 z.2).toReal) atTop (budgetSet m R)

private theorem uniform_limits (m : ℕ) {R : ℝ} (hR : 0 ≤ R) : uniformLimits m R :=
  ⟨finitePMatchingCost_tendstoUniformlyOn_bottleneck m R hR,
    finitePBoundaryTransportCost_tendstoUniformlyOn_bottleneck m R hR⟩

private def empty : Diagram ℝ := orderedQ 0 0 (Fin.elim0, Fin.elim0)

private theorem empty_finitePart : finitePart empty.points = 0 := by
  simp [empty, finitePart_orderedQ]

private theorem empty_essentialPart : essentialPart empty.points = 0 := by
  simp [empty, essentialPart_orderedQ]

private theorem empty_card : Fintype.card empty.finiteOccurrences = 0 := by
  simp only [Multiset.card_coe, empty_finitePart, Multiset.card_zero]

private instance empty_occurrences : IsEmpty empty.finiteOccurrences :=
  Fintype.card_eq_zero_iff.mp empty_card

/-- The zero-count budget contains the empty pair and its costs are actually zero. -/
private theorem empty_zero_budget {p : ℝ} (hp : 1 ≤ p) :
    (empty, empty) ∈ budgetSet 0 1 ∧ matching p empty empty = 0 ∧
      transport p empty empty = 0 ∧ bottleneck empty empty = 0 ∧ uniformLimits 0 1 := by
  have hB : bottleneck empty empty = 0 := bottleneck_self _
  exact ⟨⟨empty_essentialPart, empty_essentialPart, by simp, by simp [hB]⟩,
    finitePMatchingCost_empty hp _ _, finitePBoundaryTransportCost_empty hp _ _, hB,
    uniform_limits 0 (by norm_num)⟩

/-- Positive radius ensures the constructor retains all `n` repeated bars. -/
private def scaledBars (n : ℕ) (a : ℝ) : Diagram ℝ :=
  orderedQ n 0 (fun _ => (0, 2 * a), Fin.elim0)

private theorem scaledBars_finitePart (n : ℕ) {a : ℝ} (ha : 0 < a) :
    finitePart (scaledBars n a).points = Multiset.replicate n ((0, 2 * a) : ℝ × ℝ) := by
  have hne : (0 : ℝ) ≠ 2 * a := by linarith
  simp [scaledBars, finitePart_orderedQ, List.ofFn_const, Multiset.coe_replicate, hne]

private theorem scaledBars_essentialPart (n : ℕ) (a : ℝ) :
    essentialPart (scaledBars n a).points = 0 := by
  simp [scaledBars, essentialPart_orderedQ]

private theorem scaledBars_card (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Fintype.card (scaledBars n a).finiteOccurrences = n := by
  simp only [Multiset.card_coe, scaledBars_finitePart n ha, Multiset.card_replicate]

private theorem scaledBars_coordinates (n : ℕ) {a : ℝ} (ha : 0 < a)
    (q : (scaledBars n a).finiteOccurrences) : q.1 = ((0, 2 * a) : ℝ × ℝ) := by
  exact Multiset.eq_of_mem_replicate
    (by simpa only [scaledBars_finitePart n ha] using (Multiset.coe_mem (x := q)))

private theorem scaledBars_lifetime {a : ℝ} (ha : 0 < a) : (0 : ℝ) < 2 * a := by
  positivity

private theorem scaled_diagonal {a : ℝ} (ha : 0 < a) :
    diagonalCost ((0, 2 * a) : ℝ × ℝ) = ENNReal.ofReal a := by
  dsimp [diagonalCost]
  congr 1
  rw [sub_zero, abs_of_pos (scaledBars_lifetime ha)]
  ring

private theorem scaledBars_bottleneck (n : ℕ) (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    bottleneck (scaledBars n a) empty = ENNReal.ofReal a := by
  let : Nonempty (scaledBars n a).finiteOccurrences :=
    Fintype.card_pos_iff.mp (by rw [scaledBars_card n ha]; exact hn)
  unfold empty
  rw [bottleneck_finite_only_empty _ (scaledBars_essentialPart n a)]
  simp only [scaledBars_coordinates n ha, scaled_diagonal ha]
  exact Finset.sup_const Finset.univ_nonempty _

private theorem scaledBars_matching (n : ℕ) {a p : ℝ} (ha : 0 < a) (hp : 1 ≤ p) :
    matching p (scaledBars n a) empty = (n : ℝ) ^ p⁻¹ * a := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  unfold matching
  rw [finitePMatchingCost_of_isEmpty_right]
  simp only [scaledBars_coordinates n ha, scaled_diagonal ha, ENNReal.toReal_ofReal ha.le,
    Finset.sum_const, Finset.card_univ, scaledBars_card n ha, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg ha.le _),
    Real.rpow_rpow_inv ha.le hp0]

private theorem scaledBars_transport (n : ℕ) {a p : ℝ} (ha : 0 < a) (hp : 1 ≤ p) :
    transport p (scaledBars n a) empty = (n : ℝ) ^ p⁻¹ * a := by
  rw [transport, finitePBoundaryTransportCost_eq_matchingCost]
  exact scaledBars_matching n ha hp

/-- The zero-radius class also contains a nonempty positive diagram pair. -/
private theorem nonempty_zero_radius {p : ℝ} (hp : 1 ≤ p) :
    Fintype.card (scaledBars 1 1).finiteOccurrences = 1 ∧
    (scaledBars 1 1, scaledBars 1 1) ∈ budgetSet 2 0 ∧
    matching p (scaledBars 1 1) (scaledBars 1 1) = 0 ∧
    transport p (scaledBars 1 1) (scaledBars 1 1) = 0 ∧ uniformLimits 2 0 := by
  refine ⟨scaledBars_card 1 (by norm_num), ?_, finitePMatchingCost_self hp _,
    finitePBoundaryTransportCost_self hp _, uniform_limits 2 (le_refl 0)⟩
  exact ⟨scaledBars_essentialPart 1 1, scaledBars_essentialPart 1 1,
    by norm_num [scaledBars_card 1 (by norm_num : (0 : ℝ) < 1)], by simp [bottleneck_self]⟩

/-- Both error capstones also specialize directly to each boundary mechanism. -/
private theorem zero_budget_error_bounds {p : ℝ} (hp : 1 ≤ p) :
    |matching p empty empty - (bottleneck empty empty).toReal| ≤ 0 ∧
    |transport p empty empty - (bottleneck empty empty).toReal| ≤ 0 ∧
    |matching p (scaledBars 1 1) (scaledBars 1 1) -
      (bottleneck (scaledBars 1 1) (scaledBars 1 1)).toReal| ≤ 0 ∧
    |transport p (scaledBars 1 1) (scaledBars 1 1) -
      (bottleneck (scaledBars 1 1) (scaledBars 1 1)).toReal| ≤ 0 := by
  have he := (empty_zero_budget hp).1
  have hs := (nonempty_zero_radius hp).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using finitePMatchingCost_abs_sub_bottleneck_le_uniformBound hp empty empty
      he.1 he.2.1 he.2.2.1 (by norm_num : (0 : ℝ) ≤ 1) he.2.2.2
  · simpa using finitePBoundaryTransportCost_abs_sub_bottleneck_le_uniformBound hp empty empty
      he.1 he.2.1 he.2.2.1 (by norm_num : (0 : ℝ) ≤ 1) he.2.2.2
  · simpa using finitePMatchingCost_abs_sub_bottleneck_le_uniformBound hp _ _
      hs.1 hs.2.1 hs.2.2.1 (le_refl (0 : ℝ)) hs.2.2.2
  · simpa using finitePBoundaryTransportCost_abs_sub_bottleneck_le_uniformBound hp _ _
      hs.1 hs.2.1 hs.2.2.1 (le_refl (0 : ℝ)) hs.2.2.2

/-- Two retained occurrences attain the budget-two envelope in both models. -/
private theorem repeated_sharp {R p : ℝ} (hR : 0 < R) (hp : 1 ≤ p) :
    (scaledBars 2 R, empty) ∈ budgetSet 2 R ∧
    |matching p (scaledBars 2 R) empty - (bottleneck (scaledBars 2 R) empty).toReal| =
      ((2 : ℝ) ^ p⁻¹ - 1) * R ∧
    |transport p (scaledBars 2 R) empty - (bottleneck (scaledBars 2 R) empty).toReal| =
      ((2 : ℝ) ^ p⁻¹ - 1) * R ∧ uniformLimits 2 R := by
  have hB := scaledBars_bottleneck 2 (by norm_num) hR
  have hnonneg : 0 ≤ ((2 : ℝ) ^ p⁻¹ - 1) * R :=
    mul_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by norm_num)
      (inv_nonneg.mpr (zero_le_one.trans hp)))) hR.le
  have heq : (2 : ℝ) ^ p⁻¹ * R - R = ((2 : ℝ) ^ p⁻¹ - 1) * R := by ring
  refine ⟨⟨scaledBars_essentialPart 2 R, empty_essentialPart,
    by norm_num [scaledBars_card 2 hR, empty_card], hB.le⟩, ?_, ?_, uniform_limits 2 hR.le⟩ <;>
    simp only [scaledBars_matching 2 hR hp, scaledBars_transport 2 hR hp,
      Nat.cast_ofNat, hB, ENNReal.toReal_ofReal hR.le, heq, abs_of_nonneg hnonneg]

private theorem repeated_three_halves {R : ℝ} (hR : 0 < R) :
    |matching (3 / 2) (scaledBars 2 R) empty -
      (bottleneck (scaledBars 2 R) empty).toReal| = ((2 : ℝ) ^ (2 / 3 : ℝ) - 1) * R ∧
    |transport (3 / 2) (scaledBars 2 R) empty -
      (bottleneck (scaledBars 2 R) empty).toReal| = ((2 : ℝ) ^ (2 / 3 : ℝ) - 1) * R := by
  constructor
  · convert (repeated_sharp hR (by norm_num : (1 : ℝ) ≤ 3 / 2)).2.1 using 1
    norm_num
  · convert (repeated_sharp hR (by norm_num : (1 : ℝ) ≤ 3 / 2)).2.2.1 using 1
    norm_num

private def singleBar (b : ℝ) : Diagram ℝ :=
  orderedQ 1 0 (fun _ => (b, b + 2), Fin.elim0)

private theorem singleBar_finitePart (b : ℝ) :
    finitePart (singleBar b).points = {((b, b + 2) : ℝ × ℝ)} := by
  have hne : b ≠ b + 2 := by linarith
  simp [singleBar, finitePart_orderedQ, hne]

private theorem singleBar_card (b : ℝ) : Fintype.card (singleBar b).finiteOccurrences = 1 := by
  simp only [Multiset.card_coe, singleBar_finitePart, Multiset.card_singleton]

private theorem singleBar_essentialPart (b : ℝ) : essentialPart (singleBar b).points = 0 := by
  simp [singleBar, essentialPart_orderedQ]

private theorem singleBar_coordinates (b : ℝ) (q : (singleBar b).finiteOccurrences) :
    q.1 = ((b, b + 2) : ℝ × ℝ) := by
  exact Multiset.mem_singleton.mp
    (by simpa only [singleBar_finitePart] using (Multiset.coe_mem (x := q)))

private theorem singleBar_matching_reindex (p b c : ℝ) :
    matching p (singleBar b) (singleBar c) =
      finitePMatchingCost p (fun _ : Fin 1 => (b, b + 2))
        (fun _ : Fin 1 => (c, c + 2)) := by
  let u := (Fintype.equivFinOfCardEq (singleBar_card b)).symm
  let v := (Fintype.equivFinOfCardEq (singleBar_card c)).symm
  simpa only [matching, Function.comp_def, singleBar_coordinates] using
    (finitePMatchingCost_reindex u v p (fun q : (singleBar b).finiteOccurrences => q.1)
      (fun q : (singleBar c).finiteOccurrences => q.1)).symm

private theorem switch_bottleneck : bottleneck (singleBar 0) (singleBar (3 / 2)) = 1 := by
  have hf (b : ℝ) : (Finset.univ : Finset (Fin 1)).val.map (fun _ => (b, b + 2)) =
      finitePart (singleBar b).points := by simp [singleBar_finitePart]
  have he (b : ℝ) : (Finset.univ : Finset (Fin 0)).val.map (Fin.elim0 : Fin 0 → ℝ) =
      essentialPart (singleBar b).points := by simp [singleBar_essentialPart]
  rw [bottleneck_eq_presentation _ _ _ _ _ _ (hf 0) (hf (3 / 2)) (he 0) (he (3 / 2))]
  let delete : OccurrenceMatching (Fin 1) (Fin 1) (Fin 0) (Fin 0) :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  apply le_antisymm
  · calc
      _ ≤ delete.cost (fun _ => (0, 0 + 2)) (fun _ => (3 / 2, 3 / 2 + 2))
          Fin.elim0 Fin.elim0 := iInf_le _ delete
      _ = 1 := by
        norm_num [delete, OccurrenceMatching.cost, diagonalCost]
        simp
  · apply le_iInf
    intro M
    have hs := M.source_le_cost (fun _ => (0, 0 + 2))
      (fun _ => (3 / 2, 3 / 2 + 2)) Fin.elim0 Fin.elim0 0
    cases h : M.finite 0 with
    | none => simpa [h, diagonalCost] using hs
    | some j =>
      have : (1 : ℝ≥0∞) ≤ finitePairCost ((0, 2) : ℝ × ℝ) (3 / 2, 3 / 2 + 2) := by
        norm_num [finitePairCost]
      exact this.trans (by simpa [h] using hs)

/-- The same bounded class contains a pair whose actual optimizer changes:
pair at one, delete both at two. Canonical occurrence costs are reindexed before
using the explicit matching and zero-plan witnesses. -/
private theorem optimizer_change_in_budget :
    (singleBar 0, singleBar (3 / 2)) ∈ budgetSet 2 1 ∧
    matching 1 (singleBar 0) (singleBar (3 / 2)) = 3 / 2 ∧
    transport 1 (singleBar 0) (singleBar (3 / 2)) = 3 / 2 ∧
    matching 2 (singleBar 0) (singleBar (3 / 2)) = Real.sqrt 2 ∧
    transport 2 (singleBar 0) (singleBar (3 / 2)) = Real.sqrt 2 ∧
    FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost 1
      (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) = 3 / 2 ∧
    FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost 2
      (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) = 9 / 4 ∧
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan (Fin 1) (Fin 1)).powerCost 2
      (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) = 2 ∧
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan (Fin 1) (Fin 1)).powerCost 1
      (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) = 2 ∧
    (3 / 2 : ℝ) < 2 ∧ (2 : ℝ) < 9 / 4 ∧ uniformLimits 2 1 := by
  have hm1 : matching 1 (singleBar 0) (singleBar (3 / 2)) = 3 / 2 := by
    rw [singleBar_matching_reindex, finitePMatchingCost,
      ← finitePowerBoundaryTransportCost_eq_matchingCost]
    norm_num only [zero_add, show (3 / 2 : ℝ) + 2 = 7 / 2 by norm_num,
      FinitePBoundaryTransportExamples.switch_power_one, inv_one, Real.rpow_one]
  have hm2 : matching 2 (singleBar 0) (singleBar (3 / 2)) = Real.sqrt 2 := by
    rw [singleBar_matching_reindex]
    norm_num [finitePMatchingCost, finitePowerMatchingCost_singleton, finitePairCost,
      diagonalCost, Real.rpow_two, Real.sqrt_eq_rpow]
  have ht1 : transport 1 (singleBar 0) (singleBar (3 / 2)) = 3 / 2 := by
    rw [transport, finitePBoundaryTransportCost_eq_matchingCost]; exact hm1
  have ht2 : transport 2 (singleBar 0) (singleBar (3 / 2)) = Real.sqrt 2 := by
    rw [transport, finitePBoundaryTransportCost_eq_matchingCost]; exact hm2
  refine ⟨⟨singleBar_essentialPart 0, singleBar_essentialPart _,
    by rw [singleBar_card, singleBar_card],
    by simp [switch_bottleneck]⟩, hm1, ht1, hm2, ht2,
    ?_, ?_, ?_, ?_, by norm_num, by norm_num, uniform_limits 2 (by norm_num)⟩
  · norm_num [FinitePBoundaryTransportExamples.pairSingletons,
      OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
      finitePairCost, diagonalCost]
  · norm_num [FinitePBoundaryTransportExamples.pairSingletons,
      OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost,
      finitePairCost, diagonalCost, Real.rpow_two]
  · simpa only [FinitePBoundaryTransportExamples.switch_power_two] using
      FinitePBoundaryTransportExamples.deleting_both_optimal_at_two
  · norm_num [FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost,
      FiniteBoundaryPlan.zero, FiniteBoundaryPlan.deletionMass, FiniteBoundaryPlan.insertionMass,
      finitePairCost, diagonalCost]

/-- The natural exponents are cofinal in real `atTop`. At exponent `n≥1`,
`2^n` unit bars give error one in the radius-one essential-free class. Thus a
uniform epsilon `1/2` tail on that larger class cannot omit a count budget. -/
private theorem missing_count (n : ℕ) (hn : 1 ≤ n) :
    essentialPart (scaledBars (2 ^ n) 1).points = 0 ∧
    Fintype.card (scaledBars (2 ^ n) 1).finiteOccurrences = 2 ^ n ∧
    bottleneck (scaledBars (2 ^ n) 1) empty = 1 ∧
    matching (n : ℝ) (scaledBars (2 ^ n) 1) empty = 2 ∧
    transport (n : ℝ) (scaledBars (2 ^ n) 1) empty = 2 ∧
    |matching (n : ℝ) (scaledBars (2 ^ n) 1) empty -
      (bottleneck (scaledBars (2 ^ n) 1) empty).toReal| = 1 ∧
    |transport (n : ℝ) (scaledBars (2 ^ n) 1) empty -
      (bottleneck (scaledBars (2 ^ n) 1) empty).toReal| = 1 := by
  have hp : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) _
  have hB : bottleneck (scaledBars (2 ^ n) 1) empty = 1 := by
    simpa using scaledBars_bottleneck (2 ^ n) hN (by norm_num : (0 : ℝ) < 1)
  have hpow : (((2 : ℕ) ^ n : ℕ) : ℝ) ^ (n : ℝ)⁻¹ = 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by omega)
  have hm : matching (n : ℝ) (scaledBars (2 ^ n) 1) empty = 2 := by
    rw [scaledBars_matching _ (by norm_num) hp, hpow, mul_one]
  have ht : transport (n : ℝ) (scaledBars (2 ^ n) 1) empty = 2 := by
    rw [transport, finitePBoundaryTransportCost_eq_matchingCost]
    exact hm
  exact ⟨scaledBars_essentialPart _ _, scaledBars_card _ (by norm_num), hB, hm, ht,
    by norm_num [hm, hB], by norm_num [ht, hB]⟩

private theorem missing_count_exponents_cofinal :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop

/-- With count two fixed, the positive radius may depend on each exponent.
The actual error remains one on the essential-free count-two class without a
radius bound, so epsilon `1/2` has no uniform tail on that larger class. -/
private theorem missing_radius {p : ℝ} (hp : 1 ≤ p) :
    let a := ((2 : ℝ) ^ p⁻¹ - 1)⁻¹
    0 < a ∧ essentialPart (scaledBars 2 a).points = 0 ∧
    Fintype.card (scaledBars 2 a).finiteOccurrences = 2 ∧
    bottleneck (scaledBars 2 a) empty = ENNReal.ofReal a ∧
    matching p (scaledBars 2 a) empty = (2 : ℝ) ^ p⁻¹ * a ∧
    transport p (scaledBars 2 a) empty = (2 : ℝ) ^ p⁻¹ * a ∧
    |matching p (scaledBars 2 a) empty - (bottleneck (scaledBars 2 a) empty).toReal| = 1 ∧
    |transport p (scaledBars 2 a) empty - (bottleneck (scaledBars 2 a) empty).toReal| = 1 := by
  dsimp only
  have hgap : 0 < (2 : ℝ) ^ p⁻¹ - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num)
      (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hp)))
  have ha := inv_pos.mpr hgap
  have herr : ((2 : ℝ) ^ p⁻¹ - 1) * ((2 : ℝ) ^ p⁻¹ - 1)⁻¹ = 1 :=
    mul_inv_cancel₀ hgap.ne'
  have hsub : (2 : ℝ) ^ p⁻¹ * ((2 : ℝ) ^ p⁻¹ - 1)⁻¹ -
      ((2 : ℝ) ^ p⁻¹ - 1)⁻¹ = 1 := by nlinarith only [herr]
  refine ⟨ha, scaledBars_essentialPart 2 _, scaledBars_card 2 ha,
    scaledBars_bottleneck 2 (by norm_num) ha, scaledBars_matching 2 ha hp,
    scaledBars_transport 2 ha hp, ?_, ?_⟩ <;>
    simp only [scaledBars_matching 2 ha hp, scaledBars_transport 2 ha hp,
      scaledBars_bottleneck 2 (by norm_num) ha, ENNReal.toReal_ofReal ha.le,
      Nat.cast_ofNat, hsub, abs_one]

/-- Equal essential cardinalities and finite full bottleneck do not suffice:
the finite-part costs vanish, but the full bottleneck error is one at count zero. -/
private theorem essential_negative_control {p : ℝ} (hp : 1 ≤ p) :
    let D := FinitePBottleneckLimitExamples.essentialBirth 0
    let E := FinitePBottleneckLimitExamples.essentialBirth 1
    Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences = 0 ∧
    Fintype.card D.essentialOccurrences = 1 ∧ Fintype.card E.essentialOccurrences = 1 ∧
    bottleneck D E = 1 ∧ matching p D E = 0 ∧ transport p D E = 0 ∧
    |matching p D E - (bottleneck D E).toReal| = 1 ∧
    |transport p D E - (bottleneck D E).toReal| = 1 := by
  dsimp only
  obtain ⟨hm, hB⟩ := FinitePBottleneckLimitExamples.essential_births_zero_one hp
  have ht := hm
  rw [← finitePBoundaryTransportCost_eq_matchingCost] at ht
  refine ⟨?_, ?_, ?_, hB, hm, ht, ?_, ?_⟩
  · change Fintype.card (finitePart (FinitePBottleneckLimitExamples.essentialBirth 0).points) +
      Fintype.card (finitePart (FinitePBottleneckLimitExamples.essentialBirth 1).points) = 0
    rw [Multiset.card_coe, Multiset.card_coe]
    simp [FinitePBottleneckLimitExamples.essentialBirth, finitePart_orderedQ]
  · change Fintype.card (essentialPart (FinitePBottleneckLimitExamples.essentialBirth 0).points) = 1
    rw [Multiset.card_coe]
    simp [FinitePBottleneckLimitExamples.essentialBirth, essentialPart_orderedQ]
  · change Fintype.card (essentialPart (FinitePBottleneckLimitExamples.essentialBirth 1).points) = 1
    rw [Multiset.card_coe]
    simp [FinitePBottleneckLimitExamples.essentialBirth, essentialPart_orderedQ]
  · norm_num [matching, hm, hB]
  · norm_num [transport, ht, hB]

end TDA.Persistence.FinitePBottleneckUniformLimitExamples
