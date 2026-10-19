import TDA.Persistence.FinitePCommonEssentialBottleneck
import TDA.Persistence.FinitePBottleneckLimitExamples
import TDA.Persistence.FinitePBoundaryTransportExamples
import TDA.Persistence.FinitePBoundaryTransportLaws

/-!
# Actual diagrams with common essential births

Repeated essential values contribute no finite-part charge and match at zero
full cost. The positive finite examples retain their count, sharp rate and
change of optimizer. Equal essential counts alone fail the recovery bound.
-/

noncomputable section

namespace TDA.Persistence.FinitePCommonEssentialBottleneckExamples

open Filter
open scoped Classical Topology ENNReal

private theorem finite_card (D : Diagram ℝ) :
    Fintype.card D.finiteOccurrences = (finitePart D.points).card := by
  change Fintype.card (finitePart D.points) = _
  exact Multiset.card_coe _

private theorem essential_card (D : Diagram ℝ) :
    Fintype.card D.essentialOccurrences = (essentialPart D.points).card := by
  change Fintype.card (essentialPart D.points) = _
  exact Multiset.card_coe _

private abbrev matching (p : ℝ) (D E : Diagram ℝ) : ℝ :=
  finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
    (fun q : E.finiteOccurrences => q.1)

private abbrev transport (p : ℝ) (D E : Diagram ℝ) : ℝ :=
  finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
    (fun q : E.finiteOccurrences => q.1)

private abbrev budgetSet (m : ℕ) (R : ℝ) : Set (Diagram ℝ × Diagram ℝ) :=
  {z | essentialPart z.1.points = essentialPart z.2.points ∧
    Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤ m ∧
    bottleneck z.1 z.2 ≤ ENNReal.ofReal R}

private abbrev uniformLimits (m : ℕ) (R : ℝ) : Prop :=
  TendstoUniformlyOn (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ => matching p z.1 z.2)
    (fun z => (bottleneck z.1 z.2).toReal) atTop (budgetSet m R) ∧
  TendstoUniformlyOn (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ => transport p z.1 z.2)
    (fun z => (bottleneck z.1 z.2).toReal) atTop (budgetSet m R)

private theorem uniform_limits (m : ℕ) {R : ℝ} (hR : 0 ≤ R) : uniformLimits m R :=
  ⟨finitePMatchingCost_tendstoUniformlyOn_bottleneck_of_essentialParts_eq m R hR,
    finitePBoundaryTransportCost_tendstoUniformlyOn_bottleneck_of_essentialParts_eq m R hR⟩

/-- A concrete full matching: delete finite bars and retain essential values. -/
private def deleteFinite (D E : Diagram ℝ)
    (he : essentialPart D.points = essentialPart E.points) :
    OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences where
  finite _ := none
  finite_injective := by simp
  essential := Multiset.cast he

private theorem bottleneck_le_deletions (D E : Diagram ℝ)
    (he : essentialPart D.points = essentialPart E.points) (r : ℝ≥0∞)
    (hD : ∀ q : D.finiteOccurrences, diagonalCost q.1 ≤ r)
    (hE : ∀ q : E.finiteOccurrences, diagonalCost q.1 ≤ r) :
    bottleneck D E ≤ r := by
  refine (bottleneck_le_matching D E (deleteFinite D E he)).trans ?_
  apply OccurrenceMatching.cost_le_of
  · exact hD
  · intro j
    simpa [deleteFinite] using hE j
  · intro k
    change essentialPairCost k.1 k.1 ≤ r
    simp only [essentialPairCost_self, zero_le]

private def births : Fin 3 → ℝ := ![-3, -3, 7]
private def reorderedBirths : Fin 3 → ℝ := ![7, -3, -3]
private def essentialBlock : Diagram ℝ := orderedQ 0 3 (Fin.elim0, births)
private def reorderedBlock : Diagram ℝ := orderedQ 0 3 (Fin.elim0, reorderedBirths)

private theorem block_essential : essentialPart essentialBlock.points = {-3, -3, 7} := by
  norm_num [essentialBlock, births, essentialPart_orderedQ, List.ofFn_succ]
  simp only [← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero]

private theorem reordered_essential :
    essentialPart reorderedBlock.points = {-3, -3, 7} := by
  norm_num [reorderedBlock, reorderedBirths, essentialPart_orderedQ, List.ofFn_succ]
  simp only [← Multiset.cons_coe, Multiset.coe_nil, ← Multiset.cons_zero]
  rw [Multiset.cons_swap (7 : ℝ) (-3), Multiset.cons_swap (7 : ℝ) (-3)]

private theorem block_finite : finitePart essentialBlock.points = 0 := by
  simp [essentialBlock, finitePart_orderedQ]

private theorem reordered_finite : finitePart reorderedBlock.points = 0 := by
  simp [reorderedBlock, finitePart_orderedQ]

private instance block_empty_finite : IsEmpty essentialBlock.finiteOccurrences := by
  apply Fintype.card_eq_zero_iff.mp
  simp only [Multiset.card_coe, block_finite, Multiset.card_zero]

private instance reordered_empty_finite : IsEmpty reorderedBlock.finiteOccurrences := by
  apply Fintype.card_eq_zero_iff.mp
  simp only [Multiset.card_coe, reordered_finite, Multiset.card_zero]

/-- The repeated birth is counted twice, even in a zero-budget pair. -/
private theorem reordered_zero_budget {p : ℝ} (hp : 1 ≤ p) :
    essentialPart essentialBlock.points = essentialPart reorderedBlock.points ∧
    Fintype.card essentialBlock.essentialOccurrences = 3 ∧
    (essentialPart essentialBlock.points).count (-3) = 2 ∧
    essentialBlock.IsPositive ∧ reorderedBlock.IsPositive ∧
    (essentialBlock, reorderedBlock) ∈ budgetSet 0 0 ∧
    matching p essentialBlock reorderedBlock = 0 ∧
    transport p essentialBlock reorderedBlock = 0 ∧
    bottleneck essentialBlock reorderedBlock = 0 ∧ uniformLimits 0 0 := by
  have he := block_essential.trans reordered_essential.symm
  have hB : bottleneck essentialBlock reorderedBlock = 0 :=
    le_antisymm (bottleneck_le_deletions _ _ he 0 (fun q => isEmptyElim q)
      (fun q => isEmptyElim q)) bot_le
  refine ⟨he, ?_, ?_, ?_, ?_, ⟨he, by simp, by simp [hB]⟩,
    finitePMatchingCost_empty hp _ _, finitePBoundaryTransportCost_empty hp _ _, hB,
    uniform_limits 0 le_rfl⟩
  · simp only [Multiset.card_coe, block_essential]; norm_num
  · norm_num [block_essential]
  · exact (orderedQ_isPositive_iff _ _ _).mpr fun i => Fin.elim0 i
  · exact (orderedQ_isPositive_iff _ _ _).mpr fun i => Fin.elim0 i

private def essentialFamily (n : ℕ) (a : ℝ) : Diagram ℝ :=
  orderedQ 0 n (Fin.elim0, fun _ => a)

/-- Neither the count nor the range of common essential births is budgeted. -/
private theorem arbitrary_essential_zero_budget (n : ℕ) (a : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    Fintype.card (essentialFamily n a).essentialOccurrences = n ∧
    Fintype.card (essentialFamily n a).finiteOccurrences = 0 ∧
    (essentialFamily n a).IsPositive ∧
    (essentialFamily n a, essentialFamily n a) ∈ budgetSet 0 0 ∧
    bottleneck (essentialFamily n a) (essentialFamily n a) = 0 ∧
    matching p (essentialFamily n a) (essentialFamily n a) = 0 ∧
    transport p (essentialFamily n a) (essentialFamily n a) = 0 ∧ uniformLimits 0 0 := by
  have hc : Fintype.card (essentialFamily n a).finiteOccurrences = 0 := by
    rw [finite_card]
    simp [essentialFamily, finitePart_orderedQ]
  let : IsEmpty (essentialFamily n a).finiteOccurrences := Fintype.card_eq_zero_iff.mp hc
  refine ⟨?_, hc, ?_, ⟨rfl, by simp, by simp [bottleneck_self]⟩, bottleneck_self _,
    finitePMatchingCost_empty hp _ _, finitePBoundaryTransportCost_empty hp _ _,
    uniform_limits 0 le_rfl⟩
  · rw [essential_card]
    simp [essentialFamily, essentialPart_orderedQ]
  · exact (orderedQ_isPositive_iff _ _ _).mpr fun i => Fin.elim0 i

private def scaledBars (n : ℕ) (R : ℝ) : Diagram ℝ :=
  orderedQ n 3 (fun _ => (0, 2 * R), births)

private theorem scaled_essential (n : ℕ) (R : ℝ) :
    essentialPart (scaledBars n R).points = essentialPart essentialBlock.points := by
  simp [scaledBars, essentialBlock, essentialPart_orderedQ]

private theorem scaled_finite (n : ℕ) {R : ℝ} (hR : 0 < R) :
    finitePart (scaledBars n R).points = Multiset.replicate n ((0, 2 * R) : ℝ × ℝ) := by
  have hne : (0 : ℝ) ≠ 2 * R := by linarith
  simp [scaledBars, finitePart_orderedQ, List.ofFn_const, Multiset.coe_replicate, hne]

private theorem scaled_card (n : ℕ) {R : ℝ} (hR : 0 < R) :
    Fintype.card (scaledBars n R).finiteOccurrences = n := by
  simp only [Multiset.card_coe, scaled_finite n hR, Multiset.card_replicate]

private theorem scaled_value (n : ℕ) {R : ℝ} (hR : 0 < R)
    (q : (scaledBars n R).finiteOccurrences) : q.1 = ((0, 2 * R) : ℝ × ℝ) := by
  exact Multiset.eq_of_mem_replicate
    (by simpa only [scaled_finite n hR] using (Multiset.coe_mem (x := q)))

private theorem scaled_diagonal {R : ℝ} (hR : 0 < R) :
    diagonalCost ((0, 2 * R) : ℝ × ℝ) = ENNReal.ofReal R := by
  dsimp [diagonalCost]
  congr 1
  rw [sub_zero, abs_of_pos (by linarith : (0 : ℝ) < 2 * R)]
  ring

private theorem scaled_bottleneck (n : ℕ) (hn : 0 < n) {R : ℝ} (hR : 0 < R) :
    bottleneck (scaledBars n R) essentialBlock = ENNReal.ofReal R := by
  have he := scaled_essential n R
  apply le_antisymm
  · exact bottleneck_le_deletions _ _ he _ (fun q => by
      rw [scaled_value n hR q, scaled_diagonal hR]) (fun q => isEmptyElim q)
  · obtain ⟨M, hM⟩ := (bottleneck_optimal_iff _ _).mpr (congrArg Multiset.card he)
    let : Nonempty (scaledBars n R).finiteOccurrences :=
      Fintype.card_pos_iff.mp (by rw [scaled_card n hR]; exact hn)
    let q : (scaledBars n R).finiteOccurrences := Classical.choice inferInstance
    have h := M.source_le_cost (fun q => q.1) (fun q => q.1)
      (fun q => q.1) (fun q => q.1) q
    rw [hM] at h
    cases hf : M.finite q with
    | none => simpa only [hf, scaled_value n hR, scaled_diagonal hR] using h
    | some j => exact isEmptyElim j

private theorem scaled_matching (n : ℕ) {R p : ℝ} (hR : 0 < R) (hp : 1 ≤ p) :
    matching p (scaledBars n R) essentialBlock = (n : ℝ) ^ p⁻¹ * R := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  rw [matching, finitePMatchingCost_of_isEmpty_right]
  simp only [scaled_value n hR, scaled_diagonal hR, ENNReal.toReal_ofReal hR.le,
    Finset.sum_const, Finset.card_univ, scaled_card n hR, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hR.le _),
    Real.rpow_rpow_inv hR.le hp0]

/-- Two retained finite occurrences attain the count-two error envelope. -/
private theorem sharp_common_essential {R p : ℝ} (hR : 0 < R) (hp : 1 ≤ p) :
    essentialPart (scaledBars 2 R).points = {-3, -3, 7} ∧
    Fintype.card (scaledBars 2 R).finiteOccurrences = 2 ∧
    (scaledBars 2 R).IsPositive ∧
    (scaledBars 2 R, essentialBlock) ∈ budgetSet 2 R ∧
    bottleneck (scaledBars 2 R) essentialBlock = ENNReal.ofReal R ∧
    matching p (scaledBars 2 R) essentialBlock = (2 : ℝ) ^ p⁻¹ * R ∧
    transport p (scaledBars 2 R) essentialBlock = (2 : ℝ) ^ p⁻¹ * R ∧
    |matching p (scaledBars 2 R) essentialBlock -
      (bottleneck (scaledBars 2 R) essentialBlock).toReal| = ((2 : ℝ) ^ p⁻¹ - 1) * R ∧
    |transport p (scaledBars 2 R) essentialBlock -
      (bottleneck (scaledBars 2 R) essentialBlock).toReal| = ((2 : ℝ) ^ p⁻¹ - 1) * R ∧
    uniformLimits 2 R := by
  have hB := scaled_bottleneck 2 (by decide) hR
  have hm : matching p (scaledBars 2 R) essentialBlock = (2 : ℝ) ^ p⁻¹ * R := by
    simpa only [Nat.cast_ofNat] using scaled_matching 2 hR hp
  have ht : transport p (scaledBars 2 R) essentialBlock = (2 : ℝ) ^ p⁻¹ * R := by
    rw [transport, finitePBoundaryTransportCost_eq_matchingCost]; exact hm
  have hfactor : 1 ≤ (2 : ℝ) ^ p⁻¹ :=
    Real.one_le_rpow (by norm_num) (inv_nonneg.mpr (zero_le_one.trans hp))
  have herr : (2 : ℝ) ^ p⁻¹ * R - R = ((2 : ℝ) ^ p⁻¹ - 1) * R := by ring
  refine ⟨(scaled_essential 2 R).trans block_essential, scaled_card 2 hR, ?_,
    ⟨scaled_essential 2 R, by simp [scaled_card 2 hR], hB.le⟩, hB, hm, ht, ?_, ?_,
    uniform_limits 2 hR.le⟩
  · apply (orderedQ_isPositive_iff _ _ _).mpr
    intro i; dsimp; linarith
  · rw [hm, hB, ENNReal.toReal_ofReal hR.le, herr,
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hfactor) hR.le)]
  · rw [ht, hB, ENNReal.toReal_ofReal hR.le, herr,
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hfactor) hR.le)]

private theorem sharp_fractional {R : ℝ} (hR : 0 < R) :
    |matching (3 / 2) (scaledBars 2 R) essentialBlock - R| =
        ((2 : ℝ) ^ (2 / 3 : ℝ) - 1) * R ∧
    |transport (3 / 2) (scaledBars 2 R) essentialBlock - R| =
        ((2 : ℝ) ^ (2 / 3 : ℝ) - 1) * R := by
  obtain ⟨_, _, _, _, hB, _, _, hm, ht, _⟩ :=
    sharp_common_essential hR (by norm_num : (1 : ℝ) ≤ 3 / 2)
  norm_num [hB, ENNReal.toReal_ofReal hR.le] at hm ht
  exact ⟨hm, ht⟩

private theorem sharp_bounds {R p : ℝ} (hR : 0 < R) (hp : 1 ≤ p) :
    |matching p (scaledBars 2 R) essentialBlock - R| ≤ ((2 : ℝ) ^ p⁻¹ - 1) * R ∧
    |transport p (scaledBars 2 R) essentialBlock - R| ≤ ((2 : ℝ) ^ p⁻¹ - 1) * R := by
  have hB := scaled_bottleneck 2 (by decide) hR
  have h : (scaledBars 2 R, essentialBlock) ∈ budgetSet 2 R :=
    ⟨scaled_essential 2 R, by simp [scaled_card 2 hR], hB.le⟩
  have hm := finitePMatchingCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    hp _ _ h.1 h.2.1 hR.le h.2.2
  have ht := finitePBoundaryTransportCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    hp _ _ h.1 h.2.1 hR.le h.2.2
  exact ⟨by simpa [hB, ENNReal.toReal_ofReal hR.le] using hm,
    by simpa [hB, ENNReal.toReal_ofReal hR.le] using ht⟩

private def singleton (x : ℝ × ℝ) : Diagram ℝ := orderedQ 1 3 (fun _ => x, births)

private theorem singleton_essential (x : ℝ × ℝ) :
    essentialPart (singleton x).points = essentialPart essentialBlock.points := by
  simp [singleton, essentialBlock, essentialPart_orderedQ]

private theorem singleton_finite (x : ℝ × ℝ) (hx : x.1 ≠ x.2) :
    finitePart (singleton x).points = {x} := by
  simp [singleton, finitePart_orderedQ, List.ofFn_succ, hx]

private theorem singleton_card (x : ℝ × ℝ) (hx : x.1 ≠ x.2) :
    Fintype.card (singleton x).finiteOccurrences = 1 := by
  simp only [Multiset.card_coe, singleton_finite x hx, Multiset.card_singleton]

private theorem singleton_value (x : ℝ × ℝ) (hx : x.1 ≠ x.2)
    (q : (singleton x).finiteOccurrences) : q.1 = x := by
  simpa only [singleton_finite x hx, Multiset.mem_singleton] using Multiset.coe_mem (x := q)

private theorem singleton_matching (p : ℝ) (x y : ℝ × ℝ)
    (hx : x.1 ≠ x.2) (hy : y.1 ≠ y.2) :
    matching p (singleton x) (singleton y) =
      finitePMatchingCost p (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) := by
  let u := (Fintype.equivFinOfCardEq (singleton_card x hx)).symm
  let v := (Fintype.equivFinOfCardEq (singleton_card y hy)).symm
  have h := finitePMatchingCost_reindex u v p
    (fun q : (singleton x).finiteOccurrences => q.1)
    (fun q : (singleton y).finiteOccurrences => q.1)
  have hu : (fun q : (singleton x).finiteOccurrences => q.1) ∘ u =
      (fun _ : Fin 1 => x) := by
    funext i
    exact singleton_value x hx (u i)
  have hv : (fun q : (singleton y).finiteOccurrences => q.1) ∘ v =
      (fun _ : Fin 1 => y) := by
    funext j
    exact singleton_value y hy (v j)
  rw [hu, hv] at h
  exact h.symm

private abbrev switchLeft : Diagram ℝ := singleton (0, 2)
private abbrev switchRight : Diagram ℝ := singleton (3 / 2, 7 / 2)

private theorem switch_left_value (q : switchLeft.finiteOccurrences) :
    q.1 = ((0, 2) : ℝ × ℝ) := singleton_value _ (by norm_num) q

private theorem switch_right_value (q : switchRight.finiteOccurrences) :
    q.1 = ((3 / 2, 7 / 2) : ℝ × ℝ) := singleton_value _ (by norm_num) q

private theorem switch_left_card : Fintype.card switchLeft.finiteOccurrences = 1 :=
  singleton_card _ (by norm_num)

private theorem switch_right_card : Fintype.card switchRight.finiteOccurrences = 1 :=
  singleton_card _ (by norm_num)

private theorem switch_positive : switchLeft.IsPositive ∧ switchRight.IsPositive := by
  constructor
  · unfold switchLeft singleton
    apply (orderedQ_isPositive_iff _ _ _).mpr
    intro i; norm_num
  · unfold switchRight singleton
    apply (orderedQ_isPositive_iff _ _ _).mpr
    intro i; norm_num

private theorem switch_essential :
    essentialPart switchLeft.points = essentialPart switchRight.points :=
  (singleton_essential _).trans (singleton_essential _).symm

private theorem switch_bottleneck : bottleneck switchLeft switchRight = 1 := by
  have hx : (0 : ℝ) ≠ 2 := by norm_num
  have hy : (3 / 2 : ℝ) ≠ 7 / 2 := by norm_num
  apply le_antisymm
  · apply bottleneck_le_deletions _ _ switch_essential 1
    · intro q; norm_num [switchLeft, singleton_value _ hx q, diagonalCost]
    · intro q; norm_num [switchRight, singleton_value _ hy q, diagonalCost]
  · obtain ⟨M, hM⟩ := (bottleneck_optimal_iff _ _).mpr
      (congrArg Multiset.card switch_essential)
    let : Nonempty switchLeft.finiteOccurrences :=
      Fintype.card_pos_iff.mp (by rw [switchLeft, singleton_card _ hx]; decide)
    let q : switchLeft.finiteOccurrences := Classical.choice inferInstance
    have h := M.source_le_cost (fun q => q.1) (fun q => q.1)
      (fun q => q.1) (fun q => q.1) q
    have hq : q.1 = ((0, 2) : ℝ × ℝ) := singleton_value _ hx q
    cases hf : M.finite q with
    | none => simpa [hf, hq, diagonalCost, hM] using h
    | some j =>
      have hj : j.1 = ((3 / 2, 7 / 2) : ℝ × ℝ) := singleton_value _ hy j
      have hpair : (1 : ℝ≥0∞) ≤ finitePairCost q.1 j.1 := by
        norm_num [hq, hj, finitePairCost]
      exact hpair.trans (by simpa only [hf, hM] using h)

private theorem switch_membership : (switchLeft, switchRight) ∈ budgetSet 2 1 := by
  refine ⟨switch_essential, ?_, by simp [switch_bottleneck]⟩
  rw [switch_left_card, switch_right_card]

private theorem switch_root_values :
    matching 1 switchLeft switchRight = 3 / 2 ∧
    matching 2 switchLeft switchRight = (2 : ℝ) ^ (1 / 2 : ℝ) ∧
    transport 1 switchLeft switchRight = 3 / 2 ∧
    transport 2 switchLeft switchRight = (2 : ℝ) ^ (1 / 2 : ℝ) ∧ uniformLimits 2 1 := by
  have hmatch (p : ℝ) := singleton_matching p (0, 2) (3 / 2, 7 / 2)
    (by norm_num) (by norm_num)
  have hm1 : matching 1 switchLeft switchRight = 3 / 2 := by
    rw [switchLeft, switchRight, hmatch, finitePMatchingCost,
      ← finitePowerBoundaryTransportCost_eq_matchingCost,
      FinitePBoundaryTransportExamples.switch_power_one]
    norm_num
  have hm2 : matching 2 switchLeft switchRight = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [switchLeft, switchRight, hmatch, finitePMatchingCost,
      ← finitePowerBoundaryTransportCost_eq_matchingCost,
      FinitePBoundaryTransportExamples.switch_power_two]
    norm_num
  exact ⟨hm1, hm2, by rw [transport, finitePBoundaryTransportCost_eq_matchingCost]; exact hm1,
    by rw [transport, finitePBoundaryTransportCost_eq_matchingCost]; exact hm2,
    uniform_limits 2 (by norm_num)⟩

private theorem singleton_power (p : ℝ) :
    finitePowerBoundaryTransportCost p (fun q : switchLeft.finiteOccurrences => q.1)
        (fun q : switchRight.finiteOccurrences => q.1) =
      finitePowerBoundaryTransportCost p (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ))
        (fun _ : Fin 1 => (3 / 2, 7 / 2)) := by
  let u := (Fintype.equivFinOfCardEq (singleton_card (0, 2) (by norm_num))).symm
  let v := (Fintype.equivFinOfCardEq
    (singleton_card ((3 / 2, 7 / 2) : ℝ × ℝ) (by norm_num))).symm
  simp only [finitePowerBoundaryTransportCost_eq_matchingCost]
  have h := finitePowerMatchingCost_reindex u v p
    (fun q : switchLeft.finiteOccurrences => q.1)
    (fun q : switchRight.finiteOccurrences => q.1)
  have hu : (fun q : switchLeft.finiteOccurrences => q.1) ∘ u =
      (fun _ : Fin 1 => ((0, 2) : ℝ × ℝ)) := by
    funext i
    exact switch_left_value (u i)
  have hv : (fun q : switchRight.finiteOccurrences => q.1) ∘ v =
      (fun _ : Fin 1 => ((3 / 2, 7 / 2) : ℝ × ℝ)) := by
    funext j
    exact switch_right_value (v j)
  rw [hu, hv] at h
  exact h.symm

/-- A pairing attains p=1 and loses at p=2; the actual zero plan attains p=2. -/
private theorem actual_optimizer_change :
    (∃ M : OccurrenceMatching switchLeft.finiteOccurrences switchRight.finiteOccurrences
        PEmpty.{1} PEmpty.{1},
      M.totalFinitePowerCost 1 (fun q => q.1) (fun q => q.1) =
        finitePowerBoundaryTransportCost 1 (fun q : switchLeft.finiteOccurrences => q.1)
          (fun q : switchRight.finiteOccurrences => q.1) ∧
      finitePowerBoundaryTransportCost 2 (fun q : switchLeft.finiteOccurrences => q.1)
          (fun q : switchRight.finiteOccurrences => q.1) <
        M.totalFinitePowerCost 2 (fun q => q.1) (fun q => q.1)) ∧
    (FiniteBoundaryPlan.zero : FiniteBoundaryPlan switchLeft.finiteOccurrences
      switchRight.finiteOccurrences).powerCost 2 (fun q => q.1) (fun q => q.1) =
      finitePowerBoundaryTransportCost 2 (fun q : switchLeft.finiteOccurrences => q.1)
        (fun q : switchRight.finiteOccurrences => q.1) := by
  let u := Fintype.equivFinOfCardEq (singleton_card (0, 2) (by norm_num))
  let v := Fintype.equivFinOfCardEq
    (singleton_card ((3 / 2, 7 / 2) : ℝ × ℝ) (by norm_num))
  let M := FinitePBoundaryTransportExamples.pairSingletons.relabel u v
    (Equiv.refl _) (Equiv.refl _)
  have hx : (fun q : switchLeft.finiteOccurrences => q.1) =
      (fun _ => ((0, 2) : ℝ × ℝ)) := funext switch_left_value
  have hy : (fun q : switchRight.finiteOccurrences => q.1) =
      (fun _ => ((3 / 2, 7 / 2) : ℝ × ℝ)) := funext switch_right_value
  have hM (p : ℝ) : M.totalFinitePowerCost p (fun q => q.1) (fun q => q.1) =
      FinitePBoundaryTransportExamples.pairSingletons.totalFinitePowerCost p
        (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2)) := by
    have h := OccurrenceMatching.totalFinitePowerCost_relabel u v
      FinitePBoundaryTransportExamples.pairSingletons p
      (fun _ => (0, 2)) (fun _ => (3 / 2, 7 / 2))
    rw [hx, hy]
    simpa only [Function.comp_def] using h
  obtain ⟨h1, h2⟩ := FinitePBoundaryTransportExamples.optimizer_changes_with_exponent
  refine ⟨⟨M, ?_, ?_⟩, ?_⟩
  · rw [hM, singleton_power]; exact h1
  · rw [hM, singleton_power]; exact h2
  · rw [singleton_power, FinitePBoundaryTransportExamples.switch_power_two]
    rw [hx, hy]
    have hcL : (finitePart switchLeft.points).card = 1 := by
      rw [← finite_card]
      exact switch_left_card
    have hcR : (finitePart switchRight.points).card = 1 := by
      rw [← finite_card]
      exact switch_right_card
    norm_num [FiniteBoundaryPlan.powerCost, FiniteBoundaryPlan.linearCost,
      FiniteBoundaryPlan.zero, FiniteBoundaryPlan.deletionMass,
      FiniteBoundaryPlan.insertionMass, diagonalCost, Real.rpow_two,
      Finset.sum_const, Finset.card_univ, hcL, hcR]

/-- The four new capstones apply to actual bounded positive common-essential pairs. -/
private theorem switch_bounds {p : ℝ} (hp : 1 ≤ p) :
    |matching p switchLeft switchRight - (1 : ℝ)| ≤ (2 : ℝ) ^ p⁻¹ - 1 ∧
    |transport p switchLeft switchRight - (1 : ℝ)| ≤ (2 : ℝ) ^ p⁻¹ - 1 ∧
    (switchLeft, switchRight) ∈ budgetSet 2 1 ∧ uniformLimits 2 1 := by
  have h := switch_membership
  have hm := finitePMatchingCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    hp _ _ h.1 h.2.1 (by norm_num : (0 : ℝ) ≤ 1) h.2.2
  have ht := finitePBoundaryTransportCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    hp _ _ h.1 h.2.1 (by norm_num : (0 : ℝ) ≤ 1) h.2.2
  exact ⟨by simpa [switch_bottleneck] using hm, by simpa [switch_bottleneck] using ht,
    h, uniform_limits 2 (by norm_num)⟩

private abbrev essentialBirth := FinitePBottleneckLimitExamples.essentialBirth

/-- Equal cardinalities, with finite full B, still give error one at finite count zero. -/
private theorem cardinality_is_insufficient {p : ℝ} (hp : 1 ≤ p) :
    Fintype.card (essentialBirth 0).essentialOccurrences = 1 ∧
    Fintype.card (essentialBirth 1).essentialOccurrences = 1 ∧
    essentialPart (essentialBirth 0).points ≠ essentialPart (essentialBirth 1).points ∧
    Fintype.card (essentialBirth 0).finiteOccurrences +
      Fintype.card (essentialBirth 1).finiteOccurrences = 0 ∧
    bottleneck (essentialBirth 0) (essentialBirth 1) = 1 ∧
    matching p (essentialBirth 0) (essentialBirth 1) = 0 ∧
    transport p (essentialBirth 0) (essentialBirth 1) = 0 ∧
    |matching p (essentialBirth 0) (essentialBirth 1) -
      (bottleneck (essentialBirth 0) (essentialBirth 1)).toReal| = 1 ∧
    |transport p (essentialBirth 0) (essentialBirth 1) -
      (bottleneck (essentialBirth 0) (essentialBirth 1)).toReal| = 1 ∧
    ((((max 1 0 : ℕ) : ℝ) ^ p⁻¹) - 1) * 1 = 0 ∧
    (essentialBirth 0, essentialBirth 1) ∉ budgetSet 0 1 := by
  obtain ⟨hm, hB⟩ := FinitePBottleneckLimitExamples.essential_births_zero_one hp
  have ht : transport p (essentialBirth 0) (essentialBirth 1) = 0 := by
    rw [transport, finitePBoundaryTransportCost_eq_matchingCost]; exact hm
  have hne : essentialPart (essentialBirth 0).points ≠
      essentialPart (essentialBirth 1).points := by
    norm_num [essentialBirth, FinitePBottleneckLimitExamples.essentialBirth,
      essentialPart_orderedQ, List.ofFn_succ]
  refine ⟨?_, ?_, hne, ?_, hB, hm, ht, ?_, ?_, by simp, fun h => hne h.1⟩
  · rw [essential_card]
    simp [essentialBirth, FinitePBottleneckLimitExamples.essentialBirth,
      essentialPart_orderedQ]
  · rw [essential_card]
    simp [essentialBirth, FinitePBottleneckLimitExamples.essentialBirth,
      essentialPart_orderedQ]
  · rw [finite_card, finite_card]
    simp [essentialBirth, FinitePBottleneckLimitExamples.essentialBirth,
      finitePart_orderedQ]
  · norm_num [matching, hm, hB]
  · norm_num [transport, ht, hB]

private def empty : Diagram ℝ := orderedQ 0 0 (Fin.elim0, Fin.elim0)

private instance empty_finite : IsEmpty empty.finiteOccurrences := by
  apply Fintype.card_eq_zero_iff.mp
  rw [finite_card]
  simp [empty, finitePart_orderedQ]

/-- Unequal essential counts forbid every finite radius, regardless of toReal(top). -/
private theorem unequal_counts_excluded {p : ℝ} (hp : 1 ≤ p) :
    (essentialPart (essentialBirth 0).points).card ≠ (essentialPart empty.points).card ∧
    bottleneck (essentialBirth 0) empty = ⊤ ∧
    (∀ R : ℝ, ¬ bottleneck (essentialBirth 0) empty ≤ ENNReal.ofReal R) ∧
    (∀ m : ℕ, ∀ R : ℝ, (essentialBirth 0, empty) ∉ budgetSet m R) ∧
    matching p (essentialBirth 0) empty = 0 ∧ transport p (essentialBirth 0) empty = 0 := by
  have hcounts : (essentialPart (essentialBirth 0).points).card ≠
      (essentialPart empty.points).card := by
    simp [essentialBirth, FinitePBottleneckLimitExamples.essentialBirth,
      empty, essentialPart_orderedQ]
  have hB : bottleneck (essentialBirth 0) empty = ⊤ :=
    (bottleneck_eq_top_iff _ _).mpr hcounts
  have hR (R : ℝ) : ¬ bottleneck (essentialBirth 0) empty ≤ ENNReal.ofReal R := by
    rw [hB, top_le_iff]
    exact ENNReal.ofReal_ne_top
  let : IsEmpty (essentialBirth 0).finiteOccurrences := by
    apply Fintype.card_eq_zero_iff.mp
    rw [finite_card]
    simp [essentialBirth, FinitePBottleneckLimitExamples.essentialBirth,
      finitePart_orderedQ]
  exact ⟨hcounts, hB, hR, fun _ R h => hR R h.2.2, finitePMatchingCost_empty hp _ _,
    finitePBoundaryTransportCost_empty hp _ _⟩

private abbrev oldBudgetSet (m : ℕ) (R : ℝ) : Set (Diagram ℝ × Diagram ℝ) :=
  {z | essentialPart z.1.points = 0 ∧ essentialPart z.2.points = 0 ∧
    Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤ m ∧
    bottleneck z.1 z.2 ≤ ENNReal.ofReal R}

private theorem essential_free_inclusion (m : ℕ) (R : ℝ) :
    oldBudgetSet m R ⊆ budgetSet m R :=
  fun _ h => ⟨h.1.trans h.2.1.symm, h.2.2⟩

/-- The old literal domain is a restriction, with the old public API preserved. -/
private theorem essential_free_restriction (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ => matching p z.1 z.2)
      (fun z => (bottleneck z.1 z.2).toReal) atTop (oldBudgetSet m R) ∧
    TendstoUniformlyOn
      (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ => transport p z.1 z.2)
      (fun z => (bottleneck z.1 z.2).toReal) atTop (oldBudgetSet m R) :=
  ⟨(uniform_limits m hR).1.mono (essential_free_inclusion m R),
    (uniform_limits m hR).2.mono (essential_free_inclusion m R)⟩

private theorem essential_free_actual_examples {p : ℝ} (hp : 1 ≤ p) :
    (empty, empty) ∈ oldBudgetSet 0 0 ∧
    (FinitePBottleneckLimitExamples.unitBars 1, empty) ∈ oldBudgetSet 1 1 ∧
    (FinitePBottleneckLimitExamples.unitBars 1).IsPositive ∧
    Fintype.card (FinitePBottleneckLimitExamples.unitBars 1).finiteOccurrences = 1 ∧
    bottleneck (FinitePBottleneckLimitExamples.unitBars 1) empty = 1 ∧
    matching p (FinitePBottleneckLimitExamples.unitBars 1) empty = 1 ∧
    transport p (FinitePBottleneckLimitExamples.unitBars 1) empty = 1 ∧
    uniformLimits 0 0 ∧ uniformLimits 1 1 := by
  have he : empty = FinitePBottleneckLimitExamples.unitBars 0 := by
    apply Diagram.ext
    simp [empty, FinitePBottleneckLimitExamples.unitBars, orderedQ]
  obtain ⟨hm, ht⟩ := FinitePBottleneckLimitExamples.singleton_empty_costs hp
  have hB := FinitePBottleneckLimitExamples.singleton_empty_bottleneck
  have hc : Fintype.card (FinitePBottleneckLimitExamples.unitBars 1).finiteOccurrences = 1 := by
    rw [finite_card]
    simp [FinitePBottleneckLimitExamples.unitBars, finitePart_orderedQ,
      List.ofFn_succ]
  have hess : essentialPart (FinitePBottleneckLimitExamples.unitBars 1).points = 0 := by
    simp [FinitePBottleneckLimitExamples.unitBars, essentialPart_orderedQ]
  refine ⟨⟨?_, ?_, by simp, by simp [bottleneck_self]⟩, ?_,
    FinitePBottleneckLimitExamples.unitBars_positive 1, hc, ?_, ?_, ?_,
    uniform_limits 0 le_rfl, uniform_limits 1 (by norm_num)⟩
  · simp [empty, essentialPart_orderedQ]
  · simp [empty, essentialPart_orderedQ]
  · refine ⟨hess, ?_, ?_, ?_⟩
    · simp [empty, essentialPart_orderedQ]
    · simp [hc]
    · simpa only [he, ENNReal.ofReal_one] using hB.le
  · simpa only [he] using hB
  · simpa only [he, Nat.cast_one, Real.one_rpow, one_mul] using hm
  · simpa only [he, Nat.cast_one, Real.one_rpow, one_mul] using ht

end TDA.Persistence.FinitePCommonEssentialBottleneckExamples
