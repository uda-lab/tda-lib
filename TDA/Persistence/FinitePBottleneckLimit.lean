import TDA.Persistence.FinitePMatchingCostBottleneck

/-!
# Finite real-p transport converges to bottleneck distance

For diagrams without essential bars, the maximum charge of an actual matching is
bounded by its rooted powered sum. Choosing a minimizing finite matching supplies
the missing lower bound by the full bottleneck distance. The existing upper bound
has factor `N^(1/p)`, where `N` counts both finite occurrence families. For positive
`N` this factor tends to one; empty families are handled separately.

All multiplicities are retained. The limit varies the real matching exponent at a
fixed maximum ground norm and fixed diagrams. The real-plan result concerns the
optimized boundary-reservoir cost, using its proved equality with matching costs.
-/

noncomputable section

namespace TDA.Persistence

open Filter
open scoped BigOperators Topology ENNReal

namespace OccurrenceMatching

variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B]

/-- With no essential source occurrences, every matching charge is bounded by the
rooted sum of its finite powered charges. The matching's essential equivalence also
forces its essential target family to be empty. -/
theorem cost_le_ofReal_root_totalFinitePowerCost [IsEmpty A]
    (M : OccurrenceMatching I J A B) {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (b : A → ℝ) (c : B → ℝ) :
    M.cost x y b c ≤
      ENNReal.ofReal (M.finiteRestriction.totalFinitePowerCost p x y ^ p⁻¹) := by
  classical
  let source : I → ℝ≥0∞ := fun i => match M.finite i with
    | some j => finitePairCost (x i) (y j)
    | none => diagonalCost (x i)
  let target : J → ℝ≥0∞ := fun j =>
    if ∃ i, M.finite i = some j then 0 else diagonalCost (y j)
  let S := M.finiteRestriction.totalFinitePowerCost p x y
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hS : 0 ≤ S := M.finiteRestriction.totalFinitePowerCost_nonneg p x y
  have hsum : S = (∑ i, (source i).toReal ^ p) + ∑ j, (target j).toReal ^ p := by
    dsimp only [S, totalFinitePowerCost, totalBoundaryCost, finiteRestriction, source, target]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      cases M.finite i <;> rfl
    · apply Finset.sum_congr rfl
      intro j _
      by_cases h : ∃ i, M.finite i = some j
      · simp only [h, if_true, ENNReal.toReal_zero, Real.zero_rpow hp0]
      · simp only [h, if_false]
  have hs_nonneg : 0 ≤ ∑ i, (source i).toReal ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
  have ht_nonneg : 0 ≤ ∑ j, (target j).toReal ^ p :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _
  apply M.cost_le_of x y b c (ENNReal.ofReal (S ^ p⁻¹))
  · intro i
    change source i ≤ _
    have hpow : (source i).toReal ^ p ≤ S := by
      rw [hsum]
      exact (Finset.single_le_sum
        (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg p)
        (Finset.mem_univ i)).trans (le_add_of_nonneg_right ht_nonneg)
    have hroot := (Real.le_rpow_inv_iff_of_pos ENNReal.toReal_nonneg hS hp_pos).mpr hpow
    have hfinite : source i ≠ ⊤ := by
      dsimp only [source]
      cases M.finite i <;> simp [finitePairCost, diagonalCost]
    calc
      source i = ENNReal.ofReal (source i).toReal := (ENNReal.ofReal_toReal hfinite).symm
      _ ≤ ENNReal.ofReal (S ^ p⁻¹) := ENNReal.ofReal_le_ofReal hroot
  · intro j
    change target j ≤ _
    have hpow : (target j).toReal ^ p ≤ S := by
      rw [hsum]
      exact (Finset.single_le_sum
        (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg p)
        (Finset.mem_univ j)).trans (le_add_of_nonneg_left hs_nonneg)
    have hroot := (Real.le_rpow_inv_iff_of_pos ENNReal.toReal_nonneg hS hp_pos).mpr hpow
    have hfinite : target j ≠ ⊤ := by
      dsimp only [target]
      split_ifs <;> simp [diagonalCost]
    calc
      target j = ENNReal.ofReal (target j).toReal := (ENNReal.ofReal_toReal hfinite).symm
      _ ≤ ENNReal.ofReal (S ^ p⁻¹) := ENNReal.ofReal_le_ofReal hroot
  · intro k
    exact isEmptyElim k

end OccurrenceMatching

private theorem isEmpty_essentialOccurrences_of_eq_zero (D : Diagram ℝ)
    (hD : essentialPart D.points = 0) : IsEmpty D.essentialOccurrences := by
  apply Fintype.card_eq_zero_iff.mp
  simp only [Multiset.card_coe, hD, Multiset.card_zero]

/-- Empty essential parts guarantee that the full bottleneck is finite. -/
theorem bottleneck_lt_top_of_essentialParts_eq_zero (D E : Diagram ℝ)
    (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    bottleneck D E < ⊤ :=
  (bottleneck_lt_top_iff D E).mpr (by simp only [hD, hE])

/-- An optimizing finite partial matching extends to an actual full matching when
both essential parts are empty. Its maximum is at most its rooted powered sum. -/
theorem bottleneck_le_ofReal_finitePMatchingCost {p : ℝ} (hp : 1 ≤ p)
    (D E : Diagram ℝ) (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    bottleneck D E ≤ ENNReal.ofReal
      (finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1)) := by
  classical
  let := isEmpty_essentialOccurrences_of_eq_zero D hD
  let := isEmpty_essentialOccurrences_of_eq_zero E hE
  obtain ⟨m, hm⟩ := exists_minimizing_pMatching p
    (fun q : D.finiteOccurrences => q.1) (fun q : E.finiteOccurrences => q.1)
  let M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences :=
    { finite := m.finite
      finite_injective := m.finite_injective
      essential := Equiv.equivOfIsEmpty _ _ }
  have hcost := M.cost_le_ofReal_root_totalFinitePowerCost hp
    (fun q => q.1) (fun q => q.1) (fun q => q.1) (fun q => q.1)
  have hroot : M.finiteRestriction.totalFinitePowerCost p
      (fun q => q.1) (fun q => q.1) ^ p⁻¹ =
      finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) := by
    change m.totalFinitePowerCost p _ _ ^ p⁻¹ = _
    exact hm
  rw [hroot] at hcost
  exact (bottleneck_le_matching D E M).trans hcost

/-- Real-valued lower comparison, after establishing finiteness of the full cost. -/
theorem bottleneck_toReal_le_finitePMatchingCost {p : ℝ} (hp : 1 ≤ p)
    (D E : Diagram ℝ) (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    (bottleneck D E).toReal ≤
      finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) := by
  have hfinite := bottleneck_lt_top_of_essentialParts_eq_zero D E hD hE
  have h := (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mpr
    (bottleneck_le_ofReal_finitePMatchingCost hp D E hD hE)
  simpa only [ENNReal.toReal_ofReal (finitePMatchingCost_nonneg p _ _)] using h

/-- The lower comparison concerns the actual optimized real reservoir-plan cost. -/
theorem bottleneck_le_ofReal_finitePBoundaryTransportCost {p : ℝ} (hp : 1 ≤ p)
    (D E : Diagram ℝ) (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    bottleneck D E ≤ ENNReal.ofReal
      (finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1)) := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact bottleneck_le_ofReal_finitePMatchingCost hp D E hD hE

/-- For fixed finite diagrams without essential bars, the real matching exponent
tending to infinity recovers their full bottleneck distance. -/
theorem finitePMatchingCost_tendsto_bottleneck (D E : Diagram ℝ)
    (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    Tendsto (fun p : ℝ => finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
      (fun q : E.finiteOccurrences => q.1)) atTop (𝓝 (bottleneck D E).toReal) := by
  classical
  let N := Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences
  have hfinite := bottleneck_lt_top_of_essentialParts_eq_zero D E hD hE
  by_cases hN : N = 0
  · have hcards := Nat.add_eq_zero_iff.mp hN
    let : IsEmpty D.finiteOccurrences := Fintype.card_eq_zero_iff.mp hcards.1
    let : IsEmpty E.finiteOccurrences := Fintype.card_eq_zero_iff.mp hcards.2
    have hB : (bottleneck D E).toReal = 0 := by
      have h := bottleneck_toReal_le_finitePMatchingCost (p := 1) (by norm_num) D E hD hE
      rw [finitePMatchingCost_empty (by norm_num : (1 : ℝ) ≤ 1)] at h
      exact le_antisymm h ENNReal.toReal_nonneg
    rw [hB]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with p hp
    exact (finitePMatchingCost_empty hp _ _).symm
  · have hNcast : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hfactor : Tendsto (fun p : ℝ => (N : ℝ) ^ p⁻¹) atTop (𝓝 1) := by
      simpa only [Real.rpow_zero, Function.comp_def] using
        (Real.continuousAt_const_rpow (a := (N : ℝ)) (b := 0) hNcast).tendsto.comp
          (tendsto_inv_atTop_zero : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0))
    have hupper : Tendsto (fun p : ℝ => (N : ℝ) ^ p⁻¹ * (bottleneck D E).toReal)
        atTop (𝓝 (bottleneck D E).toReal) := by
      simpa only [one_mul] using hfactor.mul_const (bottleneck D E).toReal
    apply tendsto_const_nhds.squeeze' hupper
    · exact (eventually_ge_atTop (1 : ℝ)).mono fun p hp =>
        bottleneck_toReal_le_finitePMatchingCost hp D E hD hE
    · exact (eventually_ge_atTop (1 : ℝ)).mono fun p hp =>
        finitePMatchingCost_le_card_rpow_mul_bottleneck hp D E hfinite

/-- The actual real boundary-reservoir optimum has the same bottleneck limit. -/
theorem finitePBoundaryTransportCost_tendsto_bottleneck (D E : Diagram ℝ)
    (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    Tendsto (fun p : ℝ => finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
      (fun q : E.finiteOccurrences => q.1)) atTop (𝓝 (bottleneck D E).toReal) := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    finitePMatchingCost_tendsto_bottleneck D E hD hE

/-- Extended-valued limit identifies the actual bottleneck, with its finiteness
derived from empty essential parts before converting back from its real value. -/
theorem ofReal_finitePMatchingCost_tendsto_bottleneck (D E : Diagram ℝ)
    (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    Tendsto (fun p : ℝ => ENNReal.ofReal
      (finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1))) atTop (𝓝 (bottleneck D E)) := by
  have hfinite := bottleneck_lt_top_of_essentialParts_eq_zero D E hD hE
  simpa only [ENNReal.ofReal_toReal hfinite.ne] using
    ENNReal.tendsto_ofReal (finitePMatchingCost_tendsto_bottleneck D E hD hE)

/-- The optimized real reservoir-plan cost converges to the full extended
bottleneck value on the essential-free finite domain. -/
theorem ofReal_finitePBoundaryTransportCost_tendsto_bottleneck (D E : Diagram ℝ)
    (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0) :
    Tendsto (fun p : ℝ => ENNReal.ofReal
      (finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1))) atTop (𝓝 (bottleneck D E)) := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    ofReal_finitePMatchingCost_tendsto_bottleneck D E hD hE

end TDA.Persistence
