import TDA.Persistence.FiniteMatchingCostBottleneck
import TDA.Persistence.FinitePBoundaryTransport

/-!
# Cardinality-controlled finite real-p distances

The finite restriction of a full matching has at most one charge per source and
one per target. Bounding each by the full maximum gives a powered sum bound;
taking the root gives the occurrence-count factor to the reciprocal power.
A bottleneck minimizer then bounds the optimized finite matching and
real boundary-plan costs. Essential occurrences supply only the full bottleneck
witness and are not part of the finite transport quantity.
-/

namespace TDA.Persistence

namespace OccurrenceMatching

variable {I J E F : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype F]

/-- Every finite powered charge is bounded by the full matching maximum to `p`.
The sum counts source labels and unmatched target labels, retaining multiplicity. -/
theorem totalFinitePowerCost_finiteRestriction_le_card_mul_cost_rpow
    (M : OccurrenceMatching I J E F) {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (b : E → ℝ) (c : F → ℝ) :
    M.finiteRestriction.totalFinitePowerCost p x y ≤
      ((Fintype.card I + Fintype.card J : ℕ) : ℝ) * (M.cost x y b c).toReal ^ p := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hfinite := (occurrenceMatching_cost_lt_top x y b c M).ne
  have hs (i : I) :
      (match M.finite i with
        | some j => (finitePairCost (x i) (y j)).toReal ^ p
        | none => (diagonalCost (x i)).toReal ^ p) ≤ (M.cost x y b c).toReal ^ p := by
    have h := ENNReal.toReal_mono hfinite (M.source_le_cost x y b c i)
    cases hi : M.finite i <;> simp only [hi] at h ⊢ <;>
      exact Real.rpow_le_rpow ENNReal.toReal_nonneg h (zero_le_one.trans hp)
  have ht (j : J) :
      (if ∃ i, M.finite i = some j then 0 else (diagonalCost (y j)).toReal ^ p) ≤
        (M.cost x y b c).toReal ^ p := by
    have h := ENNReal.toReal_mono hfinite (M.target_le_cost x y b c j)
    have hpow := Real.rpow_le_rpow ENNReal.toReal_nonneg h (zero_le_one.trans hp)
    split_ifs with hj <;>
      simpa only [hj, if_true, if_false, ENNReal.toReal_zero, Real.zero_rpow hp0] using hpow
  unfold totalFinitePowerCost totalBoundaryCost
  change (∑ i, _) + (∑ j, _) ≤ _
  calc
    _ ≤ (∑ _i : I, (M.cost x y b c).toReal ^ p) +
        ∑ _j : J, (M.cost x y b c).toReal ^ p :=
      add_le_add (Finset.sum_le_sum (fun i _ => hs i))
        (Finset.sum_le_sum (fun j _ => ht j))
    _ = _ := by simp [Nat.cast_add, add_mul]

end OccurrenceMatching

/-- A bottleneck-minimizing full matching bounds the finite powered minimum.
Finiteness is needed before converting the extended bottleneck value to real. -/
theorem finitePowerMatchingCost_le_card_mul_bottleneck_rpow
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ) (hfinite : bottleneck D E < ⊤) :
    finitePowerMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) ≤
      ((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) *
        (bottleneck D E).toReal ^ p := by
  obtain ⟨M, hM⟩ := (bottleneck_optimal_iff D E).mpr
    ((bottleneck_lt_top_iff D E).mp hfinite)
  calc
    _ ≤ M.finiteRestriction.totalFinitePowerCost p _ _ :=
      finitePowerMatchingCost_le_matching p _ _ M.finiteRestriction
    _ ≤ _ := by
      simpa only [hM] using M.totalFinitePowerCost_finiteRestriction_le_card_mul_cost_rpow hp
        (fun q => q.1) (fun q => q.1) (fun q => q.1) (fun q => q.1)

/-- Finite real-p matching distance is at most the count factor `N^(1/p)`
times the full bottleneck value. Essential bars are absent from the left side. -/
theorem finitePMatchingCost_le_card_rpow_mul_bottleneck
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ) (hfinite : bottleneck D E < ⊤) :
    finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) ≤
      (((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) ^ p⁻¹) *
        (bottleneck D E).toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have h := Real.rpow_le_rpow (finitePowerMatchingCost_nonneg p _ _)
    (finitePowerMatchingCost_le_card_mul_bottleneck_rpow hp D E hfinite)
    (inv_nonneg.mpr (zero_le_one.trans hp))
  simpa only [finitePMatchingCost,
    Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg ENNReal.toReal_nonneg p),
    Real.rpow_rpow_inv ENNReal.toReal_nonneg hp0] using h

/-- The bound applies to the optimum over all feasible real reservoir plans. -/
theorem finitePBoundaryTransportCost_le_card_rpow_mul_bottleneck
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ) (hfinite : bottleneck D E < ⊤) :
    finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) ≤
      (((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) ^ p⁻¹) *
        (bottleneck D E).toReal := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_le_card_rpow_mul_bottleneck hp D E hfinite

/-- A finite bottleneck radius supplies both finiteness and a real upper bound. -/
theorem finitePBoundaryTransportCost_le_card_rpow_mul_of_bottleneck_le
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hB : bottleneck D E ≤ ENNReal.ofReal r) :
    finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) ≤
      (((Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences : ℕ) : ℝ) ^ p⁻¹) *
        r := by
  have hfinite := hB.trans_lt ENNReal.ofReal_lt_top
  have hreal : (bottleneck D E).toReal ≤ r := by
    simpa only [ENNReal.toReal_ofReal hr] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hB
  exact (finitePBoundaryTransportCost_le_card_rpow_mul_bottleneck hp D E hfinite).trans
    (mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- A uniform natural cardinality budget yields a uniform real-p radius bound. -/
theorem finitePBoundaryTransportCost_le_cardBound_rpow_mul_of_bottleneck_le
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ) {m : ℕ}
    (hcard : Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences ≤ m)
    {r : ℝ} (hr : 0 ≤ r) (hB : bottleneck D E ≤ ENNReal.ofReal r) :
    finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) ≤ (m : ℝ) ^ p⁻¹ * r := by
  have hcast : ((Fintype.card D.finiteOccurrences +
      Fintype.card E.finiteOccurrences : ℕ) : ℝ) ≤ m := by exact_mod_cast hcard
  exact (finitePBoundaryTransportCost_le_card_rpow_mul_of_bottleneck_le hp D E hr hB).trans
    (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (inv_nonneg.mpr (zero_le_one.trans hp))) hr)

end TDA.Persistence
