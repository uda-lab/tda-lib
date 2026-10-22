import TDA.Persistence.FinitePBottleneckLimit
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform bottleneck recovery with finite count and radius budgets

Write `N` for the total number of finite occurrences and `B` for the full
bottleneck distance. On the essential-free domain the existing optimized costs
satisfy `B ≤ dₚ ≤ N^(1/p) * B`. If `N ≤ m` and `B ≤ R`, the error is at most
`((max 1 m)^(1/p) - 1) * R`. This single envelope tends to zero independently of
the diagrams, including empty families and zero radius.

The four results below concern unnormalized unit occurrences at fixed maximum
ground norm. Their positive finite-diagram specialization uses the matching
convention of Divol–Lacombe, corrected v4, §1.1. The uniform estimate is a finite
library derivation. No topology on diagrams or common optimizing matching is
needed. The plan results use the optimum over all feasible real reservoir
matrices through its proved matching equality.
-/

noncomputable section

namespace TDA.Persistence

open Filter
open scoped Topology

/-- A count budget and bottleneck radius give one error bound for every
essential-free pair. `max 1 m` includes the zero-count case in the same formula. -/
theorem finitePMatchingCost_abs_sub_bottleneck_le_uniformBound
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ)
    (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0)
    {m : ℕ}
    (hcard : Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences ≤ m)
    {R : ℝ} (hR : 0 ≤ R) (hB : bottleneck D E ≤ ENNReal.ofReal R) :
    |finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) - (bottleneck D E).toReal| ≤
      ((((max 1 m : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  have hfinite := bottleneck_lt_top_of_essentialParts_eq_zero D E hD hE
  have hb : (bottleneck D E).toReal ≤ R := by
    simpa only [ENNReal.toReal_ofReal hR] using
      (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mpr hB
  have hlower := bottleneck_toReal_le_finitePMatchingCost hp D E hD hE
  have hcount : ((Fintype.card D.finiteOccurrences +
      Fintype.card E.finiteOccurrences : ℕ) : ℝ) ≤ (max 1 m : ℕ) := by
    exact_mod_cast hcard.trans (le_max_right 1 m)
  have hexp : 0 ≤ p⁻¹ := inv_nonneg.mpr (zero_le_one.trans hp)
  have hfactor : 1 ≤ ((max 1 m : ℕ) : ℝ) ^ p⁻¹ :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 m) hexp
  have hupper := (finitePMatchingCost_le_card_rpow_mul_bottleneck hp D E hfinite).trans
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hcount hexp)
      ENNReal.toReal_nonneg)
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  calc
    _ ≤ (((max 1 m : ℕ) : ℝ) ^ p⁻¹) * (bottleneck D E).toReal -
        (bottleneck D E).toReal := sub_le_sub_right hupper _
    _ = ((((max 1 m : ℕ) : ℝ) ^ p⁻¹) - 1) * (bottleneck D E).toReal := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hfactor)

/-- The same error bound holds for the optimized cost over all real plans. -/
theorem finitePBoundaryTransportCost_abs_sub_bottleneck_le_uniformBound
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ)
    (hD : essentialPart D.points = 0) (hE : essentialPart E.points = 0)
    {m : ℕ}
    (hcard : Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences ≤ m)
    {R : ℝ} (hR : 0 ≤ R) (hB : bottleneck D E ≤ ENNReal.ofReal R) :
    |finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) - (bottleneck D E).toReal| ≤
      ((((max 1 m : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_abs_sub_bottleneck_le_uniformBound hp D E hD hE hcard hR hB

private theorem uniform_errorEnvelope_tendsto (m : ℕ) (R : ℝ) :
    Tendsto (fun p : ℝ => ((((max 1 m : ℕ) : ℝ) ^ p⁻¹) - 1) * R)
      atTop (𝓝 0) := by
  have hbase : ((max 1 m : ℕ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (max 1 m : ℕ) := by exact_mod_cast le_max_left 1 m
    linarith
  have hfactor : Tendsto (fun p : ℝ => ((max 1 m : ℕ) : ℝ) ^ p⁻¹)
      atTop (𝓝 1) := by
    simpa only [Real.rpow_zero, Function.comp_def] using
      (Real.continuousAt_const_rpow (a := ((max 1 m : ℕ) : ℝ)) (b := 0) hbase).tendsto.comp
        (tendsto_inv_atTop_zero : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0))
  simpa only [sub_self, zero_mul] using (hfactor.sub_const 1).mul_const R

/-- One exponent tail works for all essential-free diagram pairs within the
specified count and radius budgets. Occurrence types may vary with the pair. -/
theorem finitePMatchingCost_tendstoUniformlyOn_bottleneck
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ =>
        finitePMatchingCost p (fun q : z.1.finiteOccurrences => q.1)
          (fun q : z.2.finiteOccurrences => q.1))
      (fun z : Diagram ℝ × Diagram ℝ => (bottleneck z.1 z.2).toReal) atTop
      {z : Diagram ℝ × Diagram ℝ |
        essentialPart z.1.points = 0 ∧ essentialPart z.2.points = 0 ∧
        Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤ m ∧
        bottleneck z.1 z.2 ≤ ENNReal.ofReal R} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(uniform_errorEnvelope_tendsto m R).eventually (gt_mem_nhds hε),
    eventually_ge_atTop (1 : ℝ)] with p herror hp
  intro z hz
  rw [Real.dist_eq, abs_sub_comm]
  exact (finitePMatchingCost_abs_sub_bottleneck_le_uniformBound hp z.1 z.2
    hz.1 hz.2.1 hz.2.2.1 hR hz.2.2.2).trans_lt herror

/-- Uniform recovery for the optimized real boundary-reservoir cost. -/
theorem finitePBoundaryTransportCost_tendstoUniformlyOn_bottleneck
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ =>
        finitePBoundaryTransportCost p (fun q : z.1.finiteOccurrences => q.1)
          (fun q : z.2.finiteOccurrences => q.1))
      (fun z : Diagram ℝ × Diagram ℝ => (bottleneck z.1 z.2).toReal) atTop
      {z : Diagram ℝ × Diagram ℝ |
        essentialPart z.1.points = 0 ∧ essentialPart z.2.points = 0 ∧
        Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤ m ∧
        bottleneck z.1 z.2 ≤ ENNReal.ofReal R} := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    finitePMatchingCost_tendstoUniformlyOn_bottleneck m R hR

end TDA.Persistence
