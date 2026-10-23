import TDA.Persistence.FinitePBottleneckUniformLimit

/-!
# Uniform recovery with a common essential-birth multiset

Matching equal essential births costs zero, including repeated occurrences.
The finite-part optima therefore recover the full bottleneck on count/radius
classes with the same essential multiset on each pair. That multiset may vary
across pairs, with no bound on its size or birth values.

These are bounds for the existing unnormalized rooted finite-part costs at a
fixed maximum ground norm. No essential p-cost is defined. Divol–Lacombe's
corrected v4 §1.1 supplies the positive finite matching convention; its Remark
1.2 describes independent finite/essential contributions as a sum, whereas this
library's full bottleneck uses a maximum. The common essential contribution is
zero here. The uniform conclusion is a finite library derivation.
-/

noncomputable section

namespace TDA.Persistence

open Filter
open scoped Topology

/-- Extend the finite optimizer by matching identical essential values. -/
private def matchCommonEssential (D E : Diagram ℝ)
    (he : essentialPart D.points = essentialPart E.points)
    (m : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences PEmpty.{1} PEmpty.{1}) :
    OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences := by
  classical
  exact
    { finite := m.finite
      finite_injective := m.finite_injective
      essential := Multiset.cast he }

/-- The cast changes only occurrence indices; each essential birth stays fixed. -/
private theorem matchCommonEssential_cost (D E : Diagram ℝ)
    (he : essentialPart D.points = essentialPart E.points)
    (m : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences PEmpty.{1} PEmpty.{1}) :
    (matchCommonEssential D E he m).cost (fun q => q.1) (fun q => q.1)
        (fun q => q.1) (fun q => q.1) =
      m.cost (fun q => q.1) (fun q => q.1) PEmpty.elim PEmpty.elim := by
  classical
  simp [matchCommonEssential, OccurrenceMatching.cost, essentialPairCost]

private theorem commonEssential_bottleneck_lt_top (D E : Diagram ℝ)
    (he : essentialPart D.points = essentialPart E.points) : bottleneck D E < ⊤ :=
  (bottleneck_lt_top_iff D E).mpr (congrArg Multiset.card he)

/-- Reuse the empty-essential charge bound on the finite minimizing matching. -/
private theorem commonEssential_bottleneck_toReal_le_matching {p : ℝ} (hp : 1 ≤ p)
    (D E : Diagram ℝ) (he : essentialPart D.points = essentialPart E.points) :
    (bottleneck D E).toReal ≤ finitePMatchingCost p
      (fun q : D.finiteOccurrences => q.1) (fun q : E.finiteOccurrences => q.1) := by
  classical
  have hfinite := commonEssential_bottleneck_lt_top D E he
  obtain ⟨m, hm⟩ := exists_minimizing_pMatching p
    (fun q : D.finiteOccurrences => q.1) (fun q : E.finiteOccurrences => q.1)
  have hcost := m.cost_le_ofReal_root_totalFinitePowerCost hp
    (fun q => q.1) (fun q => q.1) PEmpty.elim PEmpty.elim
  have hroot : m.finiteRestriction.totalFinitePowerCost p
      (fun q => q.1) (fun q => q.1) ^ p⁻¹ =
      finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) := by
    have hrestriction : m.finiteRestriction = m := by
      apply OccurrenceMatching.ext (M := m.finiteRestriction) (N := m)
      · rfl
      · ext k
        exact PEmpty.elim k
    rw [hrestriction]
    exact hm
  rw [hroot] at hcost
  have hB := (bottleneck_le_matching D E (matchCommonEssential D E he m)).trans
    ((matchCommonEssential_cost D E he m).le.trans hcost)
  have hreal := (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mpr hB
  simpa only [ENNReal.toReal_ofReal (finitePMatchingCost_nonneg p _ _)] using hreal

/-- A count budget and bottleneck radius give one error bound for pairs with
the same essential-birth multiset. `max 1 m` includes the zero-count case. -/
theorem finitePMatchingCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ)
    (he : essentialPart D.points = essentialPart E.points)
    {m : ℕ}
    (hcard : Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences ≤ m)
    {R : ℝ} (hR : 0 ≤ R) (hB : bottleneck D E ≤ ENNReal.ofReal R) :
    |finitePMatchingCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) - (bottleneck D E).toReal| ≤
      ((((max 1 m : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  have hfinite := commonEssential_bottleneck_lt_top D E he
  have hb : (bottleneck D E).toReal ≤ R := by
    simpa only [ENNReal.toReal_ofReal hR] using
      (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mpr hB
  have hlower := commonEssential_bottleneck_toReal_le_matching hp D E he
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
theorem finitePBoundaryTransportCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    {p : ℝ} (hp : 1 ≤ p) (D E : Diagram ℝ)
    (he : essentialPart D.points = essentialPart E.points)
    {m : ℕ}
    (hcard : Fintype.card D.finiteOccurrences + Fintype.card E.finiteOccurrences ≤ m)
    {R : ℝ} (hR : 0 ≤ R) (hB : bottleneck D E ≤ ENNReal.ofReal R) :
    |finitePBoundaryTransportCost p (fun q : D.finiteOccurrences => q.1)
        (fun q : E.finiteOccurrences => q.1) - (bottleneck D E).toReal| ≤
      ((((max 1 m : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    hp D E he hcard hR hB

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

/-- One exponent tail works for all pairs with equal essential-birth multisets
within the count and radius budgets. Occurrence types may vary with the pair. -/
theorem finitePMatchingCost_tendstoUniformlyOn_bottleneck_of_essentialParts_eq
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ =>
        finitePMatchingCost p (fun q : z.1.finiteOccurrences => q.1)
          (fun q : z.2.finiteOccurrences => q.1))
      (fun z : Diagram ℝ × Diagram ℝ => (bottleneck z.1 z.2).toReal) atTop
      {z : Diagram ℝ × Diagram ℝ |
        essentialPart z.1.points = essentialPart z.2.points ∧
        Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤ m ∧
        bottleneck z.1 z.2 ≤ ENNReal.ofReal R} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(uniform_errorEnvelope_tendsto m R).eventually (gt_mem_nhds hε),
    eventually_ge_atTop (1 : ℝ)] with p herror hp
  intro z hz
  rw [Real.dist_eq, abs_sub_comm]
  exact (finitePMatchingCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq hp z.1 z.2
    hz.1 hz.2.1 hR hz.2.2).trans_lt herror

/-- Uniform recovery for the optimized real boundary-reservoir cost. -/
theorem finitePBoundaryTransportCost_tendstoUniformlyOn_bottleneck_of_essentialParts_eq
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : Diagram ℝ × Diagram ℝ =>
        finitePBoundaryTransportCost p (fun q : z.1.finiteOccurrences => q.1)
          (fun q : z.2.finiteOccurrences => q.1))
      (fun z : Diagram ℝ × Diagram ℝ => (bottleneck z.1 z.2).toReal) atTop
      {z : Diagram ℝ × Diagram ℝ |
        essentialPart z.1.points = essentialPart z.2.points ∧
        Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤ m ∧
        bottleneck z.1 z.2 ≤ ENNReal.ofReal R} := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    finitePMatchingCost_tendstoUniformlyOn_bottleneck_of_essentialParts_eq m R hR

end TDA.Persistence
