import TDA.Persistence.FinitePBottleneckUniformLimit
import TDA.Persistence.CechStability
import TDA.Persistence.EssentialVanishing

/-!
# Uniform bottleneck recovery for actual Čech sublevel diagrams

On a fixed finite label type, positive-degree Čech diagrams have no essential
bars and each finite occurrence count is bounded by the number of possible
death faces. Same-label displacement bounds their full bottleneck distance.
These facts turn the generic count/radius uniform estimate into an input-level
statement, with no supplied diagram-side budget or fixed pairing.

The diagrams here are those of the existing infimal-enclosing-radius filter.
In a proper ambient space its sublevels equal the closed-ball Čech nerves;
in an arbitrary pseudometric space only the established inclusion is used.
The finite uniform estimate is a library composition at fixed maximum ground
norm and unit occurrence masses. Degree zero remains outside this consumer.
-/

noncomputable section

universe u w

open scoped Topology

namespace TDA.Persistence.Cech

open TDA.Filtration Filter

variable {V : Type u} [LinearOrder V] [Fintype V]
variable {X : Type w} [PseudoMetricSpace X]

private theorem diagramPair_mem_uniformBudget (k : Type u) [Field k]
    (a b : V → X) {n : ℕ} (hn : 1 ≤ n) {R : ℝ}
    (hδ : Cech.displacement a b ≤ R) :
    (dgm k (Cech.filter a) n, dgm k (Cech.filter b) n) ∈
      {z : Diagram ℝ × Diagram ℝ |
        essentialPart z.1.points = 0 ∧ essentialPart z.2.points = 0 ∧
        Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤
          2 * Nat.choose (Fintype.card V) (n + 2) ∧
        bottleneck z.1 z.2 ≤ ENNReal.ofReal R} := by
  refine ⟨essentialPart_dgm_eq_zero k a hn, essentialPart_dgm_eq_zero k b hn, ?_, ?_⟩
  · change Fintype.card (dgm k (Cech.filter a) n).finiteOccurrences +
      Fintype.card (dgm k (Cech.filter b) n).finiteOccurrences ≤
        2 * Nat.choose (Fintype.card V) (n + 2)
    have ha := card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter a) n
    have hb := card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter b) n
    simpa only [two_mul] using Nat.add_le_add ha hb
  · exact (bottleneck_dgm_le_displacement k a b n).trans
      (ENNReal.ofReal_le_ofReal hδ)

/-- A displacement budget supplies the count/radius error bound for actual
positive-degree Čech sublevel diagrams and the rooted matching optimum. -/
theorem finitePMatchingCost_dgm_abs_sub_bottleneck_le_uniformBound
    {p : ℝ} (hp : 1 ≤ p) (k : Type u) [Field k] (a b : V → X)
    {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R)
    (hδ : Cech.displacement a b ≤ R) :
    |finitePMatchingCost p (fun q : (dgm k (Cech.filter a) n).finiteOccurrences => q.1)
        (fun q : (dgm k (Cech.filter b) n).finiteOccurrences => q.1) -
        (bottleneck (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n)).toReal| ≤
      ((((max 1 (2 * Nat.choose (Fintype.card V) (n + 2)) : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  have h := diagramPair_mem_uniformBudget k a b hn hδ
  exact finitePMatchingCost_abs_sub_bottleneck_le_uniformBound hp _ _
    h.1 h.2.1 h.2.2.1 hR h.2.2.2

/-- The actual optimized real reservoir cost satisfies the same input-level
bound, through its equality with the optimized matching cost. -/
theorem finitePBoundaryTransportCost_dgm_abs_sub_bottleneck_le_uniformBound
    {p : ℝ} (hp : 1 ≤ p) (k : Type u) [Field k] (a b : V → X)
    {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : 0 ≤ R)
    (hδ : Cech.displacement a b ≤ R) :
    |finitePBoundaryTransportCost p
        (fun q : (dgm k (Cech.filter a) n).finiteOccurrences => q.1)
        (fun q : (dgm k (Cech.filter b) n).finiteOccurrences => q.1) -
        (bottleneck (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n)).toReal| ≤
      ((((max 1 (2 * Nat.choose (Fintype.card V) (n + 2)) : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_dgm_abs_sub_bottleneck_le_uniformBound hp k a b hn hR hδ

/-- One real exponent tail works for all cloud pairs in the literal same-label
displacement class. The cloud-to-diagram map needs no topology or continuity. -/
theorem finitePMatchingCost_dgm_tendstoUniformlyOn_bottleneck
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : (V → X) × (V → X) =>
        finitePMatchingCost p (fun q : (dgm k (Cech.filter z.1) n).finiteOccurrences => q.1)
          (fun q : (dgm k (Cech.filter z.2) n).finiteOccurrences => q.1))
      (fun z : (V → X) × (V → X) =>
        (bottleneck (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n)).toReal)
      atTop {z : (V → X) × (V → X) | Cech.displacement z.1 z.2 ≤ R} := by
  have h := (finitePMatchingCost_tendstoUniformlyOn_bottleneck
    (2 * Nat.choose (Fintype.card V) (n + 2)) R hR).comp
      (fun z : (V → X) × (V → X) => (dgm k (Cech.filter z.1) n, dgm k (Cech.filter z.2) n))
  exact h.mono fun z hz => diagramPair_mem_uniformBudget k z.1 z.2 hn hz

/-- Uniform recovery of full bottleneck by the actual rooted all-real-plan
optimum on the same displacement class of positive-degree sublevel diagrams. -/
theorem finitePBoundaryTransportCost_dgm_tendstoUniformlyOn_bottleneck
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : (V → X) × (V → X) =>
        finitePBoundaryTransportCost p
          (fun q : (dgm k (Cech.filter z.1) n).finiteOccurrences => q.1)
          (fun q : (dgm k (Cech.filter z.2) n).finiteOccurrences => q.1))
      (fun z : (V → X) × (V → X) =>
        (bottleneck (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n)).toReal)
      atTop {z : (V → X) × (V → X) | Cech.displacement z.1 z.2 ≤ R} := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    finitePMatchingCost_dgm_tendstoUniformlyOn_bottleneck (V := V) (X := X) k n hn R hR

end TDA.Persistence.Cech
