import TDA.Persistence.CechEssentialBirth
import TDA.Persistence.CechStability
import TDA.Persistence.FinitePCommonEssentialBottleneck

/-!
# Input-uniform bottleneck recovery in every Čech degree

On a fixed finite label type, the essential multisets of any two actual Čech
diagrams agree: in degree zero they are both `{0}` for nonempty labels, and in
positive degree they vanish. Empty labels require no ambient point. Finite
occurrence counts and same-label displacement supply the remaining budgets
for the existing common-essential error and uniform-convergence theorems.

These finite library consumers use the actual infimal-radius filter and the
existing optimized finite costs. The real H₀ conclusion uses its empty negative
tail; the nonnegative proper-ambient closed-nerve comparison does not identify
the whole real-indexed module with CDSO's vertex-retaining convention.
-/

noncomputable section

universe u w

namespace TDA.Persistence.Cech

open TDA.Simplicial TDA.Filtration Filter
open scoped Topology

variable {V : Type u} [LinearOrder V] [Fintype V]
variable {X : Type w} [PseudoMetricSpace X]

private theorem essentialPart_dgm_empty (k : Type u) [Field k]
    (a : V → X) [IsEmpty V] (n : ℕ) :
    essentialPart (dgm k (Cech.filter a) n).points = 0 := by
  classical
  apply Multiset.eq_zero_of_forall_notMem
  intro b hb
  obtain ⟨s, _⟩ := (FilterFunction.mem_criticalValues (Cech.filter a) b).mp
    (mem_criticalValues_of_mem_essentialPart_dgm k (Cech.filter a) hb)
  obtain ⟨v, _⟩ := (Rips.mem_fullComplex_iff s.val).mp s.property
  exact isEmptyElim v

private theorem essentialParts_dgm_eq (k : Type u) [Field k]
    (a b : V → X) (n : ℕ) :
    essentialPart (dgm k (Cech.filter a) n).points =
      essentialPart (dgm k (Cech.filter b) n).points := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    cases n with
    | zero => rw [essentialPart_dgm_zero_eq_singleton k a,
        essentialPart_dgm_zero_eq_singleton k b]
    | succ n => rw [essentialPart_dgm_eq_zero k a (Nat.succ_le_succ (Nat.zero_le n)),
        essentialPart_dgm_eq_zero k b (Nat.succ_le_succ (Nat.zero_le n))]
  · letI : IsEmpty V := ⟨fun v => hV ⟨v⟩⟩
    rw [essentialPart_dgm_empty k a n, essentialPart_dgm_empty k b n]

private theorem diagramPair_mem_commonEssentialBudget (k : Type u) [Field k]
    (a b : V → X) (n : ℕ) {R : ℝ} (hδ : Cech.displacement a b ≤ R) :
    (dgm k (Cech.filter a) n, dgm k (Cech.filter b) n) ∈
      {z : Diagram ℝ × Diagram ℝ |
        essentialPart z.1.points = essentialPart z.2.points ∧
        Fintype.card z.1.finiteOccurrences + Fintype.card z.2.finiteOccurrences ≤
          2 * Nat.choose (Fintype.card V) (n + 2) ∧
        bottleneck z.1 z.2 ≤ ENNReal.ofReal R} := by
  refine ⟨essentialParts_dgm_eq k a b n, ?_, ?_⟩
  · have ha := card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter a) n
    have hb := card_finiteOccurrences_dgm_fullComplex_le k (Cech.filter b) n
    simpa only [two_mul] using Nat.add_le_add ha hb
  · exact (bottleneck_dgm_le_displacement k a b n).trans
      (ENNReal.ofReal_le_ofReal hδ)

/-- Displacement alone supplies the finite-count/radius error estimate for the
actual rooted matching optimum in every natural degree, including H₀. -/
theorem finitePMatchingCost_dgm_abs_sub_bottleneck_le_uniformBound_allDegrees
    {p : ℝ} (hp : 1 ≤ p) (k : Type u) [Field k] (a b : V → X)
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) (hδ : Cech.displacement a b ≤ R) :
    |finitePMatchingCost p (fun q : (dgm k (Cech.filter a) n).finiteOccurrences => q.1)
        (fun q : (dgm k (Cech.filter b) n).finiteOccurrences => q.1) -
        (bottleneck (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n)).toReal| ≤
      ((((max 1 (2 * Nat.choose (Fintype.card V) (n + 2)) : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  have h := diagramPair_mem_commonEssentialBudget k a b n hδ
  exact finitePMatchingCost_abs_sub_bottleneck_le_uniformBound_of_essentialParts_eq
    hp _ _ h.1 h.2.1 hR h.2.2

/-- The optimized cost over all real reservoir plans satisfies the same
all-degree estimate through its proved equality with the matching optimum. -/
theorem finitePBoundaryTransportCost_dgm_abs_sub_bottleneck_le_uniformBound_allDegrees
    {p : ℝ} (hp : 1 ≤ p) (k : Type u) [Field k] (a b : V → X)
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) (hδ : Cech.displacement a b ≤ R) :
    |finitePBoundaryTransportCost p
        (fun q : (dgm k (Cech.filter a) n).finiteOccurrences => q.1)
        (fun q : (dgm k (Cech.filter b) n).finiteOccurrences => q.1) -
        (bottleneck (dgm k (Cech.filter a) n) (dgm k (Cech.filter b) n)).toReal| ≤
      ((((max 1 (2 * Nat.choose (Fintype.card V) (n + 2)) : ℕ) : ℝ) ^ p⁻¹) - 1) * R := by
  rw [finitePBoundaryTransportCost_eq_matchingCost]
  exact finitePMatchingCost_dgm_abs_sub_bottleneck_le_uniformBound_allDegrees
    hp k a b n hR hδ

/-- One real exponent tail works for every cloud pair in the literal
displacement class, in every natural degree. No cloud topology is required. -/
theorem finitePMatchingCost_dgm_tendstoUniformlyOn_bottleneck_allDegrees
    (k : Type u) [Field k] (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : (V → X) × (V → X) =>
        finitePMatchingCost p (fun q : (dgm k (Cech.filter z.1) n).finiteOccurrences => q.1)
          (fun q : (dgm k (Cech.filter z.2) n).finiteOccurrences => q.1))
      (fun z : (V → X) × (V → X) =>
        (bottleneck (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n)).toReal)
      atTop {z : (V → X) × (V → X) | Cech.displacement z.1 z.2 ≤ R} := by
  have h := (finitePMatchingCost_tendstoUniformlyOn_bottleneck_of_essentialParts_eq
    (2 * Nat.choose (Fintype.card V) (n + 2)) R hR).comp
      (fun z : (V → X) × (V → X) => (dgm k (Cech.filter z.1) n, dgm k (Cech.filter z.2) n))
  exact h.mono fun z hz => diagramPair_mem_commonEssentialBudget k z.1 z.2 n hz

/-- Uniform recovery by the actual all-real-plan optimum on the same literal
input class, including zero radius, empty labels and repeated labels. -/
theorem finitePBoundaryTransportCost_dgm_tendstoUniformlyOn_bottleneck_allDegrees
    (k : Type u) [Field k] (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun p : ℝ => fun z : (V → X) × (V → X) =>
        finitePBoundaryTransportCost p
          (fun q : (dgm k (Cech.filter z.1) n).finiteOccurrences => q.1)
          (fun q : (dgm k (Cech.filter z.2) n).finiteOccurrences => q.1))
      (fun z : (V → X) × (V → X) =>
        (bottleneck (dgm k (Cech.filter z.1) n) (dgm k (Cech.filter z.2) n)).toReal)
      atTop {z : (V → X) × (V → X) | Cech.displacement z.1 z.2 ≤ R} := by
  simpa only [finitePBoundaryTransportCost_eq_matchingCost] using
    finitePMatchingCost_dgm_tendstoUniformlyOn_bottleneck_allDegrees
      (V := V) (X := X) k n R hR

end TDA.Persistence.Cech
