import TDA.Filtration.CechDisplacement
import TDA.Persistence.FiniteFilterStability
import TDA.Persistence.RipsStability

/-!
# Same-label displacement stability of actual Čech diagrams

On a fixed finite ordered label type, moving every labelled point in a common pseudometric
ambient space by at most the displacement `δ` changes every Čech value by at most `δ`. The
existing finite-face stability theorem then bounds the actual Čech diagrams, with their
occurrence multiplicity and essential bars, by `δ` in every homological degree. Under
distance-compatible label metrics the actual Rips diagrams are bounded by `2 * δ`.
-/

universe w u

namespace TDA.Persistence.Cech

open TDA.Filtration

variable {X : Type w} [PseudoMetricSpace X] {V : Type u} [LinearOrder V] [Fintype V]

omit [LinearOrder V] in
theorem faceSupDifference_filter_le (p q : V → X) :
    faceSupDifference (Cech.filter p) (Cech.filter q) ≤ Cech.displacement p q := by
  classical
  apply (Finset.fold_max_le _).mpr
  exact ⟨Cech.displacement_nonneg p q,
    fun s _ => Cech.abs_filter_value_sub_le_displacement p q s⟩

/-- Actual Čech diagram stability in the same-label displacement, retaining precisely the
existing ordered-vertex, finite-carrier and coefficient-field assumptions. -/
theorem bottleneck_dgm_le_displacement (k : Type u) [Field k] (p q : V → X) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤
      ENNReal.ofReal (Cech.displacement p q) :=
  (bottleneck_dgm_le_faceSupDifference k (Cech.filter p) (Cech.filter q) n).trans
    (ENNReal.ofReal_le_ofReal (faceSupDifference_filter_le p q))

/-- Moving every labelled point by at most `ε ≥ 0` moves the actual Čech diagrams by at most
`ε`. -/
theorem bottleneck_dgm_le_of_dist_le (k : Type u) [Field k] (p q : V → X) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ v, dist (p v) (q v) ≤ ε) (n : ℕ) :
    bottleneck (dgm k (Cech.filter p) n) (dgm k (Cech.filter q) n) ≤ ENNReal.ofReal ε :=
  (bottleneck_dgm_le_displacement k p q n).trans
    (ENNReal.ofReal_le_ofReal ((Cech.displacement_le_iff p q ε).2 ⟨hε, h⟩))

/-- Under distance-compatible label metrics, the actual Rips diagrams move by at most twice
the same-label displacement. -/
theorem bottleneck_rips_dgm_le_two_mul_displacement (k : Type u) [Field k]
    (d e : MetricSpace V) (p q : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (he : ∀ v w, e.dist v w = dist (q v) (q w))
    (n : ℕ) :
    bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n) ≤
      ENNReal.ofReal (2 * Cech.displacement p q) :=
  (Rips.bottleneck_dgm_le_pairwiseDiscrepancy k d e n).trans
    (ENNReal.ofReal_le_ofReal (Cech.pairwiseDiscrepancy_le_two_mul_displacement d e p q hd he))

end TDA.Persistence.Cech
