import TDA.Filtration.Rips
import TDA.Persistence.FiniteFilterStability

/-!
# Same-label metric stability of Rips diagrams

On a fixed finite labelled vertex set, changing the metric changes every simplex
diameter by at most the maximum distance-matrix discrepancy. The existing
finite-face stability theorem then bounds the diagrams, with their existing
occurrence multiplicity and essential-bar semantics, in every homological degree.
-/

universe u

namespace TDA.Persistence.Rips

open TDA.Filtration

variable {V : Type u} [LinearOrder V] [Fintype V]

omit [LinearOrder V] in
theorem faceSupDifference_filter_le (d e : MetricSpace V) :
    faceSupDifference (Rips.filter d) (Rips.filter e) ≤ Rips.pairwiseDiscrepancy d e := by
  classical
  apply (Finset.fold_max_le _).mpr
  exact ⟨Rips.pairwiseDiscrepancy_nonneg d e,
    fun s _ => Rips.abs_diameter_sub_le_pairwiseDiscrepancy d e s.val⟩

/-- Diagram stability with diameter time, retaining precisely the existing
ordered-vertex, finite-carrier and coefficient-field assumptions. -/
theorem bottleneck_dgm_le_pairwiseDiscrepancy (k : Type u) [Field k]
    (d e : MetricSpace V) (n : ℕ) :
    bottleneck (dgm k (Rips.filter d) n) (dgm k (Rips.filter e) n) ≤
      ENNReal.ofReal (Rips.pairwiseDiscrepancy d e) :=
  (bottleneck_dgm_le_faceSupDifference k (Rips.filter d) (Rips.filter e) n).trans
    (ENNReal.ofReal_le_ofReal (faceSupDifference_filter_le d e))

end TDA.Persistence.Rips
