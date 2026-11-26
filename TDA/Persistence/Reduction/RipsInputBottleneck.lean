import TDA.Persistence.Reduction.RipsInputDiagram
import TDA.Persistence.IntegerBottleneckCorrectness

/-!
# Exact bottleneck distance between executed Rips diagrams

For two distance tables, `ripsRunInDegree` returns the records of one degree of each
reduction, and `IntegerBottleneck.twiceDistance` searches the two lists of integer points.
The value read from that search is the bottleneck distance between the F₂ Rips diagrams of
the two table metrics. The two tables may have different numbers of labels.

These are elementary library results, not attributed to a source.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.DistanceTable

open TDA.Filtration TDA.Persistence
open scoped ENNReal

variable {N M : ℕ} (D : DistanceTable N) (E : DistanceTable M)

/-- The integer presentation of a list of occurrence records. -/
def recordPresentation (out : List FiniteInput.Occurrence) : IntegerBottleneck.Presentation :=
  IntegerBottleneck.Presentation.ofPoints (out.map FiniteInput.Occurrence.point)

/-- A finite doubled value `q` returned by the integer search on the records of degree `p`
of two tables gives bottleneck distance `q / 2` between their Rips diagrams. -/
theorem bottleneck_rips_dgm_eq_of_twiceDistance {p : ℕ}
    {out₁ out₂ : List FiniteInput.Occurrence}
    (h₁ : D.ripsRunInDegree p = some out₁) (h₂ : E.ripsRunInDegree p = some out₂) (q : ℕ)
    (h : IntegerBottleneck.twiceDistance (recordPresentation out₁) (recordPresentation out₂) =
      (q : WithTop ℕ)) :
    ∃ (hD : D.Valid) (hE : E.Valid),
      bottleneck (dgm (ZMod 2) (Rips.filter (D.metric hD)) p)
        (dgm (ZMod 2) (Rips.filter (E.metric hE)) p) = (q : ℝ≥0∞) / 2 := by
  obtain ⟨hD, e₁⟩ := D.ripsRunInDegree_correct h₁
  obtain ⟨hE, e₂⟩ := E.ripsRunInDegree_correct h₂
  rw [Multiset.map_coe] at e₁ e₂
  exact ⟨hD, hE, IntegerBottleneck.bottleneck_eq_of_points_of_twiceDistance _ _ _ _ e₁ e₂ q h⟩

/-- An infinite value returned by the integer search gives infinite bottleneck distance
between the two Rips diagrams. -/
theorem bottleneck_rips_dgm_eq_top_of_twiceDistance {p : ℕ}
    {out₁ out₂ : List FiniteInput.Occurrence}
    (h₁ : D.ripsRunInDegree p = some out₁) (h₂ : E.ripsRunInDegree p = some out₂)
    (h : IntegerBottleneck.twiceDistance (recordPresentation out₁) (recordPresentation out₂) =
      ⊤) :
    ∃ (hD : D.Valid) (hE : E.Valid),
      bottleneck (dgm (ZMod 2) (Rips.filter (D.metric hD)) p)
        (dgm (ZMod 2) (Rips.filter (E.metric hE)) p) = ⊤ := by
  obtain ⟨hD, e₁⟩ := D.ripsRunInDegree_correct h₁
  obtain ⟨hE, e₂⟩ := E.ripsRunInDegree_correct h₂
  rw [Multiset.map_coe] at e₁ e₂
  exact ⟨hD, hE, IntegerBottleneck.bottleneck_eq_top_of_points_of_twiceDistance _ _ _ _ e₁ e₂ h⟩

end TDA.Persistence.Reduction.DistanceTable
