import TDA.Persistence.DiagramBottleneckLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.Bases

/-!
# Borel geometry of finite persistence diagrams

Finite diagrams carry the extended metric induced by their bottleneck distance.
Distances can be infinite when the essential-bar multiplicities differ. Every
diagram has an ordered finite-coordinate presentation, and those presentations
also show that the resulting metric topology is separable.
-/

noncomputable section

namespace TDA.Persistence

open scoped ENNReal
open TopologicalSpace

/-- The bottleneck distance is a genuine extended metric on finite diagrams.
Its value may be `∞` when the essential-bar counts differ. -/
instance instEMetricSpace : EMetricSpace (Diagram ℝ) where
  edist := bottleneck
  edist_self := bottleneck_self
  edist_comm := bottleneck_comm
  edist_triangle := bottleneck_triangle
  eq_of_edist_eq_zero := fun h => (bottleneck_eq_zero_iff _ _).mp h

theorem lipschitzWith_orderedQ (m n : ℕ) :
    LipschitzWith 1 (orderedQ (α := ℝ) m n) := by
  intro z w
  change bottleneck (orderedQ (α := ℝ) m n z)
      (orderedQ (α := ℝ) m n w) ≤ 1 * edist z w
  rw [edist_dist, dist_eq_norm]
  simpa using bottleneck_orderedQ_le_norm m n z w

theorem continuous_orderedQ (m n : ℕ) :
    Continuous (orderedQ (α := ℝ) m n) :=
  (lipschitzWith_orderedQ m n).continuous

instance instSeparableSpace : TopologicalSpace.SeparableSpace (Diagram ℝ) := by
  have hcover : (Set.univ : Set (Diagram ℝ)) =
      ⋃ p : ℕ × ℕ, Set.range (orderedQ (α := ℝ) p.1 p.2) := by
    ext D
    constructor
    · intro _
      obtain ⟨m, n, z, rfl⟩ := orderedQ_surjective D
      exact Set.mem_iUnion.mpr ⟨(m, n), ⟨z, rfl⟩⟩
    · intro _
      trivial
  rw [← isSeparable_univ_iff, hcover, isSeparable_iUnion]
  intro p
  exact isSeparable_range (continuous_orderedQ p.1 p.2)

instance instSecondCountableTopology : SecondCountableTopology (Diagram ℝ) :=
  UniformSpace.secondCountable_of_separable (Diagram ℝ)

instance instMeasurableSpace : MeasurableSpace (Diagram ℝ) := borel (Diagram ℝ)

instance instBorelSpace : BorelSpace (Diagram ℝ) := ⟨rfl⟩

theorem measurable_bottleneck :
    Measurable (fun p : Diagram ℝ × Diagram ℝ => bottleneck p.1 p.2) :=
  measurable_edist

end TDA.Persistence
