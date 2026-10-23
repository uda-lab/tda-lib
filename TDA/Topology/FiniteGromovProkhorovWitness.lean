import TDA.Topology.FiniteGromovProkhorov

/-!
# GP witnesses and concrete multicover comparisons

Every parameter strictly above the common-ambient finite-uniform GP distance
has a witness in the fixed finite sup-norm product. The witness constructs an
actual restricted-index multicover interleaving in that ambient.
-/

set_option autoImplicit false
open scoped NNReal ENNReal
universe u v w
namespace TDA.Topology.FiniteGromovProkhorov
open MeasureTheory CategoryTheory TDA.Topology.MeasureBifiltration
variable (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]

/-- An actual finite sup-norm ambient witness at a prescribed Prokhorov scale. -/
structure SupNormWitness (δ : ℝ≥0) where
  /-- The first isometric coordinate map. -/
  left : X → (X ⊕ Y) → ℝ
  /-- The second isometric coordinate map. -/
  right : Y → (X ⊕ Y) → ℝ
  /-- Distances within the first sample are preserved. -/
  left_isometry : Isometry left
  /-- Distances within the second sample are preserved. -/
  right_isometry : Isometry right
  /-- The finite uniform ambient cost is below the requested scale. -/
  cost_lt : letI : MeasurableSpace ((X ⊕ Y) → ℝ) := borel _
    levyProkhorovEDist (uniformMeasure left) (uniformMeasure right) < (δ : ℝ≥0∞)

variable {X Y}

/-- Every parameter above common-ambient GP has a concrete witness in the
fixed finite sup-norm ambient, suitable for the open Čech comparison. -/
noncomputable def supNormWitness (δ : ℝ≥0)
    (hδ : gromovProkhorovEDist X Y < (δ : ℝ≥0∞)) : SupNormWitness X Y δ := by
  classical
  let a : CommonAmbient X Y := (gromovProkhorovEDist_lt_iff.mp hδ).choose
  have ha : a.cost < (δ : ℝ≥0∞) := (gromovProkhorovEDist_lt_iff.mp hδ).choose_spec
  let : MetricSpace a.carrier := a.metric
  let : MeasurableSpace a.carrier := borel _
  let : BorelSpace a.carrier := ⟨rfl⟩
  let c := coordinatesAmbient a.left a.right a.isometry_left a.isometry_right
  refine ⟨c.left, c.right, c.isometry_left, c.isometry_right, ?_⟩
  exact (coordinatesAmbient_cost a.left a.right a.isometry_left a.isometry_right).trans_lt ha

/-- The concrete GP witness produces an actual multicover interleaving of
spaces, including all mixed composition laws. -/
noncomputable def SupNormWitness.interleaving {δ : ℝ≥0} (s : SupNormWitness X Y δ) :
    InterleavingIndex δ ⥤ TopCat.{max u v} :=
  letI : MeasurableSpace ((X ⊕ Y) → ℝ) := borel _
  letI : BorelSpace ((X ⊕ Y) → ℝ) := ⟨rfl⟩
  topologicalInterleaving (uniformMeasure s.left) (uniformMeasure s.right) δ s.cost_lt

/-- The first restriction is precisely the multicover of the first uniform sample. -/
theorem SupNormWitness.interleaving_left {δ : ℝ≥0} (s : SupNormWitness X Y δ) :
    letI : MeasurableSpace ((X ⊕ Y) → ℝ) := borel _
    letI : BorelSpace ((X ⊕ Y) → ℝ) := ⟨rfl⟩
    (copy δ false).toFunctor ⋙ s.interleaving = topologicalDiagram (uniformMeasure s.left) := rfl

/-- The second restriction is precisely the multicover of the second uniform sample. -/
theorem SupNormWitness.interleaving_right {δ : ℝ≥0} (s : SupNormWitness X Y δ) :
    letI : MeasurableSpace ((X ⊕ Y) → ℝ) := borel _
    letI : BorelSpace ((X ⊕ Y) → ℝ) := ⟨rfl⟩
    (copy δ true).toFunctor ⋙ s.interleaving = topologicalDiagram (uniformMeasure s.right) := rfl

end TDA.Topology.FiniteGromovProkhorov
