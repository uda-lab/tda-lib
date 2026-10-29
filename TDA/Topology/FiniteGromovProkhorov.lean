import TDA.Topology.FiniteUniformTransport
import Mathlib.Topology.MetricSpace.Gluing

/-!
# Common-ambient Gromov–Prokhorov comparison for finite uniform spaces

The extended distance is the infimum of ambient Lévy–Prokhorov distances over
actual metric spaces and pairs of isometric embeddings. Ambient carriers lie in
the maximum of the input universes. This construction exports witnesses and the
outlier-mass upper bound; it does not assert a metric on a quotient of spaces.
-/

set_option autoImplicit false
open scoped NNReal ENNReal
universe u v w

namespace TDA.Topology.FiniteGromovProkhorov
open MeasureTheory Metric CategoryTheory
open TDA.Topology.MeasureBifiltration

variable (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]

/-- Two metric inputs embedded isometrically in one actual metric ambient.
The two images may overlap. -/
structure CommonAmbient where
  /-- Carrier of the common ambient metric space. -/
  carrier : Type (max u v)
  /-- Its metric; no separation between the two images is imposed. -/
  metric : MetricSpace carrier
  /-- Embedding of the first input. -/
  left : X → carrier
  /-- Embedding of the second input. -/
  right : Y → carrier
  /-- The first embedding preserves the original distances. -/
  left_dist : ∀ x x', metric.dist (left x) (left x') = dist x x'
  /-- The second embedding preserves the original distances. -/
  right_dist : ∀ y y', metric.dist (right y) (right y') = dist y y'

variable {X Y}

/-- The ambient comparison really uses isometric embeddings of the first input. -/
theorem CommonAmbient.isometry_left (a : CommonAmbient X Y) :
    letI := a.metric
    Isometry a.left := by
  let : MetricSpace a.carrier := a.metric
  exact Isometry.of_dist_eq a.left_dist

/-- The second map is likewise an isometric embedding. -/
theorem CommonAmbient.isometry_right (a : CommonAmbient X Y) :
    letI := a.metric
    Isometry a.right := by
  let : MetricSpace a.carrier := a.metric
  exact Isometry.of_dist_eq a.right_dist

/-- Interchange the two embeddings without changing the common ambient. -/
def CommonAmbient.symm (a : CommonAmbient X Y) : CommonAmbient Y X where
  carrier := a.carrier
  metric := a.metric
  left := a.right
  right := a.left
  left_dist := a.right_dist
  right_dist := a.left_dist

/-- A common ambient always exists: use the standard disjoint-union metric. -/
noncomputable def disjointAmbient : CommonAmbient X Y where
  carrier := X ⊕ Y
  metric := metricSpaceSum
  left := Sum.inl
  right := Sum.inr
  left_dist _ _ := rfl
  right_dist _ _ := rfl

variable {Z : Type w} [MetricSpace Z] {I : Type*} [Fintype I]

/-- Distances to finitely many landmarks, with the finite sup norm. -/
def landmarkCoordinates (p : I → Z) (z : Z) : I → ℝ := fun i => dist (p i) z

/-- Finite distance coordinates preserve a distance whenever one endpoint is
a landmark. No finiteness of the original ambient space is required. -/
theorem landmarkCoordinates_dist (p : I → Z) (i : I) (z : Z) :
    dist (landmarkCoordinates p (p i)) (landmarkCoordinates p z) = dist (p i) z := by
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).2
    intro j
    simpa only [landmarkCoordinates, Real.dist_eq, dist_comm (p j)] using abs_dist_sub_le (p i) z (p j)
  · have h := dist_le_pi_dist (landmarkCoordinates p (p i)) (landmarkCoordinates p z) i
    simpa [landmarkCoordinates, Real.dist_eq] using h

/-- A common ambient of arbitrary size reduces to a finite sup-norm ambient
using the two finite images as landmarks. -/
def coordinatesAmbient [Fintype X] [Fintype Y] (p : X → Z) (q : Y → Z) (hp : Isometry p) (hq : Isometry q) :
    CommonAmbient X Y where
  carrier := (X ⊕ Y) → ℝ
  metric := inferInstance
  left x := landmarkCoordinates (Sum.elim p q) (p x)
  right y := landmarkCoordinates (Sum.elim p q) (q y)
  left_dist x x' := (landmarkCoordinates_dist (Sum.elim p q) (Sum.inl x) (p x')).trans
    (hp.dist_eq x x')
  right_dist y y' := (landmarkCoordinates_dist (Sum.elim p q) (Sum.inr y) (q y')).trans
    (hq.dist_eq y y')

variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]

/-- The ambient Prokhorov cost of the two finite uniform pushforward measures.
The measurable structure is the Borel structure of the actual ambient metric. -/
noncomputable def CommonAmbient.cost (a : CommonAmbient X Y) : ℝ≥0∞ :=
  letI := a.metric
  letI : MeasurableSpace a.carrier := borel a.carrier
  levyProkhorovEDist (uniformMeasure a.left) (uniformMeasure a.right)

/-- Common-ambient Gromov–Prokhorov extended distance for finite uniform inputs. -/
noncomputable def gromovProkhorovEDist (X : Type u) (Y : Type v)
    [MetricSpace X] [MetricSpace Y] [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] : ℝ≥0∞ :=
  ⨅ a : CommonAmbient X Y, a.cost

/-- Every actual common-ambient realization bounds the GP infimum. -/
theorem gromovProkhorovEDist_le_cost (a : CommonAmbient X Y) :
    gromovProkhorovEDist X Y ≤ a.cost := iInf_le _ a

/-- A parameter strictly above GP admits an actual common-ambient Prokhorov
witness below that same parameter. -/
theorem gromovProkhorovEDist_lt_iff {δ : ℝ≥0∞} :
    gromovProkhorovEDist X Y < δ ↔ ∃ a : CommonAmbient X Y, a.cost < δ :=
  iInf_lt_iff

/-- The common ambient cost is symmetric. -/
theorem CommonAmbient.cost_symm (a : CommonAmbient X Y) : a.symm.cost = a.cost := by
  let : MetricSpace a.carrier := a.metric
  let : MeasurableSpace a.carrier := borel _
  change levyProkhorovEDist (uniformMeasure a.right) (uniformMeasure a.left) =
    levyProkhorovEDist (uniformMeasure a.left) (uniformMeasure a.right)
  exact levyProkhorovEDist_comm _ _

/-- Interchanging the finite inputs does not change their GP infimum. -/
theorem gromovProkhorovEDist_comm :
    gromovProkhorovEDist X Y = gromovProkhorovEDist Y X := by
  apply le_antisymm
  · apply le_iInf
    intro a
    exact (gromovProkhorovEDist_le_cost a.symm).trans_eq a.cost_symm
  · apply le_iInf
    intro a
    exact (gromovProkhorovEDist_le_cost a.symm).trans_eq a.cost_symm

/-- Finite distance coordinates preserve the exact ambient Prokhorov cost.
This applies to an original ambient in any universe. -/
theorem coordinatesAmbient_cost [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (p : X → Z) (q : Y → Z) (hp : Isometry p) (hq : Isometry q) :
    (coordinatesAmbient p q hp hq).cost =
      levyProkhorovEDist (uniformMeasure p) (uniformMeasure q) := by
  let : MeasurableSpace ((X ⊕ Y) → ℝ) := borel _
  let : BorelSpace ((X ⊕ Y) → ℝ) := ⟨rfl⟩
  exact levyProkhorovEDist_uniform_eq_of_cross_dist_eq
    (landmarkCoordinates (Sum.elim p q) ∘ p) (landmarkCoordinates (Sum.elim p q) ∘ q) p q
    (fun x y => landmarkCoordinates_dist (Sum.elim p q) (Sum.inl x) (q y))

/-- Every common ambient, without a universe or finiteness restriction on its
carrier, gives an upper bound on the finite-input GP infimum. -/
theorem gromovProkhorovEDist_le_ambient [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (p : X → Z) (q : Y → Z) (hp : Isometry p) (hq : Isometry q) :
    gromovProkhorovEDist X Y ≤ levyProkhorovEDist (uniformMeasure p) (uniformMeasure q) :=
  (gromovProkhorovEDist_le_cost (coordinatesAmbient p q hp hq)).trans_eq
    (coordinatesAmbient_cost p q hp hq)

/-- Probability normalization bounds every common-ambient cost by one. -/
theorem CommonAmbient.cost_le_one (a : CommonAmbient X Y) : a.cost ≤ 1 := by
  let : MetricSpace a.carrier := a.metric
  let : MeasurableSpace a.carrier := borel _
  change levyProkhorovEDist (uniformMeasure a.left) (uniformMeasure a.right) ≤ 1
  simpa only [measure_univ, max_self] using
    levyProkhorovEDist_le_max_measure_univ (uniformMeasure a.left) (uniformMeasure a.right)

/-- Finite uniform GP is bounded by one; the ambient infimum is nonvacuous. -/
theorem gromovProkhorovEDist_le_one : gromovProkhorovEDist X Y ≤ 1 :=
  (gromovProkhorovEDist_le_cost (disjointAmbient (X := X) (Y := Y))).trans
    (CommonAmbient.cost_le_one _)

/-- An isometric inclusion is realized in the enlarged input itself, lifted
only to place the ambient carrier in the prescribed universe. -/
def inclusionAmbient (i : X ↪ Y) (hi : Isometry i) : CommonAmbient X Y where
  carrier := ULift.{u} Y
  metric := inferInstance
  left x := ⟨i x⟩
  right y := ⟨y⟩
  left_dist x x' := hi.dist_eq x x'
  right_dist _ _ := rfl

/-- Adding any number of points at arbitrary distances costs at most their
fraction of the enlarged finite uniform sample in common-ambient GP distance. -/
theorem gromovProkhorovEDist_embedding_le (i : X ↪ Y) (hi : Isometry i) :
    gromovProkhorovEDist X Y ≤
      ENNReal.ofReal (((Fintype.card Y : ℝ) - Fintype.card X) / Fintype.card Y) := by
  let : MeasurableSpace (ULift.{u} Y) := borel _
  let : BorelSpace (ULift.{u} Y) := ⟨rfl⟩
  apply (gromovProkhorovEDist_le_cost (inclusionAmbient i hi)).trans
  exact levyProkhorovEDist_uniform_embedding_le i (fun y : Y => (⟨y⟩ : ULift.{u} Y))

/-- A space has zero GP distance from itself. -/
@[simp] theorem gromovProkhorovEDist_self : gromovProkhorovEDist X X = 0 := by
  apply le_antisymm _ bot_le
  simpa using gromovProkhorovEDist_embedding_le (Function.Embedding.refl X) isometry_id

end TDA.Topology.FiniteGromovProkhorov
