import TDA.Persistence.RipsQTameInfiniteMetricStability
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.UnitInterval

/-!
# Client statements of the Rips Gromov--Hausdorff stability bound

Regression fixtures for #1206. Each statement is written as a downstream client writes it: the
file opens no scope and declares no instance, and imports only the public stability module and
mathlib measure theory. They replay the two inferences of the pilot: an error event for the
Rips diagram at threshold `ε` lies inside the metric error event at threshold `ε / 2`, and a
Gromov--Hausdorff tail estimate then transfers to the diagrams by measure monotonicity.

* Abstract compact spaces with independent metrics and no order, in the threshold form and with
  the distinguished diagram independent of the auxiliary vertex order.
* A sample metric that varies with the outcome on one fixed finite carrier, installed by
  `letI`, against a fixed compact target, with the tail transfer and its probability form.
* The same statement on `Fin m`, and with a target in any universe via `ULift`.
-/

universe u v w

namespace TDA.Persistence.RipsGHClientExamples

/-- The factor-two bound for abstract compact nonempty spaces, with independent metrics and no
`LinearOrder` instance. -/
theorem orderFree_bottleneck_le
    (X Y : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] (k : Type v) [Field k] (n : ℕ) :
    (Rips.qTameLocallyFiniteDiagramOrderFree X k isCompact_univ.totallyBounded n).bottleneck
      (Rips.qTameLocallyFiniteDiagramOrderFree Y k isCompact_univ.totallyBounded n) ≤
      ENNReal.ofReal (2 * GromovHausdorff.ghDist X Y) :=
  Rips.qTameLocallyFiniteDiagramOrderFree_bottleneck_le_two_mul_ghDist k n

/-- The threshold form, for every real `ε`. -/
theorem half_lt_ghDist_of_lt_bottleneck
    (X Y : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] (k : Type v) [Field k] (n : ℕ) {ε : ℝ}
    (h : ENNReal.ofReal ε <
      (Rips.qTameLocallyFiniteDiagramOrderFree X k isCompact_univ.totallyBounded n).bottleneck
        (Rips.qTameLocallyFiniteDiagramOrderFree Y k isCompact_univ.totallyBounded n)) :
    ε / 2 < GromovHausdorff.ghDist X Y :=
  Rips.half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagramOrderFree_bottleneck k n h

/-- The same threshold form for spaces that carry their own linear orders. -/
theorem half_lt_ghDist_of_lt_bottleneck_ordered
    (X Y : Type u) [LinearOrder X] [MetricSpace X] [CompactSpace X] [Nonempty X]
    [LinearOrder Y] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) {ε : ℝ}
    (h : ENNReal.ofReal ε <
      (Rips.qTameLocallyFiniteDiagram (X := X) k isCompact_univ.totallyBounded n).bottleneck
        (Rips.qTameLocallyFiniteDiagram (X := Y) k isCompact_univ.totallyBounded n)) :
    ε / 2 < GromovHausdorff.ghDist X Y :=
  Rips.half_lt_ghDist_of_ofReal_lt_qTameLocallyFiniteDiagram_bottleneck k n h

/-- A Gromov--Hausdorff distance at most `ε / 2` bounds the diagram bottleneck distance by `ε`. -/
theorem bottleneck_le_of_ghDist_le_half
    (X Y : Type u) [LinearOrder X] [MetricSpace X] [CompactSpace X] [Nonempty X]
    [LinearOrder Y] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) {ε : ℝ} (h : GromovHausdorff.ghDist X Y ≤ ε / 2) :
    (Rips.qTameLocallyFiniteDiagram (X := X) k isCompact_univ.totallyBounded n).bottleneck
        (Rips.qTameLocallyFiniteDiagram (X := Y) k isCompact_univ.totallyBounded n) ≤
      ENNReal.ofReal ε :=
  Rips.qTameLocallyFiniteDiagram_bottleneck_le_ofReal_of_ghDist_le_half k n h

/-- The diagram of the unit interval for its usual order and for the reversed order agree. -/
theorem unitInterval_diagram_reversed_order (k : Type v) [Field k] (n : ℕ) :
    @Rips.qTameLocallyFiniteDiagram unitInterval inferInstance _ k _
        isCompact_univ.totallyBounded n =
      @Rips.qTameLocallyFiniteDiagram unitInterval
        (LinearOrder.lift' (OrderDual.toDual : unitInterval → unitInterval ᵒᵈ)
          OrderDual.toDual.injective) _ k _ isCompact_univ.totallyBounded n :=
  Rips.qTameLocallyFiniteDiagram_congr_linearOrder _ _ k _ n

/-- The order-free diagram is the diagram of the supplied order. -/
theorem orderFree_eq_unitInterval_diagram (k : Type v) [Field k] (n : ℕ) :
    Rips.qTameLocallyFiniteDiagramOrderFree unitInterval k isCompact_univ.totallyBounded n =
      Rips.qTameLocallyFiniteDiagram (X := unitInterval) k isCompact_univ.totallyBounded n :=
  Rips.qTameLocallyFiniteDiagramOrderFree_eq _ k _ n

section SampleTail

variable {Ω : Type w} {S : Type u} [Finite S] [Nonempty S] (d : Ω → MetricSpace S)
  (Y : Type u) [MetricSpace Y] [CompactSpace Y] [Nonempty Y] (k : Type v) [Field k] (n : ℕ)

/-- The error event of the sample diagram at threshold `ε`, for the metric `d ω` at outcome `ω`. -/
def diagramErrorEvent (ε : ℝ) : Set Ω :=
  {ω | letI := d ω
    ENNReal.ofReal ε <
      (Rips.qTameLocallyFiniteDiagramOrderFree S k
        Set.finite_univ.totallyBounded n).bottleneck
        (Rips.qTameLocallyFiniteDiagramOrderFree Y k isCompact_univ.totallyBounded n)}

/-- The error event of the Gromov--Hausdorff distance at threshold `t`. -/
def ghErrorEvent (t : ℝ) : Set Ω :=
  {ω | letI := d ω
    t < GromovHausdorff.ghDist S Y}

/-- Event inclusion for every real `ε`, no sign condition. -/
theorem diagramErrorEvent_subset (ε : ℝ) :
    diagramErrorEvent d Y k n ε ⊆ ghErrorEvent d Y (ε / 2) :=
  Rips.setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist_of_finite d k n ε

/-- A Gromov--Hausdorff tail estimate transfers to the diagrams by measure monotonicity. -/
theorem diagram_tail_le_of_gh_tail_le [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {ε : ℝ} {δ : ENNReal} (htail : μ (ghErrorEvent d Y (ε / 2)) ≤ δ) :
    μ (diagramErrorEvent d Y k n ε) ≤ δ :=
  (MeasureTheory.measure_mono (diagramErrorEvent_subset d Y k n ε)).trans htail

/-- The probability of the good event is at least `1 - δ`. -/
theorem one_sub_le_measure_compl_diagramErrorEvent [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ] {ε : ℝ} {δ : ENNReal}
    (htail : μ (ghErrorEvent d Y (ε / 2)) ≤ δ) :
    1 - δ ≤ μ (diagramErrorEvent d Y k n ε)ᶜ := by
  have h1 : (1 : ENNReal) ≤ μ (diagramErrorEvent d Y k n ε) + μ (diagramErrorEvent d Y k n ε)ᶜ :=
    calc (1 : ENNReal) = μ Set.univ := MeasureTheory.measure_univ.symm
      _ = μ (diagramErrorEvent d Y k n ε ∪ (diagramErrorEvent d Y k n ε)ᶜ) := by
        rw [Set.union_compl_self]
      _ ≤ _ := MeasureTheory.measure_union_le _ _
  have h2 := diagram_tail_le_of_gh_tail_le d Y k n μ htail
  rw [tsub_le_iff_right]
  calc (1 : ENNReal) ≤ _ := h1
    _ ≤ δ + μ (diagramErrorEvent d Y k n ε)ᶜ := by gcongr
    _ = μ (diagramErrorEvent d Y k n ε)ᶜ + δ := add_comm _ _

end SampleTail

/-- The sample space `Fin m` with a metric depending on the outcome, against a target in `Type`. -/
theorem fin_diagram_tail_le_of_gh_tail_le
    {Ω : Type w} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {m : ℕ} [NeZero m]
    (d : Ω → MetricSpace (Fin m))
    (Y : Type) [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) {ε : ℝ} {δ : ENNReal}
    (htail : μ {ω | letI := d ω; ε / 2 < GromovHausdorff.ghDist (Fin m) Y} ≤ δ) :
    μ {ω | letI := d ω
      ENNReal.ofReal ε <
        (Rips.qTameLocallyFiniteDiagramOrderFree (Fin m) k
          Set.finite_univ.totallyBounded n).bottleneck
          (Rips.qTameLocallyFiniteDiagramOrderFree Y k isCompact_univ.totallyBounded n)} ≤ δ :=
  (MeasureTheory.measure_mono
    (Rips.setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist_of_finite d k n ε)).trans htail

/-- The same for a target in an arbitrary universe `u`, through the carrier `ULift (Fin m)`: the
stability theorems need both spaces in one universe. -/
theorem ulift_fin_diagram_tail_le_of_gh_tail_le
    {Ω : Type w} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {m : ℕ} [NeZero m]
    (d : Ω → MetricSpace (ULift.{u} (Fin m)))
    (Y : Type u) [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (k : Type v) [Field k] (n : ℕ) {ε : ℝ} {δ : ENNReal}
    (htail : μ {ω | letI := d ω; ε / 2 < GromovHausdorff.ghDist (ULift.{u} (Fin m)) Y} ≤ δ) :
    μ {ω | letI := d ω
      ENNReal.ofReal ε <
        (Rips.qTameLocallyFiniteDiagramOrderFree (ULift.{u} (Fin m)) k
          Set.finite_univ.totallyBounded n).bottleneck
          (Rips.qTameLocallyFiniteDiagramOrderFree Y k isCompact_univ.totallyBounded n)} ≤ δ :=
  (MeasureTheory.measure_mono
    (Rips.setOf_ofReal_lt_bottleneck_subset_setOf_half_lt_ghDist_of_finite d k n ε)).trans htail

end TDA.Persistence.RipsGHClientExamples
