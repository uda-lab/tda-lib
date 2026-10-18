import TDA.Persistence.CechRipsLogScaleConsumers
import TDA.Persistence.LogScaleDiagramExamples
import TDA.Persistence.LogScaleDiagramComparisonExamples
import TDA.Persistence.ArctanPersistenceImageExamples
import TDA.Filtration.CechExamples

set_option autoImplicit false

/-!
# Log-scale Rips-versus-Čech consumer fixtures

The fixtures cover the empty two-point boundary, the Euclidean triangle arctan bound, a
nonvacuous multiplicative sandwich on the certified filled triangle, the zero arctan weight,
the degree-zero constructibility obstruction, and repeated labels without a compatible metric.
-/

namespace TDA.Persistence.CechRipsLogScaleConsumersExamples

open TDA.Filtration Real
open TDA.Persistence.LogScaleDiagramExamples
open TDA.Persistence.LogScaleDiagramComparisonExamples
open TDA.Persistence.SublevelConstructibleExamples
open TDA.Persistence.FiniteConstructible
open TDA.Filtration.Cech.Examples
open MeasureTheory Set PersistenceImage
open scoped ENNReal

/-! ## (F1) Two-point boundary control -/

/-- In every positive degree, the two-point log-scale Rips and Čech diagrams coincide. -/
theorem twoPoints_logScale_diagrams_eq {n : ℕ} (hn : 1 ≤ n) :
    logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n =
      logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n := by
  apply Diagram.ext
  rw [twoPoints_rips_logDgm_pos hn, twoPoints_cech_logDgm_pos hn]

/-- For two points, the positive-degree log-scale embedding, kernel value, and image differences
vanish for every weight and every fixed diagram or pixel family. -/
theorem twoPoints_logScale_consumers_zero {n : ℕ} (hn : 1 ≤ n) (σ τ : ℝ)
    {A B : ℝ} (w : PersistenceImage.Weight A B) (D : Diagram ℝ)
    {Kp : Type*} [Fintype Kp] (P : Kp → Set (ℝ × ℝ)) :
    WeightedKernel.diagramEmbedding σ w
          (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n) -
        WeightedKernel.diagramEmbedding σ w
          (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n) = 0 ∧
      WeightedKernel.gaussianDiagramKernel σ τ w D
          (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D
          (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n) = 0 ∧
      PersistenceImage.finiteDiagramImage σ w P
          (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n) -
        PersistenceImage.finiteDiagramImage σ w P
          (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n) = 0 := by
  have hD := twoPoints_logScale_diagrams_eq hn
  simp [hD]

/-- For two points, the right-hand side of the positive-degree log-scale embedding bottleneck
bound vanishes. -/
theorem twoPoints_logScale_bound_zero {n : ℕ} (hn : 1 ≤ n) (σ : ℝ)
    {A B : ℝ} :
    WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n).finiteOccurrences +
          Fintype.card (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n).finiteOccurrences : ℕ) : ℝ) *
      (bottleneck (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n)
        (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n)).toReal = 0 := by
  have hr : Fintype.card
      (logDgm (ZMod 2) (Rips.filter TwoPoints.metric) n).finiteOccurrences = 0 := by
    rw [Multiset.card_coe]
    rw [twoPoints_rips_logDgm_pos hn]
    simp [finitePart]
  have hc : Fintype.card
      (logDgm (ZMod 2) (Cech.filter TwoPoints.pts) n).finiteOccurrences = 0 := by
    rw [Multiset.card_coe]
    rw [twoPoints_cech_logDgm_pos hn]
    simp [finitePart]
  rw [hr, hc, twoPoints_logBottleneck_pos hn]
  simp

/-! ## (F2) Triangle instantiation -/

/-- The Euclidean triangle satisfies the positive-degree log-scale arctan embedding bound. -/
theorem triangle_logScale_embedding_arctan {n : ℕ} (hn : 1 ≤ n) (σ : ℝ)
    {C : ℝ} (hC : 0 ≤ C) :
    ‖WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (logDgm (ZMod 2) (Rips.filter Triangle.metric) n) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (logDgm (ZMod 2) (Cech.filter Triangle.pts) n)‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) *
        ((Fintype.card (dgm (ZMod 2) (Rips.filter Triangle.metric) n).finiteOccurrences +
          Fintype.card (dgm (ZMod 2) (Cech.filter Triangle.pts) n).finiteOccurrences : ℕ) : ℝ) *
        Real.log 2 := by
  simpa using
    Cech.norm_diagramEmbedding_logDgm_rips_sub_cech_le_arctan (ZMod 2)
      Triangle.metric Triangle.pts Triangle.metric_dist hn σ hC

/-! ## (F3) A nonvacuous generic sandwich -/

/-- Scaling the certified filled triangle by `2` gives the generic log-scale embedding bound. -/
theorem filledReal_scale_embedding_le (σ : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w
          (logDgm (ZMod 2) (filledReal.scale 2 two_pos) 1) -
        WeightedKernel.diagramEmbedding σ w
          (logDgm (ZMod 2) filledReal 1)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (logDgm (ZMod 2) (filledReal.scale 2 two_pos) 1).finiteOccurrences +
          Fintype.card (logDgm (ZMod 2) filledReal 1).finiteOccurrences : ℕ) : ℝ) *
        Real.log 2 := by
  refine norm_diagramEmbedding_logDgm_sub_le_log (ZMod 2)
    (f := filledReal.scale 2 two_pos) (g := filledReal) (c := 2) le_rfl one_le_two ?_ ?_
      filledReal_positive σ hA hB w
  · intro s
    rw [FilterFunction.scale_value]
    have h : (0 : ℝ) ≤ filledReal.value s := by
      change (0 : ℝ) ≤ ((s.val.card - 1 : ℕ) : ℝ)
      exact Nat.cast_nonneg _
    linarith
  · intro s
    rw [FilterFunction.scale_value]

/-- The certified filled triangle has one finite occurrence in its degree-one log-scale diagram. -/
theorem filledReal_logDgm_one_card :
    Fintype.card (logDgm (ZMod 2) filledReal 1).finiteOccurrences = 1 := by
  have hp : finitePart (logDgm (ZMod 2) filledReal 1).points =
      ({((0 : ℝ), Real.log 2)} : Multiset (ℝ × ℝ)) := by
    rw [filledReal_logDgm_one]
    rfl
  classical
  rw [Multiset.card_coe, hp, Multiset.card_singleton]

/-- The filled triangle's log-scale and radius-level degree-one diagrams have equal finite
occurrence counts. -/
theorem filledReal_card_eq :
    Fintype.card (logDgm (ZMod 2) filledReal 1).finiteOccurrences =
      Fintype.card (dgm (ZMod 2) filledReal 1).finiteOccurrences := by
  exact card_finiteOccurrences_logDgm (ZMod 2) (f := filledReal) (n := 1) le_rfl
    filledReal_positive

/-! ## (F4) Zero arctan weight -/

/-- At arctan weight `C = 0`, the log-scale embedding and image differences vanish, while the
displayed arctan constants at `σ = 1` are positive. -/
theorem zero_weight_logScale_consumers {V X : Type} [LinearOrder V] [Fintype V]
    [PseudoMetricSpace X] (d : MetricSpace V) (p : V → X)
    (_hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (_hn : 1 ≤ n) (σ : ℝ)
    {Kp : Type*} [Fintype Kp] (P : Kp → Set (ℝ × ℝ)) :
    WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight 0 le_rfl)
          (logDgm (ZMod 2) (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight 0 le_rfl)
          (logDgm (ZMod 2) (Cech.filter p) n) = 0 ∧
      PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight 0 le_rfl) P
          (logDgm (ZMod 2) (Rips.filter d) n) -
        PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight 0 le_rfl) P
          (logDgm (ZMod 2) (Cech.filter p) n) = 0 ∧
      0 < 2 * 0 + √2 * π / (2 * |(1 : ℝ)|) ∧
      0 < 2 * 0 + 3 * √(π / 2) / 1 := by
  refine ⟨by simp [TDA.Persistence.ArctanPersistenceImageExamples.zero_weight_embedding],
    by simp [TDA.Persistence.ArctanPersistenceImageExamples.zero_weight_image], ?_, ?_⟩
  · have hsqrt_two : 0 < √(2 : ℝ) := by positivity
    have hpi : 0 < (π : ℝ) := Real.pi_pos
    positivity
  · have hsqrt : 0 < √(π / 2) := Real.sqrt_pos.mpr Real.pi_div_two_pos
    positivity

/-! ## (F5) Degree-zero negative control -/

/-- In degree zero, the two-point log-scale modules are not constructible on their positive-log
grids. Thus `logDgm` does not represent the log-scale module there, and no `log 2` consumer is
available in degree zero. -/
theorem degree_zero_not_constructible :
    ¬ IsConstructible (logGrid (Rips.filter TwoPoints.metric))
        (logModule (ZMod 2) (Rips.filter TwoPoints.metric) 0) ∧
      ¬ IsConstructible (logGrid (Cech.filter TwoPoints.pts))
        (logModule (ZMod 2) (Cech.filter TwoPoints.pts) 0) := by
  exact ⟨twoPoints_rips_not_isConstructible_logGrid_zero,
    twoPoints_cech_not_isConstructible_logGrid_zero⟩

/-! ## (F6) Repeated-point `PositiveOnEdges` failure -/

/-- Repeated labels admit no metric compatible with their ambient distances. -/
theorem repeated_no_compatible_metric :
    ¬ ∃ d : MetricSpace (Fin 2), ∀ v w,
      d.dist v w = dist (Repeated.pts v) (Repeated.pts w) := by
  rintro ⟨d, hd⟩
  exact repeated_not_positive (Cech.positiveOnEdges_cech d Repeated.pts hd)

end TDA.Persistence.CechRipsLogScaleConsumersExamples
