import TDA.Persistence.DiagramBottleneckTopology
import TDA.Persistence.RipsSampling
import TDA.Persistence.EssentialVanishing
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Probability laws of sampled finite Rips diagrams

Tuples are sampled with replacement. The sample diagram map is continuous in
the product metric, with the factor two coming from comparing both endpoints
of each distance-matrix entry.
-/

noncomputable section

universe u v w

namespace TDA.Persistence

open MeasureTheory
open scoped ENNReal NNReal

/-- The empty diagram is the bottleneck-space base point. -/
def Diagram.empty : Diagram ℝ :=
  orderedQ 0 0 ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ))

namespace Rips

/-- Every positive-degree diagram on a carrier with at most one point is empty.
This uses full-complex vanishing and the face-count bound, not a barcode
assumption. -/
private theorem bottleneck_diagram_card_le_one_empty (k : Type w) [Field k]
    {Y : Type u} [Fintype Y] [MetricSpace Y] (hcard : Fintype.card Y ≤ 1)
    (degree : ℕ) (hdegree : 1 ≤ degree) :
    bottleneck (diagram k Y degree) Diagram.empty = 0 := by
  classical
  let V := ULift.{w} (Fin (Fintype.card Y))
  have hcardV : Fintype.card V ≤ 1 := by simpa [V] using hcard
  let e : V ≃ Y := Equiv.ulift.trans (Fintype.equivFin Y).symm
  letI : LinearOrder V := inferInstance
  letI : MetricSpace V :=
    @MetricSpace.induced V Y e e.injective (inferInstance : MetricSpace Y)
  let D := diagram k Y degree
  have hess : essentialPart D.points = 0 := by
    change essentialPart
      (dgm k (TDA.Filtration.Rips.filter (inferInstance : MetricSpace V)) degree).points = 0
    exact TDA.Persistence.Rips.essentialPart_dgm_eq_zero k
      (inferInstance : MetricSpace V) hdegree
  have hcardD : Fintype.card D.finiteOccurrences = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      Fintype.card D.finiteOccurrences ≤ Nat.choose (Fintype.card V) (degree + 2) := by
        change Fintype.card
            (dgm k (TDA.Filtration.Rips.filter (inferInstance : MetricSpace V))
              degree).finiteOccurrences ≤ _
        exact card_finiteOccurrences_dgm_fullComplex_le k
          (TDA.Filtration.Rips.filter (inferInstance : MetricSpace V)) degree
      _ = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hempty : IsEmpty D.finiteOccurrences := Fintype.card_eq_zero_iff.mp hcardD
  change bottleneck D (orderedQ 0 0
    ((Fin.elim0 : Fin 0 → ℝ × ℝ), (Fin.elim0 : Fin 0 → ℝ))) = 0
  rw [bottleneck_finite_only_empty D hess]
  letI := hempty
  simp [Diagram.finiteOccurrences]

variable {X : Type u} {n : ℕ} [MetricSpace X]

/-- Each distance-matrix entry changes by at most twice the tuple sup distance. -/
theorem distMatrixEntry_le_two_mul_piDist (t s : Fin n → X) (i j : Fin n) :
    |dist (t i) (t j) - dist (s i) (s j)| ≤ 2 * dist t s := by
  have h := dist_dist_dist_le (t i) (t j) (s i) (s j)
  calc
    |dist (t i) (t j) - dist (s i) (s j)| =
        dist (dist (t i) (t j)) (dist (s i) (s j)) := by
      simp [Real.dist_eq]
    _ ≤ dist (t i) (s i) + dist (t j) (s j) := h
    _ ≤ dist t s + dist t s := add_le_add (dist_le_pi_dist t s i) (dist_le_pi_dist t s j)
    _ = 2 * dist t s := by ring

/-- The full finite-sample Rips diagram map is two-Lipschitz for the product
metric, including tuples with repeated entries. -/
theorem lipschitzWith_sampleDiagram (k : Type w) [Field k] (degree : ℕ) :
    LipschitzWith 2 (fun t : Fin n → X => sampleDiagram k t degree) := by
  intro t s
  let ε : ℝ≥0 := ⟨2 * dist t s, mul_nonneg (by norm_num) (dist_nonneg)⟩
  have h := bottleneck_sampleDiagram_le k t s (ε := ε)
    (fun i j => by
      change |dist (t i) (t j) - dist (s i) (s j)| ≤ 2 * dist t s
      exact distMatrixEntry_le_two_mul_piDist t s i j) degree
  have h' : bottleneck (sampleDiagram k t degree) (sampleDiagram k s degree) ≤
      ENNReal.ofReal (2 * dist t s) := by
    have hε : (ε : ℝ≥0∞) = ENNReal.ofReal (2 * dist t s) := by
      rw [ENNReal.coe_nnreal_eq]
      congr 1
    simpa only [hε] using h
  change bottleneck (sampleDiagram k t degree) (sampleDiagram k s degree) ≤
    (2 : ℝ≥0∞) * edist t s
  rw [edist_dist]
  calc
    bottleneck (sampleDiagram k t degree) (sampleDiagram k s degree) ≤
        ENNReal.ofReal (2 * dist t s) := h'
    _ = (2 : ℝ≥0∞) * ENNReal.ofReal (dist t s) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp

/-- The sample diagram map is continuous on the whole tuple space. -/
theorem continuous_sampleDiagram (k : Type w) [Field k] (degree : ℕ) :
    Continuous (fun t : Fin n → X => sampleDiagram k t degree) :=
  (lipschitzWith_sampleDiagram k degree).continuous

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

/-- The genuine probability law of the full Rips diagram of an iid tuple drawn
with replacement from a compact metric probability space. -/
def sampleLawMeasure (k : Type w) [Field k] (μ : ProbabilityMeasure X)
    (n degree : ℕ) : ProbabilityMeasure (Diagram ℝ) :=
  (ProbabilityMeasure.pi (fun _ : Fin n => μ)).map
    (continuous_sampleDiagram (X := X) k degree).measurable.aemeasurable

omit [MeasurableSpace X] [BorelSpace X] in
/-- The image of the sample map is compact. -/
theorem isCompact_range_sampleDiagram (k : Type w) [Field k] (degree : ℕ) :
    IsCompact (Set.range (fun t : Fin n → X => sampleDiagram k t degree)) := by
  exact isCompact_range (continuous_sampleDiagram k degree)

/-- The sampled law assigns full mass to the compact set of diagrams that can
arise from an input tuple. -/
theorem sampleLawMeasure_range (k : Type w) [Field k] (μ : ProbabilityMeasure X)
    (n degree : ℕ) :
    (sampleLawMeasure k μ n degree : Measure (Diagram ℝ))
      (Set.range (fun t : Fin n → X => sampleDiagram k t degree)) = 1 := by
  rw [sampleLawMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (continuous_sampleDiagram k degree).measurable
    (isCompact_range_sampleDiagram k degree).measurableSet]
  simp

/-- Isometric pushforward of the input probability measure leaves the sampled
Rips diagram law unchanged. -/
theorem sampleLawMeasure_map_isometry (k : Type w) [Field k]
    {Y : Type v} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (f : X → Y) (hf : Isometry f) (μ : ProbabilityMeasure X) (n degree : ℕ) :
    sampleLawMeasure k (μ.map hf.continuous.measurable.aemeasurable) n degree =
      sampleLawMeasure k μ n degree := by
  let g : (Fin n → X) → Fin n → Y := fun t i => f (t i)
  have hprod :
      (ProbabilityMeasure.pi (fun _ : Fin n =>
        μ.map hf.continuous.measurable.aemeasurable) : Measure (Fin n → Y)) =
        Measure.map g
          (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X)) := by
    change Measure.pi (fun _ : Fin n =>
        (μ.map hf.continuous.measurable.aemeasurable : Measure Y)) =
      Measure.map (fun t i => f (t i))
        (Measure.pi (fun _ : Fin n => (μ : Measure X)))
    exact (Measure.pi_map_pi
      (μ := fun _ : Fin n => (μ : Measure X))
      (f := fun _ : Fin n => f)
      (fun _ => hf.continuous.measurable.aemeasurable)).symm
  apply Subtype.ext
  change Measure.map (fun s : Fin n → Y => sampleDiagram k s degree)
      (ProbabilityMeasure.pi (fun _ : Fin n =>
        μ.map hf.continuous.measurable.aemeasurable) : Measure (Fin n → Y)) =
    Measure.map (fun t : Fin n → X => sampleDiagram k t degree)
      (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X))
  rw [hprod]
  have hg : Measurable g := by
    apply measurable_pi_lambda
    intro i
    exact hf.continuous.measurable.comp (measurable_pi_apply i)
  calc
    Measure.map (fun s : Fin n → Y => sampleDiagram k s degree)
        (Measure.map g (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X))) =
      Measure.map
        ((fun s : Fin n → Y => sampleDiagram k s degree) ∘ g)
        (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X)) :=
      Measure.map_map (continuous_sampleDiagram (X := Y) k degree).measurable hg
    _ = Measure.map (fun t : Fin n → X => sampleDiagram k t degree)
        (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X)) := by
      congr 1
      funext t
      exact sampleDiagram_eq_of_isometry k f hf t degree

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
private theorem iid_apply_product (μ : PMF X) (t : Fin n → X) :
    TDA.Probability.iid μ n t = ∏ i, μ (t i) := by
  induction n with
  | zero =>
    have ht : t = Fin.elim0 := Subsingleton.elim _ _
    subst t
    simp [TDA.Probability.iid]
  | succ n ih =>
    classical
    rw [TDA.Probability.iid_succ, PMF.bind_apply]
    let tail : Fin n → X := fun i => t i.succ
    let cons : X → (Fin n → X) → Fin (n + 1) → X := fun x xs => Fin.cons x xs
    have ht : t = cons (t 0) tail := by
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    rw [ht]
    have hinner (a : X) :
        (TDA.Probability.iid μ n).map (cons a) (cons (t 0) tail) =
          if a = t 0 then TDA.Probability.iid μ n tail else 0 := by
      rw [PMF.map_apply]
      by_cases ha : a = t 0
      · subst a
        simp [cons, Fin.cons_inj]
      · simp [cons, Fin.cons_inj, ha, eq_comm]
    change (∑' a : X, μ a *
      (TDA.Probability.iid μ n).map (cons a) (cons (t 0) tail)) =
      ∏ i : Fin (n + 1), μ (cons (t 0) tail i)
    simp_rw [hinner]
    have hsum :
        (∑' a : X, μ a *
          (if a = t 0 then TDA.Probability.iid μ n tail else 0)) =
          μ (t 0) * TDA.Probability.iid μ n tail := by
      calc
        (∑' a : X, μ a *
            (if a = t 0 then TDA.Probability.iid μ n tail else 0)) =
            ∑' a : X, (if a = t 0 then μ a * TDA.Probability.iid μ n tail else 0) := by
          congr 1
          funext a
          by_cases ha : a = t 0 <;> simp [ha]
        _ = μ (t 0) * TDA.Probability.iid μ n tail := by
          rw [tsum_eq_single (t 0)]
          · simp
          · intro a ha
            simp [ha]
    calc
      _ = μ (t 0) * TDA.Probability.iid μ n tail := hsum
      _ = μ (t 0) * ∏ i : Fin n, μ (tail i) := by rw [ih]
      _ = ∏ i : Fin (n + 1), μ (cons (t 0) tail i) := by
        symm
        rw [Fin.prod_univ_succ]
        simp [cons]

/-- On a finite metric input, the new Borel probability law agrees exactly
with the existing atomic iid `sampleLaw` after conversion to a measure. -/
theorem sampleLawMeasure_eq_toMeasure_sampleLaw (k : Type w) [Field k]
    [Fintype X] [MeasurableSingletonClass X]
    (μ : PMF X) (n degree : ℕ) :
    sampleLawMeasure k
        (⟨μ.toMeasure, (inferInstance : IsProbabilityMeasure μ.toMeasure)⟩ :
          ProbabilityMeasure X)
        n degree =
      (sampleLaw k μ n degree).toMeasure := by
  classical
  let μprob : ProbabilityMeasure X :=
    ⟨μ.toMeasure, (inferInstance : IsProbabilityMeasure μ.toMeasure)⟩
  have hTuple :
      (ProbabilityMeasure.pi (fun _ : Fin n => μprob) : Measure (Fin n → X)) =
        (TDA.Probability.iid μ n).toMeasure := by
    apply Measure.ext_of_singleton
    intro t
    rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_singleton]
    simp [μprob, iid_apply_product]
  change Measure.map (fun t : Fin n → X => sampleDiagram k t degree)
      (ProbabilityMeasure.pi (fun _ : Fin n =>
        (⟨μ.toMeasure, (inferInstance : IsProbabilityMeasure μ.toMeasure)⟩ :
          ProbabilityMeasure X)) : Measure (Fin n → X)) =
    ((TDA.Probability.iid μ n).map (fun t => sampleDiagram k t degree)).toMeasure
  rw [hTuple]
  exact PMF.toMeasure_map (p := TDA.Probability.iid μ n)
    (f := fun t => sampleDiagram k t degree)
    (continuous_sampleDiagram k degree).measurable

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
private theorem bottleneck_sampleDiagram_card_le_one_empty (k : Type w) [Field k]
    (t : Fin n → X) (degree : ℕ) (hdegree : 1 ≤ degree)
    (hcard : Fintype.card (Sample t) ≤ 1) :
    bottleneck (sampleDiagram k t degree) Diagram.empty = 0 := by
  classical
  change bottleneck (diagram k (Sample t) degree) Diagram.empty = 0
  exact bottleneck_diagram_card_le_one_empty k hcard degree hdegree

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
/-- A positive-degree diagram of a constant tuple is empty. -/
private theorem bottleneck_sampleDiagram_const_empty (k : Type w) [Field k]
    (x : X) (degree : ℕ) (hdegree : 1 ≤ degree) :
    bottleneck (sampleDiagram k (fun _ : Fin n => x) degree) Diagram.empty = 0 := by
  classical
  letI : Subsingleton (Sample (fun _ : Fin n => x)) := ⟨by
    rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
    apply Subtype.ext
    rfl⟩
  apply bottleneck_sampleDiagram_card_le_one_empty k _ degree hdegree
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

omit [MeasurableSpace X] [BorelSpace X] in
/-- On a compact input, every positive-degree sampled diagram lies within twice
the input diameter of the empty diagram. -/
theorem bottleneck_sampleDiagram_empty_le_two_mul_diam (k : Type w) [Field k]
    (t : Fin n → X) (degree : ℕ) (hdegree : 1 ≤ degree) :
    bottleneck (sampleDiagram k t degree) Diagram.empty ≤
      ENNReal.ofReal (2 * Metric.diam (Set.univ : Set X)) := by
  classical
  by_cases hn : n = 0
  · subst n
    letI : Subsingleton (Sample t) := ⟨by
      rintro ⟨x, i, hi⟩ _
      exact Fin.elim0 i⟩
    have hcard : Fintype.card (Sample t) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    rw [bottleneck_sampleDiagram_card_le_one_empty k t degree hdegree hcard]
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let i₀ : Fin n := ⟨0, hnpos⟩
    let c : Fin n → X := fun _ => t i₀
    have hc_empty : bottleneck (sampleDiagram k c degree) Diagram.empty = 0 :=
      bottleneck_sampleDiagram_const_empty k (t i₀) degree hdegree
    have htuple : dist t c ≤ Metric.diam (Set.univ : Set X) := by
      apply (dist_pi_le_iff (Metric.diam_nonneg : 0 ≤ Metric.diam (Set.univ : Set X))).2
      intro i
      exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded
        (Set.mem_univ (t i)) (Set.mem_univ (t i₀))
    have hLip : bottleneck (sampleDiagram k t degree) (sampleDiagram k c degree) ≤
        ENNReal.ofReal (2 * dist t c) := by
      have h := (lipschitzWith_sampleDiagram (X := X) (n := n) k degree) t c
      change bottleneck (sampleDiagram k t degree) (sampleDiagram k c degree) ≤
        (2 : ℝ≥0∞) * edist t c at h
      rw [edist_dist] at h
      calc
        bottleneck (sampleDiagram k t degree) (sampleDiagram k c degree) ≤
            (2 : ℝ≥0∞) * ENNReal.ofReal (dist t c) := h
        _ = ENNReal.ofReal (2 * dist t c) := by
          symm
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          simp
    have hdiam : ENNReal.ofReal (2 * dist t c) ≤
        ENNReal.ofReal (2 * Metric.diam (Set.univ : Set X)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left htuple (by norm_num))
    calc
      bottleneck (sampleDiagram k t degree) Diagram.empty ≤
          bottleneck (sampleDiagram k t degree) (sampleDiagram k c degree) +
            bottleneck (sampleDiagram k c degree) Diagram.empty :=
        bottleneck_triangle _ _ _
      _ ≤ ENNReal.ofReal (2 * Metric.diam (Set.univ : Set X)) + 0 :=
        add_le_add (hLip.trans hdiam) hc_empty.le
      _ = ENNReal.ofReal (2 * Metric.diam (Set.univ : Set X)) := by simp

/-- The compact-input sampled law has every positive real moment in positive
homological degree, measured from the empty diagram. -/
theorem sampleLawMeasure_finite_rpow_moment (k : Type w) [Field k]
    (μ : ProbabilityMeasure X) (n degree : ℕ) (hdegree : 1 ≤ degree)
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ D, (edist D Diagram.empty) ^ p ∂(sampleLawMeasure k μ n degree : Measure (Diagram ℝ))
      < ⊤ := by
  let bound : ℝ≥0∞ := ENNReal.ofReal (2 * Metric.diam (Set.univ : Set X))
  have hmap :
      ∫⁻ D, (edist D Diagram.empty) ^ p ∂
          (sampleLawMeasure k μ n degree : Measure (Diagram ℝ)) ≤
        ∫⁻ t, (edist (sampleDiagram k t degree) Diagram.empty) ^ p ∂
          (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X)) := by
    rw [sampleLawMeasure, ProbabilityMeasure.toMeasure_map]
    exact MeasureTheory.lintegral_map_le _ _
  have hpoint (t : Fin n → X) :
      (edist (sampleDiagram k t degree) Diagram.empty) ^ p ≤ bound ^ p := by
    change (bottleneck (sampleDiagram k t degree) Diagram.empty) ^ p ≤ bound ^ p
    exact ENNReal.rpow_le_rpow
      (bottleneck_sampleDiagram_empty_le_two_mul_diam k t degree hdegree) hp.le
  have hfinite : bound ^ p < ⊤ := by
    apply ENNReal.rpow_lt_top_of_nonneg hp.le
    dsimp [bound]
    exact ENNReal.ofReal_ne_top
  calc
    ∫⁻ D, (edist D Diagram.empty) ^ p ∂
        (sampleLawMeasure k μ n degree : Measure (Diagram ℝ)) ≤
      ∫⁻ t, (edist (sampleDiagram k t degree) Diagram.empty) ^ p ∂
        (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X)) := hmap
    _ ≤ ∫⁻ _, bound ^ p ∂
        (ProbabilityMeasure.pi (fun _ : Fin n => μ) : Measure (Fin n → X)) :=
      MeasureTheory.lintegral_mono hpoint
    _ = bound ^ p := by simp [MeasureTheory.lintegral_const]
    _ < ⊤ := hfinite

end Rips

end TDA.Persistence
