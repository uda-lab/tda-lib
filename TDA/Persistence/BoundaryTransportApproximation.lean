import TDA.Persistence.BoundaryTransportQuantization

/-!
# Same-mass finite atomic approximation

Approximation targets lie in the dense range of interior points. Every
quantizer therefore remains interior-valued, and its finite diagram retains
the original measure's total mass. The only integrability assumption is the
collapsed-boundary persistence moment.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.BoundaryTransport

open Set MeasureTheory Filter Topology
open scoped Classical ENNReal NNReal
local infixr:25 " →ₛ " => SimpleFunc

/-- A fixed interior point of depth one used by the dense-range approximation. -/
private def approximationBase : Interior := ⟨(0, 2), by norm_num⟩

private theorem approximationBase_depth : depth approximationBase = 1 := by
  norm_num [approximationBase, depth_eq]

private def unpointApprox : Space → Interior
  | .boundary => approximationBase
  | .point x => x

private def spaceApprox (n : ℕ) : Interior →ₛ Space :=
  SimpleFunc.approxOn Space.point continuous_point.measurable
    (Set.range Space.point) (Space.point approximationBase)
    ⟨approximationBase, rfl⟩ n

private theorem spaceApprox_interior (n : ℕ) (x : Interior) :
    spaceApprox n x ∈ Set.range Space.point :=
  SimpleFunc.approxOn_mem continuous_point.measurable
    (show Space.point approximationBase ∈ Set.range Space.point from
      ⟨approximationBase, rfl⟩) n x

/-- A finite-range interior quantizer, with no boundary values. -/
def interiorQuantizer (n : ℕ) : Interior →ₛ Interior :=
  (spaceApprox n).map unpointApprox

private theorem point_interiorQuantizer (n : ℕ) (x : Interior) :
    Space.point (interiorQuantizer n x) = spaceApprox n x := by
  obtain ⟨y, hy⟩ := spaceApprox_interior n x
  change Space.point (unpointApprox (spaceApprox n x)) = spaceApprox n x
  rw [← hy]
  rfl

/-- The actual native finite diagram at approximation level `n`. -/
def quantizedDiagram (μ : Measure Interior) [IsFiniteMeasure μ] (n : ℕ) :
    FiniteWeightedDiagram := simpleFuncDiagram μ (interiorQuantizer n)

theorem atomicMeasure_quantizedDiagram (μ : Measure Interior) [IsFiniteMeasure μ]
    (n : ℕ) :
    atomicMeasure (quantizedDiagram μ n) = μ.map (interiorQuantizer n) :=
  atomicMeasure_simpleFuncDiagram μ _

theorem quantizedDiagram_mass (μ : Measure Interior) [IsFiniteMeasure μ]
    (n : ℕ) : atomicMeasure (quantizedDiagram μ n) Set.univ = μ Set.univ :=
  simpleFuncDiagram_mass μ _

@[simp] theorem quantizedDiagram_zero (n : ℕ) :
    quantizedDiagram 0 n = 0 := simpleFuncDiagram_zero _

private theorem spaceApprox_tendsto (x : Interior) :
    Tendsto (fun n => spaceApprox n x) atTop (𝓝 (Space.point x)) :=
  SimpleFunc.tendsto_approxOn continuous_point.measurable
    (show Space.point approximationBase ∈ Set.range Space.point from
      ⟨approximationBase, rfl⟩)
    (subset_closure (⟨x, rfl⟩ : Space.point x ∈ Set.range Space.point))

private theorem interiorQuantizer_point_tendsto (x : Interior) :
    Tendsto (fun n => Space.point (interiorQuantizer n x)) atTop
      (𝓝 (Space.point x)) := by
  simpa only [point_interiorQuantizer] using spaceApprox_tendsto x

private theorem measurable_depth : Measurable depth := by
  have h : Continuous (fun x : Interior => (x.1.2 - x.1.1) / 2) := by fun_prop
  simpa only [← depth_eq] using h.measurable

private def quantizationError (p : ℝ) (n : ℕ) (x : Interior) : ℝ≥0∞ :=
  (edist (Space.point (interiorQuantizer n x)) (Space.point x)) ^ p

private theorem quantizationError_measurable (p : ℝ) (n : ℕ) :
    Measurable (quantizationError p n) := by
  unfold quantizationError
  exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp
    ((continuous_point.measurable.comp
      (interiorQuantizer n).measurable).edist continuous_point.measurable)

private theorem quantizationError_tendsto (p : ℝ) (hp : 0 < p) (x : Interior) :
    Tendsto (fun n => quantizationError p n x) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => edist (Space.point (interiorQuantizer n x))
      (Space.point x)) atTop (𝓝 0) := by
    simpa only [edist_self] using
      (interiorQuantizer_point_tendsto x).edist
        (tendsto_const_nhds (x := Space.point x))
  simpa only [quantizationError, ENNReal.zero_rpow_of_pos hp, Function.comp_def] using
    (ENNReal.continuous_rpow_const (y := p) |>.tendsto 0).comp hd

private theorem quantizationError_le_depth (p : ℝ) (hp : 0 ≤ p)
    (n : ℕ) (x : Interior) :
    quantizationError p n x ≤
      ((1 : ℝ≥0∞) + ENNReal.ofReal (depth x)) ^ p := by
  have hbase : edist (Space.point approximationBase) (Space.point x) ≤
      (1 : ℝ≥0∞) + ENNReal.ofReal (depth x) := by
    calc
      edist (Space.point approximationBase) (Space.point x) ≤
          edist (Space.point approximationBase) Space.boundary +
          edist Space.boundary (Space.point x) := edist_triangle _ _ _
      _ = (1 : ℝ≥0∞) + ENNReal.ofReal (depth x) := by
        simp [edist_dist, approximationBase, depth_eq]
  have happrox := SimpleFunc.edist_approxOn_le continuous_point.measurable
    (show Space.point approximationBase ∈ Set.range Space.point from
      ⟨approximationBase, rfl⟩) x n
  change edist (spaceApprox n x) (Space.point x) ≤
    edist (Space.point approximationBase) (Space.point x) at happrox
  unfold quantizationError
  rw [point_interiorQuantizer]
  exact ENNReal.rpow_le_rpow (happrox.trans hbase) hp

private def quantizationBound (p : ℝ) (x : Interior) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal (depth x ^ p))

private theorem quantizationError_le_bound (p : ℝ) (hp : 0 ≤ p)
    (n : ℕ) (x : Interior) :
    quantizationError p n x ≤ quantizationBound p x := by
  apply (quantizationError_le_depth p hp n x).trans
  have h := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
    (1 : ℝ≥0∞) (ENNReal.ofReal (depth x)) hp
  simpa only [ENNReal.one_rpow, ENNReal.ofReal_rpow_of_nonneg (depth_nonneg x) hp,
    quantizationBound] using h

private theorem quantizationBound_integrable (p : ℝ)
    (μ : Measure Interior) [IsFiniteMeasure μ]
    (hmoment : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞) :
    (∫⁻ x, quantizationBound p x ∂μ) < ∞ := by
  have hm : Measurable (fun x : Interior => ENNReal.ofReal (depth x ^ p)) := by
    exact (measurable_depth.pow_const p).ennreal_ofReal
  unfold quantizationBound
  calc
    (∫⁻ x, (2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal (depth x ^ p)) ∂μ) =
        (2 : ℝ≥0∞) ^ p * (∫⁻ x, 1 + ENNReal.ofReal (depth x ^ p) ∂μ) := by
          exact lintegral_const_mul _ (measurable_const.add hm)
    _ = (2 : ℝ≥0∞) ^ p *
        ((∫⁻ _ : Interior, (1 : ℝ≥0∞) ∂μ) +
          ∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) := by
            rw [lintegral_add_left measurable_const]
    _ < ∞ := by
      rw [lintegral_const]
      finiteness

private theorem quantizationError_lintegral_tendsto (p : ℝ) (hp : 1 ≤ p)
    (μ : Measure Interior) [IsFiniteMeasure μ]
    (hmoment : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞) :
    Tendsto (fun n => ∫⁻ x, quantizationError p n x ∂μ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence
    (μ := μ) (f := fun _ : Interior => (0 : ℝ≥0∞))
    (quantizationBound p)
    (fun n => quantizationError_measurable p n)
    (fun n => Filter.Eventually.of_forall
      (quantizationError_le_bound p (le_trans (by norm_num) hp) n))
    (quantizationBound_integrable p μ hmoment).ne
    (Filter.Eventually.of_forall fun x => quantizationError_tendsto p (by linarith) x)
  simpa only [lintegral_zero] using h

private theorem quantizationError_eq_cost (p : ℝ) (hp : 0 ≤ p)
    (n : ℕ) (x : Interior) :
    ENNReal.ofReal ((dist (Space.point x)
      (Space.point (interiorQuantizer n x))) ^ p) = quantizationError p n x := by
  rw [quantizationError, ← ENNReal.ofReal_rpow_of_nonneg dist_nonneg hp,
    ← edist_dist, edist_comm]

/-- Native powered transport to the level-`n` diagram tends to zero. -/
theorem boundaryTransportPowerValue_quantizedDiagram_tendsto
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) [IsFiniteMeasure μ]
    (hmoment : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞) :
    Tendsto (fun n => boundaryTransportPowerValue p μ
      (atomicMeasure (quantizedDiagram μ n))) atTop (𝓝 0) := by
  have herror := quantizationError_lintegral_tendsto p hp μ hmoment
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herror
  · intro n
    exact bot_le
  · intro n
    simpa only [quantizedDiagram,
      quantizationError_eq_cost p (le_trans (by norm_num) hp)] using
      boundaryTransportPowerValue_simpleFuncDiagram_le p hp μ (interiorQuantizer n)

/-- Finite same-mass atomic diagrams converge for boundary transport. -/
theorem boundaryTransportDistance_quantizedDiagram_tendsto
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) [IsFiniteMeasure μ]
    (hmoment : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞) :
    Tendsto (fun n => boundaryTransportDistance p μ
      (atomicMeasure (quantizedDiagram μ n))) atTop (𝓝 0) := by
  have hr : 0 < 1 / p := one_div_pos.mpr (by linarith)
  simpa only [boundaryTransportDistance, ENNReal.zero_rpow_of_pos hr,
    Function.comp_def] using
    ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp
      (boundaryTransportPowerValue_quantizedDiagram_tendsto p hp μ hmoment)

/-- Every finite measure with finite persistence moment has an exact-mass native
finite atomic approximation at any positive boundary transport accuracy. -/
theorem exists_atomicMeasure_approx_same_mass
    (p : ℝ) (hp : 1 ≤ p) (μ : Measure Interior) [IsFiniteMeasure μ]
    (hmoment : (∫⁻ x, ENNReal.ofReal (depth x ^ p) ∂μ) < ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ D : FiniteWeightedDiagram,
      atomicMeasure D Set.univ = μ Set.univ ∧
      boundaryTransportDistance p μ (atomicMeasure D) < ε := by
  have hconv := boundaryTransportDistance_quantizedDiagram_tendsto p hp μ hmoment
  obtain ⟨n, hn⟩ := Filter.Eventually.exists
    (hconv.eventually (Iio_mem_nhds hε))
  exact ⟨quantizedDiagram μ n, quantizedDiagram_mass μ n, hn⟩

end TDA.Persistence.BoundaryTransport
