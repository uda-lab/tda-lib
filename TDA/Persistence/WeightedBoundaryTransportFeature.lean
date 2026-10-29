import TDA.Persistence.WeightedKernelStability
import TDA.Persistence.WeightedPersistenceMeasure
import TDA.Persistence.BoundaryPlans

/-!
# Weighted Gaussian features on the native boundary-plan space

The native strict birth–death plane and the weighted-measure presentation are the
same measurable subtype. Bounded birth–persistence weights make their full-plane
Gaussian features Bochner integrable for every finite original measure. Extending
by zero at the collapsed diagonal preserves the stability constant. The endpoint
integrals below use the actual interior marginals of an admissible boundary plan.
-/

noncomputable section
namespace TDA.Persistence.WeightedKernel

open MeasureTheory Set
open scoped ENNReal

variable {A B : ℝ}

/-- The native and weighted-measure strict planes have identical coordinates and
Borel structures. This equivalence changes neither points nor their measures. -/
def interiorUpperPointEquiv : BoundaryTransport.Interior ≃ᵐ UpperPoint :=
  MeasurableEquiv.refl _

@[simp] theorem interiorUpperPointEquiv_apply (x : BoundaryTransport.Interior) :
    interiorUpperPointEquiv x = x := rfl

@[simp] theorem map_interiorUpperPointEquiv (μ : Measure BoundaryTransport.Interior) :
    μ.map interiorUpperPointEquiv = μ := by
  exact Measure.map_id

/-- The birth–persistence reading of a bounded Lipschitz weight is measurable. -/
theorem measurable_upperWeight (hA : 0 ≤ A) (w : PersistenceImage.Weight A B) :
    Measurable (upperWeight w) := by
  have hw : LipschitzWith ⟨A, hA⟩ w := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (w x) (w y) ≤ A * dist x y
    simpa only [dist_eq_norm, Real.norm_eq_abs] using w.lipschitz x y
  have ht : Continuous (fun x : UpperPoint => birthPersistence x.1) := by
    unfold birthPersistence
    fun_prop
  exact (hw.continuous.comp ht).measurable

/-- The weighted feature is globally continuous on the full birth–death plane. -/
theorem continuous_weightedFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) : Continuous (weightedFeature σ w) := by
  have hl : LipschitzWith ⟨stabilityConstant σ A B, stabilityConstant_nonneg σ hA hB⟩
      (weightedFeature σ w) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (weightedFeature σ w x) (weightedFeature σ w y) ≤
      stabilityConstant σ A B * dist x y
    simpa only [dist_eq_norm] using norm_weightedFeature_sub_le σ hB w x y
  exact hl.continuous

/-- Bounded weights give a uniform bound independently of the birth coordinate. -/
theorem norm_weightedFeature_le (σ : ℝ) (w : PersistenceImage.Weight A B) (x : ℝ × ℝ) :
    ‖weightedFeature σ w x‖ ≤ B := by
  simpa only [weightedFeature, norm_smul, Real.norm_eq_abs, norm_featureAt, mul_one,
    abs_of_nonneg (w.nonneg _)] using w.bounded (birthPersistence x)

/-- Finite original mass suffices for weighted-feature integrability, without moments. -/
theorem integrable_weightedFeature_finite (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (μ : Measure BoundaryTransport.Interior)
    [IsFiniteMeasure μ] : Integrable (fun x => weightedFeature σ w x.1) μ := by
  apply (integrable_const B).mono'
    ((continuous_weightedFeature σ hA hB w).comp continuous_subtype_val).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => norm_weightedFeature_le σ w x.1)

/-- The native integral is exactly the existing full-plane weighted Gaussian mean. -/
theorem weightedPersistenceEmbedding_eq_integral_native (σ : ℝ) (hA : 0 ≤ A)
    (w : PersistenceImage.Weight A B) (μ : Measure BoundaryTransport.Interior) :
    weightedPersistenceEmbedding σ (upperWeight w) μ =
      ∫ x, weightedFeature σ w x.1 ∂μ :=
  weightedPersistenceEmbedding_eq_integral σ (upperWeight w) (measurable_upperWeight hA w)
    (fun _ => w.nonneg _) μ

/-- Extend the actual full-plane RKHS feature by zero at the collapsed diagonal. -/
def boundaryFeature (σ : ℝ) (w : PersistenceImage.Weight A B) :
    BoundaryTransport.Space → Space σ
  | .boundary => 0
  | .point x => weightedFeature σ w x.1

@[simp] theorem boundaryFeature_boundary (σ : ℝ) (w : PersistenceImage.Weight A B) :
    boundaryFeature σ w .boundary = 0 := rfl

@[simp] theorem boundaryFeature_point (σ : ℝ) (w : PersistenceImage.Weight A B)
    (x : BoundaryTransport.Interior) :
    boundaryFeature σ w (.point x) = weightedFeature σ w x.1 := rfl

/-- On every closed upper-plane point, zero extension agrees with the original feature. -/
theorem boundaryFeature_collapse (σ : ℝ) (w : PersistenceImage.Weight A B)
    (x : BoundaryTransport.ClosedHalfPlane) :
    boundaryFeature σ w (BoundaryTransport.collapse x) = weightedFeature σ w x.1 := by
  unfold BoundaryTransport.collapse
  split_ifs with h
  · rfl
  · have heq : x.1.1 = x.1.2 := le_antisymm x.2 (le_of_not_gt h)
    have hx : x.1 = (x.1.1, x.1.1) := Prod.ext rfl heq.symm
    rw [hx, weightedFeature_diagonal]
    rfl

/-- The zero extension is Lipschitz for the collapsed-boundary metric with the same
constant as the original weighted feature. -/
theorem norm_boundaryFeature_sub_le (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (x y : BoundaryTransport.Space) :
    ‖boundaryFeature σ w x - boundaryFeature σ w y‖ ≤ stabilityConstant σ A B * dist x y := by
  cases x with
  | boundary =>
    cases y with
    | boundary => simp
    | point y =>
      simpa only [boundaryFeature, zero_sub, norm_neg, BoundaryTransport.dist_boundary_point,
        BoundaryTransport.depth] using norm_weightedFeature_le_diagonalCost σ hB w y.1
  | point x =>
    cases y with
    | boundary =>
      simpa only [boundaryFeature, sub_zero, BoundaryTransport.dist_point_boundary,
        BoundaryTransport.depth] using norm_weightedFeature_le_diagonalCost σ hB w x.1
    | point y =>
      rw [BoundaryTransport.dist_point_point, mul_min_of_nonneg _ _
        (stabilityConstant_nonneg σ hA hB)]
      apply le_min
      · simpa only [boundaryFeature, Subtype.dist_eq, dist_eq_norm] using
          norm_weightedFeature_sub_le σ hB w x.1 y.1
      · calc
          _ ≤ ‖weightedFeature σ w x.1‖ + ‖weightedFeature σ w y.1‖ := norm_sub_le _ _
          _ ≤ stabilityConstant σ A B * BoundaryTransport.depth x +
              stabilityConstant σ A B * BoundaryTransport.depth y :=
            add_le_add (norm_weightedFeature_le_diagonalCost σ hB w x.1)
              (norm_weightedFeature_le_diagonalCost σ hB w y.1)
          _ = _ := (mul_add _ _ _).symm

/-- The zero extension is globally Lipschitz on the collapsed metric space. -/
theorem lipschitz_boundaryFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) :
    LipschitzWith ⟨stabilityConstant σ A B, stabilityConstant_nonneg σ hA hB⟩
      (boundaryFeature σ w) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (boundaryFeature σ w x) (boundaryFeature σ w y) ≤
    stabilityConstant σ A B * dist x y
  simpa only [dist_eq_norm] using norm_boundaryFeature_sub_le σ hA hB w x y

/-- Collapsing the diagonal does not change the uniform weight bound. -/
theorem norm_boundaryFeature_le (σ : ℝ) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (x : BoundaryTransport.Space) : ‖boundaryFeature σ w x‖ ≤ B := by
  cases x with
  | boundary => simpa only [boundaryFeature, norm_zero] using hB
  | point x => exact norm_weightedFeature_le σ w x.1

/-- The zero extension is Bochner integrable under every finite measure on the collapsed space. -/
theorem integrable_boundaryFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (ρ : Measure BoundaryTransport.Space)
    [IsFiniteMeasure ρ] : Integrable (boundaryFeature σ w) ρ := by
  exact (integrable_const B).mono'
    (lipschitz_boundaryFeature σ hA hB w).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_boundaryFeature_le σ hB w x)

/-- The first endpoint is integrable for any finite plan, irrespective of its cost. -/
theorem integrable_planFirst_weightedFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (π : Measure BoundaryTransport.PlanSpace)
    [IsFiniteMeasure π] : Integrable (fun z => weightedFeature σ w z.1.1.1) π := by
  have hc : Continuous (fun z : BoundaryTransport.PlanSpace => weightedFeature σ w z.1.1.1) :=
    (continuous_weightedFeature σ hA hB w).comp
      (continuous_subtype_val.comp continuous_subtype_val.fst)
  exact (integrable_const B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => norm_weightedFeature_le σ w z.1.1.1)

/-- The second endpoint is integrable for any finite plan, irrespective of its cost. -/
theorem integrable_planSecond_weightedFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (π : Measure BoundaryTransport.PlanSpace)
    [IsFiniteMeasure π] : Integrable (fun z => weightedFeature σ w z.1.2.1) π := by
  have hc : Continuous (fun z : BoundaryTransport.PlanSpace => weightedFeature σ w z.1.2.1) :=
    (continuous_weightedFeature σ hA hB w).comp
      (continuous_subtype_val.comp continuous_subtype_val.snd)
  exact (integrable_const B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => norm_weightedFeature_le σ w z.1.2.1)

private theorem restricted_endpoint_map
    (π : Measure BoundaryTransport.PlanSpace) (μ : Measure BoundaryTransport.Interior)
    (e : BoundaryTransport.PlanSpace → BoundaryTransport.ClosedHalfPlane) (he : Measurable e)
    (hm : ∀ s, MeasurableSet s → π (e ⁻¹' (BoundaryTransport.interiorIncl '' s)) = μ s) :
    (π.map e).restrict (range BoundaryTransport.interiorIncl) =
      μ.map BoundaryTransport.interiorIncl := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, Measure.map_apply he
    (hs.inter BoundaryTransport.measurableEmbedding_interiorIncl.measurableSet_range),
    Measure.map_apply BoundaryTransport.measurableEmbedding_interiorIncl.measurable hs]
  have hset : s ∩ range BoundaryTransport.interiorIncl =
      BoundaryTransport.interiorIncl '' (BoundaryTransport.interiorIncl ⁻¹' s) := by
    ext x
    simp only [mem_inter_iff, mem_range, mem_image, mem_preimage]
    constructor
    · rintro ⟨hx, y, rfl⟩
      exact ⟨y, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y, rfl⟩
  rw [hset]
  exact hm _ (BoundaryTransport.measurableEmbedding_interiorIncl.measurable hs)

private theorem integral_endpoint_weightedFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B)
    (π : Measure BoundaryTransport.PlanSpace) (μ : Measure BoundaryTransport.Interior)
    (e : BoundaryTransport.PlanSpace → BoundaryTransport.ClosedHalfPlane) (he : Measurable e)
    (hm : ∀ s, MeasurableSet s → π (e ⁻¹' (BoundaryTransport.interiorIncl '' s)) = μ s) :
    (∫ z, weightedFeature σ w (e z).1 ∂π) = weightedPersistenceEmbedding σ (upperWeight w) μ := by
  have hF : Continuous (fun x : BoundaryTransport.ClosedHalfPlane => weightedFeature σ w x.1) :=
    (continuous_weightedFeature σ hA hB w).comp continuous_subtype_val
  rw [← integral_map he.aemeasurable hF.aestronglyMeasurable]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range BoundaryTransport.interiorIncl)
    (fun x hx => ?_)]
  · rw [restricted_endpoint_map π μ e he hm,
      integral_map BoundaryTransport.measurableEmbedding_interiorIncl.measurable.aemeasurable
        hF.aestronglyMeasurable,
      weightedPersistenceEmbedding_eq_integral_native σ hA w μ]
    rfl
  · have hn : ¬ x.1.1 < x.1.2 := by
      intro h
      exact hx ⟨⟨x.1, h⟩, rfl⟩
    have heq : x.1.1 = x.1.2 := le_antisymm x.2 (le_of_not_gt hn)
    rw [show x.1 = (x.1.1, x.1.1) from Prod.ext rfl heq.symm]
    exact weightedFeature_diagonal σ w _

/-- The actual first interior marginal identifies the first endpoint integral. -/
theorem integral_planFirst_weightedFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B)
    {π : Measure BoundaryTransport.PlanSpace} {μ ν : Measure BoundaryTransport.Interior}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : BoundaryTransport.IsBoundaryPlan π μ ν) :
    (∫ z, weightedFeature σ w z.1.1.1 ∂π) = weightedPersistenceEmbedding σ (upperWeight w) μ := by
  exact integral_endpoint_weightedFeature σ hA hB w π μ (fun z => z.1.1)
    (by fun_prop) hπ.first

/-- The actual second interior marginal identifies the second endpoint integral. -/
theorem integral_planSecond_weightedFeature (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B)
    {π : Measure BoundaryTransport.PlanSpace} {μ ν : Measure BoundaryTransport.Interior}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hπ : BoundaryTransport.IsBoundaryPlan π μ ν) :
    (∫ z, weightedFeature σ w z.1.2.1 ∂π) = weightedPersistenceEmbedding σ (upperWeight w) ν := by
  exact integral_endpoint_weightedFeature σ hA hB w π ν (fun z => z.1.2)
    (by fun_prop) hπ.second

end TDA.Persistence.WeightedKernel
