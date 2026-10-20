import TDA.Persistence.GaussianUniversality
import TDA.Persistence.WeightedPersistenceMeasure

/-!
# Consumers and boundary cases for Gaussian measure recovery

The countable diagram below has one unit atom at each `(0, 2⁻ⁿ)`. Its total
mass is infinite, it is locally finite in the open half-plane, and persistence
weighting makes its mass finite. The remaining examples exercise actual signed
integration, C₀ section approximation, and the zero-bandwidth/zero-weight limits.
-/

noncomputable section

namespace TDA.Persistence.GaussianUniversalityExamples

open MeasureTheory WeightedKernel Set Filter _root_.Topology
open scoped ZeroAtInfty ENNReal

/-- A signed pair of distinct atoms is detected by the actual Gaussian integral. -/
theorem signed_pair_detected :
    signedEmbedding 1 (VectorMeasure.dirac ((0 : ℝ), (1 : ℝ)) 1 -
      VectorMeasure.dirac ((0 : ℝ), (2 : ℝ)) 1) ≠ 0 := by
  intro hemb
  have h := (signedEmbedding_eq_zero_iff (by norm_num : (1 : ℝ) ≠ 0) _).1 hemb
  have hx := congrArg (fun μ : SignedMeasure (ℝ × ℝ) => μ {((0 : ℝ), (1 : ℝ))}) h
  norm_num [sub_apply, VectorMeasure.dirac] at hx

/-- The public norm/energy identity gives strictly positive signed energy for this pair. -/
theorem signed_pair_energy_pos :
    let μ : SignedMeasure (ℝ × ℝ) :=
      VectorMeasure.dirac ((0 : ℝ), (1 : ℝ)) 1 -
        VectorMeasure.dirac ((0 : ℝ), (2 : ℝ)) 1
    0 < ∫ᵛ p, (∫ᵛ q, kernel 1 p q ∂<•μ) ∂<•μ := by
  dsimp only
  rw [← norm_signedEmbedding_sq]
  exact sq_pos_of_pos (norm_pos_iff.2 signed_pair_detected)

/-- Distinct Dirac probability laws are separated through the probability API. -/
theorem probability_atoms_detected :
    positiveEmbedding 1 (Measure.dirac ((0 : ℝ), (1 : ℝ))) ≠
      positiveEmbedding 1 (Measure.dirac ((0 : ℝ), (2 : ℝ))) := by
  intro h
  have heq := probabilityEmbedding_injective (by norm_num : (1 : ℝ) ≠ 0) _ _ h
  have hx := congrArg (fun μ : Measure (ℝ × ℝ) => μ {((0 : ℝ), (1 : ℝ))}) heq
  norm_num [Measure.dirac_apply'] at hx

/-- A concrete diffuse probability law on the full birth–death plane. -/
def diffusePlaneLaw : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)

instance diffusePlaneLaw_probability : IsProbabilityMeasure diffusePlaneLaw := by
  unfold diffusePlaneLaw
  infer_instance

instance diffusePlaneLaw_noAtoms : NullSingletonClass diffusePlaneLaw := by
  have := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0)
    (by norm_num : (1 : NNReal) ≠ 0)
  unfold diffusePlaneLaw
  infer_instance

instance diffusePlaneLaw_openPositive : diffusePlaneLaw.IsOpenPosMeasure := by
  have : (ProbabilityTheory.gaussianReal 0 1).IsOpenPosMeasure :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0
      (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  unfold diffusePlaneLaw
  infer_instance

/-- Negating this diffuse law gives a non-atomic finite signed Radon input. -/
def diffuseSignedMeasure : SignedMeasure (ℝ × ℝ) := -diffusePlaneLaw.toSignedMeasure

/-- The signed witness retains the diffuse law as its total variation. -/
theorem diffuseSignedMeasure_totalVariation :
    diffuseSignedMeasure.totalVariation = diffusePlaneLaw := by
  rw [SignedMeasure.totalVariation_eq_variation]
  simp [diffuseSignedMeasure]

/-- The diffuse signed witness has Radon total variation. -/
theorem diffuseSignedMeasure_regular : diffuseSignedMeasure.totalVariation.Regular := by
  rw [diffuseSignedMeasure_totalVariation]
  infer_instance

/-- The signed witness has no atoms in its total variation. -/
theorem diffuseSignedMeasure_nonAtomic (p : ℝ × ℝ) :
    diffuseSignedMeasure.totalVariation {p} = 0 := by
  rw [diffuseSignedMeasure_totalVariation]
  simp

/-- This finite signed measure has positive variation outside every compact subset. -/
theorem diffuseSignedMeasure_noncompactSupport (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    0 < diffuseSignedMeasure.totalVariation Kᶜ := by
  rw [diffuseSignedMeasure_totalVariation]
  apply hK.isClosed.isOpen_compl.measure_pos diffusePlaneLaw
  apply nonempty_iff_ne_empty.2
  intro he
  exact hK.ne_univ (compl_empty_iff.1 he)

/-- The actual signed integral agrees with negating the positive Bochner mean. -/
theorem diffuseSignedMeasure_mean :
    signedEmbedding 1 diffuseSignedMeasure = -positiveEmbedding 1 diffusePlaneLaw := by
  simpa only [diffuseSignedMeasure, zero_sub, signedEmbedding_zero,
    signedEmbedding_toSignedMeasure] using
      signedEmbedding_sub 1 0 diffusePlaneLaw.toSignedMeasure

/-- General signed injectivity detects this non-atomic input with noncompact support. -/
theorem diffuseSignedMeasure_detected : signedEmbedding 1 diffuseSignedMeasure ≠ 0 := by
  intro hemb
  have h := (signedEmbedding_eq_zero_iff (by norm_num : (1 : ℝ) ≠ 0) _).1 hemb
  have hmass := congrArg (fun μ : SignedMeasure (ℝ × ℝ) => μ univ) h
  norm_num [diffuseSignedMeasure, neg_apply, Measure.toSignedMeasure_apply] at hmass

/-- Coincident atoms with unequal positive multiplicities have unequal actual means. -/
theorem unequal_multiplicities_detected :
    signedEmbedding 1 (VectorMeasure.dirac ((0 : ℝ), (1 : ℝ)) 1) ≠
      signedEmbedding 1 (VectorMeasure.dirac ((0 : ℝ), (1 : ℝ)) 2) := by
  intro h
  have heq := signedEmbedding_injective (by norm_num : (1 : ℝ) ≠ 0) h
  have hmass := congrArg (fun μ : SignedMeasure (ℝ × ℝ) => μ univ) heq
  norm_num [VectorMeasure.dirac] at hmass

/-- Gaussian sections themselves give a nonzero member of the C₀ image. -/
theorem section_nonzero : gaussianSection (by norm_num : (1 : ℝ) ≠ 0) (0, 1) ≠ 0 := by
  intro h
  have hp := congrArg (fun f : C₀(ℝ × ℝ, ℝ) => f (0, 1)) h
  simp [gaussianSection_apply, kernel_self] at hp

/-- The actual RKHS feature gives the same C₀ section through the public evaluation API. -/
theorem feature_c0_agrees (p : ℝ × ℝ) :
    rkhsToC0 (by norm_num : (1 : ℝ) ≠ 0) (featureAt 1 p) =
      gaussianSection (by norm_num : (1 : ℝ) ≠ 0) p := by
  ext q
  simp only [rkhsToC0_apply, featureAt_apply, gaussianSection_apply]

/-- A section with a different bandwidth admits uniform approximation by bandwidth-one
sections; the approximation theorem has no finite-support premise on the target. -/
theorem approximate_other_bandwidth :
    ∃ g ∈ Submodule.span ℝ (range (gaussianSection (by norm_num : (1 : ℝ) ≠ 0))),
      ‖g - gaussianSection (by norm_num : (2 : ℝ) ≠ 0) (0, 1)‖ < (1 / 100 : ℝ) :=
  exists_gaussian_span_approx (by norm_num) _ (by norm_num)

/-- The diagram accumulates only at the excluded diagonal in the full plane. -/
def diagonalAtom (n : ℕ) : UpperPoint :=
  ⟨(0, (1 / 2 : ℝ) ^ n), by positivity⟩

private theorem diagonalAtom_limit :
    Tendsto (fun n => (diagonalAtom n).1) atTop (𝓝 ((0 : ℝ), (0 : ℝ))) := by
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).prodMk_nhds
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))

/-- The same sequence escapes every compact subset of the open half-plane. -/
theorem diagonalAtom_escape : Tendsto diagonalAtom atTop (cocompact UpperPoint) := by
  apply tendsto_def.2
  intro s hs
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 hs
  have hclosed : IsClosed (Subtype.val '' K : Set (ℝ × ℝ)) :=
    (hK.image continuous_subtype_val).isClosed
  have hnot : ((0 : ℝ), (0 : ℝ)) ∉ (Subtype.val '' K : Set (ℝ × ℝ)) := by
    rintro ⟨p, _, hp⟩
    have hpos := p.2
    rw [hp] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have hev := diagonalAtom_limit.eventually (hclosed.isOpen_compl.mem_nhds hnot)
  filter_upwards [hev] with n hn
  apply hKs
  intro hnK
  exact hn ⟨diagonalAtom n, hnK, rfl⟩

/-- Restricting a Gaussian section to the open half-plane does not make it a C₀ function:
the excluded diagonal is an additional end of this space. -/
theorem restricted_section_not_c0 :
    ¬ ∃ f : C₀(UpperPoint, ℝ), ∀ p, f p = kernel 1 p.1 (0, 1) := by
  rintro ⟨f, hf⟩
  have hz := (zero_at_infty f).comp diagonalAtom_escape
  have hc : Continuous (fun p : ℝ × ℝ => kernel 1 p (0, 1)) := by
    unfold kernel
    fun_prop
  have hk := (hc.tendsto ((0 : ℝ), (0 : ℝ))).comp diagonalAtom_limit
  have heq : (fun n => f (diagonalAtom n)) =
      fun n => kernel 1 (diagonalAtom n).1 (0, 1) := funext fun n => hf _
  change Tendsto (fun n => f (diagonalAtom n)) atTop (𝓝 0) at hz
  rw [heq] at hz
  have hzero := tendsto_nhds_unique hk hz
  exact (Real.exp_pos _).ne' hzero

/-- One unit of mass at every occurrence of the diagonal-accumulating diagram. -/
def infiniteDiagramMeasure : Measure UpperPoint :=
  countableDiagramMeasure diagonalAtom

theorem infiniteDiagramMeasure_univ : infiniteDiagramMeasure univ = ∞ := by
  simp [infiniteDiagramMeasure, countableDiagramMeasure, Measure.sum_apply,
    ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num : (1 : ENNReal) ≠ 0)]

/-- Persistence is a continuous strictly positive weight on the open finite-bar plane. -/
def persistenceWeight (p : UpperPoint) : ℝ := p.1.2 - p.1.1

theorem persistenceWeight_continuous : Continuous persistenceWeight := by
  unfold persistenceWeight
  fun_prop

theorem persistenceWeight_pos (p : UpperPoint) : 0 < persistenceWeight p :=
  sub_pos.2 p.2

/-- A concrete positive finite bar for the finite and zero-weight controls. -/
def unitBar : UpperPoint := ⟨(0, 1), by norm_num⟩

/-- Coincident occurrences contribute twice to the actual positive-measure mean. -/
theorem two_coincident_weighted_atoms :
    weightedPersistenceEmbedding 1 persistenceWeight
        (Measure.sum fun _ : Fin 2 => Measure.dirac unitBar) =
      (2 : ℝ) • featureAt 1 (0, 1) := by
  rw [weightedPersistenceEmbedding_finite 1 persistenceWeight (fun _ : Fin 2 => unitBar)
    (fun _ => (persistenceWeight_pos unitBar).le)]
  norm_num [unitBar, persistenceWeight, Fin.sum_univ_two, two_smul]

/-- Infinite original mass is compatible with finite persistence-weighted mass. -/
theorem infiniteDiagramMeasure_weighted_finite :
    (∫⁻ p, ENNReal.ofReal (persistenceWeight p) ∂infiniteDiagramMeasure) < ∞ := by
  rw [infiniteDiagramMeasure, countableDiagramMeasure_weighted_mass]
  simp only [persistenceWeight, diagonalAtom, sub_zero]
  exact (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).tsum_ofReal_lt_top

/-- Every point has a neighborhood containing only finitely many atoms. -/
instance infiniteDiagramMeasure_locallyFinite : IsLocallyFiniteMeasure infiniteDiagramMeasure where
  finiteAtNhds p := by
    let V : Set UpperPoint := {q | persistenceWeight p / 2 < persistenceWeight q}
    have hV : IsOpen V := isOpen_lt continuous_const persistenceWeight_continuous
    have hpV : p ∈ V := by dsimp [V]; linarith [persistenceWeight_pos p]
    have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually_lt_const
      (by linarith [persistenceWeight_pos p] : 0 < persistenceWeight p / 2))
    refine ⟨V, hV.mem_nhds hpV, ?_⟩
    calc
      infiniteDiagramMeasure V = ∑ n ∈ Finset.range N, Measure.dirac (diagonalAtom n) V := by
        rw [infiniteDiagramMeasure, countableDiagramMeasure, Measure.sum_apply _ hV.measurableSet]
        apply tsum_eq_sum
        intro n hn
        have hnot : diagonalAtom n ∉ V := by
          dsimp [V, persistenceWeight, diagonalAtom]
          have hnN : N ≤ n := by simpa using hn
          have ht := hN n hnN
          dsimp [persistenceWeight] at ht
          linarith
        simp [Measure.dirac_apply' _ hV.measurableSet, hnot]
      _ < ∞ := ENNReal.sum_lt_top.2 fun n hn => measure_lt_top _ _

/-- The countable example is a Radon measure on the open half-plane. -/
theorem infiniteDiagramMeasure_regular : infiniteDiagramMeasure.Regular := inferInstance

/-- The weighted Gaussian embedding recovers this Radon diagram of infinite total mass among
all positive measures of finite persistence-weighted mass. -/
theorem recover_infiniteDiagram (ν : Measure UpperPoint)
    (hν : (∫⁻ p, ENNReal.ofReal (persistenceWeight p) ∂ν) < ∞) :
    weightedPersistenceEmbedding 1 persistenceWeight infiniteDiagramMeasure =
      weightedPersistenceEmbedding 1 persistenceWeight ν ↔ infiniteDiagramMeasure = ν :=
  weightedPersistenceEmbedding_eq_iff (by norm_num) persistenceWeight
    persistenceWeight_continuous.measurable persistenceWeight_pos _ _
    infiniteDiagramMeasure_weighted_finite hν

/-- A zero weight loses all measure information. -/
theorem zero_weight_all_equal (σ : ℝ) (μ ν : Measure UpperPoint) :
    weightedPersistenceEmbedding σ (fun _ => 0) μ =
      weightedPersistenceEmbedding σ (fun _ => 0) ν := by
  simp [weightedPersistenceEmbedding, weightedPlaneMeasure]

/-- The zero-weight map really is noninjective on positive measures. -/
theorem zero_weight_not_injective (σ : ℝ) :
    ¬ Function.Injective (weightedPersistenceEmbedding σ (fun _ => 0)) := by
  intro hinj
  have heq := hinj (zero_weight_all_equal σ 0 (Measure.dirac unitBar))
  have hmass := congrArg (fun μ : Measure UpperPoint => μ univ) heq
  simp at hmass

/-- At zero bandwidth two distinct atoms have the same actual signed mean. -/
theorem zero_bandwidth_atoms_equal :
    signedEmbedding 0 (VectorMeasure.dirac ((0 : ℝ), (1 : ℝ)) 1) =
      signedEmbedding 0 (VectorMeasure.dirac ((0 : ℝ), (2 : ℝ)) 1) := by
  simp only [signedEmbedding_dirac, one_smul]
  apply RKHS.ext
  intro p
  simp [featureAt_apply, kernel]

/-- Zero bandwidth does not identify finite signed measures. -/
theorem zero_bandwidth_not_injective : ¬ Function.Injective (signedEmbedding 0) := by
  intro hinj
  have heq := hinj zero_bandwidth_atoms_equal
  have hatom := congrArg
    (fun μ : SignedMeasure (ℝ × ℝ) => μ {((0 : ℝ), (1 : ℝ))}) heq
  norm_num [VectorMeasure.dirac] at hatom

end TDA.Persistence.GaussianUniversalityExamples
