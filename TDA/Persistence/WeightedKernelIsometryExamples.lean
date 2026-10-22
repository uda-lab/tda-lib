import TDA.Persistence.WeightedKernelIsometry
import TDA.Persistence.WeightedKernelExamples
import TDA.Persistence.WeightedKernelInjectivityExamples

/-!
# Weighted-kernel isometry consumers and boundary controls

Nonconstant arctan weights, arbitrary completed-space elements, weights approaching
zero, repeated occurrences, zero bandwidth, a vanishing-weight obstruction and
finite/essential diagram boundaries exercise the RKHS equivalence.
-/

namespace TDA.Persistence.WeightedKernelIsometryExamples

open WeightedKernel KernelWeight
open WeightedKernelExamples (singletonDiagram)
open scoped InnerProductSpace

private noncomputable abbrev w := PersistenceImage.arctanWeight 1 (by norm_num)
private def p : UpperPoint := ⟨(0, 1), by norm_num⟩
private def q : UpperPoint := ⟨(0, 2), by norm_num⟩
private def r : UpperPoint := ⟨(0, 3), by norm_num⟩
private theorem hw (x : UpperPoint) : 0 < upperWeight w x :=
  upperWeight_arctan_pos (by norm_num) x
private noncomputable abbrev T (σ : ℝ) : UpperSpace σ ≃ₗᵢ[ℝ] WeightedUpperSpace σ w :=
  upperWeightIsometry σ w hw

private theorem weight_value (x : UpperPoint) :
    upperWeight w x = Real.arctan (x.val.2 - x.val.1) :=
  PersistenceImage.arctanWeight_birthPersistence 1 (by norm_num) x.property.le |>.trans
    (by simp)

/-- The multiplier is read at the evaluation point. -/
theorem arctan_feature_evaluation :
    T 1 (baseFeature (upperKernel 1) p) q = Real.arctan 2 * Real.exp (-1 / 2) := by
  rw [upperWeightIsometry_apply, baseFeature_apply, weight_value]
  norm_num [upperKernel, kernel, p, q]

/-- A weighted base section maps to the weighted-kernel section at the same center. -/
theorem arctan_center_section :
    T 1 (Real.arctan 1 • baseFeature (upperKernel 1) p) =
      weightedFeature (upperKernel 1) (upperWeight w) p := by
  have h := weightIsometry_smul_baseFeature (upperKernel 1) (upperWeight w)
    (fun x => (hw x).ne') p
  simpa only [weight_value, p, sub_zero, T, upperWeightIsometry] using h

/-- Inverse evaluation uses division, and the completed map preserves the section norm. -/
theorem arctan_section_inverse_norm :
    (T 1).symm (weightedFeature (upperKernel 1) (upperWeight w) p) q =
      weightedFeature (upperKernel 1) (upperWeight w) p q / Real.arctan 2 ∧
    ‖T 1 (baseFeature (upperKernel 1) p)‖ = ‖baseFeature (upperKernel 1) p‖ := by
  constructor
  · simpa [T, arctanUpperWeightIsometry, weight_value, q] using
      upperWeightIsometry_symm_apply 1 w (upperWeight_arctan_pos (by norm_num))
        (weightedFeature (upperKernel 1) (upperWeight w) p) q
  · exact (T 1).norm_map _

/-- The formulas and inverse identities hold beyond the dense finite sums. -/
theorem arctan_completed_inverse (f : UpperSpace 1) (F : WeightedUpperSpace 1 w)
    (x : UpperPoint) :
    T 1 f x = upperWeight w x * f x ∧
    (T 1).symm F x = F x / upperWeight w x ∧
    (T 1).symm (T 1 f) = f ∧ T 1 ((T 1).symm F) = F := by
  exact ⟨upperWeightIsometry_apply 1 w hw f x,
    upperWeightIsometry_symm_apply 1 w hw F x,
    (T 1).symm_apply_apply f, (T 1).apply_symm_apply F⟩

/-- The intended source weight has no uniform positive lower bound. -/
theorem arctan_weights_approach_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ x : UpperPoint, 0 < upperWeight w x ∧ upperWeight w x < ε := by
  let x : UpperPoint := ⟨(0, ε / 2), by dsimp; linarith⟩
  refine ⟨x, upperWeight_arctan_pos (by norm_num) x, ?_⟩
  have h := w.lipschitz (birthPersistence x.val) (0, 0)
  have hz := w.zero_persistence 0
  have hn := w.nonneg (birthPersistence x.val)
  simp only [hz, sub_zero, abs_of_nonneg hn] at h
  have hx : ‖birthPersistence x.val - (0, 0)‖ = ε / 2 := by
    simp [x, birthPersistence, Prod.norm_def, abs_of_pos hε,
      max_eq_right (by linarith : 0 ≤ ε / 2)]
  rw [hx] at h
  change w (birthPersistence x.val) < ε
  linarith

private def twice : Fin 2 → UpperPoint := fun _ => q
private def once : Unit → UpperPoint := fun _ => r

private theorem finite_distance_formula (σ : ℝ) :
    ‖embedding σ w (fun i => (twice i).val) -
      embedding σ w (fun j => (once j).val)‖ ^ 2 =
    4 * (Real.arctan 2) ^ 2 + (Real.arctan 3) ^ 2 -
      4 * Real.arctan 2 * Real.arctan 3 * Real.exp (-1 / (2 * σ ^ 2)) := by
  rw [norm_embedding_sub_sq]
  norm_num [linearKernel, twice, once, w, PersistenceImage.arctanWeight_apply,
    birthPersistence, q, r, Fin.sum_univ_two, kernel]
  ring

/-- Repeated labels and unequal cardinalities retain their exact cross term. -/
theorem repeated_arctan_distance :
    ‖weightedUpperEmbedding 1 w twice - weightedUpperEmbedding 1 w once‖ ^ 2 =
      4 * (Real.arctan 2) ^ 2 + (Real.arctan 3) ^ 2 -
        4 * Real.arctan 2 * Real.arctan 3 * Real.exp (-1 / 2) ∧
    ‖embedding 1 w (fun i => (twice i).val) -
      embedding 1 w (fun j => (once j).val)‖ ^ 2 =
      4 * (Real.arctan 2) ^ 2 + (Real.arctan 3) ^ 2 -
        4 * Real.arctan 2 * Real.arctan 3 * Real.exp (-1 / 2) := by
  have h := finite_distance_formula 1
  simp only [one_pow, mul_one] at h
  exact ⟨by rw [norm_weightedUpperEmbedding_sub]; exact h, h⟩

/-- The exact repeated-occurrence distance is genuinely positive. -/
theorem repeated_arctan_distance_pos :
    0 < ‖weightedUpperEmbedding 1 w twice - weightedUpperEmbedding 1 w once‖ ^ 2 := by
  rw [repeated_arctan_distance.1]
  have h₂ : 0 < Real.arctan 2 := Real.arctan_pos.mpr (by norm_num)
  have h₃ : 0 < Real.arctan 3 := Real.arctan_pos.mpr (by norm_num)
  have he : Real.exp (-1 / 2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hp := mul_pos (mul_pos h₂ h₃) (sub_pos.mpr he)
  nlinarith [sq_nonneg (2 * Real.arctan 2 - Real.arctan 3)]

/-- Zero bandwidth retains the completed isometry and collapses sums to total weight. -/
theorem zero_bandwidth_distance :
    (T 0).symm (T 0 (upperEmbedding 0 w twice)) = upperEmbedding 0 w twice ∧
    ‖weightedUpperEmbedding 0 w twice - weightedUpperEmbedding 0 w once‖ ^ 2 =
      (2 * Real.arctan 2 - Real.arctan 3) ^ 2 := by
  refine ⟨(T 0).symm_apply_apply _, ?_⟩
  rw [norm_weightedUpperEmbedding_sub, finite_distance_formula]
  norm_num
  ring

private noncomputable def finiteKernel : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => kernel 1 (WeightedKernelExamples.pair i) (WeightedKernelExamples.pair j)

private instance : Fact finiteKernel.PosSemidef := ⟨WeightedKernelExamples.pair_posSemidef⟩
private def erasingWeight : Fin 2 → ℝ := ![0, 1]
private noncomputable def obstruction : BaseSpace finiteKernel :=
  baseFeature finiteKernel 0 - Real.exp (-1 / 2) • baseFeature finiteKernel 1

private theorem finiteKernel_value (i j : Fin 2) :
    finiteKernel i j = if i = j then 1 else Real.exp (-1 / 2) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [finiteKernel, WeightedKernelExamples.pair, kernel]

/-- A nonzero base vector is killed by pointwise multiplication when a weight vanishes. -/
theorem vanishing_weight_obstruction :
    ‖obstruction‖ ^ 2 = 1 - (Real.exp (-1 / 2)) ^ 2 ∧
    0 < ‖obstruction‖ ^ 2 ∧
    ∀ i, erasingWeight i * obstruction i = 0 := by
  have hn : ‖obstruction‖ ^ 2 = 1 - (Real.exp (-1 / 2)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [obstruction, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, inner_baseFeature, finiteKernel_value, ite_true,
      if_neg (show (0 : Fin 2) ≠ 1 by decide), if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    ring
  refine ⟨hn, ?_, ?_⟩
  · rw [hn]
    have hp := Real.exp_pos (-1 / 2)
    have he : Real.exp (-1 / 2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    nlinarith
  · intro i
    fin_cases i <;>
      simp [erasingWeight, obstruction, RKHS.coe_sub, RKHS.coe_smul,
        baseFeature_apply, finiteKernel_value]

/-- There can be no multiplication isometry in the vanishing-weight example. -/
theorem no_vanishing_weight_isometry :
    ¬ ∃ S : BaseSpace finiteKernel ≃ₗᵢ[ℝ] WeightedSpace finiteKernel erasingWeight,
      ∀ (F : BaseSpace finiteKernel) (i : Fin 2), S F i = erasingWeight i * F i := by
  rintro ⟨S, hS⟩
  have hz : S obstruction = 0 := by
    apply RKHS.ext
    intro i
    rw [hS, vanishing_weight_obstruction.2.2]
    simp
  have hn : ‖obstruction‖ = 0 := by
    rw [← S.norm_map obstruction, hz, norm_zero]
  have hp := vanishing_weight_obstruction.2.1
  rw [hn] at hp
  norm_num at hp

private def finiteEssential := WeightedKernelInjectivityExamples.finiteEssentialDiagram
private def finiteOnly := singletonDiagram 0 2 (by norm_num)
private def essentialOnly := WeightedKernelExamples.essentialOnly
private theorem finiteEssential_positive : finiteEssential.IsPositive := by
  intro z hz
  have hz' : z = ((0 : ℝ), (2 : WithTop ℝ)) ∨ z = ((0 : ℝ), (⊤ : WithTop ℝ)) := by
    simpa [finiteEssential, WeightedKernelInjectivityExamples.finiteEssentialDiagram] using hz
  rcases hz' with rfl | rfl <;> norm_num
private theorem finiteOnly_positive : finiteOnly.IsPositive := by
  intro z hz
  have hz' : z = ((0 : ℝ), (2 : WithTop ℝ)) := by simpa [finiteOnly, singletonDiagram] using hz
  subst z
  norm_num
private theorem essentialOnly_positive : essentialOnly.IsPositive := by
  intro z hz
  have hz' : z = ((0 : ℝ), (⊤ : WithTop ℝ)) := by
    simpa [essentialOnly, WeightedKernelExamples.essentialOnly] using hz
  subst z
  simp

/-- Essential bars remain absent from the weighted-upper representation. -/
theorem essential_parts_omitted :
    weightedUpperDiagramEmbedding 1 w finiteEssential finiteEssential_positive =
      weightedUpperDiagramEmbedding 1 w finiteOnly finiteOnly_positive ∧
    weightedUpperDiagramEmbedding 1 w essentialOnly essentialOnly_positive = 0 ∧
    ‖weightedUpperDiagramEmbedding 1 w finiteEssential finiteEssential_positive -
      weightedUpperDiagramEmbedding 1 w essentialOnly essentialOnly_positive‖ =
      ‖diagramEmbedding 1 w finiteEssential - diagramEmbedding 1 w essentialOnly‖ := by
  refine ⟨?_, ?_, norm_weightedUpperDiagramEmbedding_sub 1 w _ _ _ _⟩
  · apply norm_sub_eq_zero_iff.mp
    rw [norm_weightedUpperDiagramEmbedding_sub]
    rw [diagramEmbedding_eq_sum, diagramEmbedding_eq_sum,
      show finitePart finiteEssential.points = {(0, 2)} from rfl,
      show finitePart finiteOnly.points = {(0, 2)} from rfl]
    simp
  · apply norm_eq_zero.mp
    apply (sq_eq_zero_iff).mp
    rw [← real_inner_self_eq_norm_sq, inner_weightedUpperDiagramEmbedding]
    rw [diagramEmbedding_eq_sum, show finitePart essentialOnly.points = 0 from rfl]
    simp

/-- An empty finite input needs no nonemptiness hypothesis. -/
theorem empty_weighted_upper :
    weightedUpperEmbedding 1 w (Fin.elim0 : Fin 0 → UpperPoint) = 0 := by
  simp [weightedUpperEmbedding]

end TDA.Persistence.WeightedKernelIsometryExamples
