import TDA.Persistence.GaussianFeature
import TDA.Persistence.WeightedKernel
import TDA.Persistence.PersistenceImageDiagram
import TDA.Persistence.ArctanWeight
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Multiplication isometry for weighted kernels

For a real positive semidefinite kernel and a nowhere-zero weight, multiplication
by the weight identifies the completed RKHSs by a linear isometry equivalence.
This proves the multiplication claim of KFH18 Proposition 7 without requiring
C₀-universality. The Gaussian specialization uses the open upper half-plane;
its finite-sum norms agree with the existing full-plane diagram embedding.
No full-plane restriction isomorphism or essential-bar feature is asserted.
-/

namespace TDA.Persistence.WeightedKernel

open scoped InnerProductSpace
open Submodule

namespace KernelWeight

variable {X : Type*}

/-- A scalar kernel acting on the scalar output space. -/
noncomputable def scalarOp (k : Matrix X X ℝ) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => k x y • ContinuousLinearMap.id ℝ ℝ

/-- Weight both arguments of a scalar kernel. -/
noncomputable def weightedKernel (k : Matrix X X ℝ) (g : X → ℝ) : Matrix X X ℝ :=
  Matrix.of fun x y => g x * k x y * g y

theorem posSemidef_weightedKernel (k : Matrix X X ℝ) [Fact k.PosSemidef] (g : X → ℝ) :
    (weightedKernel k g).PosSemidef :=
  posSemidef_diag_mul_mul_diag Fact.out g

instance fact_posSemidef_weightedKernel (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) : Fact (weightedKernel k g).PosSemidef :=
  ⟨posSemidef_weightedKernel k g⟩

instance fact_posSemidef_scalarOp (k : Matrix X X ℝ) [Fact k.PosSemidef] :
    Fact (scalarOp k).PosSemidef := ⟨posSemidef_scalarOp Fact.out⟩

/-- The scalar-output RKHS of a scalar kernel. -/
abbrev BaseSpace (k : Matrix X X ℝ) [Fact k.PosSemidef] := RKHS.OfKernel (scalarOp k)

/-- The RKHS of the weighted kernel, including weights with zeros. -/
abbrev WeightedSpace (k : Matrix X X ℝ) [Fact k.PosSemidef] (g : X → ℝ) :=
  BaseSpace (weightedKernel k g)

/-- The base kernel section centered at `x`. -/
noncomputable def baseFeature (k : Matrix X X ℝ) [Fact k.PosSemidef] (x : X) :
    BaseSpace k := RKHS.kerFun (BaseSpace k) x 1

/-- The weighted kernel section centered at `x`. -/
noncomputable def weightedFeature (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (x : X) : WeightedSpace k g := baseFeature (weightedKernel k g) x

theorem baseFeature_apply (k : Matrix X X ℝ) [Fact k.PosSemidef] (x z : X) :
    baseFeature k x z = k z x := by
  rw [baseFeature, RKHS.kerFun_apply, RKHS.OfKernel.kernel_ofKernel]
  simp [scalarOp]

theorem inner_baseFeature (k : Matrix X X ℝ) [Fact k.PosSemidef] (x y : X) :
    ⟪baseFeature k x, baseFeature k y⟫_ℝ = k x y := by
  change ⟪RKHS.kerFun (BaseSpace k) x 1, baseFeature k y⟫_ℝ = _
  rw [RKHS.kerFun_inner, baseFeature_apply, Real.inner_apply, one_mul]

theorem weightedFeature_apply (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (x z : X) : weightedFeature k g x z = g z * k z x * g x :=
  baseFeature_apply (weightedKernel k g) x z

theorem inner_weightedFeature (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (x y : X) :
    ⟪weightedFeature k g x, weightedFeature k g y⟫_ℝ = g x * k x y * g y :=
  inner_baseFeature (weightedKernel k g) x y

private noncomputable def baseSum (k : Matrix X X ℝ) [Fact k.PosSemidef] (g : X → ℝ) :
    (X →₀ ℝ) →ₗ[ℝ] BaseSpace k :=
  Finsupp.linearCombination ℝ (fun x => g x • baseFeature k x)

private noncomputable def weightedSum (k : Matrix X X ℝ) [Fact k.PosSemidef] (g : X → ℝ) :
    (X →₀ ℝ) →ₗ[ℝ] WeightedSpace k g :=
  Finsupp.linearCombination ℝ (weightedFeature k g)

private theorem norm_sums_eq (k : Matrix X X ℝ) [Fact k.PosSemidef] (g : X → ℝ)
    (μ : X →₀ ℝ) : ‖weightedSum k g μ‖ = ‖baseSum k g μ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [weightedSum, baseSum, Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left, real_inner_smul_right,
    inner_weightedFeature, inner_baseFeature]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem sums_eq_iff (k : Matrix X X ℝ) [Fact k.PosSemidef] (g : X → ℝ)
    (μ ν : X →₀ ℝ) : baseSum k g μ = baseSum k g ν ↔ weightedSum k g μ = weightedSum k g ν := by
  constructor
  · intro h
    apply norm_sub_eq_zero_iff.mp
    rw [← map_sub, norm_sums_eq, map_sub, h, sub_self, norm_zero]
  · intro h
    apply norm_sub_eq_zero_iff.mp
    rw [← map_sub, ← norm_sums_eq, map_sub, h, sub_self, norm_zero]

private theorem span_weighted_baseFeature (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0) :
    span ℝ (Set.range (fun x => g x • baseFeature k x)) =
      span ℝ (Set.range (baseFeature k)) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro f ⟨x, rfl⟩
    exact Submodule.smul_mem _ _ (subset_span ⟨x, rfl⟩)
  · apply span_le.mpr
    rintro f ⟨x, rfl⟩
    have h := Submodule.smul_mem
      (span ℝ (Set.range (fun x => g x • baseFeature k x))) (g x)⁻¹
      (subset_span (Set.mem_range_self x))
    simpa [smul_smul, inv_mul_cancel₀ (hg x)] using h

private theorem dense_baseSum (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0) : DenseRange (baseSum k g) := by
  change Dense (↑(LinearMap.range (baseSum k g)) : Set (BaseSpace k))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  have hs : span ℝ {RKHS.kerFun (BaseSpace k) x v | (x) (v)} ≤
      LinearMap.range (baseSum k g) := by
    apply span_le.mpr
    rintro f ⟨x, v, rfl⟩
    refine ⟨Finsupp.single x (v / g x), ?_⟩
    simp only [baseSum, Finsupp.linearCombination_single, smul_smul]
    rw [div_mul_cancel₀ _ (hg x)]
    simp [baseFeature, ← map_smul]
  have hc := Submodule.topologicalClosure_mono hs
  rw [RKHS.kerFun_dense] at hc
  exact hc

private theorem dense_weightedSum (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) : DenseRange (weightedSum k g) := by
  change Dense (↑(LinearMap.range (weightedSum k g)) : Set (WeightedSpace k g))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  have hs : span ℝ {RKHS.kerFun (WeightedSpace k g) x v | (x) (v)} ≤
      LinearMap.range (weightedSum k g) := by
    apply span_le.mpr
    rintro f ⟨x, v, rfl⟩
    refine ⟨Finsupp.single x v, ?_⟩
    simp [weightedSum, weightedFeature, baseFeature, ← map_smul]
  have hc := Submodule.topologicalClosure_mono hs
  rw [RKHS.kerFun_dense] at hc
  exact hc

/-- Multiplication by a nowhere-zero weight, extended from dense finite sums. -/
noncomputable def weightIsometry (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0) : BaseSpace k ≃ₗᵢ[ℝ] WeightedSpace k g :=
  (LinearEquiv.refl ℝ (X →₀ ℝ)).extendOfIsometry (baseSum k g) (weightedSum k g)
    (dense_baseSum k g hg) (dense_weightedSum k g) (norm_sums_eq k g)

theorem weightIsometry_smul_baseFeature (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0) (x : X) :
    weightIsometry k g hg (g x • baseFeature k x) = weightedFeature k g x := by
  have h := (LinearEquiv.refl ℝ (X →₀ ℝ)).extendOfIsometry_eq
    (baseSum k g) (weightedSum k g) (dense_baseSum k g hg) (dense_weightedSum k g)
    (norm_sums_eq k g) (Finsupp.single x 1)
  simpa [weightIsometry, baseSum, weightedSum] using h

theorem weightIsometry_apply (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0) (f : BaseSpace k) (x : X) :
    weightIsometry k g hg f x = g x * f x := by
  have h := (weightIsometry k g hg).inner_map_map (g x • baseFeature k x) f
  rw [weightIsometry_smul_baseFeature] at h
  simpa [weightedFeature, baseFeature, RKHS.kerFun_inner, real_inner_smul_left,
    Real.inner_apply] using h

theorem weightIsometry_symm_apply (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0) (F : WeightedSpace k g) (x : X) :
    (weightIsometry k g hg).symm F x = F x / g x := by
  have h := weightIsometry_apply k g hg ((weightIsometry k g hg).symm F) x
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact (eq_div_iff (hg x)).mpr (by simpa [mul_comm] using h.symm)

theorem weightIsometry_sum (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0) {I : Type*} [Fintype I]
    (x : I → X) (c : I → ℝ) :
    weightIsometry k g hg (∑ i, c i • (g (x i) • baseFeature k (x i))) =
      ∑ i, c i • weightedFeature k g (x i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, weightIsometry_smul_baseFeature]

theorem weightIsometry_unique (k : Matrix X X ℝ) [Fact k.PosSemidef]
    (g : X → ℝ) (hg : ∀ x, g x ≠ 0)
    (T : BaseSpace k ≃ₗᵢ[ℝ] WeightedSpace k g)
    (hT : ∀ (f : BaseSpace k) (x : X), T f x = g x * f x) :
    T = weightIsometry k g hg := by
  ext f x
  rw [hT, weightIsometry_apply]

end KernelWeight

/-- Birth–death points strictly above the diagonal. -/
abbrev UpperPoint := {p : ℝ × ℝ // p.1 < p.2}

/-- Restrict the Gaussian to the source's open upper half-plane. -/
noncomputable def upperKernel (σ : ℝ) : Matrix UpperPoint UpperPoint ℝ :=
  Matrix.of fun p q => kernel σ p.val q.val

theorem posSemidef_upperKernel (σ : ℝ) : (upperKernel σ).PosSemidef :=
  posSemidef_kernel_family σ Subtype.val

instance fact_posSemidef_upperKernel (σ : ℝ) : Fact (upperKernel σ).PosSemidef :=
  ⟨posSemidef_upperKernel σ⟩

/-- Read a persistence-image weight in birth–persistence coordinates. -/
noncomputable def upperWeight {A B : ℝ} (w : PersistenceImage.Weight A B)
    (p : UpperPoint) : ℝ := w (birthPersistence p.val)

/-- Gaussian RKHS on the open upper half-plane. -/
abbrev UpperSpace (σ : ℝ) := KernelWeight.BaseSpace (upperKernel σ)

/-- Weighted Gaussian RKHS on the same open upper half-plane. -/
abbrev WeightedUpperSpace {A B : ℝ} (σ : ℝ) (w : PersistenceImage.Weight A B) :=
  KernelWeight.WeightedSpace (upperKernel σ) (upperWeight w)

variable {A B : ℝ}

/-- KFH18 Proposition 7 on its positive domain, for every real bandwidth. -/
noncomputable def upperWeightIsometry (σ : ℝ) (w : PersistenceImage.Weight A B)
    (hw : ∀ p : UpperPoint, 0 < upperWeight w p) :
    UpperSpace σ ≃ₗᵢ[ℝ] WeightedUpperSpace σ w :=
  KernelWeight.weightIsometry (upperKernel σ) (upperWeight w) (fun p => (hw p).ne')

theorem upperWeightIsometry_apply (σ : ℝ) (w : PersistenceImage.Weight A B)
    (hw : ∀ p : UpperPoint, 0 < upperWeight w p) (f : UpperSpace σ) (p : UpperPoint) :
    upperWeightIsometry σ w hw f p = upperWeight w p * f p :=
  KernelWeight.weightIsometry_apply _ _ _ _ _

theorem upperWeightIsometry_symm_apply (σ : ℝ) (w : PersistenceImage.Weight A B)
    (hw : ∀ p : UpperPoint, 0 < upperWeight w p) (F : WeightedUpperSpace σ w)
    (p : UpperPoint) : (upperWeightIsometry σ w hw).symm F p = F p / upperWeight w p :=
  KernelWeight.weightIsometry_symm_apply _ _ _ _ _

/-- Weight a finite occurrence family in the upper-domain base RKHS. -/
noncomputable def upperEmbedding {I : Type*} [Fintype I] (σ : ℝ)
    (w : PersistenceImage.Weight A B) (x : I → UpperPoint) : UpperSpace σ :=
  ∑ i, upperWeight w (x i) • KernelWeight.baseFeature (upperKernel σ) (x i)

/-- Unweighted occurrence sum in the weighted-kernel RKHS, KFH18 eq. (4). -/
noncomputable def weightedUpperEmbedding {I : Type*} [Fintype I] (σ : ℝ)
    (w : PersistenceImage.Weight A B) (x : I → UpperPoint) : WeightedUpperSpace σ w :=
  ∑ i, KernelWeight.weightedFeature (upperKernel σ) (upperWeight w) (x i)

theorem upperWeightIsometry_embedding {I : Type*} [Fintype I] (σ : ℝ)
    (w : PersistenceImage.Weight A B) (hw : ∀ p : UpperPoint, 0 < upperWeight w p)
    (x : I → UpperPoint) :
    upperWeightIsometry σ w hw (upperEmbedding σ w x) = weightedUpperEmbedding σ w x := by
  simpa [upperEmbedding, weightedUpperEmbedding, upperWeightIsometry] using
    KernelWeight.weightIsometry_sum (upperKernel σ) (upperWeight w)
      (fun p => (hw p).ne') x (fun _ => 1)

theorem inner_weightedUpperEmbedding {I J : Type*} [Fintype I] [Fintype J] (σ : ℝ)
    (w : PersistenceImage.Weight A B) (x : I → UpperPoint) (y : J → UpperPoint) :
    ⟪weightedUpperEmbedding σ w x, weightedUpperEmbedding σ w y⟫_ℝ =
      linearKernel σ w (fun i => (x i).val) (fun j => (y j).val) := by
  unfold weightedUpperEmbedding linearKernel
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [KernelWeight.inner_weightedFeature]
  simp only [upperWeight, upperKernel, Matrix.of_apply]
  ring

/-- The finite-sum norm bridge needs no positive-weight or bandwidth hypothesis. -/
theorem norm_weightedUpperEmbedding_sub {I J : Type*} [Fintype I] [Fintype J] (σ : ℝ)
    (w : PersistenceImage.Weight A B) (x : I → UpperPoint) (y : J → UpperPoint) :
    ‖weightedUpperEmbedding σ w x - weightedUpperEmbedding σ w y‖ =
      ‖embedding σ w (fun i => (x i).val) - embedding σ w (fun j => (y j).val)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sub_sq_real, norm_embedding_sub_sq]
  simp only [← real_inner_self_eq_norm_sq, inner_weightedUpperEmbedding]
  ring

/-- Canonical finite labels lifted to the positive domain. -/
def upperFiniteOccurrence (D : Diagram ℝ) (hD : D.IsPositive) :
    D.finiteOccurrences → UpperPoint := fun p => ⟨p.1, hD.finiteOccurrence p⟩

/-- Weighted-measure sum of a positive diagram's finite part on the upper domain. -/
noncomputable def upperDiagramEmbedding (σ : ℝ) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) (hD : D.IsPositive) : UpperSpace σ :=
  upperEmbedding σ w (upperFiniteOccurrence D hD)

/-- Weighted-kernel sum of a positive diagram's finite part. -/
noncomputable def weightedUpperDiagramEmbedding (σ : ℝ) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) (hD : D.IsPositive) : WeightedUpperSpace σ w :=
  weightedUpperEmbedding σ w (upperFiniteOccurrence D hD)

theorem upperWeightIsometry_diagramEmbedding (σ : ℝ) (w : PersistenceImage.Weight A B)
    (hw : ∀ p : UpperPoint, 0 < upperWeight w p) (D : Diagram ℝ) (hD : D.IsPositive) :
    upperWeightIsometry σ w hw (upperDiagramEmbedding σ w D hD) =
      weightedUpperDiagramEmbedding σ w D hD :=
  upperWeightIsometry_embedding σ w hw _

theorem inner_weightedUpperDiagramEmbedding (σ : ℝ) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) (hD : D.IsPositive) (E : Diagram ℝ) (hE : E.IsPositive) :
    ⟪weightedUpperDiagramEmbedding σ w D hD, weightedUpperDiagramEmbedding σ w E hE⟫_ℝ =
      ⟪diagramEmbedding σ w D, diagramEmbedding σ w E⟫_ℝ := by
  rw [weightedUpperDiagramEmbedding, weightedUpperDiagramEmbedding,
    inner_weightedUpperEmbedding, inner_diagramEmbedding]
  rfl

theorem norm_weightedUpperDiagramEmbedding_sub (σ : ℝ) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) (hD : D.IsPositive) (E : Diagram ℝ) (hE : E.IsPositive) :
    ‖weightedUpperDiagramEmbedding σ w D hD - weightedUpperDiagramEmbedding σ w E hE‖ =
      ‖diagramEmbedding σ w D - diagramEmbedding σ w E‖ :=
  norm_weightedUpperEmbedding_sub σ w _ _

theorem upperWeight_arctan_pos {C : ℝ} (hC : 0 < C) (p : UpperPoint) :
    0 < upperWeight (PersistenceImage.arctanWeight C hC.le) p := by
  rw [upperWeight, PersistenceImage.arctanWeight_birthPersistence C hC.le p.property.le]
  exact Real.arctan_pos.mpr (mul_pos hC (sub_pos.mpr p.property))

/-- The source arctan weight requires no uniform positive lower bound. -/
noncomputable def arctanUpperWeightIsometry (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    UpperSpace σ ≃ₗᵢ[ℝ] WeightedUpperSpace σ (PersistenceImage.arctanWeight C hC.le) :=
  upperWeightIsometry σ _ (upperWeight_arctan_pos hC)

end TDA.Persistence.WeightedKernel
