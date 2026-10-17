import TDA.Persistence.WeightedKernel

/-! # Weighted Gaussian kernel embedding consumers

Concrete kernel values, a finite positive semidefinite consumer and a sign-flipped negative
control, repeated occurrences, an RKHS distance, the diagonal and essential-only boundary
cases, and a Gaussian diagram Gram matrix. All embeddings use bandwidth one and the weight
`min |persistence| 1`. -/

namespace TDA.Persistence.WeightedKernelExamples

open Matrix WeightedKernel
open scoped InnerProductSpace

/-- Clip the absolute persistence coordinate at one. -/
noncomputable def clippedWeight : PersistenceImage.Weight 1 1 where
  toFun u := min |u.2| 1
  nonneg u := le_min (abs_nonneg _) (by norm_num)
  bounded u := min_le_right _ _
  lipschitz u v := by
    have h := abs_min_sub_min_le_max |u.2| 1 |v.2| 1
    simp only [sub_self, abs_zero] at h
    rw [max_eq_left (abs_nonneg (|u.2| - |v.2|))] at h
    calc
      _ ≤ abs (abs u.2 - abs v.2) := h
      _ ≤ |u.2 - v.2| := abs_abs_sub_abs_le_abs_sub _ _
      _ ≤ 1 * ‖u - v‖ := by
        simpa only [one_mul, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
          using le_max_right |u.1 - v.1| |u.2 - v.2|
  zero_persistence b := by simp

private theorem weight_two : clippedWeight (birthPersistence (0, 2)) = 1 := by
  norm_num [clippedWeight, birthPersistence]

private theorem weight_three : clippedWeight (birthPersistence (0, 3)) = 1 := by
  norm_num [clippedWeight, birthPersistence]

/-! ## Kernel values -/

theorem kernel_same : kernel 1 (0, 2) (0, 2) = 1 := kernel_self 1 _

theorem kernel_adjacent : kernel 1 (0, 2) (0, 3) = Real.exp (-1 / 2) := by
  norm_num [kernel]

private theorem kernel_adjacent' : kernel 1 (0, 3) (0, 2) = Real.exp (-1 / 2) := by
  rw [kernel_symm, kernel_adjacent]

private theorem exp_neg_half_lt_one : Real.exp (-1 / 2) < 1 :=
  Real.exp_lt_one_iff.mpr (by norm_num)

/-! ## A finite positive semidefinite consumer and a negative control -/

/-- Two birth–death points at Euclidean distance one. -/
def pair : Fin 2 → ℝ × ℝ := ![(0, 2), (0, 3)]

/-- The coefficient vector `(1, -1)`. -/
def alternating : Fin 2 → ℝ := ![1, -1]

theorem pair_posSemidef : (Matrix.of fun i j => kernel 1 (pair i) (pair j)).PosSemidef :=
  posSemidef_kernel_family 1 pair

/-- The quadratic form at `(1, -1)` is `2 - 2 exp (-1/2)`; it is nonnegative by positive
semidefiniteness and in fact positive. -/
theorem pair_quadratic :
    star alternating ⬝ᵥ ((Matrix.of fun i j => kernel 1 (pair i) (pair j)) *ᵥ alternating) =
      2 - 2 * Real.exp (-1 / 2) ∧
    0 ≤ star alternating ⬝ᵥ
      ((Matrix.of fun i j => kernel 1 (pair i) (pair j)) *ᵥ alternating) ∧
    0 < 2 - 2 * Real.exp (-1 / 2) := by
  have h : star alternating ⬝ᵥ
      ((Matrix.of fun i j => kernel 1 (pair i) (pair j)) *ᵥ alternating) =
        2 - 2 * Real.exp (-1 / 2) := by
    simp [dotProduct, mulVec, Fin.sum_univ_two, pair, alternating, kernel_adjacent,
      kernel_adjacent']
    ring
  exact ⟨h, pair_posSemidef.dotProduct_mulVec_nonneg _, by linarith [exp_neg_half_lt_one]⟩

/-- The kernel formula with the minus sign dropped. -/
noncomputable def flipped : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    Real.exp ((((pair i).1 - (pair j).1) ^ 2 + ((pair i).2 - (pair j).2) ^ 2) / 2)

theorem flipped_quadratic :
    star alternating ⬝ᵥ (flipped *ᵥ alternating) = 2 - 2 * Real.exp (1 / 2) ∧
      2 - 2 * Real.exp (1 / 2) < 0 := by
  constructor
  · simp [dotProduct, mulVec, Fin.sum_univ_two, pair, alternating, flipped]
    norm_num
    ring
  · linarith [Real.add_one_lt_exp (show (1 / 2 : ℝ) ≠ 0 by norm_num)]

/-- The sign-flipped matrix is not positive semidefinite. -/
theorem flipped_not_posSemidef : ¬ flipped.PosSemidef := fun h => by
  have h0 := h.dotProduct_mulVec_nonneg alternating
  obtain ⟨he, hneg⟩ := flipped_quadratic
  rw [he] at h0
  linarith

/-! ## Repeated occurrences and distances -/

/-- Two occurrences with the same value. -/
def duplicate : Fin 2 → ℝ × ℝ := fun _ => (0, 2)

/-- Equal values are not deduplicated: the squared norm is `2²`. -/
theorem duplicate_norm_sq : ‖embedding 1 clippedWeight duplicate‖ ^ 2 = 4 := by
  rw [← real_inner_self_eq_norm_sq, inner_embedding]
  simp [linearKernel, duplicate, weight_two]
  norm_num

theorem duplicate_apply : embedding 1 clippedWeight duplicate (0, 2) = 2 := by
  rw [embedding_apply]
  simp [duplicate, weight_two]

/-- One occurrence at `p`. -/
def single (p : ℝ × ℝ) : Unit → ℝ × ℝ := fun _ => p

theorem single_distance :
    ‖embedding 1 clippedWeight (single (0, 2)) - embedding 1 clippedWeight (single (0, 3))‖ ^ 2 =
      2 - 2 * Real.exp (-1 / 2) ∧
    ‖embedding 1 clippedWeight (single (0, 2)) -
      embedding 1 clippedWeight (single (0, 3))‖ ^ 2 ≠ 0 := by
  have h : ‖embedding 1 clippedWeight (single (0, 2)) -
      embedding 1 clippedWeight (single (0, 3))‖ ^ 2 = 2 - 2 * Real.exp (-1 / 2) := by
    rw [norm_embedding_sub_sq]
    simp [linearKernel, single, weight_two, weight_three, kernel_adjacent]
    ring
  refine ⟨h, ?_⟩
  rw [h]
  linarith [exp_neg_half_lt_one]

/-! ## Boundary cases -/

/-- A diagonal occurrence has weight zero and embeds like the empty family. -/
theorem diagonal_embedding :
    embedding 1 clippedWeight (single (1, 1)) = 0 ∧
      embedding 1 clippedWeight (Fin.elim0 : Fin 0 → ℝ × ℝ) = 0 := by
  constructor
  · simp [embedding, finiteFeatureSum, single, clippedWeight, birthPersistence]
  · simp [embedding]

/-- A diagram with one essential bar `(0, ⊤)` and no finite point. -/
def essentialOnly : Diagram ℝ where
  points := {((0 : ℝ), (⊤ : WithTop ℝ))}
  offDiagonal := by simp

theorem essentialOnly_embedding : diagramEmbedding 1 clippedWeight essentialOnly = 0 := by
  rw [diagramEmbedding_eq_sum]
  have h : finitePart essentialOnly.points = 0 := rfl
  rw [h, Multiset.map_zero, Multiset.sum_zero]

/-! ## A Gaussian diagram Gram matrix -/

/-- A diagram with one finite point. -/
def singletonDiagram (b d : ℝ) (h : b ≠ d) : Diagram ℝ where
  points := {(b, (d : WithTop ℝ))}
  offDiagonal := by simpa using h

private theorem singletonDiagram_embedding (b d : ℝ) (h : b ≠ d) :
    diagramEmbedding 1 clippedWeight (singletonDiagram b d h) =
      embedding 1 clippedWeight (single (b, d)) := by
  rw [diagramEmbedding_eq_sum]
  have hp : finitePart (singletonDiagram b d h).points = {(b, d)} := rfl
  rw [hp, Multiset.map_singleton, Multiset.sum_singleton]
  simp [embedding, finiteFeatureSum, single]

/-- The one-point diagrams `{(0, 2)}` and `{(0, 3)}`. -/
def diagrams : Fin 2 → Diagram ℝ :=
  ![singletonDiagram 0 2 (by norm_num), singletonDiagram 0 3 (by norm_num)]

theorem gaussianDiagramGram_consumer :
    (gaussianGram 1 fun a => diagramEmbedding 1 clippedWeight (diagrams a)).PosSemidef ∧
      gaussianGram 1 (fun a => diagramEmbedding 1 clippedWeight (diagrams a)) 0 1 =
        Real.exp (-(2 - 2 * Real.exp (-1 / 2)) / 2) := by
  refine ⟨posSemidef_gaussianDiagramGram 1 1 clippedWeight diagrams, ?_⟩
  simp only [gaussianGram, Matrix.of_apply, diagrams, Matrix.cons_val_zero,
    Matrix.cons_val_one, singletonDiagram_embedding, single_distance.1]
  norm_num

end TDA.Persistence.WeightedKernelExamples
