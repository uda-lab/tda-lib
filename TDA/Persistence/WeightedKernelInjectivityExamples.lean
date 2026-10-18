import TDA.Persistence.WeightedKernelInjectivity
import TDA.Persistence.WeightedKernelExamples
import TDA.Persistence.ArctanWeight

/-!
# Fixtures for injectivity of the weighted Gaussian kernel embedding

These examples record strict positive definiteness, the zero-bandwidth and zero-weight
negative controls, multiplicity detection, positive-diagram consumers, and recovery of a
finite diagram together with its essential part.
-/

namespace TDA.Persistence.WeightedKernelInjectivityExamples

open Matrix WeightedKernel WeightedKernelExamples
open PersistenceImage (arctanWeight arctanWeight_apply)
open scoped InnerProductSpace

/-! ## F1: strict positive definiteness -/

/-- Three distinct birth--death points used for the strict positive-definiteness fixture. -/
def distinctPoints : Fin 3 → ℝ × ℝ := ![(0, 2), (0, 3), (1, 3)]

/-- The three-point family is injective. -/
theorem distinctPoints_injective : Function.Injective distinctPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [distinctPoints, Prod.ext_iff] at hij ⊢

/-- The Gaussian Gram matrix on the three distinct points is positive definite. -/
theorem distinctPoints_posDef :
    (Matrix.of fun i j => kernel 1 (distinctPoints i) (distinctPoints j)).PosDef := by
  exact posDef_kernel_family (by norm_num) distinctPoints distinctPoints_injective

/-- The quadratic form of the three-point Gram matrix is positive at `(1, -1, 0)`. -/
theorem distinctPoints_quadratic_pos :
    0 < star (![1, -1, 0] : Fin 3 → ℝ) ⬝ᵥ
      ((Matrix.of fun i j => kernel 1 (distinctPoints i) (distinctPoints j)) *ᵥ
        (![1, -1, 0] : Fin 3 → ℝ)) := by
  apply distinctPoints_posDef.dotProduct_mulVec_pos
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-! ## F2: repeated labels -/

/-- The repeated-label quadratic form vanishes at `single 0 1 - single 1 1`. -/
theorem duplicate_quadratic_zero :
    (Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 2 →₀ ℝ).sum
        (fun i a => (Finsupp.single 0 1 - Finsupp.single 1 1 : Fin 2 →₀ ℝ).sum
          (fun j b => star a *
            (Matrix.of fun i j => kernel 1 (duplicate i) (duplicate j)) i j * b)) = 0 := by
  classical
  simp [Finsupp.sum_fintype, Fin.sum_univ_two, duplicate, Matrix.of_apply,
    kernel_self, kernel_symm] <;> ring

/-- The repeated-label Gram matrix is not positive definite. -/
theorem duplicate_not_posDef :
    ¬ (Matrix.of fun i j => kernel 1 (duplicate i) (duplicate j)).PosDef := by
  intro h
  let v : Fin 2 →₀ ℝ := Finsupp.single 0 1 - Finsupp.single 1 1
  have hv : v ≠ 0 := by
    intro hv
    have hv0 := congrArg (fun f : Fin 2 →₀ ℝ => f 0) hv
    simp [v] at hv0
  have hp := h.2 hv
  have hz : v.sum (fun i a => v.sum (fun j b => star a *
      (Matrix.of fun i j => kernel 1 (duplicate i) (duplicate j)) i j * b)) = 0 := by
    simpa [v] using duplicate_quadratic_zero
  rw [hz] at hp
  linarith

/-! ## F3: zero bandwidth -/

/-- At zero bandwidth all RKHS kernel features are equal. -/
theorem featureAt_zero_eq (p q : ℝ × ℝ) : featureAt 0 p = featureAt 0 q := by
  apply RKHS.ext
  intro z
  rw [featureAt_apply, featureAt_apply]
  simp [kernel]

/-- The zero-bandwidth feature family is not linearly independent. -/
theorem featureAt_zero_not_linearIndependent :
    ¬ LinearIndependent ℝ (featureAt 0) := by
  intro h
  have hpq : (0, 0) = (0, 1) :=
    h.injective (featureAt_zero_eq (0, 0) (0, 1))
  norm_num at hpq

/-- The zero-bandwidth finite-support measure embedding is not injective. -/
theorem measureEmbedding_zero_not_injective :
    ¬ Function.Injective (measureEmbedding 0) := by
  intro h
  have heq : measureEmbedding 0 (Finsupp.single (0, 2) 1) =
      measureEmbedding 0 (Finsupp.single (0, 3) 1) := by
    rw [measureEmbedding_single, measureEmbedding_single,
      featureAt_zero_eq]
  have hs : (Finsupp.single (0, 2) 1 : ℝ × ℝ →₀ ℝ) =
      Finsupp.single (0, 3) 1 := h heq
  have hs0 := congrArg (fun μ : ℝ × ℝ →₀ ℝ => μ (0, 2)) hs
  simp at hs0

/-- The clipped weights at the two positive singleton points are both one. -/
theorem clippedWeight_two_three :
    clippedWeight (birthPersistence (0, 2)) = 1 ∧
      clippedWeight (birthPersistence (0, 3)) = 1 := by
  constructor <;> norm_num [clippedWeight, birthPersistence]

/-- Zero bandwidth identifies the two singleton diagrams despite their different finite parts. -/
theorem zero_bandwidth_diagramEmbedding_eq :
    diagramEmbedding 0 clippedWeight (singletonDiagram 0 2 (by norm_num)) =
      diagramEmbedding 0 clippedWeight (singletonDiagram 0 3 (by norm_num)) := by
  rw [diagramEmbedding_eq_sum, diagramEmbedding_eq_sum]
  have h2 : finitePart (singletonDiagram 0 2 (by norm_num)).points = {(0, 2)} := rfl
  have h3 : finitePart (singletonDiagram 0 3 (by norm_num)).points = {(0, 3)} := rfl
  rw [h2, h3, Multiset.map_singleton, Multiset.sum_singleton,
    Multiset.map_singleton, Multiset.sum_singleton]
  rw [featureAt_zero_eq (0, 2) (0, 3)]
  norm_num [clippedWeight, birthPersistence]

/-- The two singleton finite parts in the zero-bandwidth fixture are different. -/
theorem singleton_two_three_finitePart_ne :
    finitePart (singletonDiagram 0 2 (by norm_num)).points ≠
      finitePart (singletonDiagram 0 3 (by norm_num)).points := by
  intro h
  have hc := congrArg (fun s : Multiset (ℝ × ℝ) => s.count (0, 2)) h
  norm_num [singletonDiagram, finitePart] at hc

/-! ## F4: multiplicity -/

/-- A diagram with two occurrences of the same finite point. -/
def twice : Diagram ℝ where
  points := {((0 : ℝ), (2 : WithTop ℝ)), ((0 : ℝ), (2 : WithTop ℝ))}
  offDiagonal := by simp

/-- The weighted measure of `twice` counts both occurrences. -/
theorem weightedMeasure_twice_at_two :
    weightedMeasure clippedWeight twice (0, 2) = 2 := by
  rw [weightedMeasure_apply]
  norm_num [twice, clippedWeight, birthPersistence]

/-- The weighted measure of the singleton `{(0,2)}` is one. -/
theorem weightedMeasure_singleton_two :
    weightedMeasure clippedWeight (singletonDiagram 0 2 (by norm_num)) (0, 2) = 1 := by
  rw [weightedMeasure_apply]
  norm_num [singletonDiagram, clippedWeight, birthPersistence]

/-- The embedding detects the repeated occurrence. -/
theorem twice_embedding_ne_singleton :
    diagramEmbedding 1 clippedWeight twice ≠
      diagramEmbedding 1 clippedWeight (singletonDiagram 0 2 (by norm_num)) := by
  intro h
  have hm := (diagramEmbedding_eq_iff_weightedMeasure_eq (σ := 1) (by norm_num)
    clippedWeight twice (singletonDiagram 0 2 (by norm_num))).mp h
  have hc := congrArg (fun μ : ℝ × ℝ →₀ ℝ => μ (0, 2)) hm
  rw [weightedMeasure_twice_at_two, weightedMeasure_singleton_two] at hc
  norm_num at hc

/-! ## F5: vanishing weights -/

/-- The zero arctan weight identifies a finite singleton with an essential-only diagram. -/
theorem zero_arctan_singleton_eq_essentialOnly :
    diagramEmbedding 1 (arctanWeight 0 le_rfl)
        (singletonDiagram 0 2 (by norm_num)) =
      diagramEmbedding 1 (arctanWeight 0 le_rfl) essentialOnly := by
  rw [diagramEmbedding_eq_sum, diagramEmbedding_eq_sum]
  have hs : finitePart (singletonDiagram 0 2 (by norm_num)).points = {(0, 2)} := rfl
  have he : finitePart essentialOnly.points = 0 := rfl
  rw [hs, he, Multiset.map_singleton, Multiset.sum_singleton,
    Multiset.map_zero, Multiset.sum_zero]
  simp [arctanWeight_apply, birthPersistence]

/-- The finite part of the zero-arctan singleton differs from the essential-only finite part. -/
theorem zero_arctan_finitePart_ne_essentialOnly :
    finitePart (singletonDiagram 0 2 (by norm_num)).points ≠
      finitePart essentialOnly.points := by
  intro h
  have hc := congrArg (fun s : Multiset (ℝ × ℝ) => s.card) h
  norm_num [singletonDiagram, essentialOnly, finitePart] at hc

/-- The positive arctan weight vanishes on the below-diagonal singleton. -/
theorem arctan_below_diagonal_singleton_eq_essentialOnly :
    diagramEmbedding 1 (arctanWeight 1 zero_le_one)
        (singletonDiagram 1 0 (by norm_num)) =
      diagramEmbedding 1 (arctanWeight 1 zero_le_one) essentialOnly := by
  rw [diagramEmbedding_eq_sum, diagramEmbedding_eq_sum]
  have hs : finitePart (singletonDiagram 1 0 (by norm_num)).points = {(1, 0)} := rfl
  have he : finitePart essentialOnly.points = 0 := rfl
  rw [hs, he, Multiset.map_singleton, Multiset.sum_singleton,
    Multiset.map_zero, Multiset.sum_zero]
  simp [arctanWeight_apply, birthPersistence]

/-- The below-diagonal singleton and the essential-only diagram have different finite parts. -/
theorem arctan_below_diagonal_finitePart_ne_essentialOnly :
    finitePart (singletonDiagram 1 0 (by norm_num)).points ≠
      finitePart essentialOnly.points := by
  intro h
  have hc := congrArg (fun s : Multiset (ℝ × ℝ) => s.card) h
  norm_num [singletonDiagram, essentialOnly, finitePart] at hc

/-! ## F6: positive consumers -/

private theorem singleton_two_isPositive :
    (singletonDiagram 0 2 (by norm_num)).IsPositive := by
  intro p hp
  simp only [singletonDiagram, Multiset.mem_singleton] at hp
  subst p
  norm_num

private theorem singleton_three_isPositive :
    (singletonDiagram 0 3 (by norm_num)).IsPositive := by
  intro p hp
  simp only [singletonDiagram, Multiset.mem_singleton] at hp
  subst p
  norm_num

private theorem singleton_below_clipped_positive :
    ∀ p ∈ finitePart (singletonDiagram 1 0 (by norm_num)).points,
      0 < clippedWeight (birthPersistence p) := by
  intro p hp
  have hp' : p = (1, 0) := by
    simpa [singletonDiagram, finitePart] using hp
  subst p
  norm_num [clippedWeight, birthPersistence]

private theorem essentialOnly_no_finite_clipped_positive :
    ∀ p ∈ finitePart essentialOnly.points, 0 < clippedWeight (birthPersistence p) := by
  intro p hp
  simp [essentialOnly, finitePart] at hp

/-- The arctan-weight embedding separates the two positive singleton diagrams. -/
theorem arctan_singletons_embedding_ne :
    diagramEmbedding 1 (arctanWeight 1 zero_le_one)
        (singletonDiagram 0 2 (by norm_num)) ≠
      diagramEmbedding 1 (arctanWeight 1 zero_le_one)
        (singletonDiagram 0 3 (by norm_num)) := by
  have hw : ∀ u : ℝ × ℝ, 0 < u.2 →
      0 < arctanWeight 1 zero_le_one u := by
    intro u hu
    rw [arctanWeight_apply, max_eq_left hu.le]
    simpa using (Real.arctan_pos.mpr hu)
  intro h
  have hp := (diagramEmbedding_eq_iff_of_isPositive (σ := 1) (by norm_num)
    (arctanWeight 1 zero_le_one) hw singleton_two_isPositive singleton_three_isPositive).mp h
  exact singleton_two_three_finitePart_ne hp

/-- The clipped weight separates a below-diagonal singleton from the essential-only diagram. -/
theorem clipped_below_diagonal_embedding_ne :
    diagramEmbedding 1 clippedWeight (singletonDiagram 1 0 (by norm_num)) ≠
      diagramEmbedding 1 clippedWeight essentialOnly := by
  intro h
  have hp := (diagramEmbedding_eq_iff (σ := 1) (by norm_num) clippedWeight
    singleton_below_clipped_positive essentialOnly_no_finite_clipped_positive).mp h
  exact arctan_below_diagonal_finitePart_ne_essentialOnly hp

/-! ## F7: distance and whole-diagram recovery -/

/-- A diagram with finite point `(0,2)` and essential birth `0`. -/
def finiteEssentialDiagram : Diagram ℝ where
  points := {((0 : ℝ), (2 : WithTop ℝ)), ((0 : ℝ), (⊤ : WithTop ℝ))}
  offDiagonal := by simp

/-- The finite and essential parts of `finiteEssentialDiagram`. -/
theorem finiteEssentialDiagram_parts :
    finitePart finiteEssentialDiagram.points = {(0, 2)} ∧
      essentialPart finiteEssentialDiagram.points = {(0 : ℝ)} := by
  rfl

private theorem finiteEssentialDiagram_clipped_positive :
    ∀ p ∈ finitePart finiteEssentialDiagram.points,
      0 < clippedWeight (birthPersistence p) := by
  intro p hp
  have hp' : p = (0, 2) := by
    simpa [finiteEssentialDiagram, finitePart] using hp
  subst p
  norm_num [clippedWeight, birthPersistence]

/-- The two positive singleton embeddings have nonzero RKHS distance. -/
theorem diagramEmbedding_singleton_distance_ne_zero :
    ‖diagramEmbedding 1 clippedWeight (singletonDiagram 0 2 (by norm_num)) -
        diagramEmbedding 1 clippedWeight (singletonDiagram 0 3 (by norm_num))‖ ≠ 0 := by
  intro hz
  have heq := norm_sub_eq_zero_iff.mp hz
  have hp := (diagramEmbedding_eq_iff (σ := 1) (by norm_num) clippedWeight
    (by
      intro p hp
      have hp' : p = (0, 2) := by
        simpa [singletonDiagram, finitePart] using hp
      subst p
      norm_num [clippedWeight, birthPersistence])
    (by
      intro p hp
      have hp' : p = (0, 3) := by
        simpa [singletonDiagram, finitePart] using hp
      subst p
      norm_num [clippedWeight, birthPersistence])).mp heq
  exact singleton_two_three_finitePart_ne hp

/-- Equal embedding and equal essential part recover the whole finite-essential diagram. -/
theorem whole_diagram_recovery {E : Diagram ℝ}
    (hE : ∀ p ∈ finitePart E.points, 0 < clippedWeight (birthPersistence p))
    (hess : essentialPart E.points = {(0 : ℝ)})
    (h : diagramEmbedding 1 clippedWeight E =
      diagramEmbedding 1 clippedWeight finiteEssentialDiagram) :
    E = finiteEssentialDiagram := by
  have htarget : ∀ p ∈ finitePart finiteEssentialDiagram.points,
      0 < clippedWeight (birthPersistence p) := finiteEssentialDiagram_clipped_positive
  have hess' : essentialPart E.points = essentialPart finiteEssentialDiagram.points := by
    simpa [finiteEssentialDiagram, essentialPart] using hess
  exact eq_of_diagramEmbedding_eq (σ := 1) (by norm_num) clippedWeight hE htarget hess' h

end TDA.Persistence.WeightedKernelInjectivityExamples
