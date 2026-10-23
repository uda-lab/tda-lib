import TDA.Persistence.CechPersistenceImage
import TDA.Persistence.CechStabilityExamples
import TDA.Filtration.CechExamples
import TDA.Filtration.CechDisplacementExamples
import TDA.Persistence.ArctanWeightExamples

set_option autoImplicit false

/-! # Čech weighted-kernel and persistence-image consumers

One point of a two-point configuration moved by one, generically and for the arctan weight;
the three-point family with displacement `1`, for the arctan image and embedding; zero
displacement and the empty carrier, where embeddings, kernel values and images coincide; and
a repeated-label configuration that admits no distance-compatible label metric, so that the
Rips consumers do not apply, while the Čech consumers do. Unless stated otherwise the
coefficient field is `ℚ`. -/

namespace TDA.Persistence.CechWeightedKernelExamples

open TDA.Filtration Real
open PersistenceImage (Weight arctanWeight finiteDiagramImage)

variable {A B : ℝ} (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : Weight A B)

/-! ## One point moved by one -/

namespace MovedPoint

open TDA.Persistence.Cech.Examples.MovedPoint

/-- The Čech diagrams are at finite bottleneck distance, with real conversion at most `1`. -/
theorem bottleneck_bounds (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter q) n) < ⊤ ∧
      (bottleneck (dgm ℚ (Cech.filter p) n) (dgm ℚ (Cech.filter q) n)).toReal ≤ 1 := by
  refine ⟨Cech.bottleneck_dgm_lt_top ℚ p q n, ?_⟩
  simpa only [displacement_eq] using Cech.toReal_bottleneck_dgm_le_displacement ℚ p q n

include hA hB in
/-- The embedding and kernel-value bounds with the displacement replaced by `1`. -/
theorem kernel_bounds (n : ℕ) (D : Diagram ℝ) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter q) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (dgm ℚ (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) ∧
    |WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter p) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter q) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm ℚ (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) := by
  constructor
  · simpa only [displacement_eq, mul_one] using
      Cech.norm_diagramEmbedding_sub_le_displacement ℚ p q n σ hA hB w
  · simpa only [displacement_eq, mul_one] using
      Cech.abs_gaussianDiagramKernel_sub_le_displacement ℚ p q n σ τ hA hB w D

/-- The arctan kernel-value bound at `σ = τ = C = 1`. -/
theorem kernel_arctan (n : ℕ) (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel 1 1 (arctanWeight 1 zero_le_one) D
          (dgm ℚ (Cech.filter p) n) -
        WeightedKernel.gaussianDiagramKernel 1 1 (arctanWeight 1 zero_le_one) D
          (dgm ℚ (Cech.filter q) n)| ≤
      (2 + √2 * π / 2) *
        ((Fintype.card (dgm ℚ (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) := by
  have h := Cech.abs_gaussianDiagramKernel_sub_le_displacement_arctan ℚ p q n 1 1
    zero_le_one D
  rw [displacement_eq, mul_one] at h
  convert h using 2
  norm_num

end MovedPoint

/-! ## Three points on the line -/

namespace ThreePoints

open TDA.Filtration.Cech.DisplacementExamples.ThreePoints

/-- The arctan image bound at `σ = C = 1` for every measurable disjoint pixel family, and the
arctan embedding bound at `σ = C = 1`. -/
theorem arctan_bounds (n : ℕ) {K : Type*} [Fintype K] (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j)) (hd : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖finiteDiagramImage 1 (arctanWeight 1 zero_le_one) P (dgm ℚ (Cech.filter p) n) -
        finiteDiagramImage 1 (arctanWeight 1 zero_le_one) P (dgm ℚ (Cech.filter q) n)‖ ≤
      (2 + 3 * √(π / 2)) *
        ((Fintype.card (dgm ℚ (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) ∧
    ‖WeightedKernel.diagramEmbedding 1 (arctanWeight 1 zero_le_one)
          (dgm ℚ (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding 1 (arctanWeight 1 zero_le_one)
          (dgm ℚ (Cech.filter q) n)‖ ≤
      (2 + √2 * π / 2) *
        ((Fintype.card (dgm ℚ (Cech.filter p) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter q) n).finiteOccurrences : ℕ) : ℝ) := by
  constructor
  · have h := Cech.norm_finiteDiagramImage_sub_le_displacement_arctan ℚ p q n one_pos
      zero_le_one P hm hd
    rw [displacement_eq, mul_one] at h
    convert h using 2
    norm_num
  · have h := Cech.norm_diagramEmbedding_sub_le_displacement_arctan ℚ p q n 1 zero_le_one
    rw [displacement_eq, mul_one] at h
    convert h using 2
    norm_num

end ThreePoints

/-! ## Zero displacement and the empty carrier -/

variable {K : Type*} [Fintype K] (P : K → Set (ℝ × ℝ))

include hA hB in
private theorem coincide_of_displacement_eq_zero {V : Type} [LinearOrder V] [Fintype V]
    (p q : V → ℝ) (h0 : Cech.displacement p q = 0) {σ' : ℝ} (hσ : 0 < σ')
    (hm : ∀ j, MeasurableSet (P j)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (n : ℕ) (D : Diagram ℝ) :
    WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter p) n) =
        WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter q) n) ∧
      WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter p) n) =
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter q) n) ∧
      finiteDiagramImage σ' w P (dgm ℚ (Cech.filter p) n) =
        finiteDiagramImage σ' w P (dgm ℚ (Cech.filter q) n) := by
  have h₁ := Cech.norm_diagramEmbedding_sub_le_displacement ℚ p q n σ hA hB w
  have h₂ := Cech.abs_gaussianDiagramKernel_sub_le_displacement ℚ p q n σ τ hA hB w D
  have h₃ := Cech.norm_finiteDiagramImage_sub_le_displacement ℚ p q n hσ hA hB w P hm hd
  rw [h0, mul_zero] at h₁ h₂ h₃
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h₁ (norm_nonneg _))),
    sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h₂ (abs_nonneg _))),
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h₃ (norm_nonneg _)))⟩

include hA hB in
/-- A configuration against itself: the embedding, kernel-value (against every `D`) and image
bounds of the Čech consumers read `≤ 0`, by `Cech.displacement_self`. -/
theorem self_bounds (p : Fin 2 → ℝ) {σ' : ℝ} (hσ : 0 < σ')
    (hm : ∀ j, MeasurableSet (P j)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (n : ℕ) (D : Diagram ℝ) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter p) n)‖ ≤ 0 ∧
      |WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter p) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter p) n)| ≤ 0 ∧
      ‖finiteDiagramImage σ' w P (dgm ℚ (Cech.filter p) n) -
        finiteDiagramImage σ' w P (dgm ℚ (Cech.filter p) n)‖ ≤ 0 := by
  have h₁ := Cech.norm_diagramEmbedding_sub_le_displacement ℚ p p n σ hA hB w
  have h₂ := Cech.abs_gaussianDiagramKernel_sub_le_displacement ℚ p p n σ τ hA hB w D
  have h₃ := Cech.norm_finiteDiagramImage_sub_le_displacement ℚ p p n hσ hA hB w P hm hd
  rw [Cech.displacement_self, mul_zero] at h₁ h₂ h₃
  exact ⟨h₁, h₂, h₃⟩

include hA hB in
/-- On the empty carrier: embeddings, kernel values against every `D` and images coincide. -/
theorem empty_coincide (p q : Fin 0 → ℝ) {σ' : ℝ} (hσ : 0 < σ')
    (hm : ∀ j, MeasurableSet (P j)) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (n : ℕ) (D : Diagram ℝ) :
    WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter p) n) =
        WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter q) n) ∧
      WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter p) n) =
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter q) n) ∧
      finiteDiagramImage σ' w P (dgm ℚ (Cech.filter p) n) =
        finiteDiagramImage σ' w P (dgm ℚ (Cech.filter q) n) :=
  coincide_of_displacement_eq_zero σ τ hA hB w P p q (Cech.displacement_of_isEmpty p q) hσ hm
    hd n D

/-! ## Negative control: no label metric is needed -/

namespace Repeated

/-- Both labels at `0`. -/
abbrev pts : Fin 2 → ℝ := TDA.Filtration.Cech.Examples.Repeated.pts

/-- The labelled points `0, 2`. -/
abbrev twoPoints : Fin 2 → ℝ := TDA.Filtration.Cech.Examples.TwoPoints.pts

/-- No metric on the labels is distance-compatible with the repeated configuration, so
`Cech.bottleneck_rips_dgm_le_two_mul_displacement` and the Rips consumers do not apply. -/
theorem no_label_metric :
    ¬ ∃ d : MetricSpace (Fin 2), ∀ v w, d.dist v w = dist (pts v) (pts w) := by
  rintro ⟨d, hd⟩
  have h : d.dist 0 1 = 0 := by
    rw [hd]
    simp [pts, TDA.Filtration.Cech.Examples.Repeated.pts]
  have h01 : (0 : Fin 2) = 1 := @eq_of_dist_eq_zero _ d 0 1 h
  exact absurd h01 (by decide)

theorem displacement_eq : Cech.displacement pts twoPoints = 2 := by
  apply le_antisymm
  · refine (Cech.displacement_le_iff pts twoPoints 2).2 ⟨zero_le_two, fun v => ?_⟩
    fin_cases v <;>
      norm_num [pts, twoPoints, TDA.Filtration.Cech.Examples.Repeated.pts,
        TDA.Filtration.Cech.Examples.TwoPoints.pts, Real.dist_eq]
  · have h := Cech.dist_le_displacement pts twoPoints 1
    norm_num [pts, twoPoints, TDA.Filtration.Cech.Examples.Repeated.pts,
      TDA.Filtration.Cech.Examples.TwoPoints.pts, Real.dist_eq] at h
    exact h

include hA hB in
/-- Against the two points `0, 2` the Čech embedding, kernel-value and image bounds apply
with displacement `2`, although no label metric exists for the repeated configuration. -/
theorem cech_bounds {σ' : ℝ} (hσ : 0 < σ') (hm : ∀ j, MeasurableSet (P j))
    (hd : Pairwise (fun i j => Disjoint (P i) (P j))) (n : ℕ) (D : Diagram ℝ) :
    ‖WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter pts) n) -
        WeightedKernel.diagramEmbedding σ w (dgm ℚ (Cech.filter twoPoints) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (dgm ℚ (Cech.filter pts) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter twoPoints) n).finiteOccurrences : ℕ) : ℝ) * 2 ∧
    |WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter pts) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (dgm ℚ (Cech.filter twoPoints) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm ℚ (Cech.filter pts) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter twoPoints) n).finiteOccurrences : ℕ) : ℝ) * 2 ∧
    ‖finiteDiagramImage σ' w P (dgm ℚ (Cech.filter pts) n) -
        finiteDiagramImage σ' w P (dgm ℚ (Cech.filter twoPoints) n)‖ ≤
      PersistenceImage.stabilityConstant σ' A B *
        ((Fintype.card (dgm ℚ (Cech.filter pts) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter twoPoints) n).finiteOccurrences : ℕ) : ℝ) * 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [displacement_eq] using
      Cech.norm_diagramEmbedding_sub_le_displacement ℚ pts twoPoints n σ hA hB w
  · simpa only [displacement_eq] using
      Cech.abs_gaussianDiagramKernel_sub_le_displacement ℚ pts twoPoints n σ τ hA hB w D
  · simpa only [displacement_eq] using
      Cech.norm_finiteDiagramImage_sub_le_displacement ℚ pts twoPoints n hσ hA hB w P hm hd

end Repeated

end TDA.Persistence.CechWeightedKernelExamples
