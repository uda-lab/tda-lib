import TDA.Persistence.CechRipsAdditive
import TDA.Filtration.CechSupNormExamples
import TDA.Persistence.CechSupNormDiagramExamples
import TDA.Persistence.CechStabilityExamples
import TDA.Persistence.ArctanPersistenceImageExamples

set_option autoImplicit false

/-!
# Sup-norm Čech consumer and additive-comparison fixtures

The fixtures cover the moved sup-norm pair, the comparison of half discrepancy with displacement,
zero weights, zero discrepancy, the line half-discrepancy bound, sharp additive scaling, two-point
and triangular Rips-versus-Čech bounds, and the Euclidean negative control.
-/

namespace TDA.Persistence.CechSupNormConsumersExamples

open TDA.Filtration Real
open MeasureTheory Set PersistenceImage
open scoped ENNReal

/-! ## (F1) A moved point in the sup-norm plane -/

namespace Moved

/-- The points `(0,0)` and `(3,3)` in the sup-norm plane. -/
def pts : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![3, 3]]

/-- The two moved sup-norm points have distinct labels. -/
theorem pts_injective : Function.Injective pts := by
  intro i j h
  have h0 : pts i 0 = pts j 0 := congrFun h 0
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [pts] at h0

/-- The label metric induced by the moved sup-norm points. -/
noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced pts pts_injective inferInstance

/-- The induced metric is the sup distance of the labelled points. -/
theorem metric_dist (v w : Fin 2) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- The two moved sup-norm points are at distance `3`. -/
theorem dist_pts : dist (pts 0) (pts 1) = 3 := by
  apply le_antisymm
  · exact TDA.Filtration.Cech.SupNormExamples.dist_le_of_coord (by norm_num)
      (by norm_num [pts]) (by norm_num [pts])
  · have h := TDA.Filtration.Cech.SupNormExamples.coord_le_dist (pts 0) (pts 1) 0
    norm_num [pts] at h
    exact h

/-- The discrepancy between the diagonal pair and the moved pair is exactly `1`. -/
theorem pairwiseDiscrepancy_eq :
    Rips.pairwiseDiscrepancy TDA.Filtration.Cech.SupNormExamples.Diagonal.metric metric = 1 := by
  classical
  apply le_antisymm
  · unfold Rips.pairwiseDiscrepancy
    refine (Finset.fold_max_le _).2 ⟨zero_le_one, ?_⟩
    rintro ⟨v, w⟩ -
    change |TDA.Filtration.Cech.SupNormExamples.Diagonal.metric.dist v w -
      metric.dist v w| ≤ 1
    rw [TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist, metric_dist]
    fin_cases v <;> fin_cases w
    · simp
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
      rw [TDA.Filtration.Cech.SupNormExamples.Diagonal.dist_pts, dist_pts]
      norm_num
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
      rw [dist_comm (TDA.Filtration.Cech.SupNormExamples.Diagonal.pts 1)
        (TDA.Filtration.Cech.SupNormExamples.Diagonal.pts 0),
        dist_comm (pts 1) (pts 0),
        TDA.Filtration.Cech.SupNormExamples.Diagonal.dist_pts, dist_pts]
      norm_num
    · simp
  · have h := Rips.abs_dist_sub_le_pairwiseDiscrepancy
      TDA.Filtration.Cech.SupNormExamples.Diagonal.metric metric 0 1
    rw [TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist, metric_dist,
      TDA.Filtration.Cech.SupNormExamples.Diagonal.dist_pts, dist_pts] at h
    norm_num at h
    exact h

/-- The displacement between the diagonal pair and the moved pair is exactly `1`. -/
theorem displacement_eq :
    Cech.displacement TDA.Filtration.Cech.SupNormExamples.Diagonal.pts pts = 1 := by
  apply le_antisymm
  · refine (Cech.displacement_le_iff _ _ 1).2 ⟨zero_le_one, ?_⟩
    intro v
    fin_cases v
    · simp [TDA.Filtration.Cech.SupNormExamples.Diagonal.pts, pts]
    · exact TDA.Filtration.Cech.SupNormExamples.dist_le_of_coord (by norm_num)
        (by norm_num [TDA.Filtration.Cech.SupNormExamples.Diagonal.pts, pts])
        (by norm_num [TDA.Filtration.Cech.SupNormExamples.Diagonal.pts, pts])
  · have h := Cech.dist_le_displacement
      TDA.Filtration.Cech.SupNormExamples.Diagonal.pts pts 1
    have hcoord := TDA.Filtration.Cech.SupNormExamples.coord_le_dist
      (TDA.Filtration.Cech.SupNormExamples.Diagonal.pts 1) (pts 1) 0
    norm_num [TDA.Filtration.Cech.SupNormExamples.Diagonal.pts, pts] at hcoord
    exact hcoord.trans h

/-- The sup-norm Čech bottleneck real conversion is at most `1/2` for the moved pair. -/
theorem toReal_bottleneck_le_half (n : ℕ) :
    (bottleneck (dgm ℚ (Cech.filter
        TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n)
      (dgm ℚ (Cech.filter pts) n)).toReal ≤ 1 / 2 := by
  simpa [pairwiseDiscrepancy_eq] using
    Cech.toReal_bottleneck_dgm_le_half_pairwiseDiscrepancy ℚ
      TDA.Filtration.Cech.SupNormExamples.Diagonal.metric metric
      TDA.Filtration.Cech.SupNormExamples.Diagonal.pts pts
      TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist metric_dist n

/-- The arctan embedding bound for the moved sup-norm pair is half the displacement bound. -/
theorem embedding_arctan (n : ℕ) :
    ‖WeightedKernel.diagramEmbedding 1 (PersistenceImage.arctanWeight 1 zero_le_one)
          (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n) -
        WeightedKernel.diagramEmbedding 1 (PersistenceImage.arctanWeight 1 zero_le_one)
          (dgm ℚ (Cech.filter pts) n)‖ ≤
      (2 + √2 * π / 2) *
        ((Fintype.card (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter pts) n).finiteOccurrences : ℕ) : ℝ) * (1 / 2) := by
  have h := Cech.norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy_arctan ℚ
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.pts pts
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist metric_dist n 1 zero_le_one
  simpa [pairwiseDiscrepancy_eq] using h

/-- The arctan kernel-value bound for the moved sup-norm pair is half the displacement bound. -/
theorem kernel_arctan (n : ℕ) (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel 1 1
          (PersistenceImage.arctanWeight 1 zero_le_one) D
          (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n) -
        WeightedKernel.gaussianDiagramKernel 1 1
          (PersistenceImage.arctanWeight 1 zero_le_one) D
          (dgm ℚ (Cech.filter pts) n)| ≤
      (2 + √2 * π / 2) *
        ((Fintype.card (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter pts) n).finiteOccurrences : ℕ) : ℝ) * (1 / 2) := by
  have h := Cech.abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy_arctan ℚ
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.pts pts
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist metric_dist n 1 1
      zero_le_one D
  simpa [pairwiseDiscrepancy_eq] using h

/-- The arctan persistence-image bound for the moved sup-norm pair is half the displacement bound. -/
theorem image_arctan (n : ℕ) {K : Type*} [Fintype K] (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage 1
          (PersistenceImage.arctanWeight 1 zero_le_one) P
          (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n) -
        PersistenceImage.finiteDiagramImage 1
          (PersistenceImage.arctanWeight 1 zero_le_one) P
          (dgm ℚ (Cech.filter pts) n)‖ ≤
      (2 + 3 * √(π / 2)) *
        ((Fintype.card (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter pts) n).finiteOccurrences : ℕ) : ℝ) * (1 / 2) := by
  have h := Cech.norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy_arctan ℚ
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.pts pts
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist metric_dist n one_pos
      zero_le_one P hm hdisj
  simpa [pairwiseDiscrepancy_eq] using h

end Moved

/-! ## (F2) Discrepancy versus displacement -/

/-- Half the distance-matrix discrepancy is bounded by same-label displacement. -/
theorem half_pairwiseDiscrepancy_le_displacement {V : Type*} [Fintype V]
    {ι : Type*} [Fintype ι] (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) :
    Rips.pairwiseDiscrepancy d e / 2 ≤ Cech.displacement p q := by
  have h := Cech.pairwiseDiscrepancy_le_two_mul_displacement d e p q hd he
  linarith

/-- The moved sup-norm pair shows that the half-discrepancy comparison can be strict. -/
theorem half_pairwiseDiscrepancy_lt_displacement :
    Rips.pairwiseDiscrepancy
        TDA.Filtration.Cech.SupNormExamples.Diagonal.metric Moved.metric / 2 <
      Cech.displacement TDA.Filtration.Cech.SupNormExamples.Diagonal.pts Moved.pts := by
  rw [Moved.pairwiseDiscrepancy_eq, Moved.displacement_eq]
  norm_num

/-! ## (F3) Zero weight -/

/-- At arctan weight `C = 0`, the image and embedding differences vanish while their displayed
stability constants at `σ = 1` remain positive. -/
theorem zero_weight_consumers {V : Type} [LinearOrder V] [Fintype V]
    {ι : Type*} [Fintype ι] (σ : ℝ) (d e : MetricSpace V) (p q : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (he : ∀ v w, e.dist v w = dist (q v) (q w)) (n : ℕ)
    {K : Type*} [Fintype K] (P : K → Set (ℝ × ℝ)) :
    PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight 0 le_rfl) P
          (dgm ℚ (Cech.filter p) n) -
        PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight 0 le_rfl) P
          (dgm ℚ (Cech.filter q) n) = 0 ∧
      WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight 0 le_rfl)
          (dgm ℚ (Cech.filter p) n) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight 0 le_rfl)
          (dgm ℚ (Cech.filter q) n) = 0 ∧
      0 < 3 * √(π / 2) ∧ 0 < √2 * π / 2 := by
  have hsqrt : 0 < √(π / 2) := Real.sqrt_pos.mpr Real.pi_div_two_pos
  refine ⟨by simp [TDA.Persistence.ArctanPersistenceImageExamples.zero_weight_image],
    by simp [TDA.Persistence.ArctanPersistenceImageExamples.zero_weight_embedding], ?_, ?_⟩
  · positivity
  · have hsqrt_two : 0 < √(2 : ℝ) := by positivity
    have hpi : 0 < (π : ℝ) := Real.pi_pos
    positivity

/-! ## (F4) Zero discrepancy -/

/-- The embedding, kernel value and image of any configuration with the same label distances as
the diagonal configuration (zero pairwise discrepancy), for example the diagonal configuration
itself, coincide by the half-discrepancy consumer bounds. -/
theorem self_coincide (n : ℕ) (q : Fin 2 → Fin 2 → ℝ)
    (hq : ∀ v w, TDA.Filtration.Cech.SupNormExamples.Diagonal.metric.dist v w =
      dist (q v) (q w)) (σ τ : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (D : Diagram ℝ)
    {K : Type*} [Fintype K] {σ' : ℝ} (hσ' : 0 < σ') (P : K → Set (ℝ × ℝ))
    (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    WeightedKernel.diagramEmbedding σ w
          (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n) =
        WeightedKernel.diagramEmbedding σ w
          (dgm ℚ (Cech.filter q) n) ∧
      WeightedKernel.gaussianDiagramKernel σ τ w D
          (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n) =
        WeightedKernel.gaussianDiagramKernel σ τ w D
          (dgm ℚ (Cech.filter q) n) ∧
      PersistenceImage.finiteDiagramImage σ' w P
          (dgm ℚ (Cech.filter
            TDA.Filtration.Cech.SupNormExamples.Diagonal.pts) n) =
        PersistenceImage.finiteDiagramImage σ' w P
          (dgm ℚ (Cech.filter q) n) := by
  have h₁ := Cech.norm_diagramEmbedding_sub_le_half_pairwiseDiscrepancy ℚ
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.pts
    q
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist
    hq n σ hA hB w
  have h₂ := Cech.abs_gaussianDiagramKernel_sub_le_half_pairwiseDiscrepancy ℚ
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.pts
    q
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist
    hq n σ τ hA hB w D
  have h₃ := Cech.norm_finiteDiagramImage_sub_le_half_pairwiseDiscrepancy ℚ
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric
    TDA.Filtration.Cech.SupNormExamples.Diagonal.pts
    q
    TDA.Filtration.Cech.SupNormExamples.Diagonal.metric_dist
    hq n hσ' hA hB w P hm hdisj
  rw [Rips.pairwiseDiscrepancy_self, zero_div, mul_zero] at h₁ h₂ h₃
  refine ⟨?_, ?_, ?_⟩
  · exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h₁ (norm_nonneg _)))
  · exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h₂ (abs_nonneg _)))
  · exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h₃ (norm_nonneg _)))

/-! ## (F5) The line half-discrepancy bound -/

/-- The general line half-discrepancy theorem recovers the moved two-point bound `1/2`. -/
theorem line_bottleneck_le_half (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter TDA.Filtration.Cech.Examples.TwoPoints.pts) n)
        (dgm ℚ (Cech.filter TDA.Persistence.Cech.Examples.MovedPoint.q) n) ≤
      ENNReal.ofReal (1 / 2) := by
  have h := Cech.bottleneck_dgm_le_half_pairwiseDiscrepancy_real ℚ
    TDA.Filtration.Cech.Examples.TwoPoints.metric
    TDA.Persistence.Cech.Examples.MovedPoint.metricQ
    TDA.Filtration.Cech.Examples.TwoPoints.pts
    TDA.Persistence.Cech.Examples.MovedPoint.q
    TDA.Filtration.Cech.Examples.TwoPoints.metric_dist
    TDA.Persistence.Cech.Examples.MovedPoint.metricQ_dist n
  have hδ := TDA.Persistence.Cech.SupNormDiagramExamples.MovedPoint.pairwiseDiscrepancy_le
  exact h.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right hδ (by norm_num)))

/-! ## (F6) Sharp additive scaling -/

/-- The one-bar diagram with finite point `(0, 2)`. -/
def bar : Diagram ℝ :=
  ⟨{((0 : ℝ), ((2 : ℝ) : WithTop ℝ))}, by
    intro p hp
    rw [Multiset.mem_singleton] at hp
    subst p
    norm_num⟩

/-- Scaling `bar` by `1/2` gives the one-bar point `(0, 1)`. -/
theorem bar_scale_points :
    (bar.scale 2⁻¹ (inv_pos.2 zero_lt_two)).points =
      {((0 : ℝ), ((1 : ℝ) : WithTop ℝ))} := by
  rw [Diagram.scale, Diagram.map_points]
  norm_num [bar, scaleFinitePair]

/-- The additive scaling bound gives the sharp upper bound `1` for `bar`. -/
theorem bar_bottleneck_le :
    bottleneck bar (bar.scale 2⁻¹ (inv_pos.2 zero_lt_two)) ≤ 1 := by
  classical
  have h := bottleneck_self_scale_le bar (c := (2 : ℝ)⁻¹)
    (inv_pos.2 zero_lt_two) (M := 2)
    (by
      intro p hp
      have hp0 : ((0 : ℝ), (2 : ℝ)) = p := by
        simpa [bar, finitePart] using hp
      have hp' : p = ((0 : ℝ), (2 : ℝ)) := hp0.symm
      subst p
      norm_num)
    (by
      intro b hb
      simp [bar, essentialPart] at hb)
  convert h using 1 <;> norm_num

/-- The additive scaling bound is attained by `bar`: its bottleneck distance is exactly `1`. -/
theorem bar_bottleneck_eq :
    bottleneck bar (bar.scale 2⁻¹ (inv_pos.2 zero_lt_two)) = 1 := by
  classical
  have hpresentation :
      bottleneck bar (bar.scale 2⁻¹ (inv_pos.2 zero_lt_two)) =
        presentationBottleneck
          (fun _ : Fin 1 => ((0 : ℝ), (2 : ℝ)))
          (fun _ : Fin 1 => ((0 : ℝ), (1 : ℝ)))
          (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) := by
    refine bottleneck_eq_presentation _ _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals (try rw [bar_scale_points])
    all_goals simp [bar, finitePart, essentialPart]
    all_goals rfl
  rw [hpresentation]
  let M : OccurrenceMatching (Fin 1) (Fin 1) (Fin 0) (Fin 0) :=
    { finite := fun _ => some 0
      finite_injective := fun i i' _ _ _ => Subsingleton.elim i i'
      essential := Equiv.refl _ }
  have hupper :
      presentationBottleneck
          (fun _ : Fin 1 => ((0 : ℝ), (2 : ℝ)))
          (fun _ : Fin 1 => ((0 : ℝ), (1 : ℝ)))
          (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) ≤ 1 := by
    calc
      _ ≤ M.cost (fun _ : Fin 1 => ((0 : ℝ), (2 : ℝ)))
          (fun _ : Fin 1 => ((0 : ℝ), (1 : ℝ)))
          (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) :=
        presentationBottleneck_le_cost _ _ _ _ M
      _ = 1 := by
        simp [M, OccurrenceMatching.cost, finitePairCost]
        norm_num
  have hlower :
      1 ≤ presentationBottleneck
          (fun _ : Fin 1 => ((0 : ℝ), (2 : ℝ)))
          (fun _ : Fin 1 => ((0 : ℝ), (1 : ℝ)))
          (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) := by
    apply le_iInf
    intro M
    unfold OccurrenceMatching.cost
    apply le_trans ?_ (le_max_left _ _)
    have hle := (Finset.le_sup (s := (Finset.univ : Finset (Fin 1)))
      (f := fun i => match M.finite i with
        | some j => finitePairCost ((fun _ : Fin 1 => ((0 : ℝ), (2 : ℝ))) i)
            ((fun _ : Fin 1 => ((0 : ℝ), (1 : ℝ))) j)
        | none => diagonalCost ((fun _ : Fin 1 => ((0 : ℝ), (2 : ℝ))) i))
      (Finset.mem_univ 0))
    cases h : M.finite 0 with
    | none =>
        exact le_trans
          (show (1 : ℝ≥0∞) ≤ diagonalCost ((0 : ℝ), (2 : ℝ)) by
            norm_num [diagonalCost])
          (by simpa [h] using hle)
    | some j =>
        have hj : j = 0 := by fin_cases j; rfl
        exact le_trans
          (show (1 : ℝ≥0∞) ≤ finitePairCost ((0 : ℝ), (2 : ℝ))
              ((0 : ℝ), (1 : ℝ)) by
            norm_num [finitePairCost, hj])
          (by simpa [h, hj] using hle)
  exact le_antisymm hupper hlower

/-! ## (F7) Two-point Rips-versus-Čech bounds -/

namespace TwoPoints

open TDA.Filtration.Cech.Examples.TwoPoints

/-- The diameter of the two-point label metric is `2`. -/
theorem diameter_eq : Rips.diameter metric Finset.univ = 2 := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    Rips.diameter_pair, metric_dist, dist_pts]

/-- The two-point Rips and Čech diagrams are at bottleneck distance at most `1`. -/
theorem rips_cech_line_le (k : Type) [Field k] (n : ℕ) :
    bottleneck (dgm k (Rips.filter metric) n) (dgm k (Cech.filter pts) n) ≤ 1 := by
  have h := Cech.bottleneck_rips_cech_dgm_le_half_diameter_real k metric pts metric_dist n
  rw [diameter_eq] at h
  (convert h using 1; norm_num)

end TwoPoints

namespace Diagonal

open TDA.Filtration.Cech.SupNormExamples.Diagonal

/-- The diameter of the diagonal sup-norm pair is `2`. -/
theorem diameter_eq : Rips.diameter metric Finset.univ = 2 := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    Rips.diameter_pair, metric_dist, dist_pts]

/-- The arctan persistence-image Rips-versus-Čech bound for the diagonal pair has the full
half-diameter constant, which is `1` here. -/
theorem rips_cech_image_arctan (n : ℕ) {K : Type*} [Fintype K]
    (P : K → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage 1
          (PersistenceImage.arctanWeight 1 zero_le_one) P
          (dgm ℚ (Rips.filter metric) n) -
        PersistenceImage.finiteDiagramImage 1
          (PersistenceImage.arctanWeight 1 zero_le_one) P
          (dgm ℚ (Cech.filter pts) n)‖ ≤
      (2 + 3 * √(π / 2)) *
        ((Fintype.card (dgm ℚ (Rips.filter metric) n).finiteOccurrences +
          Fintype.card (dgm ℚ (Cech.filter pts) n).finiteOccurrences : ℕ) : ℝ) * 1 := by
  have h := Cech.norm_finiteDiagramImage_rips_sub_cech_le ℚ metric pts metric_dist n
    one_pos zero_le_one Real.pi_div_two_pos.le
    (PersistenceImage.arctanWeight 1 zero_le_one) P hm hdisj
  rw [PersistenceImage.stabilityConstant_arctan, diameter_eq] at h
  convert h using 2 <;> norm_num

end Diagonal

/-! ## (F8) The sup-norm triangle -/

namespace Triangle

open TDA.Filtration.Cech.SupNormExamples.Triangle

/-- The diameter of the sup-norm triangle is `2`. -/
theorem diameter_eq : Rips.diameter metric Finset.univ = 2 := by
  apply le_antisymm
  · apply (Rips.diameter_le_iff metric Finset.univ 2).2
    refine ⟨zero_le_two, ?_⟩
    intro v hv w hw
    rw [metric_dist]
    exact dist_pts_le v w
  · have h := Rips.dist_le_diameter metric (s := Finset.univ) (v := 0) (w := 1)
      (by simp) (by simp)
    rw [metric_dist, dist_pts_zero_one] at h
    exact h

/-- The sup-norm triangle has Rips-versus-Čech bottleneck distance at most `1`. -/
theorem rips_cech_le (n : ℕ) :
    bottleneck (dgm ℚ (Rips.filter metric) n) (dgm ℚ (Cech.filter pts) n) ≤ 1 := by
  have h := Cech.bottleneck_rips_cech_dgm_le_half_diameter ℚ metric pts metric_dist n
  rw [diameter_eq] at h
  (convert h using 1; norm_num)

end Triangle

/-! ## (F9) Euclidean negative control -/

/-- The Euclidean triangle does not satisfy the sup-norm halving identity: its Čech complex at
`6/5` differs from the Rips sublevel at twice that radius. -/
theorem euclidean_complex_ne_ripsSublevel :
    Cech.complex TDA.Filtration.Cech.Examples.Triangle.pts (6 / 5) ≠
      (Rips.filter TDA.Filtration.Cech.Examples.Triangle.metric).sublevel (2 * (6 / 5)) := by
  intro hEq
  apply TDA.Filtration.Cech.Examples.Triangle.tri_not_mem_complex
  rw [hEq]
  (convert TDA.Filtration.Cech.Examples.Triangle.tri_mem_rips using 1; norm_num)

end TDA.Persistence.CechSupNormConsumersExamples
