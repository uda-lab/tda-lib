import TDA.Persistence.LogScaleDiagramComparison
import TDA.Persistence.ArctanPersistenceImage

set_option autoImplicit false

/-!
# Log-scale Rips-versus-Čech weighted-kernel and persistence-image consumers

The generic layer composes the multiplicative sandwich bound for log-scale diagrams with the
merged weighted Gaussian kernel and persistence-image stability results. The Čech layer composes
the general-ambient log-scale Rips-versus-Čech bottleneck bound with the same consumers, both at
the exact log-scale bottleneck and at the resulting `log 2` bound. These are library compositions:
the KFH18 and AE17 ingredients enter through the merged consumers, and the BL15-v4 ingredient
enters through `bottleneck_logDgm_le_log`.

The finite occurrence counts in the embedding and image consumers omit essential bars, while
essential bars remain part of the bottleneck comparison. The hypothesis `1 ≤ n` is necessary for
the positive-degree log-scale comparison. In degree `0`, `logDgm` does not represent the
log-scale module: `not_isConstructible_logModule_zero` gives the obstruction, so no `log 2`
consumer is available there.
-/

universe u u'

namespace TDA.Persistence

open TDA.Filtration
open TDA.Simplicial
open TDA.Persistence.FiniteConstructible
open scoped NNReal ENNReal

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable {A B : ℝ}

/-! ### Generic log-scale consumers -/

/-- Every log-scale diagram is positive, without hypotheses on the filter or degree. -/
theorem logDgm_isPositive (f : FilterFunction K ℝ) (n : ℕ) :
    (logDgm k f n).IsPositive := by
  unfold logDgm
  exact moduleDiagram_isPositive (logGrid f) (logModule k f n) _

/-- In positive degrees, a positive-off-vertices filter has the same finite-occurrence count in
its log-scale diagram and its radius-level diagram. -/
theorem card_finiteOccurrences_logDgm {f : FilterFunction K ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hf : PositiveOnEdges f) :
    Fintype.card (logDgm k f n).finiteOccurrences = Fintype.card (dgm k f n).finiteOccurrences := by
  classical
  rw [← logDgm_map_exp k hn hf]
  simp only [Diagram.finiteOccurrences, Multiset.card_coe, finitePart_map_points,
    Multiset.card_map]

/-- A multiplicative sandwich gives a finite bottleneck between the corresponding log-scale
diagrams. -/
theorem bottleneck_logDgm_lt_top_of_le_mul {n : ℕ} (hn : 1 ≤ n)
    {f g : FilterFunction K ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hgf : ∀ s, g.value s ≤ f.value s) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (hg : PositiveOnEdges g) : bottleneck (logDgm k f n) (logDgm k g n) < ⊤ :=
  (bottleneck_logDgm_le_log k hn hc hgf hfc hg).trans_lt ENNReal.ofReal_lt_top

/-- The real bottleneck of a multiplicative log-scale sandwich is at most `log c`. -/
theorem toReal_bottleneck_logDgm_le_log {n : ℕ} (hn : 1 ≤ n)
    {f g : FilterFunction K ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hgf : ∀ s, g.value s ≤ f.value s) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (hg : PositiveOnEdges g) :
    (bottleneck (logDgm k f n) (logDgm k g n)).toReal ≤ Real.log c := by
  have hbound := bottleneck_logDgm_le_log k hn hc hgf hfc hg
  simpa only [ENNReal.toReal_ofReal (Real.log_nonneg hc)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

/-- The weighted-kernel embedding difference of two multiplicatively sandwiched log-scale
diagrams is bounded by the occurrence count times `log c`. -/
theorem norm_diagramEmbedding_logDgm_sub_le_log {n : ℕ} (hn : 1 ≤ n)
    {f g : FilterFunction K ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hgf : ∀ s, g.value s ≤ f.value s) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (hg : PositiveOnEdges g) (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (logDgm k f n) -
        WeightedKernel.diagramEmbedding σ w (logDgm k g n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (logDgm k f n).finiteOccurrences +
          Fintype.card (logDgm k g n).finiteOccurrences : ℕ) : ℝ) * Real.log c := by
  exact (WeightedKernel.norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w _ _
    (logDgm_isPositive k f n) (logDgm_isPositive k g n)
    (bottleneck_logDgm_lt_top_of_le_mul k hn hc hgf hfc hg)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_logDgm_le_log k hn hc hgf hfc hg)
        (mul_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (Nat.cast_nonneg _)))

/-- The second-level Gaussian feature difference of two multiplicatively sandwiched log-scale
diagrams is bounded by the occurrence count times `log c`. -/
theorem norm_diagramGaussianFeature_logDgm_sub_le_log {n : ℕ} (hn : 1 ≤ n)
    {f g : FilterFunction K ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hgf : ∀ s, g.value s ≤ f.value s) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (hg : PositiveOnEdges g) (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramGaussianFeature σ τ w (logDgm k f n) -
        WeightedKernel.diagramGaussianFeature σ τ w (logDgm k g n)‖ ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (logDgm k f n).finiteOccurrences +
          Fintype.card (logDgm k g n).finiteOccurrences : ℕ) : ℝ) * Real.log c := by
  exact (WeightedKernel.norm_diagramGaussianFeature_sub_le_card_mul_bottleneck σ τ hA hB w _ _
    (logDgm_isPositive k f n) (logDgm_isPositive k g n)
    (bottleneck_logDgm_lt_top_of_le_mul k hn hc hgf hfc hg)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_logDgm_le_log k hn hc hgf hfc hg)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

/-- A `(k, w)`-Gaussian kernel value against a fixed diagram changes by at most the second-level
feature constant times the occurrence count and `log c` under a multiplicative sandwich. -/
theorem abs_gaussianDiagramKernel_logDgm_sub_le_log {n : ℕ} (hn : 1 ≤ n)
    {f g : FilterFunction K ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hgf : ∀ s, g.value s ≤ f.value s) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (hg : PositiveOnEdges g) (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : PersistenceImage.Weight A B) (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ w D (logDgm k f n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (logDgm k g n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (logDgm k f n).finiteOccurrences +
          Fintype.card (logDgm k g n).finiteOccurrences : ℕ) : ℝ) * Real.log c := by
  exact (WeightedKernel.abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck σ τ hA hB w D _ _
    (logDgm_isPositive k f n) (logDgm_isPositive k g n)
    (bottleneck_logDgm_lt_top_of_le_mul k hn hc hgf hfc hg)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_logDgm_le_log k hn hc hgf hfc hg)
        (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
          (abs_nonneg τ)) (Nat.cast_nonneg _)))

/-- The finite-part persistence-image difference of two multiplicatively sandwiched log-scale
diagrams is bounded by the image constant times the occurrence count and `log c`. -/
theorem norm_finiteDiagramImage_logDgm_sub_le_log {n : ℕ} (hn : 1 ≤ n)
    {f g : FilterFunction K ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hgf : ∀ s, g.value s ≤ f.value s) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (hg : PositiveOnEdges g) {Kp : Type*} [Fintype Kp] {σ : ℝ} (hσ : 0 < σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (P : Kp → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (logDgm k f n) -
        PersistenceImage.finiteDiagramImage σ w P (logDgm k g n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        ((Fintype.card (logDgm k f n).finiteOccurrences +
          Fintype.card (logDgm k g n).finiteOccurrences : ℕ) : ℝ) * Real.log c := by
  exact (PersistenceImage.norm_finiteDiagramImage_sub_le_card_mul_bottleneck hσ hA hB w P hm hdisj
    _ _ (logDgm_isPositive k f n) (logDgm_isPositive k g n)
    (bottleneck_logDgm_lt_top_of_le_mul k hn hc hgf hfc hg)).trans
      (mul_le_mul_of_nonneg_left
        (toReal_bottleneck_logDgm_le_log k hn hc hgf hfc hg)
        (mul_nonneg (PersistenceImage.stabilityConstant_nonneg hσ hA hB)
          (Nat.cast_nonneg _)))

namespace Cech

open Real MeasureTheory Set PersistenceImage

variable {X : Type u'} [PseudoMetricSpace X]
variable (k : Type u) [Field k]

/-! ### Exact log-scale bottleneck consumers -/

/-- The log-scale Rips and Čech diagrams of one finite configuration have finite bottleneck in
every positive degree. -/
theorem bottleneck_logDgm_rips_cech_lt_top [Fintype V] (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm k (Rips.filter d) n) (logDgm k (Cech.filter p) n) < ⊤ :=
  (bottleneck_logDgm_rips_cech_le k d p hd hn).trans_lt ENNReal.ofReal_lt_top

/-- The real bottleneck of the log-scale Rips-versus-Čech comparison is at most `log 2`. -/
theorem toReal_bottleneck_logDgm_rips_cech_le [Fintype V] (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n) :
    (bottleneck (logDgm k (Rips.filter d) n) (logDgm k (Cech.filter p) n)).toReal ≤ Real.log 2 := by
  have hbound := bottleneck_logDgm_rips_cech_le k d p hd hn
  simpa only [ENNReal.toReal_ofReal (Real.log_nonneg one_le_two)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

/-- The weighted-kernel embedding difference of log-scale Rips and Čech diagrams is bounded by
the exact log-scale bottleneck. -/
theorem norm_diagramEmbedding_logDgm_rips_sub_cech_le_bottleneck [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (logDgm k (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ w (logDgm k (Cech.filter p) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (logDgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (logDgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) *
            (bottleneck (logDgm k (Rips.filter d) n)
              (logDgm k (Cech.filter p) n)).toReal := by
  exact WeightedKernel.norm_diagramEmbedding_sub_le_card_mul_bottleneck σ hA hB w _ _
    (logDgm_isPositive k (Rips.filter d) n) (logDgm_isPositive k (Cech.filter p) n)
    (bottleneck_logDgm_rips_cech_lt_top k d p hd hn)

/-- The second-level Gaussian feature difference of log-scale Rips and Čech diagrams is bounded
by the exact log-scale bottleneck. -/
theorem norm_diagramGaussianFeature_logDgm_rips_sub_cech_le_bottleneck [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramGaussianFeature σ τ w (logDgm k (Rips.filter d) n) -
        WeightedKernel.diagramGaussianFeature σ τ w (logDgm k (Cech.filter p) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (logDgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (logDgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) *
            (bottleneck (logDgm k (Rips.filter d) n)
              (logDgm k (Cech.filter p) n)).toReal := by
  exact WeightedKernel.norm_diagramGaussianFeature_sub_le_card_mul_bottleneck σ τ hA hB w _ _
    (logDgm_isPositive k (Rips.filter d) n) (logDgm_isPositive k (Cech.filter p) n)
    (bottleneck_logDgm_rips_cech_lt_top k d p hd hn)

/-- A fixed-diagram `(k, w)`-Gaussian kernel value on log-scale Rips and Čech diagrams is bounded
by the exact log-scale bottleneck. -/
theorem abs_gaussianDiagramKernel_logDgm_rips_sub_cech_le_bottleneck [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ w D (logDgm k (Rips.filter d) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (logDgm k (Cech.filter p) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (logDgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (logDgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) *
            (bottleneck (logDgm k (Rips.filter d) n)
              (logDgm k (Cech.filter p) n)).toReal := by
  exact WeightedKernel.abs_gaussianDiagramKernel_sub_le_card_mul_bottleneck σ τ hA hB w D _ _
    (logDgm_isPositive k (Rips.filter d) n) (logDgm_isPositive k (Cech.filter p) n)
    (bottleneck_logDgm_rips_cech_lt_top k d p hd hn)

/-- The finite-part persistence-image difference of log-scale Rips and Čech diagrams is bounded
by the exact log-scale bottleneck. -/
theorem norm_finiteDiagramImage_logDgm_rips_sub_cech_le_bottleneck [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    {Kp : Type*} [Fintype Kp] {σ : ℝ} (hσ : 0 < σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (P : Kp → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (logDgm k (Rips.filter d) n) -
        PersistenceImage.finiteDiagramImage σ w P (logDgm k (Cech.filter p) n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        ((Fintype.card (logDgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (logDgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) *
            (bottleneck (logDgm k (Rips.filter d) n)
              (logDgm k (Cech.filter p) n)).toReal := by
  exact PersistenceImage.norm_finiteDiagramImage_sub_le_card_mul_bottleneck hσ hA hB w P hm hdisj
    _ _ (logDgm_isPositive k (Rips.filter d) n) (logDgm_isPositive k (Cech.filter p) n)
    (bottleneck_logDgm_rips_cech_lt_top k d p hd hn)

/-! ### `log 2` consumers -/

/-- The weighted-kernel embedding difference of log-scale Rips and Čech diagrams is bounded by
the radius-level occurrence count times `log 2`. -/
theorem norm_diagramEmbedding_logDgm_rips_sub_cech_le [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramEmbedding σ w (logDgm k (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ w (logDgm k (Cech.filter p) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) * Real.log 2 := by
  have h := norm_diagramEmbedding_logDgm_rips_sub_cech_le_bottleneck k d p hd hn σ hA hB w
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (toReal_bottleneck_logDgm_rips_cech_le k d p hd hn)
    (mul_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
      (Nat.cast_nonneg _)))
  rw [card_finiteOccurrences_logDgm k hn (positiveOnEdges_rips d),
    card_finiteOccurrences_logDgm k hn (positiveOnEdges_cech d p hd)] at h'
  exact h'

/-- The second-level Gaussian feature difference of log-scale Rips and Čech diagrams is bounded
by the radius-level occurrence count times `log 2`. -/
theorem norm_diagramGaussianFeature_logDgm_rips_sub_cech_le [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B) :
    ‖WeightedKernel.diagramGaussianFeature σ τ w (logDgm k (Rips.filter d) n) -
        WeightedKernel.diagramGaussianFeature σ τ w (logDgm k (Cech.filter p) n)‖ ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) * Real.log 2 := by
  have h := norm_diagramGaussianFeature_logDgm_rips_sub_cech_le_bottleneck k d p hd hn σ τ hA hB w
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (toReal_bottleneck_logDgm_rips_cech_le k d p hd hn)
    (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
      (abs_nonneg τ)) (Nat.cast_nonneg _)))
  rw [card_finiteOccurrences_logDgm k hn (positiveOnEdges_rips d),
    card_finiteOccurrences_logDgm k hn (positiveOnEdges_cech d p hd)] at h'
  exact h'

/-- A fixed-diagram `(k, w)`-Gaussian kernel value on log-scale Rips and Čech diagrams is bounded
by the radius-level occurrence count times `log 2`. -/
theorem abs_gaussianDiagramKernel_logDgm_rips_sub_cech_le [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ τ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ w D (logDgm k (Rips.filter d) n) -
        WeightedKernel.gaussianDiagramKernel σ τ w D (logDgm k (Cech.filter p) n)| ≤
      WeightedKernel.stabilityConstant σ A B / |τ| *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) * Real.log 2 := by
  have h := abs_gaussianDiagramKernel_logDgm_rips_sub_cech_le_bottleneck k d p hd hn σ τ hA hB w D
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (toReal_bottleneck_logDgm_rips_cech_le k d p hd hn)
    (mul_nonneg (div_nonneg (WeightedKernel.stabilityConstant_nonneg σ hA hB)
      (abs_nonneg τ)) (Nat.cast_nonneg _)))
  rw [card_finiteOccurrences_logDgm k hn (positiveOnEdges_rips d),
    card_finiteOccurrences_logDgm k hn (positiveOnEdges_cech d p hd)] at h'
  exact h'

/-- The finite-part persistence-image difference of log-scale Rips and Čech diagrams is bounded
by the radius-level occurrence count times `log 2`. -/
theorem norm_finiteDiagramImage_logDgm_rips_sub_cech_le [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    {Kp : Type*} [Fintype Kp] {σ : ℝ} (hσ : 0 < σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (w : PersistenceImage.Weight A B)
    (P : Kp → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ w P (logDgm k (Rips.filter d) n) -
        PersistenceImage.finiteDiagramImage σ w P (logDgm k (Cech.filter p) n)‖ ≤
      PersistenceImage.stabilityConstant σ A B *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) * Real.log 2 := by
  have h := norm_finiteDiagramImage_logDgm_rips_sub_cech_le_bottleneck k d p hd hn hσ hA hB w
    P hm hdisj
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (toReal_bottleneck_logDgm_rips_cech_le k d p hd hn)
    (mul_nonneg (PersistenceImage.stabilityConstant_nonneg hσ hA hB)
      (Nat.cast_nonneg _)))
  rw [card_finiteOccurrences_logDgm k hn (positiveOnEdges_rips d),
    card_finiteOccurrences_logDgm k hn (positiveOnEdges_cech d p hd)] at h'
  exact h'

/-- The arctan-weight embedding instance of the log-scale `log 2` Rips-versus-Čech bound. -/
theorem norm_diagramEmbedding_logDgm_rips_sub_cech_le_arctan [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    ‖WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (logDgm k (Rips.filter d) n) -
        WeightedKernel.diagramEmbedding σ (PersistenceImage.arctanWeight C hC)
          (logDgm k (Cech.filter p) n)‖ ≤
      (2 * C + √2 * π / (2 * |σ|)) *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) * Real.log 2 := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    norm_diagramEmbedding_logDgm_rips_sub_cech_le k d p hd hn σ hC Real.pi_div_two_pos.le
      (PersistenceImage.arctanWeight C hC)

/-- The arctan-weight fixed-diagram Gaussian-kernel instance of the log-scale `log 2`
Rips-versus-Čech bound. -/
theorem abs_gaussianDiagramKernel_logDgm_rips_sub_cech_le_arctan [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    (σ τ : ℝ) {C : ℝ} (hC : 0 ≤ C) (D : Diagram ℝ) :
    |WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (logDgm k (Rips.filter d) n) -
        WeightedKernel.gaussianDiagramKernel σ τ (PersistenceImage.arctanWeight C hC) D
          (logDgm k (Cech.filter p) n)| ≤
      (2 * C + √2 * π / (2 * |σ|)) / |τ| *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) * Real.log 2 := by
  simpa only [WeightedKernel.stabilityConstant_arctan] using
    abs_gaussianDiagramKernel_logDgm_rips_sub_cech_le k d p hd hn σ τ hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC) D

/-- The arctan-weight finite-part persistence-image instance of the log-scale `log 2`
Rips-versus-Čech bound. -/
theorem norm_finiteDiagramImage_logDgm_rips_sub_cech_le_arctan [Fintype V]
    (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n)
    {Kp : Type*} [Fintype Kp] {σ : ℝ} (hσ : 0 < σ) {C : ℝ} (hC : 0 ≤ C)
    (P : Kp → Set (ℝ × ℝ)) (hm : ∀ j, MeasurableSet (P j))
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ‖PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (logDgm k (Rips.filter d) n) -
        PersistenceImage.finiteDiagramImage σ (PersistenceImage.arctanWeight C hC) P
          (logDgm k (Cech.filter p) n)‖ ≤
      (2 * C + 3 * √(π / 2) / σ) *
        ((Fintype.card (dgm k (Rips.filter d) n).finiteOccurrences +
          Fintype.card (dgm k (Cech.filter p) n).finiteOccurrences : ℕ) : ℝ) * Real.log 2 := by
  simpa only [PersistenceImage.stabilityConstant_arctan] using
    norm_finiteDiagramImage_logDgm_rips_sub_cech_le k d p hd hn hσ hC
      Real.pi_div_two_pos.le (PersistenceImage.arctanWeight C hC) P hm hdisj

end Cech
end TDA.Persistence
