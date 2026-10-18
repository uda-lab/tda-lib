import TDA.Persistence.LogScaleDiagramComparison
import TDA.Persistence.SublevelScaling
import TDA.Persistence.DiagramBottleneckScaling

set_option autoImplicit false

/-!
# Scaling and translation of log-scale persistence diagrams

Positive scaling of a filter translates its log-scale diagrams by `Real.log c` for every
`0 < c`.  The bottleneck distance is invariant under a common translation, and the
logarithmic shift isomorphism is supplied on both sides of `c = 1`.  The resulting
scale invariance also applies to the log-scale Rips--Čech comparison.

The translation-invariant cost is the one used by Cohen--Steiner, Edelsbrunner and Harer
(CSEH07); the shift and interleaving conventions follow Chazal, de Silva, Glisse and Oudot
(CdSGO16, §§3--4).  These are library extensions of the existing diagram and filtration APIs.
-/

universe u v u'

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits RealShift
open TDA.Filtration TDA.Simplicial
open TDA.Persistence.FiniteConstructible
open scoped Classical ENNReal NNReal

variable {V : Type u} [LinearOrder V]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TDA.Simplicial.TotalFace K)]

private def translateFinitePair (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + a, p.2 + a)

private theorem finitePairCost_translate (p q : ℝ × ℝ) (a : ℝ) :
    finitePairCost (translateFinitePair a p) (translateFinitePair a q) =
      finitePairCost p q := by
  unfold finitePairCost translateFinitePair
  rw [show p.1 + a - (q.1 + a) = p.1 - q.1 by ring,
    show p.2 + a - (q.2 + a) = p.2 - q.2 by ring]

private theorem diagonalCost_translate (p : ℝ × ℝ) (a : ℝ) :
    diagonalCost (translateFinitePair a p) = diagonalCost p := by
  unfold diagonalCost translateFinitePair
  rw [show (p.2 + a) - (p.1 + a) = p.2 - p.1 by ring]

private theorem essentialPairCost_translate (b c a : ℝ) :
    essentialPairCost (b + a) (c + a) = essentialPairCost b c := by
  unfold essentialPairCost
  rw [show b + a - (c + a) = b - c by ring]

private theorem occurrenceMatching_cost_translate
    {F₁ F₂ E₁ E₂ : Type*} [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (M : OccurrenceMatching F₁ F₂ E₁ E₂)
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ) (b : E₁ → ℝ) (c : E₂ → ℝ) (a : ℝ) :
    M.cost (translateFinitePair a ∘ x) (translateFinitePair a ∘ y)
      (fun i => b i + a) (fun j => c j + a) = M.cost x y b c := by
  classical
  unfold OccurrenceMatching.cost
  simp only [Function.comp_apply]
  congr 1
  · apply Finset.sup_congr rfl
    intro i hi
    cases h : M.finite i with
    | none => simp [h, diagonalCost_translate]
    | some j => simp [h, finitePairCost_translate]
  · congr 1
    · apply Finset.sup_congr rfl
      intro j hj
      by_cases h : ∃ i, M.finite i = some j
      · simp [h]
      · simp [h, diagonalCost_translate]
    · apply Finset.sup_congr rfl
      intro i hi
      simp [essentialPairCost_translate]

private theorem presentationBottleneck_translate
    {F₁ F₂ E₁ E₂ : Type*} [Fintype F₁] [Fintype F₂] [Fintype E₁] [Fintype E₂]
    (x : F₁ → ℝ × ℝ) (y : F₂ → ℝ × ℝ)
    (b : E₁ → ℝ) (c : E₂ → ℝ) (a : ℝ) :
    presentationBottleneck (translateFinitePair a ∘ x) (translateFinitePair a ∘ y)
      (fun i => b i + a) (fun j => c j + a) =
      presentationBottleneck x y b c := by
  unfold presentationBottleneck
  exact iInf_congr fun M => occurrenceMatching_cost_translate M x y b c a

private theorem finitePart_map_translate_points (s : Multiset (ℝ × WithTop ℝ)) (a : ℝ) :
    finitePart (s.map (translateDiagramPoint a)) =
      (finitePart s).map (fun p => (p.1 + a, p.2 + a)) := by
  simp only [finitePart, Multiset.filterMap_map, Multiset.map_filterMap]
  apply congrArg (fun f : (ℝ × WithTop ℝ) → Option (ℝ × ℝ) => s.filterMap f)
  funext p
  obtain ⟨b, d⟩ := p
  cases d <;> rfl

private theorem essentialPart_map_translate_points (s : Multiset (ℝ × WithTop ℝ)) (a : ℝ) :
    essentialPart (s.map (translateDiagramPoint a)) =
      (essentialPart s).map (fun b => b + a) := by
  simp only [essentialPart, Multiset.filterMap_map, Multiset.map_filterMap]
  apply congrArg (fun f : (ℝ × WithTop ℝ) → Option ℝ => s.filterMap f)
  funext p
  obtain ⟨b, d⟩ := p
  cases d <;> rfl

/-- Public finite-part formula for common diagram translation. -/
theorem finitePart_translateDiagram_points (D : Diagram ℝ) (a : ℝ) :
    finitePart (translateDiagram D a).points =
      (finitePart D.points).map (fun p => (p.1 + a, p.2 + a)) := by
  exact finitePart_map_translate_points D.points a

/-- Public essential-part formula for common diagram translation. -/
theorem essentialPart_translateDiagram_points (D : Diagram ℝ) (a : ℝ) :
    essentialPart (translateDiagram D a).points =
      (essentialPart D.points).map (fun b => b + a) := by
  exact essentialPart_map_translate_points D.points a

/-- The bottleneck distance is invariant under a common translation, including `⊤`. -/
theorem bottleneck_translateDiagram (D E : Diagram ℝ) (a : ℝ) :
    bottleneck (translateDiagram D a) (translateDiagram E a) = bottleneck D E := by
  rw [bottleneck_eq_presentation (translateDiagram D a) (translateDiagram E a)
    (translateFinitePair a ∘ fun p : D.finiteOccurrences => p.1)
    (translateFinitePair a ∘ fun p : E.finiteOccurrences => p.1)
    (fun i : D.essentialOccurrences => i.1 + a)
    (fun j : E.essentialOccurrences => j.1 + a)
    ((Multiset.map_univ _ _).trans (finitePart_translateDiagram_points D a).symm)
    ((Multiset.map_univ _ _).trans (finitePart_translateDiagram_points E a).symm)
    ((Multiset.map_univ _ _).trans (essentialPart_translateDiagram_points D a).symm)
    ((Multiset.map_univ _ _).trans (essentialPart_translateDiagram_points E a).symm)]
  rw [bottleneck_eq_presentation D E
    (fun p : D.finiteOccurrences => p.1)
    (fun p : E.finiteOccurrences => p.1)
    (fun i : D.essentialOccurrences => i.1)
    (fun j : E.essentialOccurrences => j.1)
    (Multiset.map_univ_coe _)
    (Multiset.map_univ_coe _)
    (Multiset.map_univ_coe _)
    (Multiset.map_univ_coe _)]
  exact presentationBottleneck_translate _ _ _ _ a

/-- Positive scaling preserves positivity on all non-vertex faces. -/
theorem positiveOnEdges_scale_iff {f : FilterFunction K ℝ} {c : ℝ} (hc : 0 < c) :
    PositiveOnEdges (f.scale c hc) ↔ PositiveOnEdges f := by
  constructor
  · intro h σ hσ
    exact pos_of_mul_pos_right (by simpa using h σ hσ) hc.le
  · intro h σ hσ
    simpa using mul_pos hc (h σ hσ)

/-- Positive-on-edges filters remain positive after positive scaling. -/
theorem PositiveOnEdges.scale {f : FilterFunction K ℝ}
    (hf : PositiveOnEdges f) {c : ℝ} (hc : 0 < c) :
    PositiveOnEdges (f.scale c hc) :=
  (positiveOnEdges_scale_iff hc).2 hf

/-- The positive-log critical values translate by `log c` under scaling. -/
theorem logCriticalValues_scale (f : FilterFunction K ℝ) {c : ℝ} (hc : 0 < c) :
    logCriticalValues (f.scale c hc) =
      (logCriticalValues f).image (fun x => x + Real.log c) := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, hσ, hlog⟩ := (mem_logCriticalValues (f.scale c hc) x).1 hx
    have hσ' : 0 < f.value σ :=
      pos_of_mul_pos_right (by simpa using hσ) hc.le
    refine Finset.mem_image.mpr ⟨Real.log (f.value σ),
      (mem_logCriticalValues f _).2 ⟨σ, hσ', rfl⟩, ?_⟩
    rw [← hlog, FilterFunction.scale_value, Real.log_mul hc.ne' hσ'.ne']
    ring
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨σ, hσ, hlog⟩ := (mem_logCriticalValues f y).1 hy
    apply (mem_logCriticalValues (f.scale c hc) _).2
    refine ⟨σ, ?_, ?_⟩
    · simpa using mul_pos hc hσ
    · rw [FilterFunction.scale_value, Real.log_mul hc.ne' hσ.ne', hlog]
      ring

/-- The positive-log critical-value cardinality is unchanged by positive scaling. -/
theorem logCriticalValues_scale_card (f : FilterFunction K ℝ) {c : ℝ} (hc : 0 < c) :
    (logCriticalValues (f.scale c hc)).card = (logCriticalValues f).card := by
  rw [logCriticalValues_scale]
  exact Finset.card_image_of_injective _ (add_left_injective (Real.log c))

/-- The increasing log grid translates pointwise under positive scaling. -/
theorem logGrid_scale_apply (f : FilterFunction K ℝ) {c : ℝ} (hc : 0 < c)
    (i : Fin (logCriticalValues (f.scale c hc)).card) :
    logGrid (f.scale c hc) i =
      logGrid f (Fin.cast (logCriticalValues_scale_card f hc) i) + Real.log c := by
  let h := logCriticalValues_scale_card f hc
  have hmem : ∀ i : Fin (logCriticalValues (f.scale c hc)).card,
      logGrid f (Fin.cast h i) + Real.log c ∈ logCriticalValues (f.scale c hc) := by
    intro i
    have hi : logGrid f (Fin.cast h i) ∈ logCriticalValues f :=
      logGrid_mem f (Fin.cast h i)
    have himage : logGrid f (Fin.cast h i) + Real.log c ∈
        (logCriticalValues f).image (fun x => x + Real.log c) :=
      Finset.mem_image.mpr ⟨logGrid f (Fin.cast h i), hi, rfl⟩
    exact (Finset.ext_iff.mp (logCriticalValues_scale f hc) _).mpr himage
  have hmono : StrictMono (fun i : Fin (logCriticalValues (f.scale c hc)).card =>
      logGrid f (Fin.cast h i) + Real.log c) := by
    intro i j hij
    exact add_lt_add_left ((logGrid f).strictMono (Fin.cast_strictMono h hij)) _
  have heq := Finset.orderEmbOfFin_unique (s := logCriticalValues (f.scale c hc))
    (k := (logCriticalValues (f.scale c hc)).card) rfl hmem hmono
  simpa [logGrid, h] using (congrFun heq i).symm

/-- Log-scale points translate by `log c` under positive scaling. -/
theorem logDgm_scale_points (k : Type u) [Field k] {n : ℕ} (hn : 1 ≤ n)
    (f : FilterFunction K ℝ) (hf : PositiveOnEdges f) {c : ℝ} (hc : 0 < c) :
    (logDgm k (f.scale c hc) n).points =
      (logDgm k f n).points.map (translateDiagramPoint (Real.log c)) := by
  rw [logDgm_points_eq_map_log k hn (hf.scale hc),
    dgm_scale k f n hc, Diagram.scale, Diagram.map_points,
    Multiset.map_map, logDgm_points_eq_map_log k hn hf, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p hp
  obtain ⟨b, d⟩ := p
  have hb := dgm_birth_pos k hn hf hp
  have hd := dgm_death_pos k hn hf hp
  cases d with
  | top =>
    have hlog : Real.log (c * b) = Real.log b + Real.log c := by
      rw [Real.log_mul hc.ne' hb.ne']
      ring
    refine Prod.ext ?_ ?_
    · change Real.log (c * b) = Real.log b + Real.log c
      exact hlog
    · change (⊤ : WithTop ℝ) = ⊤
      rfl
  | coe d =>
    have hd' : 0 < d := WithTop.coe_pos.mp hd
    refine Prod.ext ?_ ?_
    · change Real.log (c * b) = Real.log b + Real.log c
      rw [Real.log_mul hc.ne' hb.ne']
      ring
    · change (Real.log (c * d) : WithTop ℝ) =
        ((Real.log d + Real.log c : ℝ) : WithTop ℝ)
      exact congrArg (fun x : ℝ => (x : WithTop ℝ)) (by
        rw [Real.log_mul hc.ne' hd'.ne']
        ring)

/-- The full log-scale diagram translates by `log c` under positive scaling. -/
theorem logDgm_scale (k : Type u) [Field k] {n : ℕ} (hn : 1 ≤ n)
    (f : FilterFunction K ℝ) (hf : PositiveOnEdges f) {c : ℝ} (hc : 0 < c) :
    logDgm k (f.scale c hc) n = translateDiagram (logDgm k f n) (Real.log c) := by
  apply Diagram.ext
  simpa [translateDiagram] using logDgm_scale_points k hn f hf hc

/-- Successive positive scalings add their logarithmic translations. -/
theorem logDgm_scale_scale (k : Type u) [Field k] {n : ℕ} (hn : 1 ≤ n)
    (f : FilterFunction K ℝ) (hf : PositiveOnEdges f) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    logDgm k ((f.scale a ha).scale b hb) n =
      translateDiagram (logDgm k f n) (Real.log a + Real.log b) := by
  rw [FilterFunction.scale_scale, logDgm_scale k hn f hf (mul_pos hb ha)]
  rw [Real.log_mul hb.ne' ha.ne']
  rw [add_comm]

private theorem scale_inv_scale (f : FilterFunction K ℝ) {c : ℝ} (hc : 0 < c) :
    (f.scale c hc).scale c⁻¹ (inv_pos.mpr hc) = f := by
  apply FilterFunction.ext
  intro s
  simp [FilterFunction.scale_value, inv_mul_cancel_left₀ hc.ne']

/-- The logarithmic shift isomorphism for a factor `0 < c ≤ 1`. -/
noncomputable def logModule_scale_shiftIso_of_le_one
    (R : Type v) [Ring R] (n : ℕ) (f : FilterFunction K ℝ)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (shift (logParam c⁻¹)).obj (logModule R f n) ≅
      logModule R (f.scale c hc) n := by
  let hinv : 0 < c⁻¹ := inv_pos.mpr hc
  let hinv1 : 1 ≤ c⁻¹ := (one_le_inv₀ hc).2 hc1
  have hff : (f.scale c hc).scale c⁻¹ hinv = f := by
    simpa [hinv] using scale_inv_scale f hc
  exact eqToIso (congrArg (fun g =>
      (shift (logParam c⁻¹)).obj (logModule R g n)) hff.symm) ≪≫
    logModule_scale_shiftIso R n (f.scale c hc) hinv hinv1

/-- Component formula for the two-sided logarithmic shift isomorphism. -/
theorem logModule_scale_shiftIso_of_le_one_hom_app
    (R : Type v) [Ring R] (n : ℕ) (f : FilterFunction K ℝ)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (t : ℝ) :
    (logModule_scale_shiftIso_of_le_one R n f hc hc1).hom.app t =
      (eqToIso (congrArg (fun g =>
        (shift (logParam c⁻¹)).obj (logModule R g n))
        (show (f.scale c hc).scale c⁻¹ (inv_pos.mpr hc) = f by
          exact scale_inv_scale f hc).symm)).hom.app t ≫
        (logModule_scale_shiftIso R n (f.scale c hc) (inv_pos.mpr hc)
          ((one_le_inv₀ hc).2 hc1)).hom.app t := by
  rfl

/-- The log-scale bottleneck distance is invariant under common positive scaling. -/
theorem bottleneck_logDgm_scale (k : Type u) [Field k] {n : ℕ} (hn : 1 ≤ n)
    (f g : FilterFunction K ℝ) (hf : PositiveOnEdges f) (hg : PositiveOnEdges g)
    {c : ℝ} (hc : 0 < c) :
    bottleneck (logDgm k (f.scale c hc) n) (logDgm k (g.scale c hc) n) =
      bottleneck (logDgm k f n) (logDgm k g n) := by
  rw [logDgm_scale k hn f hf hc, logDgm_scale k hn g hg hc]
  exact bottleneck_translateDiagram _ _ _

/-- The real interleaving distance of log-scale modules is invariant under common scaling. -/
theorem realInterleavingDistance_logModule_scale
    (k : Type u) [Field k] {n : ℕ} (hn : 1 ≤ n)
    (f g : FilterFunction K ℝ) (hf : PositiveOnEdges f) (hg : PositiveOnEdges g)
    {c : ℝ} (hc : 0 < c) :
    realInterleavingDistance (logModule k (f.scale c hc) n)
        (logModule k (g.scale c hc) n) =
      realInterleavingDistance (logModule k f n) (logModule k g n) := by
  rw [← bottleneck_logDgm_eq_realInterleavingDistance k hn
      (hf.scale hc) (hg.scale hc),
    ← bottleneck_logDgm_eq_realInterleavingDistance k hn hf hg,
    bottleneck_logDgm_scale k hn f g hf hg hc]

namespace Rips

omit [LinearOrder V] in
/-- A metric scaled pointwise by `c` gives the scaled Rips filter. -/
theorem filter_eq_scale_of_dist (d d' : MetricSpace V) {c : ℝ}
    (hc : 0 < c) (h : ∀ v w, d'.dist v w = c * d.dist v w) :
    Rips.filter d' = (Rips.filter d).scale c hc := by
  apply FilterFunction.ext
  intro s
  change Rips.diameter d' s.val = c * Rips.diameter d s.val
  apply le_antisymm
  · apply (Rips.diameter_le_iff d' s.val _).2
    refine ⟨mul_nonneg hc.le (Rips.diameter_nonneg d s.val), ?_⟩
    intro v hv w hw
    rw [h]
    exact mul_le_mul_of_nonneg_left (Rips.dist_le_diameter d hv hw) hc.le
  · have hdiv : Rips.diameter d s.val ≤ Rips.diameter d' s.val / c := by
      apply (Rips.diameter_le_iff d s.val _).2
      refine ⟨div_nonneg (Rips.diameter_nonneg d' s.val) hc.le, ?_⟩
      intro v hv w hw
      apply (le_div_iff₀ hc).2
      calc
        d.dist v w * c = c * d.dist v w := mul_comm _ _
        _ = d'.dist v w := (h v w).symm
        _ ≤ Rips.diameter d' s.val := Rips.dist_le_diameter d' hv hw
    simpa [mul_comm] using (le_div_iff₀ hc).1 hdiv

end Rips

namespace Cech

variable {X : Type u'} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [LinearOrder V] in
private theorem radiusAt_smul (p : V → X) {c : ℝ} (hc : 0 < c) (y : X)
    (s : Finset V) :
    TDA.Filtration.Cech.radiusAt (fun v => c • p v) (c • y) s =
      c * TDA.Filtration.Cech.radiusAt p y s := by
  apply le_antisymm
  · apply (TDA.Filtration.Cech.radiusAt_le_iff _ _ _ _).2
    refine ⟨mul_nonneg hc.le (TDA.Filtration.Cech.radiusAt_nonneg p y s), ?_⟩
    intro v hv
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left
      (TDA.Filtration.Cech.dist_le_radiusAt p y hv) hc.le
  · have hdiv : TDA.Filtration.Cech.radiusAt p y s ≤
        TDA.Filtration.Cech.radiusAt (fun v => c • p v) (c • y) s / c := by
      apply (TDA.Filtration.Cech.radiusAt_le_iff p y s _).2
      refine ⟨div_nonneg
        (TDA.Filtration.Cech.radiusAt_nonneg (fun v => c • p v) (c • y) s) hc.le, ?_⟩
      intro v hv
      apply (le_div_iff₀ hc).2
      calc
        dist y (p v) * c = c * dist y (p v) := mul_comm _ _
        _ = dist (c • y) (c • p v) := by
          rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc]
        _ ≤ TDA.Filtration.Cech.radiusAt (fun v => c • p v) (c • y) s :=
          TDA.Filtration.Cech.dist_le_radiusAt (fun v => c • p v) (c • y) hv
    simpa [mul_comm] using (le_div_iff₀ hc).1 hdiv

omit [LinearOrder V] in
/-- Scaling all ambient points scales the Čech filter by the same factor. -/
theorem filter_smul (p : V → X) {c : ℝ} (hc : 0 < c) :
    Cech.filter (fun v => c • p v) = (Cech.filter p).scale c hc := by
  let e : X ≃ X :=
    { toFun := fun y => c • y
      invFun := fun x => c⁻¹ • x
      left_inv := by
        intro y
        change c⁻¹ • (c • y) = y
        rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      right_inv := by
        intro x
        change c • (c⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] }
  apply FilterFunction.ext
  intro s
  change (⨅ x : X, TDA.Filtration.Cech.radiusAt (fun v => c • p v) x s.val) =
    c * ⨅ y : X, TDA.Filtration.Cech.radiusAt p y s.val
  calc
    (⨅ x : X, TDA.Filtration.Cech.radiusAt (fun v => c • p v) x s.val) =
        ⨅ y : X, TDA.Filtration.Cech.radiusAt (fun v => c • p v) (c • y) s.val :=
      (e.surjective.iInf_comp _).symm
    _ = ⨅ y : X, c * TDA.Filtration.Cech.radiusAt p y s.val := by
      apply iInf_congr
      intro y
      exact radiusAt_smul p hc y s.val
    _ = c * ⨅ y : X, TDA.Filtration.Cech.radiusAt p y s.val := by
      rw [Real.mul_iInf_of_nonneg hc.le]

/-- Common scaling preserves the log-scale Rips--Čech bottleneck. -/
theorem bottleneck_logDgm_rips_cech_scale
    (k : Type u) [Field k] [Fintype V] (d d' : MetricSpace V) (p : V → X)
    {c : ℝ} (hc : 0 < c) (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    (h : ∀ v w, d'.dist v w = c * d.dist v w) {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm k (Rips.filter d') n)
        (logDgm k (Cech.filter (fun v => c • p v)) n) =
      bottleneck (logDgm k (Rips.filter d) n) (logDgm k (Cech.filter p) n) := by
  rw [Rips.filter_eq_scale_of_dist d d' hc h, filter_smul p hc]
  exact bottleneck_logDgm_scale (V := V) (K := Rips.fullComplex V) k hn _ _
    (positiveOnEdges_rips d) (positiveOnEdges_cech d p hd) hc

end Cech

end TDA.Persistence
