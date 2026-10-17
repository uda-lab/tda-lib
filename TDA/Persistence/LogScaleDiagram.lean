import TDA.Persistence.CechRipsInterleaving
import TDA.Persistence.SublevelConstructible
import TDA.Simplicial.H0Augmentation

set_option autoImplicit false

/-!
# Log-scale diagrams in degrees `n ≥ 1`

The log-scale module `logModule R f n` is the homology of the sublevel at `exp t`. Assume every
face with at least two vertices has positive value. Below the logarithm of the smallest
positive value the sublevel at `exp t` contains only vertices, so its homology vanishes in
every degree `n ≥ 1`. Between consecutive logarithms of positive values the sublevel does not
change. The log-scale module is therefore finite-constructible on the increasing enumeration
`logGrid f` of the logarithms of the positive critical values, and its module diagram on that
grid is the log-scale diagram `logDgm k f n`.

The finite-constructible isometry identifies the bottleneck distance of two log-scale diagrams
with the interleaving distance of the log-scale modules. A multiplicative sandwich
`g ≤ f ≤ c · g` bounds it by `log c`, and the Rips and Čech filters of finite metric data are
at bottleneck distance at most `log 2`.

In degree `0` every vertex of nonpositive value is present at every log time, so the log-scale
module is not constructible on any finite grid. No statement is made about degree `0`, and no
relation between `logDgm` and the radius-level diagram `dgm` is stated.

These are library extensions proved from the merged definitions.
-/

universe u v u'

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration
open TDA.Persistence.FiniteConstructible
open scoped NNReal ENNReal

variable {V : Type u} [LinearOrder V]

/-! ### Vanishing of higher homology -/

section Vanishing

variable {K : PreAbstractSimplicialComplex V} (R : Type v) [Ring R]

/-- A complex without `n`-faces has zero homology in degree `n`, over every ring. -/
theorem isZero_simplicialHomology_of_isEmpty_face (n : ℕ) [IsEmpty (Face K n)] :
    IsZero (simplicialHomology K R n) := by
  have hX : IsZero ((simplicialChainComplex K R).X n) := by
    rw [simplicialChainComplex_X]
    exact ModuleCat.isZero_of_subsingleton _
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX

/-- A complex whose faces have at most one vertex has zero homology in every degree `n ≥ 1`,
over every ring. -/
theorem isZero_simplicialHomology_of_card_le_one (hK : ∀ s ∈ K, s.card ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) : IsZero (simplicialHomology K R n) := by
  have : IsEmpty (Face K n) := ⟨fun σ => by
    have h1 := hK σ.1 σ.2.1
    have h2 := σ.2.2
    omega⟩
  exact isZero_simplicialHomology_of_isEmpty_face R n

end Vanishing

/-! ### Positivity off vertices -/

section Positivity

variable {K : PreAbstractSimplicialComplex V}

/-- Every face with at least two vertices has positive value. By monotonicity this is
equivalent to positivity on edges; vertex values are unrestricted. -/
def PositiveOnEdges (f : FilterFunction K ℝ) : Prop :=
  ∀ σ : TotalFace K, 2 ≤ σ.val.card → 0 < f.value σ

omit [LinearOrder V] in
/-- Positivity off vertices passes to a pointwise larger filter. -/
theorem PositiveOnEdges.of_le {f g : FilterFunction K ℝ} (hgf : ∀ s, g.value s ≤ f.value s)
    (hg : PositiveOnEdges g) : PositiveOnEdges f :=
  fun σ hσ => (hg σ hσ).trans_le (hgf σ)

end Positivity

omit [LinearOrder V] in
/-- The Rips filter of a metric is positive on every face with at least two vertices. -/
theorem positiveOnEdges_rips (d : MetricSpace V) : PositiveOnEdges (Rips.filter d) :=
  fun _ hσ => Rips.diameter_pos d hσ

namespace Cech

variable {X : Type u'} [PseudoMetricSpace X]

omit [LinearOrder V] in
/-- The Čech filter of labelled points is positive off vertices when a label metric is
compatible with the ambient distance. -/
theorem positiveOnEdges_cech (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) : PositiveOnEdges (Cech.filter p) := by
  intro σ hσ
  have h1 := positiveOnEdges_rips d σ hσ
  have h2 := Cech.rips_le_two_mul_filter_value d p hd σ
  linarith

end Cech

/-! ### The positive-log grid -/

section Grid

variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]

/-- The logarithms of the positive critical values. -/
noncomputable def logCriticalValues (f : FilterFunction K ℝ) : Finset ℝ :=
  (f.criticalValues.filter (fun c => 0 < c)).image Real.log

/-- The increasing enumeration of the logarithms of the positive critical values. -/
noncomputable def logGrid (f : FilterFunction K ℝ) : Fin (logCriticalValues f).card ↪o ℝ :=
  (logCriticalValues f).orderEmbOfFin rfl

omit [LinearOrder V] in
/-- Membership in the logarithms of the positive critical values. -/
theorem mem_logCriticalValues (f : FilterFunction K ℝ) (x : ℝ) :
    x ∈ logCriticalValues f ↔
      ∃ σ : TotalFace K, 0 < f.value σ ∧ Real.log (f.value σ) = x := by
  simp only [logCriticalValues, Finset.mem_image, Finset.mem_filter,
    FilterFunction.mem_criticalValues]
  constructor
  · rintro ⟨c, ⟨⟨σ, rfl⟩, hc⟩, rfl⟩
    exact ⟨σ, hc, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, ⟨⟨σ, rfl⟩, hσ⟩, rfl⟩

omit [LinearOrder V] in
/-- Every grid value is the logarithm of a positive face value. -/
theorem logGrid_mem (f : FilterFunction K ℝ) (i : Fin (logCriticalValues f).card) :
    logGrid f i ∈ logCriticalValues f :=
  Finset.orderEmbOfFin_mem _ rfl i

omit [LinearOrder V] in
/-- The logarithm of every positive face value is a grid value. -/
theorem exists_logGrid_eq (f : FilterFunction K ℝ) (σ : TotalFace K) (hσ : 0 < f.value σ) :
    ∃ i, logGrid f i = Real.log (f.value σ) := by
  have hmem : Real.log (f.value σ) ∈ Set.range (logGrid f) := by
    rw [logGrid, Finset.range_orderEmbOfFin]
    exact (mem_logCriticalValues f _).2 ⟨σ, hσ, rfl⟩
  exact hmem

omit [LinearOrder V] in
/-- The exponential of a grid value is a positive critical value. -/
theorem exp_logGrid_mem (f : FilterFunction K ℝ) (i : Fin (logCriticalValues f).card) :
    Real.exp (logGrid f i) ∈ f.criticalValues ∧ 0 < Real.exp (logGrid f i) := by
  obtain ⟨σ, hσ, hlog⟩ := (mem_logCriticalValues f _).1 (logGrid_mem f i)
  refine ⟨?_, Real.exp_pos _⟩
  rw [← hlog, Real.exp_log hσ]
  exact (f.mem_criticalValues _).2 ⟨σ, rfl⟩

omit [LinearOrder V] in
/-- Two ordered log times in the same cell of the positive-log grid have the same sublevel at
their exponentials. No positivity is assumed. -/
theorem sublevel_exp_eq_of_cellIndex_eq (f : FilterFunction K ℝ) {s t : ℝ} (hst : s ≤ t)
    (h : cellIndex (logGrid f) s = cellIndex (logGrid f) t) :
    f.sublevel (Real.exp s) = f.sublevel (Real.exp t) := by
  apply le_antisymm (f.sublevel_mono (Real.exp_le_exp.2 hst))
  intro σ hσ
  obtain ⟨hσK, hσt⟩ := (f.mem_sublevel_iff _ σ).1 hσ
  refine (f.mem_sublevel_iff _ σ).2 ⟨hσK, ?_⟩
  rcases le_or_gt (f.value ⟨σ, hσK⟩) 0 with hv | hv
  · exact hv.trans (Real.exp_pos s).le
  · obtain ⟨i, hi⟩ := exists_logGrid_eq f ⟨σ, hσK⟩ hv
    have hit : i.val < (cellIndex (logGrid f) t).val :=
      (lt_cellIndex_iff _ i t).2 (hi ▸ (Real.log_le_iff_le_exp hv).2 hσt)
    rw [← h] at hit
    have his := (lt_cellIndex_iff _ i s).1 hit
    rw [hi] at his
    exact (Real.log_le_iff_le_exp hv).1 his

omit [LinearOrder V] in
/-- Below every grid value, the sublevel at the exponential contains only vertices. -/
theorem card_le_one_of_mem_sublevel_exp {f : FilterFunction K ℝ} (hf : PositiveOnEdges f)
    {t : ℝ} (ht : ∀ i, t < logGrid f i) : ∀ s ∈ f.sublevel (Real.exp t), s.card ≤ 1 := by
  intro s hs
  obtain ⟨hsK, hst⟩ := (f.mem_sublevel_iff _ s).1 hs
  by_contra hcard
  have hv := hf ⟨s, hsK⟩ (show 2 ≤ s.card by omega)
  obtain ⟨i, hi⟩ := exists_logGrid_eq f ⟨s, hsK⟩ hv
  have hti := ht i
  rw [hi, Real.lt_log_iff_exp_lt hv] at hti
  exact absurd hst (not_le.2 hti)

variable (R : Type v) [Ring R] (n : ℕ)

/-- In every degree `n ≥ 1`, the log-scale module of a filter positive off vertices is
finite-constructible on the positive-log grid, over every ring. Vertex values are
unrestricted. -/
theorem logModule_isConstructible {f : FilterFunction K ℝ} (hn : 1 ≤ n)
    (hf : PositiveOnEdges f) : IsConstructible (logGrid f) (logModule R f n) where
  zero_left t ht := by
    change IsZero (simplicialHomology (f.sublevel (Real.exp t)) R n)
    exact isZero_simplicialHomology_of_card_le_one R (card_le_one_of_mem_sublevel_exp hf ht) hn
  isIso_map s t hst h :=
    isIso_simplicialHomologyIncl_of_eq R (sublevel_exp_eq_of_cellIndex_eq f hst h)
      (f.sublevel_mono (Real.exp_le_exp.2 hst)) n

end Grid

/-! ### The log-scale diagram and its bottleneck bounds -/

section Field

variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable (k : Type u) [Field k]

/-- Over a field, every fiber of the log-scale module of a filter on a finite complex is
finite-dimensional. -/
theorem logModule_finiteDimensional (n : ℕ) (f : FilterFunction K ℝ) (t : ℝ) :
    FiniteDimensional k ((logModule k f n).obj t) := by
  change FiniteDimensional k (simplicialHomology (f.sublevel (Real.exp t)) k n)
  let _ : Finite (Face K n) := faceFiniteOfTotalFinite K n
  let _ : Finite (Face (f.sublevel (Real.exp t)) n) :=
    Finite.of_injective (faceIncl (f.sublevel_le _) n) (by
      intro a b hab
      exact Subtype.ext (congrArg (fun s : Face K n => s.1) hab))
  infer_instance

/-- The log-scale diagram: the module diagram of the log-scale module on the positive-log grid.
The definition has no hypothesis. It represents the module through `barcodeRealizationIso`
under the hypotheses of `logModule_isConstructible`, namely degree `n ≥ 1` and positivity off
vertices. In degree `0` the module is not constructible on any finite grid when some vertex has
nonpositive value (`not_isConstructible_logModule_zero`), and the diagram does not represent
it. -/
noncomputable def logDgm (f : FilterFunction K ℝ) (n : ℕ) : Diagram ℝ :=
  moduleDiagram (logGrid f) (logModule k f n)
    (fun i => logModule_finiteDimensional k n f (logGrid f i))

/-- In every degree `n ≥ 1`, for two filters on the same finite complex that are positive off
vertices, the bottleneck distance of the log-scale diagrams is the interleaving distance of the
log-scale modules. The two grids are unrelated. -/
theorem bottleneck_logDgm_eq_realInterleavingDistance {n : ℕ} (hn : 1 ≤ n)
    {f g : FilterFunction K ℝ} (hf : PositiveOnEdges f) (hg : PositiveOnEdges g) :
    bottleneck (logDgm k f n) (logDgm k g n) =
      realInterleavingDistance (logModule k f n) (logModule k g n) :=
  bottleneck_eq_distance (logModule_isConstructible k n hn hf)
    (logModule_isConstructible k n hn hg) _ _

/-- A multiplicative sandwich `g ≤ f ≤ c · g` with `1 ≤ c` and `g` positive off vertices bounds
the bottleneck distance of the log-scale diagrams by `log c`, in every degree `n ≥ 1`. -/
theorem bottleneck_logDgm_le_log {n : ℕ} (hn : 1 ≤ n) {f g : FilterFunction K ℝ} {c : ℝ}
    (hc : 1 ≤ c) (hgf : ∀ s, g.value s ≤ f.value s) (hfc : ∀ s, f.value s ≤ c * g.value s)
    (hg : PositiveOnEdges g) :
    bottleneck (logDgm k f n) (logDgm k g n) ≤ ENNReal.ofReal (Real.log c) := by
  rw [bottleneck_logDgm_eq_realInterleavingDistance k hn (hg.of_le hgf) hg]
  exact realInterleavingDistance_log_le k n hc hgf hfc

end Field

namespace Cech

variable {X : Type u'} [PseudoMetricSpace X]
variable (k : Type u) [Field k]

/-- In every degree `n ≥ 1`, the log-scale Rips and Čech diagrams of finite metric data are at
bottleneck distance at most `log 2`, in every pseudometric ambient space. -/
theorem bottleneck_logDgm_rips_cech_le [Fintype V] (d : MetricSpace V) (p : V → X)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) {n : ℕ} (hn : 1 ≤ n) :
    bottleneck (logDgm k (Rips.filter d) n) (logDgm k (Cech.filter p) n) ≤
      ENNReal.ofReal (Real.log 2) :=
  bottleneck_logDgm_le_log k hn one_le_two (Cech.filter_value_le_rips d p hd)
    (Cech.rips_le_two_mul_filter_value d p hd) (positiveOnEdges_cech d p hd)

end Cech

/-! ### The degree-0 obstruction -/

section DegreeZero

variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]

/-- If some vertex has nonpositive value, the degree-0 log-scale module is not
finite-constructible on any finite grid: the vertex is present at every log time, so no zero
left tail exists. -/
theorem not_isConstructible_logModule_zero (k : Type v) [Field k] {m : ℕ} (c : Fin m ↪o ℝ)
    {f : FilterFunction K ℝ} (σ : TotalFace K) (hσ : σ.val.card = 1) (hfσ : f.value σ ≤ 0) :
    ¬ IsConstructible c (logModule k f 0) := by
  intro hM
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ∀ i, t < c i := by
    cases m with
    | zero => exact ⟨0, fun i => Fin.elim0 i⟩
    | succ m' =>
      exact ⟨c 0 - 1, fun i => by
        have := c.monotone (Fin.zero_le i)
        linarith⟩
  have hz : IsZero (simplicialHomology (f.sublevel (Real.exp t)) k 0) := hM.zero_left t ht
  have hσL : σ.val ∈ f.sublevel (Real.exp t) :=
    (f.mem_sublevel_iff _ _).2 ⟨σ.2, hfσ.trans (Real.exp_pos t).le⟩
  let τ : Face (f.sublevel (Real.exp t)) 0 := ⟨σ.val, hσL, hσ⟩
  let _ : Finite (TotalFace (f.sublevel (Real.exp t))) :=
    Finite.of_injective (fun s : TotalFace (f.sublevel (Real.exp t)) =>
      (⟨s.1, f.sublevel_le _ s.2⟩ : TotalFace K)) (by
        intro a b hab
        exact Subtype.ext (congrArg (fun s : TotalFace K => s.1) hab))
  have hpos := finrank_homologyIncl_range_pos_of_vertex (f.sublevel (Real.exp t)) k
    (le_refl (f.sublevel (Real.exp t))) τ
  have h0 : simplicialHomologyIncl k (le_refl (f.sublevel (Real.exp t))) 0 = 0 :=
    hz.eq_of_src _ _
  rw [h0, ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot] at hpos
  exact lt_irrefl 0 hpos

end DegreeZero

end TDA.Persistence
