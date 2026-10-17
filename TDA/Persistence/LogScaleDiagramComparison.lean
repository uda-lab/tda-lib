import TDA.Persistence.LogScaleDiagram
import TDA.Persistence.ConstructibleRefinementBarcode
import TDA.Persistence.DiagramMap

set_option autoImplicit false

/-!
# Comparison of log-scale and radius-level diagrams

These are library extensions proved from the merged module-diagram, constructibility,
and log-scale definitions. The exponential is used to transport the log diagram to
the positive radius grid; no degree-zero log-scale statement is made.
-/

universe u v w

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits TDA.Simplicial TDA.Filtration
open TDA.Persistence.FiniteConstructible
open scoped NNReal ENNReal

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable (R : Type v) [Ring R]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable {m : ℕ}

/-- Mapping the module diagram of a reindexed module agrees with the module diagram
on the transported grid. -/
theorem moduleDiagram_reindex_map (c : Fin m ↪o ℝ) (φ : ℝ ↪o ℝ)
    (M : PModule.{u,0,u} k ℝ)
    (hfd : ∀ i, FiniteDimensional k (M.obj (φ (c i)))) :
    (moduleDiagram c (reindex φ.toOrderHom M) hfd).map φ =
      moduleDiagram (c.trans φ) M hfd := by
  unfold moduleDiagram
  apply Diagram.ext
  rw [Diagram.map_points, RealBarcode.ofIndexBars_points,
    RealBarcode.ofIndexBars_points, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro I hI
  unfold RealBarcode.endpoints
  by_cases hd : I.death < m
  · simp [hd, RelEmbedding.trans_apply]
  · simp [hd, RelEmbedding.trans_apply]

/-- The exponential as a strictly increasing order embedding of the reals. -/
noncomputable def expEmb : ℝ ↪o ℝ :=
  OrderEmbedding.ofStrictMono Real.exp Real.exp_strictMono

@[simp] theorem expEmb_apply (t : ℝ) : expEmb t = Real.exp t :=
  by
    change OrderEmbedding.ofStrictMono Real.exp Real.exp_strictMono t = Real.exp t
    exact congrFun (OrderEmbedding.coe_ofStrictMono Real.exp_strictMono) t

/-- The order hom underlying `expEmb` is the log-scale reindexing hom. -/
theorem expEmb_toOrderHom : expEmb.toOrderHom = expHom := by
  apply OrderHom.ext _ _
  exact funext (fun t => rfl)

/-- The positive radius grid obtained by exponentiating the positive-log grid. -/
noncomputable def positiveGrid (f : FilterFunction K ℝ) :
    Fin (logCriticalValues f).card ↪o ℝ :=
  (logGrid f).trans expEmb

omit [LinearOrder V] in
@[simp] theorem positiveGrid_apply (f : FilterFunction K ℝ)
    (i : Fin (logCriticalValues f).card) :
    positiveGrid f i = Real.exp (logGrid f i) := by
  rw [positiveGrid, RelEmbedding.trans_apply, expEmb_apply]

/-- The range of the positive grid is exactly the positive attained critical values. -/
theorem mem_range_positiveGrid_iff (f : FilterFunction K ℝ) (x : ℝ) :
    x ∈ Set.range (positiveGrid f) ↔ x ∈ f.criticalValues ∧ 0 < x := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [positiveGrid_apply]
    exact exp_logGrid_mem f i
  · rintro ⟨hx, hpos⟩
    obtain ⟨σ, hσ⟩ := (f.mem_criticalValues x).1 hx
    have hposσ : 0 < f.value σ := by simpa [hσ] using hpos
    obtain ⟨i, hi⟩ := exists_logGrid_eq f σ hposσ
    refine ⟨i, ?_⟩
    rw [positiveGrid_apply, hi, Real.exp_log hposσ, hσ]

/-- The positive grid refines the full critical-value grid. -/
theorem refines_positiveGrid (f : FilterFunction K ℝ) :
    Refines (positiveGrid f) f.criticalValue := by
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  rw [positiveGrid_apply, FilterFunction.criticalValue,
    Finset.range_orderEmbOfFin]
  exact (exp_logGrid_mem f i).1

private theorem card_le_one_of_mem_sublevel_positiveGrid
    {f : FilterFunction K ℝ} (hf : PositiveOnEdges f) {t : ℝ}
    (ht : ∀ i, t < positiveGrid f i) :
    ∀ s ∈ f.sublevel t, s.card ≤ 1 := by
  intro s hs
  obtain ⟨hsK, hst⟩ := (f.mem_sublevel_iff _ s).1 hs
  by_contra hcard
  have hv := hf ⟨s, hsK⟩ (show 2 ≤ s.card by omega)
  have hcrit : f.value ⟨s, hsK⟩ ∈ f.criticalValues :=
    (f.mem_criticalValues _).2 ⟨⟨s, hsK⟩, rfl⟩
  obtain ⟨i, hi⟩ := (mem_range_positiveGrid_iff f _).2 ⟨hcrit, hv⟩
  have hti := ht i
  rw [hi] at hti
  exact (not_lt_of_ge hst) hti

/-- In degrees at least one, the radius sublevel module is constructible on the
positive critical grid under positivity on edges. -/
theorem sublevelModule_isConstructible_positiveGrid {f : FilterFunction K ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hf : PositiveOnEdges f) :
    IsConstructible (positiveGrid f) (sublevelModule R f n) := by
  have zero_left' : ∀ t, (∀ i, t < positiveGrid f i) →
      IsZero ((sublevelModule R f n).obj t) := by
    intro t ht
    change IsZero (simplicialHomology (f.sublevel t) R n)
    exact isZero_simplicialHomology_of_card_le_one R
      (card_le_one_of_mem_sublevel_positiveGrid hf ht) hn
  exact
    { zero_left := zero_left'
      isIso_map := by
        intro s t hst h
        by_cases hzero : cellIndex (positiveGrid f) t = 0
        · have hs_zero : cellIndex (positiveGrid f) s = 0 := h.trans hzero
          change IsIso (simplicialHomologyIncl R (f.sublevel_mono hst) n)
          exact (zero_left' s ((cellIndex_eq_zero_iff _ _).mp hs_zero)).isIso
            (zero_left' t ((cellIndex_eq_zero_iff _ _).mp hzero)) _
        · have hs_nonzero : cellIndex (positiveGrid f) s ≠ 0 := by
            intro hs_zero
            apply hzero
            rw [← h, hs_zero]
          have hs_pos : 0 < (cellIndex (positiveGrid f) s).val :=
            Nat.pos_of_ne_zero (fun h => hs_nonzero (Fin.ext h))
          have hcard : 0 < (logCriticalValues f).card := by
            have hs_lt := (cellIndex (positiveGrid f) s).isLt
            omega
          let i₀ : Fin (logCriticalValues f).card := ⟨0, hcard⟩
          have hi₀ : positiveGrid f i₀ ≤ s := by
            apply (lt_cellIndex_iff (positiveGrid f) i₀ s).1
            simpa [i₀] using hs_pos
          have hspos : 0 < s := by
            exact lt_of_lt_of_le
              (by rw [positiveGrid_apply]; exact Real.exp_pos _) hi₀
          have heq : f.sublevel s = f.sublevel t := by
            apply le_antisymm (f.sublevel_mono hst)
            intro σ hσ
            obtain ⟨hσK, hσt⟩ := (f.mem_sublevel_iff _ σ).1 hσ
            rcases le_or_gt (f.value ⟨σ, hσK⟩) 0 with hv | hv
            · exact (f.mem_sublevel_iff _ σ).2 ⟨hσK, hv.trans hspos.le⟩
            · have hcrit : f.value ⟨σ, hσK⟩ ∈ f.criticalValues :=
                (f.mem_criticalValues _).2 ⟨⟨σ, hσK⟩, rfl⟩
              obtain ⟨i, hi⟩ := (mem_range_positiveGrid_iff f _).2 ⟨hcrit, hv⟩
              have hle : positiveGrid f i ≤ t := by simpa [hi] using hσt
              have hit : i.val < (cellIndex (positiveGrid f) t).val :=
                (lt_cellIndex_iff _ i t).2 hle
              rw [← h] at hit
              have his := (lt_cellIndex_iff _ i s).1 hit
              exact (f.mem_sublevel_iff _ σ).2 ⟨hσK, by simpa [hi] using his⟩
          exact isIso_simplicialHomologyIncl_of_eq R heq
            (f.sublevel_mono hst) n }

/-- Exponentiating the log-scale diagram recovers the radius-level diagram in
positive degrees under positivity on edges. -/
theorem logDgm_map_exp {f : FilterFunction K ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hf : PositiveOnEdges f) : (logDgm k f n).map expEmb = dgm k f n := by
  unfold logDgm
  change
    (moduleDiagram (logGrid f)
      (reindex expEmb.toOrderHom (sublevelModule k f n))
      (fun i => logModule_finiteDimensional k n f (logGrid f i))).map expEmb =
      dgm k f n
  rw [moduleDiagram_reindex_map k (logGrid f) expEmb (sublevelModule k f n)
    (fun i => logModule_finiteDimensional k n f (logGrid f i))]
  change moduleDiagram (positiveGrid f) (sublevelModule k f n)
      (fun i => logModule_finiteDimensional k n f (logGrid f i)) = dgm k f n
  rw [← moduleDiagram_refinement (sublevelModule k f n) (refines_positiveGrid f)
    (sublevelModule_isConstructible_positiveGrid k hn hf)
    (fun i => logModule_finiteDimensional k n f (logGrid f i))]
  exact moduleDiagram_sublevelModule k n f

/-- The log-scale points are obtained from radius-level points by applying logarithm
to both finite coordinates, with the essential death fixed. -/
theorem logDgm_points_eq_map_log {f : FilterFunction K ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hf : PositiveOnEdges f) :
    (logDgm k f n).points =
      (dgm k f n).points.map (fun p => (Real.log p.1, WithTop.map Real.log p.2)) := by
  rw [← logDgm_map_exp k hn hf, Diagram.map_points, Multiset.map_map]
  conv_lhs => rw [← Multiset.map_id' (logDgm k f n).points]
  apply Multiset.map_congr rfl
  intro p hp
  obtain ⟨b, d⟩ := p
  cases d <;> simp [Function.comp_def]

/-- Every birth of a positive-degree radius-level diagram is positive. -/
theorem dgm_birth_pos {f : FilterFunction K ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hf : PositiveOnEdges f) {p : ℝ × WithTop ℝ} (hp : p ∈ (dgm k f n).points) :
    0 < p.1 := by
  rw [← logDgm_map_exp k hn hf, Diagram.map_points] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  simpa [expEmb_apply] using Real.exp_pos q.1

/-- Every death of a positive-degree radius-level diagram is positive; essential deaths
are handled by the top element of `WithTop ℝ`. -/
theorem dgm_death_pos {f : FilterFunction K ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hf : PositiveOnEdges f) {p : ℝ × WithTop ℝ} (hp : p ∈ (dgm k f n).points) :
    (0 : WithTop ℝ) < p.2 := by
  rw [← logDgm_map_exp k hn hf, Diagram.map_points] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  cases q.2 with
  | top => simp
  | coe d =>
      simp only [WithTop.map_coe, expEmb_apply]
      exact WithTop.coe_pos.mpr (Real.exp_pos d)

end TDA.Persistence
