import TDA.Mapper.GraphPLCosheaf
import TDA.Reeb.ConstructibleQuotient
import TDA.Reeb.ConstructibleComparison
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.ProjIcc

/-!
# The Reeb quotient of graph-PL height

For a finite graph and a graph-PL height, this module constructs the direct continuous,
height-preserving map from the graph realization to the realization of its finite graph-PL Reeb
data, proves its descent to a homeomorphism `ReebQuotient (plHeight G h) ≃ₜ` the finite
realization, and proves the slice isomorphism with `RGraph.toOver S (graphPLReebData G h S)`
for every covering list.  It also proves the coherence with `graphPLCosheafIso` and the
list-free corollaries that the Reeb quotient is an ℝ-graph, that its interval-component
comparison is an isomorphism, and that its geometric interleaving distance is the corresponding
interleaving distance of interval-component precosheaves.

The general statements use `[Finite V]` and a covering list
`CoversVertexHeights S h`; the realization and homeomorphism are universe-polymorphic, while the
statements over `Over (TopCat.of ℝ)`, the coherence with the graph-PL cosheaf, and the final
corollaries use `V : Type` because the corresponding categorical APIs live in universe `0`.
The route is direct: first construct the height-preserving map, descend it through
`RGraph.quotientLift`, and use compactness of the quotient together with Hausdorffness of the
finite realization.  The graph-PL statements here are library results and make no external source
claim; the shape of the quotient argument is the one suggested by DMP15 Proposition 2.12.
Constructibility of `graphPLOver G h` and the identification of
`graphPLReebQuotientIsoOfIso` with the general `quotientIsoOfIso` are proved in
`TDA.Mapper.GraphPLConstructible`.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Reeb.RGraph

noncomputable section

universe u

section general

variable {V : Type u} [Finite V] (G : SimpleGraph V) (h : V → ℝ) {n : ℕ} {S : CriticalValues n}

/-- The graph realization is compact when its vertex type is finite. -/
theorem compactSpace_realization : CompactSpace (Realization G) := by
  classical
  let _ : TopologicalSpace V := ⊥
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let _ : Fintype G.Dart := SimpleGraph.Dart.fintype
  let _ : CompactSpace V := @Finite.compactSpace V ⊥ inferInstance
  let _ : CompactSpace (Σ _ : G.Dart, unitInterval) := by
    constructor
    rw [Sigma.univ]
    exact isCompact_iUnion fun d => isCompact_range continuous_sigmaMk
  let _ : CompactSpace (Cells G) := by
    constructor
    change IsCompact (Set.univ : Set (V ⊕ Σ _ : G.Dart, unitInterval))
    rw [← range_inl_union_range_inr]
    exact (isCompact_range continuous_inl).union (isCompact_range continuous_inr)
  exact Quot.compactSpace

/-- Some finite critical-value list covers all vertex heights. -/
theorem exists_coversVertexHeights : ∃ (n : ℕ) (S : CriticalValues n), CoversVertexHeights S h := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · refine ⟨0, ⟨(fun _ : Fin 1 => (0 : ℝ)), ?_⟩, ?_⟩
    · let _ : Subsingleton (Fin (0 + 1)) := ⟨fun i j =>
        (Fin.eq_zero i).trans (Fin.eq_zero j).symm⟩
      exact Subsingleton.strictMono _
    · intro v
      exact isEmptyElim v
  · let _ : Nonempty V := hV
    let _ : Fintype V := Fintype.ofFinite V
    refine ⟨_, vertexHeightLevels h, ?_⟩
    exact coversVertexHeights_vertexHeightLevels h

omit [Finite V] in
private theorem reebQuot_dartHeight_mem_Icc (d : G.Dart) (t : unitInterval) :
    dartHeight h d t ∈ Icc (min (h d.fst) (h d.snd)) (max (h d.fst) (h d.snd)) := by
  rcases le_total (h d.fst) (h d.snd) with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    change h d.fst ≤ (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ∧
      (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ≤ h d.snd
    constructor
    · nlinarith [mul_nonneg t.2.1 (sub_nonneg.2 hab)]
    · nlinarith [mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hab)]
  · rw [min_eq_right hba, max_eq_left hba]
    change h d.snd ≤ (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ∧
      (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ≤ h d.fst
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 hba)]
    · nlinarith [mul_nonneg t.2.1 (sub_nonneg.2 hba)]

omit [Finite V] in
private theorem reebQuot_dartHeight_injective {d : G.Dart}
    (hne : h d.fst ≠ h d.snd) : Function.Injective (dartHeight h d) := by
  intro s t hst
  apply Subtype.ext
  have hprod : ((s : ℝ) - (t : ℝ)) * (h d.snd - h d.fst) = 0 := by
    unfold dartHeight at hst
    linear_combination hst
  rcases mul_eq_zero.mp hprod with hst' | hab
  · exact sub_eq_zero.mp hst'
  · exact False.elim (hne (sub_eq_zero.mp hab).symm)

omit [Finite V] in
private theorem reebQuot_plHeight_mem_Icc (hS : CoversVertexHeights S h)
    (x : Realization G) :
    plHeight G h x ∈ Icc (S.value 0) (S.value (Fin.last n)) := by
  apply plHeight_mem_Icc_of_forall (m := S.value 0) (M := S.value (Fin.last n))
  intro v
  obtain ⟨i, hi⟩ := hS v
  rw [← hi]
  exact ⟨S.strictMono.monotone (Fin.zero_le i), S.strictMono.monotone (Fin.le_last i)⟩

omit [Finite V] in
private theorem reebQuot_exists_mem_K {x : ℝ}
    (hx : x ∈ Icc (S.value 0) (S.value (Fin.last n)))
    (hne : ∀ i, S.value i ≠ x) : ∃ e : Fin n, x ∈ (S.K e : Set ℝ) := by
  obtain ⟨p, hp, hp'⟩ := S.exists_piece x
  cases p with
  | star i => exact (hne i (hp' i (S.value_mem_J i))).elim
  | gap e => exact ⟨e, hp⟩
  | lowerTail => exact (not_lt_of_ge hx.1 hp).elim
  | upperTail => exact (not_lt_of_ge hx.2 hp).elim

omit [Finite V] in
private theorem reebQuot_edgeSpans_of_mem_K (hS : CoversVertexHeights S h)
    {e : Fin n} (d : G.Dart) {t : unitInterval}
    (ht : dartHeight h d t ∈ S.K e) :
    EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d) :=
  ((activeEdgeEquivSpans (G := G) (S.value_castSucc_lt_succ e)
    (fun v => hS.notMem_K e v))
    ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩).2

omit [Finite V] in
private theorem reebQuot_edgeCrosses_of_level {i : Fin (n + 1)} (d : G.Dart)
    {t : unitInterval} (ht : dartHeight h d t = S.value i)
    (hne : ∀ v ∈ (dartEdge d : Sym2 V), h v ≠ S.value i) :
    EdgeCrosses G h (S.value i) (dartEdge d) := by
  apply (edgeCrosses_dartEdge_iff d).2
  have hrange := reebQuot_dartHeight_mem_Icc G h d t
  rw [ht] at hrange
  constructor
  · rcases min_choice (h d.fst) (h d.snd) with hm | hm
    · rw [hm] at hrange ⊢
      exact lt_of_le_of_ne hrange.1 (hne d.fst (fst_mem_dartEdge d))
    · rw [hm] at hrange ⊢
      exact lt_of_le_of_ne hrange.1 (hne d.snd (snd_mem_dartEdge d))
  · rcases max_choice (h d.fst) (h d.snd) with hm | hm
    · rw [hm] at hrange ⊢
      exact lt_of_le_of_ne hrange.2 (Ne.symm (hne d.fst (fst_mem_dartEdge d)))
    · rw [hm] at hrange ⊢
      exact lt_of_le_of_ne hrange.2 (Ne.symm (hne d.snd (snd_mem_dartEdge d)))

omit [Finite V] in
private theorem reebQuot_dart_mem_gap (hS : CoversVertexHeights S h) (d : G.Dart)
    (t : unitInterval) (hi : ¬ ∃ i, dartHeight h d t = S.value i) :
    ∃ e : Fin n, dartHeight h d t ∈ (S.K e : Set ℝ) := by
  apply reebQuot_exists_mem_K
  · simpa [plHeight_edgePoint] using
      reebQuot_plHeight_mem_Icc G h hS (edgePoint G d t)
  · intro i hci
    exact hi ⟨i, hci.symm⟩

private theorem reebQuot_ofVertex_levelEnd_congr (d : G.Dart) {j k : Fin (n + 1)} (hjk : j = k)
    (hxj : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ S.value j) → EdgeCrosses G h (S.value j) (dartEdge d))
    (hxk : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ S.value k) → EdgeCrosses G h (S.value k) (dartEdge d)) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S j
        (levelEnd G h (S.value j) (dartEdge d) hxj) =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S k
        (levelEnd G h (S.value k) (dartEdge d) hxk) := by
  subst hjk
  rfl

private theorem reebQuot_ofVertex_levelEnd_edge_congr {j k : Fin (n + 1)} {ε ε' : G.edgeSet}
    (hjk : j = k) (hεε' : ε = ε')
    (hxj : (∀ v ∈ (ε : Sym2 V), h v ≠ S.value j) → EdgeCrosses G h (S.value j) ε)
    (hxk : (∀ v ∈ (ε' : Sym2 V), h v ≠ S.value k) → EdgeCrosses G h (S.value k) ε') :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S j
        (levelEnd G h (S.value j) ε hxj) =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S k
        (levelEnd G h (S.value k) ε' hxk) := by
  subst hjk
  subst hεε'
  rfl

private theorem reebQuot_ofVertex_levelComponent_congr (v : V) {j k : Fin (n + 1)}
    (hjk : j = k) (hj : h v = S.value j) (hk : h v = S.value k) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S j
        (Sum.inl ((G.induce {w | h w = S.value j}).connectedComponentMk ⟨v, hj⟩)) =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S k
        (Sum.inl ((G.induce {w | h w = S.value k}).connectedComponentMk ⟨v, hk⟩)) := by
  subst hjk
  rfl

private noncomputable def reebQuot_dartValue (hS : CoversVertexHeights S h)
    (d : G.Dart) (t : unitInterval) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S :=
  if hi : ∃ i, dartHeight h d t = S.value i then
    let i := Classical.choose hi
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S i
      (levelEnd G h (S.value i) (dartEdge d)
        (fun hne => reebQuot_edgeCrosses_of_level G h (i := i) d (t := t)
          (Classical.choose_spec hi) hne))
  else
    let e := Classical.choose (reebQuot_dart_mem_gap G h hS d t hi)
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
      (⟨dartEdge d, reebQuot_edgeSpans_of_mem_K G h hS d
        (Classical.choose_spec (reebQuot_dart_mem_gap G h hS d t hi))⟩,
        ⟨dartHeight h d t,
          Classical.choose_spec (reebQuot_dart_mem_gap G h hS d t hi)⟩)

private theorem reebQuot_dartValue_of_level (hS : CoversVertexHeights S h)
    {i : Fin (n + 1)} (d : G.Dart) (t : unitInterval)
    (ht : dartHeight h d t = S.value i) :
    reebQuot_dartValue G h hS d t =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S i
      (levelEnd G h (S.value i) (dartEdge d)
          (fun hne => reebQuot_edgeCrosses_of_level G h (i := i) d (t := t) ht hne)) := by
  classical
  unfold reebQuot_dartValue
  rw [dif_pos ⟨i, ht⟩]
  have hidx : Classical.choose (show ∃ j, dartHeight h d t = S.value j from ⟨i, ht⟩) = i := by
    apply S.strictMono.injective
    exact (Classical.choose_spec (show ∃ j, dartHeight h d t = S.value j from ⟨i, ht⟩)).symm.trans ht
  dsimp only
  exact reebQuot_ofVertex_levelEnd_congr G h d hidx _ _

private theorem reebQuot_dartValue_of_mem_K (hS : CoversVertexHeights S h)
    {e : Fin n} (d : G.Dart) (t : unitInterval)
    (ht : dartHeight h d t ∈ S.K e) :
    reebQuot_dartValue G h hS d t =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
        (⟨dartEdge d, reebQuot_edgeSpans_of_mem_K G h hS d ht⟩, ⟨dartHeight h d t, ht⟩) := by
  classical
  have hnot : ¬ ∃ i, dartHeight h d t = S.value i := by
    rintro ⟨i, hi⟩
    exact S.value_notMem_K e i (hi ▸ ht)
  unfold reebQuot_dartValue
  rw [dif_neg hnot]
  have heq : Classical.choose (reebQuot_dart_mem_gap G h hS d t hnot) = e := by
    apply S.eq_of_K_inf_K_nonempty
    exact ⟨dartHeight h d t,
      Classical.choose_spec (reebQuot_dart_mem_gap G h hS d t hnot), ht⟩
  cases heq
  rfl

private theorem reebQuot_dartValue_symm (hS : CoversVertexHeights S h) (d : G.Dart)
    (t : unitInterval) :
    reebQuot_dartValue G h hS d.symm (unitInterval.symm t) =
      reebQuot_dartValue G h hS d t := by
  classical
  by_cases hi : ∃ i, dartHeight h d t = S.value i
  · obtain ⟨i, hi⟩ := hi
    rw [reebQuot_dartValue_of_level G h hS (i := i) d.symm (unitInterval.symm t) (by
      rw [dartHeight_symm]; exact hi),
      reebQuot_dartValue_of_level G h hS (i := i) d t hi]
    exact reebQuot_ofVertex_levelEnd_edge_congr G h (j := i) (k := i)
      (ε := dartEdge d.symm) (ε' := dartEdge d) rfl (dartEdge_symm d) _ _
  · have hi' : ¬ ∃ i, dartHeight h d.symm (unitInterval.symm t) = S.value i := by
      simpa [dartHeight_symm] using hi
    obtain ⟨e, he⟩ : ∃ e : Fin n, dartHeight h d t ∈ (S.K e : Set ℝ) :=
      reebQuot_dart_mem_gap G h hS d t hi
    have he' : dartHeight h d.symm (unitInterval.symm t) ∈ S.K e := by
      simpa [dartHeight_symm] using he
    rw [reebQuot_dartValue_of_mem_K G h hS d.symm (unitInterval.symm t) he',
      reebQuot_dartValue_of_mem_K G h hS d t he]
    apply congrArg (fun p =>
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e p)
    apply Prod.ext
    · apply Subtype.ext
      exact dartEdge_symm d
    · apply Subtype.ext
      exact dartHeight_symm h d t

private noncomputable def reebQuot_vertexValue (hS : CoversVertexHeights S h) (v : V) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S :=
  let i := Classical.choose (hS v)
  (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S i
    (Sum.inl ((G.induce {w | h w = S.value i}).connectedComponentMk
      ⟨v, (Classical.choose_spec (hS v)).symm⟩))

private theorem reebQuot_dartValue_zero (hS : CoversVertexHeights S h) (d : G.Dart) :
    reebQuot_dartValue G h hS d 0 = reebQuot_vertexValue G h hS d.fst := by
  classical
  let i := Classical.choose (hS d.fst)
  have hi : dartHeight h d 0 = S.value i := by
    rw [dartHeight_zero]
    exact (Classical.choose_spec (hS d.fst)).symm
  rw [reebQuot_dartValue_of_level G h hS (i := i) d 0 hi]
  rw [levelEnd_of_mem G h (fun hne =>
      reebQuot_edgeCrosses_of_level G h (i := i) d (t := 0) hi hne)
    (fst_mem_dartEdge d)
    (Classical.choose_spec (hS d.fst)).symm]
  rfl

omit [Finite V] in
private theorem reebQuot_segments_cover (hS : CoversVertexHeights S h) (hn : 0 < n)
    (d : G.Dart) (t : unitInterval) :
    ∃ e : Fin n, dartHeight h d t ∈ (CylinderPresentation.Seg S e : Set ℝ) := by
  have hc : dartHeight h d t ∈ Icc (S.value 0) (S.value (Fin.last n)) := by
    simpa [plHeight_edgePoint] using
      reebQuot_plHeight_mem_Icc G h hS (edgePoint G d t)
  obtain ⟨p, hp, hp'⟩ := S.exists_piece (dartHeight h d t)
  cases p with
  | star i =>
      have hi : S.value i = dartHeight h d t := hp' i (S.value_mem_J i)
      cases i using Fin.cases with
      | zero =>
          refine ⟨⟨0, hn⟩, ?_⟩
          rw [← hi]
          exact ⟨le_rfl, S.strictMono.monotone (Fin.zero_le _)
            ⟩
      | succ k =>
          refine ⟨k, ?_⟩
          rw [← hi]
          exact ⟨S.strictMono.monotone (Fin.castSucc_le_succ k), le_rfl⟩
  | gap e => exact ⟨e, ⟨hp.1.le, hp.2.le⟩⟩
  | lowerTail => exact (not_lt_of_ge hc.1 hp).elim
  | upperTail => exact (not_lt_of_ge hc.2 hp).elim

private theorem reebQuot_segment_subsingleton (hS : CoversVertexHeights S h)
    {d : G.Dart} (hne : h d.fst ≠ h d.snd) (e : Fin n)
    (hspan : ¬ EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d)) :
    Set.Subsingleton ((dartHeight h d) ⁻¹'
      (CylinderPresentation.Seg S e : Set ℝ)) := by
  intro s hs t ht
  have hendpoint : ∀ r : unitInterval,
      r ∈ (dartHeight h d) ⁻¹' (CylinderPresentation.Seg S e : Set ℝ) →
        dartHeight h d r = S.value e.castSucc ∨
          dartHeight h d r = S.value e.succ := by
    intro r hr
    change dartHeight h d r ∈ Icc (S.value e.castSucc) (S.value e.succ) at hr
    by_cases hlevel : ∃ i, dartHeight h d r = S.value i
    · obtain ⟨i, hi⟩ := hlevel
      have hlow : e.castSucc ≤ i := by
        have hlow' : S.value e.castSucc ≤ S.value i := by simpa [hi] using hr.1
        by_contra hnot
        exact (not_lt_of_ge hlow') (S.strictMono (lt_of_not_ge hnot))
      have hupp : i ≤ e.succ := by
        have hupp' : S.value i ≤ S.value e.succ := by simpa [hi] using hr.2
        by_contra hnot
        exact (not_lt_of_ge hupp') (S.strictMono (lt_of_not_ge hnot))
      rcases eq_or_ne i e.castSucc with rfl | hne'
      · exact Or.inl hi
      · right
        have hlt : e.castSucc < i := lt_of_le_of_ne hlow (Ne.symm hne')
        exact hi.trans (congrArg S.value
          (le_antisymm hupp (Fin.castSucc_lt_iff_succ_le.1 hlt)))
    · have hca : dartHeight h d r ≠ S.value e.castSucc := by
        intro hca
        exact hlevel ⟨e.castSucc, hca⟩
      have hcb : dartHeight h d r ≠ S.value e.succ := by
        intro hcb
        exact hlevel ⟨e.succ, hcb⟩
      have hrK : dartHeight h d r ∈ S.K e := by
        exact ⟨lt_of_le_of_ne hr.1 (Ne.symm hca), lt_of_le_of_ne hr.2 hcb⟩
      obtain ⟨e', he'⟩ : ∃ e' : Fin n, dartHeight h d r ∈ (S.K e' : Set ℝ) :=
        reebQuot_dart_mem_gap G h hS d r hlevel
      have heq : e' = e := by
        apply S.eq_of_K_inf_K_nonempty
        exact ⟨dartHeight h d r, he', hrK⟩
      exact (hspan (by simpa [heq] using
        reebQuot_edgeSpans_of_mem_K G h hS d he')).elim
  have hs' := hendpoint s hs
  have ht' := hendpoint t ht
  by_cases hst : dartHeight h d s = dartHeight h d t
  · exact reebQuot_dartHeight_injective G h hne hst
  apply Subtype.ext
  rcases hs' with hs' | hs' <;> rcases ht' with ht' | ht'
  · exact (hst (hs'.trans ht'.symm)).elim
  · have hrs : min (h d.fst) (h d.snd) ≤ S.value e.castSucc := by
      simpa [hs'] using (reebQuot_dartHeight_mem_Icc G h d s).1
    have hrt : S.value e.succ ≤ max (h d.fst) (h d.snd) := by
      simpa [ht'] using (reebQuot_dartHeight_mem_Icc G h d t).2
    exact (hspan ((edgeSpans_dartEdge_iff d).2 ⟨hrs, hrt⟩)).elim
  · have hrs : min (h d.fst) (h d.snd) ≤ S.value e.castSucc := by
      simpa [ht'] using (reebQuot_dartHeight_mem_Icc G h d t).1
    have hrt : S.value e.succ ≤ max (h d.fst) (h d.snd) := by
      simpa [hs'] using (reebQuot_dartHeight_mem_Icc G h d s).2
    exact (hspan ((edgeSpans_dartEdge_iff d).2 ⟨hrs, hrt⟩)).elim
  · exact (hst (hs'.trans ht'.symm)).elim

private theorem reebQuot_dartValue_continuousOn (hS : CoversVertexHeights S h)
    {d : G.Dart} (hne : h d.fst ≠ h d.snd) (e : Fin n) :
    ContinuousOn (reebQuot_dartValue G h hS d)
      ((dartHeight h d) ⁻¹' (CylinderPresentation.Seg S e : Set ℝ)) := by
  by_cases hspan : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d)
  · let y : (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).E e :=
      ⟨dartEdge d, hspan⟩
    let f : unitInterval →
        (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S :=
      fun r => (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofCylinder S e
        (y, Set.projIcc (S.value e.castSucc) (S.value e.succ)
          (S.value_castSucc_lt_succ e).le (dartHeight h d r))
    have hf : Continuous f :=
      (CylinderPresentation.continuous_ofCylinder
        S (CylinderPresentation.ofFiniteData (graphPLReebData G h S)) e).comp
        (continuous_const.prodMk
          (continuous_projIcc.comp (continuous_dartHeight h d)))
    refine hf.continuousOn.congr ?_
    intro r hr
    change dartHeight h d r ∈ Icc (S.value e.castSucc) (S.value e.succ) at hr
    by_cases hlow : dartHeight h d r = S.value e.castSucc
    · rw [reebQuot_dartValue_of_level G h hS d r hlow]
      dsimp only [f]
      have hp : Set.projIcc (S.value e.castSucc) (S.value e.succ)
          (S.value_castSucc_lt_succ e).le (dartHeight h d r) =
          CylinderPresentation.segBot S e := by
        rw [Set.projIcc_of_mem _ hr]
        apply Subtype.ext
        exact hlow
      rw [hp, CylinderPresentation.ofCylinder_segBot]
      rfl
    · by_cases hupp : dartHeight h d r = S.value e.succ
      · rw [reebQuot_dartValue_of_level G h hS d r hupp]
        dsimp only [f]
        have hp : Set.projIcc (S.value e.castSucc) (S.value e.succ)
            (S.value_castSucc_lt_succ e).le (dartHeight h d r) =
            CylinderPresentation.segTop S e := by
          rw [Set.projIcc_of_mem _ hr]
          apply Subtype.ext
          exact hupp
        rw [hp, CylinderPresentation.ofCylinder_segTop]
        rfl
      · have hK : dartHeight h d r ∈ S.K e :=
          ⟨lt_of_le_of_ne hr.1 (Ne.symm hlow), lt_of_le_of_ne hr.2 hupp⟩
        rw [reebQuot_dartValue_of_mem_K G h hS d r hK,
          CylinderPresentation.ofStrip_eq_ofCylinder]
        dsimp only [f]
        rw [Set.projIcc_of_mem _ hr]
        rfl
  · exact (reebQuot_segment_subsingleton G h hS hne e hspan).continuousOn _

private theorem reebQuot_dartValue_continuous (hS : CoversVertexHeights S h)
    {d : G.Dart} (hne : h d.fst ≠ h d.snd) :
    Continuous (reebQuot_dartValue G h hS d) := by
  classical
  have hn : 0 < n := by
    by_contra hn'
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn'
    subst n
    rcases hS d.fst with ⟨i, hi⟩
    rcases hS d.snd with ⟨j, hj⟩
    have hi0 : i = 0 := Fin.eq_zero i
    have hj0 : j = 0 := Fin.eq_zero j
    have hfst : h d.fst = S.value 0 := hi.symm.trans (by rw [hi0])
    have hsnd : h d.snd = S.value 0 := hj.symm.trans (by rw [hj0])
    exact hne (hfst.trans hsnd.symm)
  let F : Fin n → Set unitInterval := fun e =>
    (dartHeight h d) ⁻¹' (CylinderPresentation.Seg S e : Set ℝ)
  have hcover : ⋃ e, F e = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨e, he⟩ := reebQuot_segments_cover G h hS hn d t
    exact Set.mem_iUnion.2 ⟨e, he⟩
  apply (locallyFinite_of_finite F).continuous hcover
  · intro e
    exact isClosed_Icc.preimage (continuous_dartHeight h d)
  · intro e
    exact reebQuot_dartValue_continuousOn G h hS hne e

private theorem reebQuot_dartValue_continuous_horizontal (hS : CoversVertexHeights S h)
    {d : G.Dart} (hd : h d.fst = h d.snd) :
    Continuous (reebQuot_dartValue G h hS d) := by
  have hconst : ∀ t : unitInterval,
      reebQuot_dartValue G h hS d t = reebQuot_dartValue G h hS d 0 := by
    intro t
    obtain ⟨i, hi⟩ := hS d.fst
    have ht : dartHeight h d t = S.value i := by
      rw [dartHeight_of_eq h hd, hi.symm]
    have h0 : dartHeight h d 0 = S.value i := by
      rw [dartHeight_zero, hi.symm]
    rw [reebQuot_dartValue_of_level G h hS d t ht,
      reebQuot_dartValue_of_level G h hS d 0 h0]
  rw [show (reebQuot_dartValue G h hS d) =
      (fun _ : unitInterval => reebQuot_dartValue G h hS d 0) from funext hconst]
  exact continuous_const

private noncomputable def reebQuot_edgeMap (hS : CoversVertexHeights S h) (d : G.Dart) :
    C(unitInterval, (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S) :=
  ⟨reebQuot_dartValue G h hS d,
    by
      by_cases hd : h d.fst = h d.snd
      · exact reebQuot_dartValue_continuous_horizontal G h hS hd
      · exact reebQuot_dartValue_continuous G h hS hd⟩

private noncomputable def graphPLReebVertexMap (hS : CoversVertexHeights S h) (v : V) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S :=
  reebQuot_vertexValue G h hS v

private theorem reebQuot_dartValue_height (hS : CoversVertexHeights S h) (d : G.Dart)
    (t : unitInterval) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
        (reebQuot_dartValue G h hS d t) = dartHeight h d t := by
  classical
  by_cases hi : ∃ i, dartHeight h d t = S.value i
  · obtain ⟨i, hi⟩ := hi
    rw [reebQuot_dartValue_of_level G h hS d t hi]
    change S.value i = dartHeight h d t
    exact hi.symm
  · obtain ⟨e, he⟩ : ∃ e : Fin n, dartHeight h d t ∈ (S.K e : Set ℝ) :=
      reebQuot_dart_mem_gap G h hS d t hi
    rw [reebQuot_dartValue_of_mem_K G h hS d t he,
      CylinderPresentation.height_ofStrip]

private theorem reebQuot_edgeMap_symm (hS : CoversVertexHeights S h) (d : G.Dart)
    (t : unitInterval) :
    (reebQuot_edgeMap G h hS d.symm) (unitInterval.symm t) =
      (reebQuot_edgeMap G h hS d) t := by
  change reebQuot_dartValue G h hS d.symm (unitInterval.symm t) =
    reebQuot_dartValue G h hS d t
  exact reebQuot_dartValue_symm G h hS d t

private theorem reebQuot_edgeMap_zero (hS : CoversVertexHeights S h) (d : G.Dart) :
    (reebQuot_edgeMap G h hS d) 0 = graphPLReebVertexMap G h hS d.fst := by
  change reebQuot_dartValue G h hS d 0 = reebQuot_vertexValue G h hS d.fst
  exact reebQuot_dartValue_zero G h hS d

/-- A continuous height-preserving map from the graph realization to its finite Reeb realization. -/
noncomputable def graphPLReebMap (hS : CoversVertexHeights S h) :
    C(Realization G, (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S) :=
  continuousLift G (graphPLReebVertexMap G h hS)
    (fun d => reebQuot_edgeMap G h hS d)
    (fun d t => reebQuot_edgeMap_symm G h hS d t)
    (fun d => reebQuot_edgeMap_zero G h hS d)

/-- The finite-realization height of `graphPLReebMap` is the original graph-PL height. -/
theorem height_graphPLReebMap (hS : CoversVertexHeights S h) (x : Realization G) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
      (graphPLReebMap G h hS x) = plHeight G h x := by
  induction x using ind G with
  | vertex v =>
      change (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
        (graphPLReebVertexMap G h hS v) = h v
      change (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
        (reebQuot_vertexValue G h hS v) = h v
      dsimp [reebQuot_vertexValue]
      change S.value (Classical.choose (hS v)) = h v
      exact Classical.choose_spec (hS v)
  | edgePoint d t =>
      change (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
          (reebQuot_dartValue G h hS d t) = dartHeight h d t
      exact reebQuot_dartValue_height G h hS d t

/-- The map sends a vertex to the level component containing that vertex. -/
theorem graphPLReebMap_vertex (hS : CoversVertexHeights S h) {i : Fin (n + 1)} (v : V)
    (hv : h v = S.value i) :
    graphPLReebMap G h hS (vertex G v) =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S i
        (Sum.inl ((G.induce {w | h w = S.value i}).connectedComponentMk ⟨v, hv⟩)) := by
  classical
  change graphPLReebVertexMap G h hS v = _
  change reebQuot_vertexValue G h hS v = _
  dsimp [reebQuot_vertexValue]
  have hi : Classical.choose (hS v) = i := by
    apply S.strictMono.injective
    exact (Classical.choose_spec (hS v)).trans hv
  exact reebQuot_ofVertex_levelComponent_congr G h v hi
    (Classical.choose_spec (hS v)).symm hv

/-- On a regular gap, the map sends an edge point to the corresponding open strip point. -/
theorem graphPLReebMap_edgePoint_of_mem_K (hS : CoversVertexHeights S h) {e : Fin n}
    (d : G.Dart) (t : unitInterval) (ht : dartHeight h d t ∈ S.K e)
    (hsp : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d)) :
    graphPLReebMap G h hS (edgePoint G d t) =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e
        (⟨dartEdge d, hsp⟩, ⟨dartHeight h d t, ht⟩) := by
  change reebQuot_dartValue G h hS d t = _
  exact reebQuot_dartValue_of_mem_K G h hS d t ht

private theorem reebQuot_closedLevelComponentsEquiv_mk_edgePoint
    {c : ℝ} (d : G.Dart) (t : unitInterval)
    (hp : plHeight G h (edgePoint G d t) ∈ ({c} : Set ℝ))
    (hx : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ c) →
      EdgeCrosses G h c (dartEdge d)) :
    closedLevelComponentsEquiv G h c
        (ZerothHomotopy.mk ⟨edgePoint G d t, hp⟩) = levelEnd G h c (dartEdge d) hx := by
  have ht : dartHeight h d t = c := by
    simpa [plHeight_edgePoint] using hp
  obtain ⟨η, _hη, hI⟩ := exists_isLevelWindow h c
  have htI : dartHeight h d t ∈ (ioo (c - η) (c + η) : Set ℝ) := by
    rw [ht]
    exact hI.1
  rw [closedLevelComponentsEquiv_eq G h hI]
  exact levelWindowEquiv_mk_edgePoint G h hI d t htI hx

/-- The map sends every point of a closed level to its finite-data vertex point. -/
theorem graphPLReebMap_of_level (hS : CoversVertexHeights S h) (i : Fin (n + 1))
    (p : ClosedLevel G h (S.value i)) :
    graphPLReebMap G h hS p.1 =
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S i
        (closedLevelComponentsEquiv G h (S.value i) (ZerothHomotopy.mk p)) := by
  rcases p with ⟨p, hp⟩
  induction p using ind G with
  | vertex v =>
      have hv : h v = S.value i := by
        simpa [plHeight_vertex] using hp
      change graphPLReebMap G h hS (vertex G v) = _
      rw [graphPLReebMap_vertex G h hS v hv,
        closedLevelComponentsEquiv_mk_vertex G h v hv]
  | edgePoint d t =>
      have ht : dartHeight h d t = S.value i := by
        simpa [plHeight_edgePoint] using hp
      change reebQuot_dartValue G h hS d t = _
      let hx : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ S.value i) →
          EdgeCrosses G h (S.value i) (dartEdge d) := fun hne =>
        reebQuot_edgeCrosses_of_level G h (i := i) d ht hne
      rw [reebQuot_dartValue_of_level G h hS (i := i) d t ht,
        reebQuot_closedLevelComponentsEquiv_mk_edgePoint G h d t hp hx]

private theorem reebQuot_reebRel_of_level_map_eq (hS : CoversVertexHeights S h)
    (i : Fin (n + 1)) {x x' : Realization G}
    (hx : plHeight G h x = S.value i) (hx' : plHeight G h x' = S.value i)
    (hmap : graphPLReebMap G h hS x = graphPLReebMap G h hS x') :
    ReebRel (plHeight G h) x x' := by
  let px : ClosedLevel G h (S.value i) := ⟨x, by simp [hx]⟩
  let px' : ClosedLevel G h (S.value i) := ⟨x', by simp [hx']⟩
  have hlabels :
      closedLevelComponentsEquiv G h (S.value i) (ZerothHomotopy.mk px) =
        closedLevelComponentsEquiv G h (S.value i) (ZerothHomotopy.mk px') := by
    apply (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex_injective S i
    rw [← graphPLReebMap_of_level G h hS i px,
      ← graphPLReebMap_of_level G h hS i px']
    exact hmap
  have hcomp : ZerothHomotopy.mk px = ZerothHomotopy.mk px' :=
    (closedLevelComponentsEquiv G h (S.value i)).injective hlabels
  obtain ⟨γ⟩ := Quotient.exact hcomp
  refine ⟨γ.map continuous_subtype_val, ?_⟩
  intro t
  have hγ : plHeight G h (γ t).1 = S.value i := Set.mem_singleton_iff.mp (γ t).2
  exact hγ.trans hx.symm

private theorem reebQuot_edgePoint_eq_of_map_eq (hS : CoversVertexHeights S h)
    {d d' : G.Dart} {e e' : Fin n} (t t' : unitInterval)
    (ht : dartHeight h d t ∈ S.K e) (ht' : dartHeight h d' t' ∈ S.K e')
    (hmap : graphPLReebMap G h hS (edgePoint G d t) =
      graphPLReebMap G h hS (edgePoint G d' t')) :
    edgePoint G d t = edgePoint G d' t' := by
  have hheight : dartHeight h d t = dartHeight h d' t' := by
    calc
      dartHeight h d t = plHeight G h (edgePoint G d t) := by
        rw [plHeight_edgePoint]
      _ = (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
          (graphPLReebMap G h hS (edgePoint G d t)) :=
        (height_graphPLReebMap G h hS (edgePoint G d t)).symm
      _ = (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
          (graphPLReebMap G h hS (edgePoint G d' t')) := congrArg _ hmap
      _ = plHeight G h (edgePoint G d' t') :=
        height_graphPLReebMap G h hS (edgePoint G d' t')
      _ = dartHeight h d' t' := by
        rw [plHeight_edgePoint]
  have hte' : dartHeight h d t ∈ (S.K e' : Set ℝ) := by
    rw [hheight]
    exact ht'
  have heq : e = e' := S.eq_of_K_inf_K_nonempty ⟨dartHeight h d t, ht, hte'⟩
  subst e'
  have hsp : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d) :=
    reebQuot_edgeSpans_of_mem_K G h hS d ht
  have hsp' : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d') :=
    reebQuot_edgeSpans_of_mem_K G h hS d' ht'
  have hne : h d.fst ≠ h d.snd := by
    intro heq
    have hconst : dartHeight h d t = h d.fst := dartHeight_of_eq h heq t
    exact (hS.notMem_K e d.fst) (hconst ▸ ht)
  have hne' : h d'.fst ≠ h d'.snd := by
    intro heq
    have hconst : dartHeight h d' t' = h d'.fst := dartHeight_of_eq h heq t'
    exact (hS.notMem_K e d'.fst) (hconst ▸ ht')
  rw [graphPLReebMap_edgePoint_of_mem_K G h hS d t ht hsp,
    graphPLReebMap_edgePoint_of_mem_K G h hS d' t' ht' hsp'] at hmap
  have hp := (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip_injective S e hmap
  have hde : dartEdge d = dartEdge d' :=
    congrArg Subtype.val (congrArg Prod.fst hp)
  have hdt : dartHeight h d t = dartHeight h d' t' :=
    congrArg Subtype.val (congrArg Prod.snd hp)
  rcases (dartEdge_eq_iff).1 hde with hdd | hdd
  · subst d'
    have htt : t = t' := reebQuot_dartHeight_injective G h hne hdt
    subst t'
    rfl
  · have hdt' : dartHeight h d' (unitInterval.symm t) = dartHeight h d' t' := by
      have hsymm := dartHeight_symm h d' (unitInterval.symm t)
      rw [unitInterval.symm_symm] at hsymm
      exact hsymm.symm.trans (by simpa [hdd] using hdt)
    have htt : unitInterval.symm t = t' :=
      reebQuot_dartHeight_injective G h hne' hdt'
    calc
      edgePoint G d t = edgePoint G d'.symm t := by rw [hdd]
      _ = edgePoint G d' (unitInterval.symm t) := by
        have hsymm := edgePoint_symm G d' (unitInterval.symm t)
        rw [unitInterval.symm_symm] at hsymm
        exact hsymm
      _ = edgePoint G d' t' := congrArg (edgePoint G d') htt

private theorem reebQuot_graphPLReebMap_eq_iff (hS : CoversVertexHeights S h)
    {x x' : Realization G} :
    graphPLReebMap G h hS x = graphPLReebMap G h hS x' ↔
      ReebRel (plHeight G h) x x' := by
  constructor
  · intro hmap
    have hheight : plHeight G h x = plHeight G h x' := by
      calc
        plHeight G h x =
            (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
              (graphPLReebMap G h hS x) :=
          (height_graphPLReebMap G h hS x).symm
        _ = (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
              (graphPLReebMap G h hS x') := congrArg _ hmap
        _ = plHeight G h x' := height_graphPLReebMap G h hS x'
    by_cases hlevel : ∃ i, plHeight G h x = S.value i
    · obtain ⟨i, hi⟩ := hlevel
      exact reebQuot_reebRel_of_level_map_eq G h hS i hi (hheight.symm.trans hi) hmap
    · have hlevel' : ¬ ∃ i, plHeight G h x' = S.value i := by
        intro hi'
        apply hlevel
        obtain ⟨i, hi'⟩ := hi'
        exact ⟨i, hheight.trans hi'⟩
      have hx : ∃ d t, x = edgePoint G d t := by
        induction x using ind G with
        | vertex v =>
            obtain ⟨i, hi⟩ := hS v
            exact (hlevel ⟨i, by simpa [plHeight_vertex] using hi.symm⟩).elim
        | edgePoint d t => exact ⟨d, t, rfl⟩
      have hx' : ∃ d t, x' = edgePoint G d t := by
        induction x' using ind G with
        | vertex v =>
            obtain ⟨i, hi⟩ := hS v
            exact (hlevel' ⟨i, by simpa [plHeight_vertex] using hi.symm⟩).elim
        | edgePoint d t => exact ⟨d, t, rfl⟩
      obtain ⟨d, t, rfl⟩ := hx
      obtain ⟨d', t', rfl⟩ := hx'
      have hgap : ∃ e, dartHeight h d t ∈ (S.K e : Set ℝ) := by
        refine reebQuot_dart_mem_gap G h hS d t ?_
        rintro ⟨i, hi⟩
        apply hlevel
        exact ⟨i, by simpa [plHeight_edgePoint] using hi⟩
      have hgap' : ∃ e, dartHeight h d' t' ∈ (S.K e : Set ℝ) := by
        refine reebQuot_dart_mem_gap G h hS d' t' ?_
        rintro ⟨i, hi⟩
        apply hlevel'
        exact ⟨i, by simpa [plHeight_edgePoint] using hi⟩
      obtain ⟨e, ht⟩ := hgap
      obtain ⟨e', ht'⟩ := hgap'
      have hpoint := reebQuot_edgePoint_eq_of_map_eq G h hS t t' ht ht' hmap
      rw [hpoint]
      exact ReebRel.refl _ _
  · intro hreeb
    exact RGraph.apply_eq_of_reebRel S (graphPLReebMap G h hS)
      (height_graphPLReebMap G h hS) hreeb

private theorem reebQuot_strip_crossing (e : Fin n)
    (p : (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).E e ×
      (S.K e : Set ℝ)) :
    ∃ d : G.Dart, ∃ t : unitInterval,
      dartEdge d = p.1.1 ∧ dartHeight h d t = (p.2 : ℝ) := by
  rcases p.1.2 with ⟨d, hd, hmin, hmax⟩
  have hcross : min (h d.fst) (h d.snd) < (p.2 : ℝ) ∧
      (p.2 : ℝ) < max (h d.fst) (h d.snd) := by
    exact ⟨hmin.trans_lt p.2.property.1, p.2.property.2.trans_le hmax⟩
  rcases le_total (h d.fst) (h d.snd) with hab | hba
  · have h₁ : h d.fst < (p.2 : ℝ) := by
      simpa [min_eq_left hab] using hcross.1
    have h₂ : (p.2 : ℝ) < h d.snd := by
      simpa [max_eq_right hab] using hcross.2
    exact ⟨d, crossingParam G h h₁ h₂, hd,
      dartHeight_crossingParam G h h₁ h₂⟩
  · have h₁ : h d.snd < (p.2 : ℝ) := by
      simpa [min_eq_right hba] using hcross.1
    have h₂ : (p.2 : ℝ) < h d.fst := by
      simpa [max_eq_left hba] using hcross.2
    refine ⟨d.symm, crossingParam G h (d := d.symm) (by simpa using h₁)
      (by simpa using h₂), ?_, ?_⟩
    · rw [dartEdge_symm]
      exact hd
    · exact dartHeight_crossingParam G h (d := d.symm) (by simpa using h₁)
        (by simpa using h₂)

/-- The descended continuous map from the Reeb quotient to the finite realization. -/
noncomputable def graphPLReebQuotientMap (hS : CoversVertexHeights S h) :
    C(ReebQuotient (plHeight G h),
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S) :=
  RGraph.quotientLift S (graphPLReebMap G h hS) (height_graphPLReebMap G h hS)

/-- The quotient map agrees with `graphPLReebMap` on representatives. -/
@[simp] theorem graphPLReebQuotientMap_mk (hS : CoversVertexHeights S h)
    (x : Realization G) :
    graphPLReebQuotientMap G h hS (ReebQuotient.mk _ x) = graphPLReebMap G h hS x := rfl

/-- The descended graph-PL map is bijective. -/
theorem graphPLReebQuotientMap_bijective (hS : CoversVertexHeights S h) :
    Function.Bijective (graphPLReebQuotientMap G h hS) := by
  constructor
  · intro q q' hq
    induction q using ReebQuotient.ind with
    | h x =>
        induction q' using ReebQuotient.ind with
        | h x' =>
            exact (ReebQuotient.mk_eq_mk_iff _).2
              ((reebQuot_graphPLReebMap_eq_iff G h hS).1 hq)
  · intro y
    rcases (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).exists_rep S y with
      ⟨i, z, rfl⟩ | ⟨e, p, rfl⟩
    · obtain ⟨x, hx⟩ := (closedLevelComponentsEquiv G h (S.value i)).surjective z
      obtain ⟨p, hp⟩ := ZerothHomotopy.mk_surjective x
      exact ⟨ReebQuotient.mk _ p.1, by
        rw [graphPLReebQuotientMap_mk, graphPLReebMap_of_level G h hS i p]
        simp [hp, hx]⟩
    · obtain ⟨d, t, hd, htval⟩ := reebQuot_strip_crossing G h e p
      have ht : dartHeight h d t ∈ (S.K e : Set ℝ) := by
        rw [htval]
        exact p.2.2
      have hsp := reebQuot_edgeSpans_of_mem_K G h hS d ht
      exact ⟨ReebQuotient.mk _ (edgePoint G d t), by
        rw [graphPLReebQuotientMap_mk,
          graphPLReebMap_edgePoint_of_mem_K G h hS d t ht hsp]
        have hp : (⟨dartEdge d, hsp⟩, ⟨dartHeight h d t, ht⟩) = p := by
          apply Prod.ext
          · exact Subtype.ext hd
          · exact Subtype.ext htval
        exact congrArg (fun z =>
          (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e z) hp⟩

/-- The Reeb quotient is homeomorphic to the finite graph-PL realization. -/
noncomputable def graphPLReebQuotientHomeomorph (hS : CoversVertexHeights S h) :
    ReebQuotient (plHeight G h) ≃ₜ
      (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).Realization S :=
  letI := compactSpace_realization G
  letI := (ReebQuotient.mk_surjective (plHeight G h)).compactSpace
    (ReebQuotient.continuous_mk (plHeight G h))
  letI := CylinderPresentation.finiteData_t2Space S (graphPLReebData G h S)
  (graphPLReebQuotientMap G h hS).continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ (graphPLReebQuotientMap_bijective G h hS))

/-- The homeomorphism agrees with `graphPLReebMap` on quotient representatives. -/
@[simp] theorem graphPLReebQuotientHomeomorph_mk (hS : CoversVertexHeights S h)
    (x : Realization G) :
    graphPLReebQuotientHomeomorph G h hS (ReebQuotient.mk _ x) =
      graphPLReebMap G h hS x := rfl

/-- The quotient homeomorphism preserves the real-valued height. -/
theorem height_graphPLReebQuotientHomeomorph (hS : CoversVertexHeights S h)
    (q : ReebQuotient (plHeight G h)) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
        (graphPLReebQuotientHomeomorph G h hS q) = ReebQuotient.height _ q := by
  induction q using ReebQuotient.ind with
  | h x =>
      exact height_graphPLReebMap G h hS x

end general

section slice

variable {V : Type} [Finite V] (G : SimpleGraph V) (h : V → ℝ) {n : ℕ} {S : CriticalValues n}

/-- The graph realization over `ℝ`, with the graph-PL height as its structure map. -/
abbrev graphPLOver : Over (TopCat.of ℝ) := Over.mk (TopCat.ofHom (plHeight G h))

/-- The Reeb quotient of a graph-PL realization is isomorphic over `ℝ` to its finite realization. -/
noncomputable def graphPLReebQuotientIso (hS : CoversVertexHeights S h) :
    (ReebQuotient.quotientFunctor ℝ).obj (graphPLOver G h) ≅
      RGraph.toOver S (graphPLReebData G h S) :=
  Over.isoMk (TopCat.isoOfHomeo (graphPLReebQuotientHomeomorph G h hS))
    (by ext q; exact height_graphPLReebQuotientHomeomorph G h hS q)

/-- Transport the graph-PL Reeb quotient isomorphism to isomorphic finite Reeb data. -/
noncomputable def graphPLReebQuotientIsoOfIso (hS : CoversVertexHeights S h)
    {D : FiniteReebData.{0} n} (e : D ≅ graphPLReebData G h S) :
    (ReebQuotient.quotientFunctor ℝ).obj (graphPLOver G h) ≅ RGraph.toOver S D :=
  graphPLReebQuotientIso G h hS ≪≫ (RGraph.realizationFunctor S).mapIso e.symm

private theorem intervalComponentNatTrans_graphPLReebMap_on_vertexLabel
    (hS : CoversVertexHeights S h) {i : Fin (n + 1)}
    (x : (graphPLReebData G h S).V i) :
    (intervalComponentNatTrans (graphPLReebMap G h hS)
        (height_graphPLReebMap G h hS)).app (S.J i)
        ((graphPLCosheafIso G h hS).hom.app (S.J i)
          ((graphPLReebData G h S).vertexLabel S i x)) =
      (graphPLReebData G h S).vertexLabel S i x := by
  classical
  rw [graphPLCosheafIso_hom_app_J G h hS i x]
  let z : ZerothHomotopy (ClosedLevel G h (S.value i)) :=
    (closedLevelComponentsEquiv G h (S.value i)).symm x
  obtain ⟨p, hp⟩ := ZerothHomotopy.mk_surjective z
  have hstar :
      graphPLStarEquiv G h S hS i
          (TDA.Topology.componentMap (levelInclusion G h (S.value_mem_J i))
            (ZerothHomotopy.mk p)) = x := by
    have hstar' := congrFun
      (graphPLStarEquiv_comp_componentMap_levelInclusion G h S hS i)
      (ZerothHomotopy.mk p)
    have hstar'' :
        graphPLStarEquiv G h S hS i
            (TDA.Topology.componentMap (levelInclusion G h (S.value_mem_J i))
              (ZerothHomotopy.mk p)) =
          closedLevelComponentsEquiv G h (S.value i) (ZerothHomotopy.mk p) := by
      exact hstar'
    exact hstar''.trans (by
      rw [hp]
      exact (closedLevelComponentsEquiv G h (S.value i)).apply_symm_apply x)
  have hcomponent :
      TDA.Topology.componentMap (levelInclusion G h (S.value_mem_J i))
          (ZerothHomotopy.mk p) =
        (graphPLStarEquiv G h S hS i).symm x := by
    apply (graphPLStarEquiv G h S hS i).injective
    exact hstar.trans ((graphPLStarEquiv G h S hS i).apply_symm_apply x).symm
  rw [← hcomponent]
  change (intervalComponentNatTrans (graphPLReebMap G h hS)
      (height_graphPLReebMap G h hS)).app (S.J i)
      (ZerothHomotopy.mk (levelInclusion G h (S.value_mem_J i) p)) = _
  rw [intervalComponentNatTrans_app_mk
        (h := graphPLReebMap G h hS)
        (comm := height_graphPLReebMap G h hS)
        (I := S.J i)
        (x := levelInclusion G h (S.value_mem_J i) p)]
  have hx : closedLevelComponentsEquiv G h (S.value i) (ZerothHomotopy.mk p) = x := by
    rw [hp]
    exact (closedLevelComponentsEquiv G h (S.value i)).apply_symm_apply x
  rw [(graphPLReebData G h S).vertexLabel_apply S i x]
  refine congrArg ZerothHomotopy.mk (Subtype.ext ?_)
  exact (graphPLReebMap_of_level G h hS i p).trans
    (congrArg ((CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofVertex S i) hx)

private theorem intervalComponentNatTrans_graphPLReebMap_on_edgeLabel
    (hS : CoversVertexHeights S h) {e : Fin n}
    (y : (graphPLReebData G h S).E e) :
    (intervalComponentNatTrans (graphPLReebMap G h hS)
        (height_graphPLReebMap G h hS)).app (S.K e)
        ((graphPLCosheafIso G h hS).hom.app (S.K e)
          ((graphPLReebData G h S).edgeLabel S e y)) =
      (graphPLReebData G h S).edgeLabel S e y := by
  classical
  rw [graphPLCosheafIso_hom_app_K G h hS e y]
  obtain ⟨d, t, hd, htval⟩ :=
    reebQuot_strip_crossing G h e (y, S.gapMidpoint e)
  have ht : dartHeight h d t ∈ (S.K e : Set ℝ) := by
    rw [htval]
    exact (S.gapMidpoint e).2
  have hsp : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d) :=
    reebQuot_edgeSpans_of_mem_K G h hS d ht
  have hge :
      graphPLGapEquiv G h S hS e
          (ZerothHomotopy.mk (⟨edgePoint G d t, ht⟩ :
            {p : Realization G // plHeight G h p ∈ S.K e})) = y := by
    rw [graphPLGapEquiv_mk_edgePoint G h S hS d t ht hsp]
    exact Subtype.ext hd
  have hpoint :
      (graphPLGapEquiv G h S hS e).symm y =
        ZerothHomotopy.mk (⟨edgePoint G d t, ht⟩ :
          {p : Realization G // plHeight G h p ∈ S.K e}) := by
    have hpoint' := congrArg (graphPLGapEquiv G h S hS e).symm hge
    exact hpoint'.symm.trans
      ((graphPLGapEquiv G h S hS e).symm_apply_apply _)
  rw [hpoint]
  refine (intervalComponentNatTrans_app_mk (graphPLReebMap G h hS)
    (height_graphPLReebMap G h hS) (S.K e)
    (⟨edgePoint G d t, ht⟩ : {p : Realization G // plHeight G h p ∈ S.K e})).trans ?_
  have hp :
      (⟨dartEdge d, hsp⟩, ⟨dartHeight h d t, ht⟩) =
        (y, S.gapMidpoint e) := by
    apply Prod.ext
    · exact Subtype.ext hd
    · exact Subtype.ext htval
  rw [(graphPLReebData G h S).edgeLabel_apply S e (S.gapMidpoint e) y]
  refine congrArg ZerothHomotopy.mk (Subtype.ext ?_)
  exact (graphPLReebMap_edgePoint_of_mem_K G h hS d t ht hsp).trans
    (congrArg ((CylinderPresentation.ofFiniteData (graphPLReebData G h S)).ofStrip S e) hp)

/-- The component map induced by graphPLReebMap is the inverse of the graph-PL cosheaf
identification. -/
theorem intervalComponentNatTrans_graphPLReebMap (hS : CoversVertexHeights S h) :
    intervalComponentNatTrans (graphPLReebMap G h hS) (height_graphPLReebMap G h hS) =
      (graphPLCosheafIso G h hS).inv := by
  have hcomp :
      (graphPLCosheafIso G h hS).hom ≫
          intervalComponentNatTrans (graphPLReebMap G h hS)
            (height_graphPLReebMap G h hS) =
        𝟙 _ := by
    refine S.natTrans_ext
      (FiniteReebData.toCosheaf_isConstructibleAt (graphPLReebData G h S) S)
      (FiniteReebData.toCosheaf_isIntervalCosheaf (graphPLReebData G h S) S)
      (FiniteReebData.toCosheaf_isConstructibleAt (graphPLReebData G h S) S)
      (FiniteReebData.toCosheaf_isIntervalCosheaf (graphPLReebData G h S) S)
      ?_ ?_
    · intro i x
      obtain ⟨v, rfl⟩ := (graphPLReebData G h S).vertexLabel S i |>.surjective x
      change (intervalComponentNatTrans (graphPLReebMap G h hS)
          (height_graphPLReebMap G h hS)).app (S.J i)
          ((graphPLCosheafIso G h hS).hom.app (S.J i)
            ((graphPLReebData G h S).vertexLabel S i v)) =
        (graphPLReebData G h S).vertexLabel S i v
      exact intervalComponentNatTrans_graphPLReebMap_on_vertexLabel G h hS v
    · intro e x
      obtain ⟨y, rfl⟩ := (graphPLReebData G h S).edgeLabel S e |>.surjective x
      change (intervalComponentNatTrans (graphPLReebMap G h hS)
          (height_graphPLReebMap G h hS)).app (S.K e)
          ((graphPLCosheafIso G h hS).hom.app (S.K e)
            ((graphPLReebData G h S).edgeLabel S e y)) =
        (graphPLReebData G h S).edgeLabel S e y
      exact intervalComponentNatTrans_graphPLReebMap_on_edgeLabel G h hS y
  exact (Iso.hom_comp_eq_id (graphPLCosheafIso G h hS)).mp hcomp

/-- The descended quotient map has the height-preservation equation used by the interval
component comparison. -/
theorem height_graphPLReebQuotientMap (hS : CoversVertexHeights S h)
    (q : ReebQuotient (plHeight G h)) :
    (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
        (graphPLReebQuotientMap G h hS q) = ReebQuotient.height _ q := by
  induction q using ReebQuotient.ind with
  | h x =>
      change (CylinderPresentation.ofFiniteData (graphPLReebData G h S)).height S
          (graphPLReebMap G h hS x) = plHeight G h x
      exact height_graphPLReebMap G h hS x

/-- The interval-component comparison followed by the descended map is the inverse graph-PL
cosheaf identification. -/
theorem intervalComponentComparison_comp_graphPLReebQuotientMap
    (hS : CoversVertexHeights S h) :
    ReebQuotient.intervalComponentComparison (plHeight G h) ≫
        intervalComponentNatTrans (graphPLReebQuotientMap G h hS)
          (height_graphPLReebQuotientMap G h hS) =
      (graphPLCosheafIso G h hS).inv := by
  have hcomp :
      ReebQuotient.intervalComponentComparison (plHeight G h) ≫
          intervalComponentNatTrans (graphPLReebQuotientMap G h hS)
            (height_graphPLReebQuotientMap G h hS) =
        intervalComponentNatTrans (graphPLReebMap G h hS)
          (height_graphPLReebMap G h hS) := by
    ext I c
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  rw [hcomp, intervalComponentNatTrans_graphPLReebMap]

/-- The Reeb quotient of a finite graph-PL realization is an R-graph. -/
theorem isRGraph_graphPLReebQuotient :
    RGraph.IsRGraph ((ReebQuotient.quotientFunctor ℝ).obj (graphPLOver G h)) := by
  obtain ⟨n, S, hS⟩ := exists_coversVertexHeights h
  exact ⟨n, S, graphPLReebData G h S, ⟨graphPLReebQuotientIso G h hS⟩⟩

/-- The graph-PL Reeb quotient, regarded as an object of the R-graph category. -/
noncomputable def graphPLReebGraph : RGraph.RGraphCat :=
  ⟨(ReebQuotient.quotientFunctor ℝ).obj (graphPLOver G h),
    isRGraph_graphPLReebQuotient G h⟩

/-- The graph-PL Reeb quotient graph is isomorphic to every finite realization obtained from a
covering critical-value list. -/
noncomputable def graphPLReebGraphIso (hS : CoversVertexHeights S h) :
    graphPLReebGraph G h ≅ (RGraph.toRGraph S).obj (graphPLReebData G h S) :=
  ObjectProperty.isoMk _ (graphPLReebQuotientIso G h hS)

/-- The interval-component comparison of a graph-PL height is an isomorphism. -/
instance isIso_intervalComponentComparison_plHeight :
    IsIso (ReebQuotient.intervalComponentComparison (plHeight G h)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro I
  rw [isIso_iff_bijective]
  constructor
  · intro x y hxy
    obtain ⟨n, S, hS⟩ := exists_coversVertexHeights h
    have hnat := congrArg (fun α => α.app I)
      (intervalComponentComparison_comp_graphPLReebQuotientMap G h hS)
    have hinv :
        (graphPLCosheafIso G h hS).inv.app I x =
          (graphPLCosheafIso G h hS).inv.app I y := by
      rw [← hnat]
      change (intervalComponentNatTrans (graphPLReebQuotientMap G h hS)
          (height_graphPLReebQuotientMap G h hS)).app I
          ((ReebQuotient.intervalComponentComparison (plHeight G h)).app I x) =
        (intervalComponentNatTrans (graphPLReebQuotientMap G h hS)
          (height_graphPLReebQuotientMap G h hS)).app I
          ((ReebQuotient.intervalComponentComparison (plHeight G h)).app I y)
      exact congrArg _ hxy
    exact ((isIso_iff_bijective ((graphPLCosheafIso G h hS).inv.app I)).1
      inferInstance).1 hinv
  · exact ReebQuotient.intervalComponentComparison_app_surjective (plHeight G h) I

/-- The geometric interleaving distance between graph-PL Reeb quotients is the interleaving
distance between their interval-component precosheaves. -/
theorem geometricInterleavingDistance_graphPLReebGraph {V' : Type} [Finite V']
    (G' : SimpleGraph V') (h' : V' → ℝ) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G' h') =
      interleavingDistance (intervalComponents (plHeight G h))
        (intervalComponents (plHeight G' h')) := by
  obtain ⟨n, S, hS⟩ := exists_coversVertexHeights h
  obtain ⟨m, T, hT⟩ := exists_coversVertexHeights h'
  rw [geometricInterleavingDistance_congr
    (graphPLReebGraphIso G h hS) (graphPLReebGraphIso G' h' hT)]
  exact geometricInterleavingDistance_graphPL G h G' h' hS hT

end slice

end

end TDA.Mapper.GraphPL
