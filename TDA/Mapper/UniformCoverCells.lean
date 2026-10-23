import TDA.Mapper.MultiNerveGraphPL

/-!
# Height-separating uniform covers and the cells of the MultiNerve Mapper

For `V : Type u`, `G : SimpleGraph V` and vertex heights `h : V → ℝ`, this module classifies the
cells of the MultiNerve Mapper of a height-separating uniform cover combinatorially: by
vertex-height level components, edges crossing a level, and edges spanning a regular interval.
These are the terms in which a later finite Reeb graph of graph-PL input is to be described; no
Reeb graph is constructed or compared here.

## Attained range

For a connected graph with a lowest vertex `lo` and a highest vertex `hi`, the graph-PL height
attains exactly `[h lo, h hi]` (`range_plHeight_eq_Icc`); a finite connected graph has such
vertices (`exists_range_plHeight_eq_Icc`). Connectedness is mathlib's `SimpleGraph.Connected`,
which includes nonemptiness, and cannot be dropped.

## Height-separating uniform covers

`HeightSeparating h U` says that every member of `U : Fin n → OpenInterval` contains at most one
vertex height and every consecutive overlap contains none. Vertex heights are a witness set in
the sense of `TDA.Reeb.CriticalValues`, not a minimal critical set: a degree-two monotone vertex
counts as a height to be separated. For a finite vertex type, vertex heights in `[m, M]` and any
resolution bound `ρ > 0`, some `uniformCover a r g n` is height-separating, with `0 < g`,
`2g ≤ r`, `r < ρ`, `0 < n`, the anchoring `m - (r - g) < a < m` and `M < a + n(r - g) + g`
(`exists_heightSeparating_uniformCover`); it covers the attained range of every graph on `V`
(`heightSeparating_covers_range`). The construction is explicit: a step below the minimal positive
height gap, a base point avoiding a finite set, and an overlap length below a positive distance.
No minimality of `n` and no canonicity of the parameters is claimed.

## Splitting incidence components

For every open interval `K`, the connected components of the incidence graph `cellGraph G h K`
are the components of the graph induced on the surviving vertices together with the uncovered
edges, the active edges with no endpoint height in `K` (`cellComponentsEquivSum`). No coverage,
finiteness or decidability is assumed. Under endpoint coverage the second summand is empty and the
first summand is `cellInducedEquiv`; without surviving vertices the first summand is empty and the
second recovers `cellGraphComponentsEquivActiveEdges`.

## Cell classification

The MultiNerve Mapper cells with label set `{i}` are the path components of `f ⁻¹' U i`
(`vertexCellsEquiv`), for graph-PL input the incidence components over `U i`
(`vertexCellsCellGraphEquiv`). Over a height-separating uniform cover `uniformCover a r g n`:

* a member containing the vertex height `c` carries the vertex cells
  `(G.induce {v | h v = c}).ConnectedComponent ⊕ {e // EdgeCrosses G h c e}`
  (`uniformVertexCellsEquivLevel`);
* for `0 < r`, a member `(p, q)` containing no vertex height carries one vertex cell per edge
  spanning `[p, q]` (`uniformVertexCellsEquivSpans`);
* for `0 < g ≤ r`, consecutive labels carry one edge cell per edge spanning the overlap
  (`uniformEdgeCellsEquivSpans`).

For `2g ≤ r`, labels at distance at least two carry no edge cell
(`isEmpty_uniformEdgeCells_of_far`). Height separation alone does not give this: for the single
edge of heights `0` and `2`, `uniformCover (-1/4) (3/2) 1 3` is height-separating, while its labels
`0` and `2` meet in `(3/4, 5/4)` and carry an edge cell. These are
elementary library results, not attributed to a source. The face maps between these cells and the
comparison with a finite Reeb graph are not part of this module. See `docs/math/mapper.md`.
-/

namespace TDA.Mapper

open Set SimpleGraph
open TDA.Topology TDA.Reeb TDA.Reeb.OpenInterval
open TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

universe u v w

/-! ## The attained range -/

section range

variable {V : Type u}

/-- **Attained range.** For a connected graph with a lowest and a highest vertex, the graph-PL
height attains exactly the interval between their heights. -/
theorem range_plHeight_eq_Icc {G : SimpleGraph V} {h : V → ℝ} (hG : G.Connected) {lo hi : V}
    (hlo : ∀ v, h lo ≤ h v) (hhi : ∀ v, h v ≤ h hi) :
    Set.range (plHeight G h) = Set.Icc (h lo) (h hi) := by
  refine Subset.antisymm (range_plHeight_subset_Icc fun v => ⟨hlo v, hhi v⟩) ?_
  have := (connected_iff_pathConnectedSpace G).1 hG
  exact (isPreconnected_range (plHeight G h).continuous).Icc_subset
    ⟨vertex G lo, plHeight_vertex G h lo⟩ ⟨vertex G hi, plHeight_vertex G h hi⟩

/-- A finite connected graph has a lowest and a highest vertex, and its graph-PL height attains
exactly the interval between their heights. -/
theorem exists_range_plHeight_eq_Icc [Finite V] {G : SimpleGraph V} (h : V → ℝ)
    (hG : G.Connected) :
    ∃ lo hi : V, (∀ v, h lo ≤ h v) ∧ (∀ v, h v ≤ h hi) ∧
      Set.range (plHeight G h) = Set.Icc (h lo) (h hi) := by
  have := hG.nonempty
  obtain ⟨lo, hlo⟩ := Finite.exists_min h
  obtain ⟨hi, hhi⟩ := Finite.exists_max h
  exact ⟨lo, hi, hlo, hhi, range_plHeight_eq_Icc hG hlo hhi⟩

end range

/-! ## Height-separating uniform covers -/

section separating

variable {V : Type u}

/-- Every member contains at most one vertex height, and every consecutive overlap contains none. -/
def HeightSeparating (h : V → ℝ) {n : ℕ} (U : Fin n → OpenInterval) : Prop :=
  (∀ k v w, h v ∈ U k → h w ∈ U k → h v = h w) ∧
    ∀ k l : Fin n, (k : ℕ) + 1 = l → ∀ v, h v ∉ U k ⊓ U l

/-- A finite family of nonzero reals is bounded away from zero. -/
private theorem exists_pos_le_abs {ι : Type*} [Finite ι] (F : ι → ℝ) (hF : ∀ i, F i ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ |F i| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i => |F i|
    exact ⟨|F i₀|, abs_pos.2 (hF i₀), hi₀⟩

/-- **Existence.** For a finite vertex type, vertex heights in `[m, M]` and a resolution bound
`ρ > 0`, some uniform cover with `0 < g`, `2g ≤ r < ρ` and `0 < n`, anchored by
`m - (r - g) < a < m` and reaching beyond `M`, is height-separating. The height bounds are not
needed for separation; they enter through the coverage of the attained range
(`heightSeparating_covers_range`). -/
theorem exists_heightSeparating_uniformCover [Finite V] (h : V → ℝ) {m M ρ : ℝ}
    (_hh : ∀ v, h v ∈ Set.Icc m M) (hρ : 0 < ρ) :
    ∃ (a r g : ℝ) (n : ℕ), 0 < g ∧ 2 * g ≤ r ∧ r < ρ ∧ 0 < n ∧
      m - (r - g) < a ∧ a < m ∧ M < a + n * (r - g) + g ∧
      HeightSeparating h (uniformCover a r g n) := by
  -- The minimal positive height gap `δ`.
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_abs (ι := {p : V × V // h p.1 ≠ h p.2})
    (fun p => h p.1.1 - h p.1.2) fun p => sub_ne_zero.2 p.2
  -- The step `s`.
  set s : ℝ := min ρ δ / 2 with hs_def
  have hs : 0 < s := half_pos (lt_min hρ hδ)
  have hsρ : s ≤ ρ / 2 := div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
  have hsδ : s ≤ δ / 2 := div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
  -- The count `n`.
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((M - m) / s)
  set n : ℕ := n₀ + 1 with hn_def
  have hn : 0 < n := Nat.succ_pos n₀
  have hns : M - m + s < n * s := by
    rw [div_lt_iff₀ hs] at hn₀
    rw [hn_def]
    push_cast
    linarith
  -- The base point `a`, avoiding every `h v - l s`.
  have hB : (Set.range fun p : V × Fin n => h p.1 - ((p.2 : ℕ) : ℝ) * s).Finite :=
    Set.finite_range _
  obtain ⟨a, ha, haB⟩ :=
    (Set.Ioo_infinite (by linarith : m - s < m)).exists_notMem_finite hB
  -- The overlap length `g`, below the distance from `a + l s` to every vertex height.
  obtain ⟨ε, hε, hεle⟩ := exists_pos_le_abs (ι := V × Fin n)
    (fun p => h p.1 - (a + ((p.2 : ℕ) : ℝ) * s)) fun p hp =>
      haB ⟨p, by
        have hp' : h p.1 - (a + ((p.2 : ℕ) : ℝ) * s) = 0 := hp
        show h p.1 - ((p.2 : ℕ) : ℝ) * s = a
        linarith⟩
  set g : ℝ := min ε s / 2 with hg_def
  have hg : 0 < g := half_pos (lt_min hε hs)
  have hgε : g < ε := lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two)
    (half_lt_self hε)
  have hgs : g ≤ s / 2 := div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
  set r : ℝ := s + g with hr_def
  have hrg : r - g = s := by rw [hr_def]; ring
  have hgr : g ≤ r := by linarith
  refine ⟨a, r, g, n, hg, by linarith, by linarith, hn, by rw [hrg]; exact ha.1, ha.2,
    by rw [hrg]; linarith [ha.1], ?_, ?_⟩
  · -- Two heights in one member differ by less than `r < δ`.
    intro k v w hv hw
    rw [uniformCover_apply, mem_uniformInterval, hrg] at hv hw
    obtain ⟨hv₁, hv₂⟩ := hv
    obtain ⟨hw₁, hw₂⟩ := hw
    by_contra hne
    have hgap : δ ≤ |h v - h w| := hδle ⟨(v, w), hne⟩
    have : |h v - h w| < r := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    linarith
  · -- A height in the overlap `(a + l s, a + l s + g)` would be closer than `ε` to `a + l s`.
    intro k l hkl v hv
    rw [GraphPL.uniformCover_inf_of_succ hgr hkl, mem_ioo, hrg] at hv
    have hdist : ε ≤ |h v - (a + ((l : ℕ) : ℝ) * s)| := hεle (v, l)
    have : |h v - (a + ((l : ℕ) : ℝ) * s)| < g :=
      abs_sub_lt_iff.2 ⟨by linarith [hv.2], by linarith [hv.1]⟩
    linarith

/-- **Coverage of the attained range.** The height-separating uniform cover of
`exists_heightSeparating_uniformCover` covers the attained range of the graph-PL height of every
graph on `V`. -/
theorem heightSeparating_covers_range [Finite V] (h : V → ℝ) {m M ρ : ℝ}
    (hh : ∀ v, h v ∈ Set.Icc m M) (hρ : 0 < ρ) :
    ∃ (a r g : ℝ) (n : ℕ), 0 < g ∧ 2 * g ≤ r ∧ r < ρ ∧ 0 < n ∧
      m - (r - g) < a ∧ a < m ∧ M < a + n * (r - g) + g ∧
      HeightSeparating h (uniformCover a r g n) ∧
      ∀ G : SimpleGraph V,
        Covers (fun k => (uniformCover a r g n k : Set ℝ)) (Set.range (plHeight G h)) := by
  obtain ⟨a, r, g, n, hg, hgr, hrρ, hn, ha₁, ha₂, hM, hsep⟩ :=
    exists_heightSeparating_uniformCover h hh hρ
  exact ⟨a, r, g, n, hg, hgr, hrρ, hn, ha₁, ha₂, hM, hsep, fun _ =>
    uniformCover_covers_range hh ha₂ hM hg hn⟩

end separating

/-! ## Graph-PL cells -/

namespace GraphPL

section split

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) (K : OpenInterval)

/-- Active edges with no endpoint height in `K`. -/
def UncoveredEdge : Type u :=
  {e : G.edgeSet // EdgeActive G h K e ∧ ∀ v ∈ (e : Sym2 V), h v ∉ K}

/-- The node label of an edge node: the induced class of a classically chosen surviving endpoint
when one exists, and the uncovered edge otherwise. Only the induced class of the endpoint enters
the laws (`edgeSplit_of_mem`). -/
private def edgeSplit (e : {e : G.edgeSet // EdgeActive G h K e}) :
    (G.induce (h ⁻¹' (K : Set ℝ))).ConnectedComponent ⊕ UncoveredEdge G h K :=
  haveI := Classical.propDecidable (∃ v ∈ (e.1 : Sym2 V), h v ∈ K)
  if hv : ∃ v ∈ (e.1 : Sym2 V), h v ∈ K then
    Sum.inl ((G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk
      ⟨Classical.choose hv, (Classical.choose_spec hv).2⟩)
  else Sum.inr ⟨e.1, e.2, fun v hv' hvK => hv ⟨v, hv', hvK⟩⟩

/-- The node label on all nodes of the incidence graph. -/
private def splitNode :
    Cell G h K → (G.induce (h ⁻¹' (K : Set ℝ))).ConnectedComponent ⊕ UncoveredEdge G h K :=
  Sum.elim (fun v => Sum.inl ((G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk v))
    (edgeSplit G h K)

variable {G h K}

private theorem edgeSplit_of_mem (e : {e : G.edgeSet // EdgeActive G h K e})
    {w : ↥(h ⁻¹' (K : Set ℝ))} (hw : (w : V) ∈ (e.1 : Sym2 V)) :
    edgeSplit G h K e = Sum.inl ((G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk w) := by
  have hv : ∃ v ∈ (e.1 : Sym2 V), h v ∈ K := ⟨w, hw, w.2⟩
  unfold edgeSplit
  rw [dif_pos hv]
  exact congrArg Sum.inl (induce_mk_eq_of_mem G h K (Classical.choose_spec hv).1 hw)

private theorem edgeSplit_of_not (e : {e : G.edgeSet // EdgeActive G h K e})
    (hv : ¬ ∃ v ∈ (e.1 : Sym2 V), h v ∈ K) :
    edgeSplit G h K e = Sum.inr ⟨e.1, e.2, fun v hv' hvK => hv ⟨v, hv', hvK⟩⟩ := by
  unfold edgeSplit
  rw [dif_neg hv]

private theorem splitNode_eq_of_adj {x y : Cell G h K} (hxy : (cellGraph G h K).Adj x y) :
    splitNode G h K x = splitNode G h K y := by
  rcases x with v | e <;> rcases y with w | e'
  · exact (hxy : False).elim
  · exact (edgeSplit_of_mem e' hxy).symm
  · exact edgeSplit_of_mem e hxy
  · exact (hxy : False).elim

variable (G h K)

/-- **Splitting incidence components.** The connected components of the incidence graph over `K`
are the components of the graph induced on the surviving vertices, together with the active
edges having no endpoint height in `K`. No coverage, finiteness or decidability is assumed. -/
def cellComponentsEquivSum :
    (cellGraph G h K).ConnectedComponent ≃
      (G.induce (h ⁻¹' (K : Set ℝ))).ConnectedComponent ⊕ UncoveredEdge G h K where
  toFun := ConnectedComponent.lift (splitNode G h K) fun _ _ p _ =>
    eq_of_walk (fun _ _ => splitNode_eq_of_adj) p
  invFun := Sum.elim (inducedToCell G h K)
    fun e => (cellGraph G h K).connectedComponentMk (Sum.inr ⟨e.1, e.2.1⟩)
  left_inv c := by
    induction c using ConnectedComponent.ind with
    | h x =>
      rcases x with v | e
      · rfl
      · by_cases hv : ∃ v ∈ (e.1 : Sym2 V), h v ∈ K
        · obtain ⟨w, hw, hwK⟩ := hv
          show Sum.elim _ _ (edgeSplit G h K e) = _
          rw [edgeSplit_of_mem e (w := ⟨w, hwK⟩) hw]
          exact connectedComponentMk_inl_eq_inr G h K hw
        · show Sum.elim _ _ (edgeSplit G h K e) = _
          rw [edgeSplit_of_not e hv]
          rfl
  right_inv c := by
    rcases c with c | e
    · induction c using ConnectedComponent.ind with
      | h v => rfl
    · show edgeSplit G h K ⟨e.1, e.2.1⟩ = _
      rw [edgeSplit_of_not _ fun ⟨v, hv, hvK⟩ => e.2.2 v hv hvK]
      rfl

/-- A vertex node goes to the induced class of its vertex. -/
@[simp] theorem cellComponentsEquivSum_inl (v : {v : V // h v ∈ K}) :
    cellComponentsEquivSum G h K ((cellGraph G h K).connectedComponentMk (Sum.inl v)) =
      Sum.inl ((G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk v) := rfl

/-- An edge node with a surviving endpoint goes to the induced class of that endpoint, for every
such endpoint. -/
theorem cellComponentsEquivSum_inr_of_mem (e : {e : G.edgeSet // EdgeActive G h K e})
    {w : ↥(h ⁻¹' (K : Set ℝ))} (hw : (w : V) ∈ (e.1 : Sym2 V)) :
    cellComponentsEquivSum G h K ((cellGraph G h K).connectedComponentMk (Sum.inr e)) =
      Sum.inl ((G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk w) :=
  edgeSplit_of_mem e hw

/-- An uncovered edge node goes to the uncovered edge. -/
@[simp] theorem cellComponentsEquivSum_inr_uncovered (e : UncoveredEdge G h K) :
    cellComponentsEquivSum G h K ((cellGraph G h K).connectedComponentMk (Sum.inr ⟨e.1, e.2.1⟩)) =
      Sum.inr e :=
  (cellComponentsEquivSum G h K).apply_symm_apply (Sum.inr e)

@[simp] theorem cellComponentsEquivSum_symm_inl
    (c : (G.induce (h ⁻¹' (K : Set ℝ))).ConnectedComponent) :
    (cellComponentsEquivSum G h K).symm (Sum.inl c) = inducedToCell G h K c := rfl

@[simp] theorem cellComponentsEquivSum_symm_inr (e : UncoveredEdge G h K) :
    (cellComponentsEquivSum G h K).symm (Sum.inr e) =
      (cellGraph G h K).connectedComponentMk (Sum.inr ⟨e.1, e.2.1⟩) := rfl

/-- Under endpoint coverage no edge is uncovered. -/
theorem isEmpty_uncoveredEdge_of_coverage (hcov : EndpointCoverage G h K) :
    IsEmpty (UncoveredEdge G h K) :=
  ⟨fun e => by
    obtain ⟨v, hv, hvK⟩ := hcov e.1 e.2.1
    exact e.2.2 v hv hvK⟩

/-- **Consistency with `cellInducedEquiv`.** Under endpoint coverage the splitting lands in the
first summand, through the merged vertex-only corollary. -/
theorem cellComponentsEquivSum_eq_inl_of_coverage (hcov : EndpointCoverage G h K)
    (c : (cellGraph G h K).ConnectedComponent) :
    cellComponentsEquivSum G h K c = Sum.inl (cellInducedEquiv G h K hcov c) := by
  induction c using ConnectedComponent.ind with
  | h x =>
    rcases x with v | e
    · rfl
    · exact cellComponentsEquivSum_inr_of_mem G h K e (coverEndpoint_mem G h K hcov e)

/-- **Consistency with `cellGraphComponentsEquivActiveEdges`.** Without a vertex height in `K`
the splitting lands in the second summand, at the active edge of the class. -/
theorem cellComponentsEquivSum_eq_inr_of_forall_not_mem (hK : ∀ v, h v ∉ K)
    (c : (cellGraph G h K).ConnectedComponent) :
    cellComponentsEquivSum G h K c =
      Sum.inr ⟨(cellGraphComponentsEquivActiveEdges hK c).1,
        (cellGraphComponentsEquivActiveEdges hK c).2, fun v _ => hK v⟩ := by
  induction c using ConnectedComponent.ind with
  | h x =>
    rcases x with v | e
    · exact (hK v.1 v.2).elim
    · show edgeSplit G h K e = _
      rw [edgeSplit_of_not e fun ⟨v, _, hvK⟩ => hK v hvK]
      rfl

end split

section vertexCells

variable {V : Type u} {I : Type w} (G : SimpleGraph V) (h : V → ℝ)

/-- **Graph-PL vertex cells.** The MultiNerve Mapper cells of a graph-PL height with label set
`{i}` are the connected components of the incidence graph over `U i`. -/
def vertexCellsCellGraphEquiv [DecidableEq I] (U : I → OpenInterval) (i : I) :
    {c : multiNerveMapper (plHeight G h) (fun i => (U i : Set ℝ)) //
        c.support.image Sigma.fst = {i}} ≃ (cellGraph G h (U i)).ConnectedComponent :=
  (vertexCellsEquiv (plHeight G h) (fun i => (U i : Set ℝ)) i).trans
    (preimageComponentsEquiv G h (U i))

end vertexCells

/-! ## Crossing and spanning edges -/

section predicates

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- Some dart of `e` has endpoint heights strictly on both sides of `c`. -/
def EdgeCrosses (c : ℝ) (e : G.edgeSet) : Prop :=
  ∃ d : G.Dart, dartEdge d = e ∧ min (h d.fst) (h d.snd) < c ∧ c < max (h d.fst) (h d.snd)

/-- Some dart of `e` has height interval containing `[p, q]`. -/
def EdgeSpans (p q : ℝ) (e : G.edgeSet) : Prop :=
  ∃ d : G.Dart, dartEdge d = e ∧ min (h d.fst) (h d.snd) ≤ p ∧ q ≤ max (h d.fst) (h d.snd)

variable {G h}

/-- **Orientation independence** of crossing: every dart of the edge decides it. -/
theorem edgeCrosses_dartEdge_iff {c : ℝ} (d : G.Dart) :
    EdgeCrosses G h c (dartEdge d) ↔
      min (h d.fst) (h d.snd) < c ∧ c < max (h d.fst) (h d.snd) := by
  refine ⟨fun ⟨d', hd', h₁, h₂⟩ => ?_, fun hd => ⟨d, rfl, hd⟩⟩
  rcases dartEdge_eq_iff.1 hd' with rfl | rfl
  · exact ⟨h₁, h₂⟩
  · exact ⟨by rw [min_comm]; exact h₁, by rw [max_comm]; exact h₂⟩

/-- **Orientation independence** of spanning: every dart of the edge decides it. -/
theorem edgeSpans_dartEdge_iff {p q : ℝ} (d : G.Dart) :
    EdgeSpans G h p q (dartEdge d) ↔
      min (h d.fst) (h d.snd) ≤ p ∧ q ≤ max (h d.fst) (h d.snd) := by
  refine ⟨fun ⟨d', hd', h₁, h₂⟩ => ?_, fun hd => ⟨d, rfl, hd⟩⟩
  rcases dartEdge_eq_iff.1 hd' with rfl | rfl
  · exact ⟨h₁, h₂⟩
  · exact ⟨by rw [min_comm]; exact h₁, by rw [max_comm]; exact h₂⟩

/-- An endpoint height below `q` and not in `(p, q)` is at most `p`. -/
private theorem le_of_not_mem_of_lt {p q y : ℝ} (hy : y ∉ ioo p q) (hyq : y < q) : y ≤ p :=
  not_lt.1 fun hpy => hy (mem_ioo.2 ⟨hpy, hyq⟩)

/-- An endpoint height above `p` and not in `(p, q)` is at least `q`. -/
private theorem ge_of_not_mem_of_lt {p q y : ℝ} (hy : y ∉ ioo p q) (hpy : p < y) : q ≤ y :=
  not_lt.1 fun hyq => hy (mem_ioo.2 ⟨hpy, hyq⟩)

/-- **Uncovered edges at a single level.** If `p < c < q` and every vertex height in `(p, q)`
equals `c`, the active edges with no endpoint height in `(p, q)` are the edges crossing `c`. -/
def uncoveredEdgeEquivCrosses {p q c : ℝ} (hpc : p < c) (hcq : c < q)
    (hlev : ∀ v, h v ∈ ioo p q → h v = c) :
    UncoveredEdge G h (ioo p q) ≃ {e // EdgeCrosses G h c e} :=
  Equiv.subtypeEquivRight fun e => by
    obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
    rw [edgeCrosses_dartEdge_iff]
    constructor
    · rintro ⟨hact, hunc⟩
      have h₁ := hunc d.fst (fst_mem_dartEdge d)
      have h₂ := hunc d.snd (snd_mem_dartEdge d)
      obtain ⟨hmin, hmax⟩ :=
        (edgeActive_ioo_iff_of_endpoints (hpc.trans hcq) d h₁ h₂).1 hact
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hmin, hmax⟩
      -- An endpoint with height in `(p, q)` would have height `c`.
      have hnot : ∀ v ∈ (dartEdge d : Sym2 V), h v ∉ ioo p q := by
        intro v hv hvK
        have hvc := hlev v hvK
        rcases mem_dartEdge.1 hv with rfl | rfl
        · rw [hvc] at hmin hmax
          rcases min_lt_iff.1 hmin with h' | h'
          · exact lt_irrefl _ h'
          · rcases lt_max_iff.1 hmax with h'' | h''
            · exact lt_irrefl _ h''
            · linarith
        · rw [hvc] at hmin hmax
          rcases min_lt_iff.1 hmin with h' | h'
          · rcases lt_max_iff.1 hmax with h'' | h''
            · linarith
            · exact lt_irrefl _ h''
          · exact lt_irrefl _ h'
      have h₁ := hnot d.fst (fst_mem_dartEdge d)
      have h₂ := hnot d.snd (snd_mem_dartEdge d)
      refine ⟨(edgeActive_ioo_iff_of_endpoints (hpc.trans hcq) d h₁ h₂).2 ⟨?_, ?_⟩, hnot⟩
      · rcases min_choice (h d.fst) (h d.snd) with hm | hm <;> rw [hm] at hmin ⊢
        · exact le_of_not_mem_of_lt h₁ (by linarith)
        · exact le_of_not_mem_of_lt h₂ (by linarith)
      · rcases max_choice (h d.fst) (h d.snd) with hm | hm <;> rw [hm] at hmax ⊢
        · exact ge_of_not_mem_of_lt h₁ (by linarith)
        · exact ge_of_not_mem_of_lt h₂ (by linarith)

/-- **Active edges without levels.** If `p < q` and no vertex height lies in `(p, q)`, the active
edges over `(p, q)` are the edges spanning `[p, q]`. -/
def activeEdgeEquivSpans {p q : ℝ} (hpq : p < q) (hK : ∀ v, h v ∉ ioo p q) :
    {e // EdgeActive G h (ioo p q) e} ≃ {e // EdgeSpans G h p q e} :=
  Equiv.subtypeEquivRight fun e => by
    obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
    rw [edgeSpans_dartEdge_iff]
    exact edgeActive_ioo_iff_of_endpoints hpq d (hK _) (hK _)

end predicates

/-! ## The classification over a height-separating uniform cover -/

section classification

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- The vertices of a member containing the height `h v₀` of a height-separating family are the
vertices at that height. -/
theorem preimage_eq_level_of_heightSeparating {n : ℕ} {U : Fin n → OpenInterval}
    (hsep : HeightSeparating h U) {k : Fin n} {v₀ : V} (hv₀ : h v₀ ∈ U k) :
    h ⁻¹' (U k : Set ℝ) = {v | h v = h v₀} := by
  ext v
  constructor
  · intro hv
    exact hsep.1 k v v₀ hv hv₀
  · intro hv
    show h v ∈ U k
    rw [show h v = h v₀ from hv]
    exact hv₀

/-- **Vertex cells at a level.** Over a height-separating uniform cover, the vertex cells over a
member containing the vertex height `h v₀` are the components of the graph induced on the
vertices of height `h v₀`, together with the edges crossing `h v₀`. -/
def uniformVertexCellsEquivLevel {a r g : ℝ} {n : ℕ}
    (hsep : HeightSeparating h (uniformCover a r g n)) (k : Fin n) (v₀ : V)
    (hv₀ : h v₀ ∈ uniformCover a r g n k) :
    {c : multiNerveMapper (plHeight G h) (fun i => (uniformCover a r g n i : Set ℝ)) //
        c.support.image Sigma.fst = {k}} ≃
      (G.induce {v | h v = h v₀}).ConnectedComponent ⊕ {e // EdgeCrosses G h (h v₀) e} :=
  (vertexCellsCellGraphEquiv G h (uniformCover a r g n) k).trans
    ((cellComponentsEquivSum G h (uniformCover a r g n k)).trans
      (Equiv.sumCongr
        (Equiv.cast (congrArg (fun S => (G.induce S).ConnectedComponent)
          (preimage_eq_level_of_heightSeparating h hsep hv₀)))
        (uncoveredEdgeEquivCrosses (mem_ioo.1 hv₀).1 (mem_ioo.1 hv₀).2
          fun v hv => hsep.1 k v v₀ hv hv₀)))

/-- **Vertex cells without a level.** For `0 < r` and a member `(p, q)` of the uniform family
containing no vertex height, the vertex cells over it are the edges spanning `[p, q]`. -/
def uniformVertexCellsEquivSpans {a r g : ℝ} {n : ℕ} (k : Fin n)
    (hk : ∀ v, h v ∉ uniformCover a r g n k) (hr : 0 < r) :
    {c : multiNerveMapper (plHeight G h) (fun i => (uniformCover a r g n i : Set ℝ)) //
        c.support.image Sigma.fst = {k}} ≃
      {e // EdgeSpans G h (a + (k : ℕ) * (r - g)) (a + (k : ℕ) * (r - g) + r) e} :=
  (vertexCellsCellGraphEquiv G h (uniformCover a r g n) k).trans
    ((cellGraphComponentsEquivActiveEdges hk).trans
      (activeEdgeEquivSpans (by linarith) hk))

/-- **Edge cells.** Over a height-separating uniform cover with `0 < g ≤ r`, the edge cells over
consecutive labels `k`, `l = k + 1` are the edges spanning the overlap
`[a + l(r - g), a + l(r - g) + g]`. Only the second clause of `HeightSeparating` is used. -/
def uniformEdgeCellsEquivSpans {a r g : ℝ} {n : ℕ}
    (hsep : HeightSeparating h (uniformCover a r g n)) (hgr : g ≤ r) (hg : 0 < g) {k l : Fin n}
    (hkl : (k : ℕ) + 1 = l) :
    {c : multiNerveMapper (plHeight G h) (fun i => (uniformCover a r g n i : Set ℝ)) //
        c.support.image Sigma.fst = {k, l}} ≃
      {e // EdgeSpans G h (a + (l : ℕ) * (r - g)) (a + (l : ℕ) * (r - g) + g) e} :=
  have hK : ∀ v, h v ∉ ioo (a + (l : ℕ) * (r - g)) (a + (l : ℕ) * (r - g) + g) := fun v hv =>
    hsep.2 k l hkl v (by rw [uniformCover_inf_of_succ hgr hkl]; exact hv)
  (uniformEdgeCellsEquiv G h hgr hkl).trans
    ((cellGraphComponentsEquivActiveEdges hK).trans (activeEdgeEquivSpans (by linarith) hK))

end classification

end GraphPL

end

end TDA.Mapper
