import TDA.Mapper.GraphPLReebExtremal
import TDA.Reeb.InterleavingCardinality

/-!
# Component counts of graph-PL heights and the Reeb distance of a merge-height change

For a simple graph `G`, vertex heights `h` and an open interval `I`, the interval components of
`plHeight G h` at `I` are the connected components of the incidence graph `cellGraph G h I`
(`TDA.Reeb.GraphPL.intervalComponentsIso`). Two counts are recorded:

* if no vertex height lies in `I`, the incidence graph has no edges and its components are the
  active edges (`cellComponentsEquivActiveEdges`, `card_cellComponents_eq_card_activeEdges`);
* if `h w ∈ I`, every active edge has an endpoint with height in `I` (`EndpointCoverage`), and every
  vertex with height in `I` is `w` or adjacent to `w`, there is exactly one component
  (`card_cellComponents_eq_one`).

At `⊤` the components are those of `G` (`card_intervalComponents_plHeight_top`), so finite graphs
with different numbers of connected components have graph-PL Reeb quotients at geometric distance
`⊤` for all heights (`geometricInterleavingDistance_graphPLReebGraph_eq_top_of_card_ne`).

## The merge tree

`mergeY` is the tree on `Fin 4` with edges `0 — 2`, `1 — 2`, `2 — 3`, and `mergeHeights a M` puts
the leaves `0, 1` at height `0`, the apex `2` at `a` and the top vertex `3` at `M`. For
`0 < a < b ≤ 2a` and `b ≤ M`,

`geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
  (graphPLReebGraph mergeY (mergeHeights b M)) = ENNReal.ofReal (b - a)`

(`geometricInterleavingDistance_mergeY`). The value is `edist` of the two height vectors
(`edist_mergeHeights`); both extremal displacements of
`max_ofReal_abs_sub_le_geometricInterleavingDistance_graphPLReebGraph` are `0`
(`max_ofReal_abs_sub_mergeHeights_eq_zero`). The upper bound is the vertex budget `b - a`. For the
lower bound, let `ε < b - a` and `I = (0, b - 2ε)`, a nonempty interval because `b ≤ 2a`. With apex
at `b`, no vertex height lies in `I` and the two leaf edges are active, so there are two components
(`card_cellComponents_mergeHeights_ioo`); they stay apart in `T_ε T_ε I = (-2ε, b)`, which does not
contain the apex height (`injective_cellComponentFunctor_mergeHeights_map`). With apex at `a`, the
apex height lies in `T_ε I = (-ε, b - ε)`, so there is one component
(`card_cellComponents_mergeHeights_eq_one`). The cardinality obstruction
`le_interleavingDistance_of_forall_exists_card_lt_symm` gives `ENNReal.ofReal (b - a)` as a lower
bound.

The hypothesis `b ≤ 2a` is used only by this obstruction family: for `b > 2a` and `ε` close to
`b - a`, the interval `(0, b - 2ε)` is empty. The distance for `b > 2a` is not determined here.
These are library statements; de Silva–Munch–Patel, Definition 4.4 and Theorem 4.6(i), are the
distance and the upper bound used. See `docs/math/reeb-graph-pl.md`.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.RGraph TDA.Reeb.OpenInterval
open scoped NNReal ENNReal

section counting

variable {V : Type*} {G : SimpleGraph V} {h : V → ℝ} {I : OpenInterval}

/-- The active edge of an edge node; a vertex node is excluded by `hI`. -/
private def edgeOfCell (hI : ∀ v, h v ∉ I) : Cell G h I → {e : G.edgeSet // EdgeActive G h I e}
  | Sum.inl v => (hI v v.2).elim
  | Sum.inr e => e

/-- Without vertex heights in `I`, the incidence components over `I` are the active edges. -/
noncomputable def cellComponentsEquivActiveEdges (hI : ∀ v, h v ∉ I) :
    (cellGraph G h I).ConnectedComponent ≃ {e : G.edgeSet // EdgeActive G h I e} where
  toFun := ConnectedComponent.lift (edgeOfCell hI) fun _ _ p _ => eq_of_walk (fun x y hxy => by
    rcases x with v | e
    · exact (hI v v.2).elim
    rcases y with w | e'
    · exact (hI w w.2).elim
    · exact (not_cellGraph_adj_inr_inr hxy).elim) p
  invFun e := (cellGraph G h I).connectedComponentMk (Sum.inr e)
  left_inv c := by
    induction c using ConnectedComponent.ind with
    | h x =>
      rcases x with v | e
      · exact (hI v v.2).elim
      · rfl
  right_inv _ := rfl

theorem card_cellComponents_eq_card_activeEdges (hI : ∀ v, h v ∉ I) :
    Nat.card (cellGraph G h I).ConnectedComponent =
      Nat.card {e : G.edgeSet // EdgeActive G h I e} :=
  Nat.card_congr (cellComponentsEquivActiveEdges hI)

/-- Under endpoint coverage, a vertex `w` with `h w ∈ I` that equals or is adjacent to every
vertex with height in `I` makes the incidence graph over `I` connected. -/
theorem card_cellComponents_eq_one {w : V} (hw : h w ∈ I) (hcov : EndpointCoverage G h I)
    (hadj : ∀ v, h v ∈ I → v = w ∨ G.Adj v w) :
    Nat.card (cellGraph G h I).ConnectedComponent = 1 := by
  let c₀ := (cellGraph G h I).connectedComponentMk (Sum.inl ⟨w, hw⟩)
  have hvert (v : {v : V // h v ∈ I}) :
      (cellGraph G h I).connectedComponentMk (Sum.inl v) = c₀ := by
    obtain ⟨v, hv⟩ := v
    rcases hadj v hv with rfl | hvw
    · rfl
    · exact connectedComponentMk_inl_eq_of_adj G h I (u := ⟨v, hv⟩) (w := ⟨w, hw⟩) hvw
  have hall (c : (cellGraph G h I).ConnectedComponent) : c = c₀ := by
    induction c using ConnectedComponent.ind with
    | h x =>
      rcases x with v | e
      · exact hvert v
      · obtain ⟨u, hu, huI⟩ := hcov e.1 e.2
        exact (connectedComponentMk_inl_eq_inr G h I (v := ⟨u, huI⟩) hu).symm.trans
          (hvert ⟨u, huI⟩)
  exact Nat.card_eq_one_iff_unique.2
    ⟨⟨fun c d => (hall c).trans (hall d).symm⟩, ⟨c₀⟩⟩

end counting

section top

variable {V : Type*} (G : SimpleGraph V) (h : V → ℝ)

/-- The graph induced on the vertices with height in `⊤` is `G`. -/
private def induceTopIso : G.induce (h ⁻¹' ((⊤ : OpenInterval) : Set ℝ)) ≃g G where
  toEquiv := Equiv.subtypeUnivEquiv fun _ => trivial
  map_rel_iff' := Iff.rfl

/-- The interval components of `plHeight G h` at `⊤` are as many as the connected components
of `G`. -/
theorem card_intervalComponents_plHeight_top :
    Nat.card ((intervalComponents (plHeight G h)).obj ⊤) = Nat.card G.ConnectedComponent :=
  Nat.card_congr ((preimageInducedEquiv G h ⊤ (endpointCoverage_top G h)).trans
    (induceTopIso G h).connectedComponentEquiv)

end top

/-- Finite graphs with different numbers of connected components have graph-PL Reeb quotients at
geometric interleaving distance `⊤`, for all vertex heights. -/
theorem geometricInterleavingDistance_graphPLReebGraph_eq_top_of_card_ne {V V' : Type}
    [Finite V] [Finite V'] (G : SimpleGraph V) (h : V → ℝ) (G' : SimpleGraph V') (h' : V' → ℝ)
    (hc : Nat.card G.ConnectedComponent ≠ Nat.card G'.ConnectedComponent) :
    geometricInterleavingDistance (graphPLReebGraph G h) (graphPLReebGraph G' h') = ⊤ := by
  rw [geometricInterleavingDistance_graphPLReebGraph]
  apply interleavingDistance_eq_top_of_card_ne
  rwa [card_intervalComponents_plHeight_top, card_intervalComponents_plHeight_top]

section merge

/-- The tree with leaves `0`, `1`, apex `2` and top vertex `3`: edges `0 — 2`, `1 — 2`, `2 — 3`. -/
def mergeY : SimpleGraph (Fin 4) := SimpleGraph.fromEdgeSet {s(0, 2), s(1, 2), s(2, 3)}

/-- Leaves at height `0`, apex at `a`, top vertex at `M`. -/
def mergeHeights (a M : ℝ) : Fin 4 → ℝ := ![0, 0, a, M]

/-- The adjacency relation of the merge tree. -/
theorem mergeY_adj (u v : Fin 4) :
    mergeY.Adj u v ↔ (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) := by
  fin_cases u <;> fin_cases v <;> simp [mergeY, fromEdgeSet_adj]

private def d02 : mergeY.Dart := ⟨(0, 2), (mergeY_adj 0 2).2 (by decide)⟩

private def d12 : mergeY.Dart := ⟨(1, 2), (mergeY_adj 1 2).2 (by decide)⟩

private def d23 : mergeY.Dart := ⟨(2, 3), (mergeY_adj 2 3).2 (by decide)⟩

private theorem mergeY_edge_cases (e : mergeY.edgeSet) :
    e = dartEdge d02 ∨ e = dartEdge d12 ∨ e = dartEdge d23 := by
  obtain ⟨⟨⟨u, v⟩, huv⟩, rfl⟩ := exists_dartEdge_eq e
  rcases (mergeY_adj u v).1 huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inl rfl
  · exact .inl (Subtype.ext Sym2.eq_swap)
  · exact .inr (.inl rfl)
  · exact .inr (.inl (Subtype.ext Sym2.eq_swap))
  · exact .inr (.inr rfl)
  · exact .inr (.inr (Subtype.ext Sym2.eq_swap))

private theorem two_mem_edge (e : mergeY.edgeSet) : (2 : Fin 4) ∈ (e : Sym2 (Fin 4)) := by
  rcases mergeY_edge_cases e with rfl | rfl | rfl <;> decide

variable {a M : ℝ}

@[simp] private theorem mergeHeights_zero : mergeHeights a M 0 = 0 := rfl

@[simp] private theorem mergeHeights_one : mergeHeights a M 1 = 0 := rfl

@[simp] private theorem mergeHeights_two : mergeHeights a M 2 = a := rfl

@[simp] private theorem mergeHeights_three : mergeHeights a M 3 = M := rfl

/-- A leaf edge from height `0` to `a > 0` is active over `(0, c)` for `0 < c ≤ a`. -/
private theorem edgeActive_leaf {d : mergeY.Dart} (hd₀ : mergeHeights a M d.fst = 0)
    (hd₁ : mergeHeights a M d.snd = a) {c : ℝ} (hc : 0 < c) (hca : c ≤ a) :
    EdgeActive mergeY (mergeHeights a M) (ioo 0 c) (dartEdge d) := by
  have ha : 0 < a := hc.trans_le hca
  have ht : c / (2 * a) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by positivity)).2 (by linarith)⟩
  refine edgeActive_dartEdge_of_mem (t := ⟨c / (2 * a), ht⟩) ?_
  rw [dartHeight, hd₀, hd₁, mem_ioo]
  have hval : (1 - c / (2 * a)) * 0 + c / (2 * a) * a = c / 2 := by field_simp; ring
  simp only [hval]
  constructor <;> linarith

/-- The top edge is not active over an interval below the apex height `a ≤ M`. -/
private theorem not_edgeActive_top {K : OpenInterval} (haM : a ≤ M) (hK : ∀ x ∈ K, x < a) :
    ¬ EdgeActive mergeY (mergeHeights a M) K (dartEdge d23) := fun hact => by
  obtain ⟨t, -, -, ht⟩ := hact.exists_mem rfl
  have hlt := hK _ ht
  have h₀ : (0 : ℝ) ≤ t := t.2.1
  have hmul : (t : ℝ) * a ≤ t * M := mul_le_mul_of_nonneg_left haM h₀
  change (1 - (t : ℝ)) * a + t * M < a at hlt
  linarith

/-- An edge active over an interval below the apex height is a leaf edge. -/
private theorem leaf_of_edgeActive {K : OpenInterval} (haM : a ≤ M) (hK : ∀ x ∈ K, x < a)
    {e : mergeY.edgeSet} (he : EdgeActive mergeY (mergeHeights a M) K e) :
    e = dartEdge d02 ∨ e = dartEdge d12 := by
  rcases mergeY_edge_cases e with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr rfl
  · exact (not_edgeActive_top haM hK he).elim

/-- With apex height `a`, the incidence graph over `(0, c)`, `0 < c ≤ a ≤ M`, has two components:
the two leaf edges. -/
theorem card_cellComponents_mergeHeights_ioo {c : ℝ} (hc : 0 < c) (hca : c ≤ a) (haM : a ≤ M) :
    Nat.card (cellGraph mergeY (mergeHeights a M) (ioo 0 c)).ConnectedComponent = 2 := by
  have hI : ∀ v, mergeHeights a M v ∉ ioo 0 c := fun v hv => by
    rw [mem_ioo] at hv
    fin_cases v <;> simp at hv <;> linarith [hv.1, hv.2]
  rw [card_cellComponents_eq_card_activeEdges hI]
  refine Nat.card_eq_two_iff.2 ⟨⟨dartEdge d02, edgeActive_leaf rfl rfl hc hca⟩,
    ⟨dartEdge d12, edgeActive_leaf rfl rfl hc hca⟩, fun h => ?_, ?_⟩
  · have h' : (s(0, 2) : Sym2 (Fin 4)) = s(1, 2) :=
      congrArg (fun e => ((e.1 : mergeY.edgeSet) : Sym2 (Fin 4))) h
    exact absurd h' (by decide)
  · refine eq_univ_of_forall fun e => ?_
    rcases leaf_of_edgeActive (K := ioo 0 c) haM (fun x hx => (mem_ioo.1 hx).2.trans_le hca)
      e.2 with he | he
    · exact .inl (Subtype.ext he)
    · exact .inr (Subtype.ext he)

/-- The incidence graph is connected over every interval containing the apex height. -/
theorem card_cellComponents_mergeHeights_eq_one {K : OpenInterval} (hK : a ∈ K) :
    Nat.card (cellGraph mergeY (mergeHeights a M) K).ConnectedComponent = 1 := by
  refine card_cellComponents_eq_one (w := 2) hK (fun e _ => ⟨2, two_mem_edge e, hK⟩) fun v _ => ?_
  fin_cases v
  · exact .inr ((mergeY_adj 0 2).2 (by decide))
  · exact .inr ((mergeY_adj 1 2).2 (by decide))
  · exact .inl rfl
  · exact .inr ((mergeY_adj 3 2).2 (by decide))

/-- The side of a node over an interval below the apex: the leaf `0` or the edge at `0`. -/
private def leafSide (K : OpenInterval) : Cell mergeY (mergeHeights a M) K → Prop
  | Sum.inl v => (v : Fin 4) = 0
  | Sum.inr e => (0 : Fin 4) ∈ ((e.1 : mergeY.edgeSet) : Sym2 (Fin 4))

private theorem leafSide_adj {K : OpenInterval} (haM : a ≤ M) (hK : ∀ x ∈ K, x < a)
    {x y : Cell mergeY (mergeHeights a M) K}
    (hxy : (cellGraph mergeY (mergeHeights a M) K).Adj x y) : leafSide K x = leafSide K y := by
  have key (v : Fin 4) (hvK : mergeHeights a M v ∈ K) (e : mergeY.edgeSet)
      (he : EdgeActive mergeY (mergeHeights a M) K e) (hv : v ∈ (e : Sym2 (Fin 4))) :
      (v = 0) = ((0 : Fin 4) ∈ (e : Sym2 (Fin 4))) := by
    have hv01 : v = 0 ∨ v = 1 := by
      have hlt := hK _ hvK
      fin_cases v
      · exact .inl rfl
      · exact .inr rfl
      · exact (lt_irrefl _ hlt).elim
      · exact absurd hlt (not_lt.2 haM)
    clear hvK
    rcases leaf_of_edgeActive haM hK he with rfl | rfl <;> clear he <;>
      rcases hv01 with rfl | rfl <;> revert hv <;> decide
  rcases x with v | e <;> rcases y with w | e'
  · exact (hxy : False).elim
  · exact key v.1 v.2 e'.1 e'.2 hxy
  · exact (key w.1 w.2 e.1 e.2 hxy).symm
  · exact (hxy : False).elim

/-- With apex height `a ≤ M`, the restriction of the incidence components from `(0, c)` to an
interval `K` below `a` is injective: the two leaf edges stay in different components. -/
theorem injective_cellComponentFunctor_mergeHeights_map {c : ℝ} (hc : 0 < c) (haM : a ≤ M)
    {K : OpenInterval} (f : ioo 0 c ⟶ K) (hK : ∀ x ∈ K, x < a) :
    Function.Injective ((cellComponentFunctor mergeY (mergeHeights a M)).map f) := by
  have hca : c ≤ a := by
    by_contra hlt
    push Not at hlt
    have hx : max (c / 2) a ∈ ioo 0 c :=
      mem_ioo.2 ⟨lt_max_of_lt_left (by linarith), max_lt (by linarith) hlt⟩
    exact absurd (hK _ (OpenInterval.le_iff_subset.1 f.le hx)) (not_lt.2 (le_max_right _ _))
  have hI : ∀ v, mergeHeights a M v ∉ ioo 0 c := fun v hv => by
    rw [mem_ioo] at hv
    fin_cases v <;> simp at hv <;> linarith [hv.1, hv.2]
  intro c₁ c₂ heq
  induction c₁ using ConnectedComponent.ind with
  | h x =>
  induction c₂ using ConnectedComponent.ind with
  | h y =>
  rcases x with v | e
  · exact (hI v v.2).elim
  rcases y with w | e'
  · exact (hI w w.2).elim
  have heq' : (cellGraph mergeY (mergeHeights a M) K).connectedComponentMk
      (Sum.inr ⟨e.1, e.2.mono f.le⟩) =
      (cellGraph mergeY (mergeHeights a M) K).connectedComponentMk
        (Sum.inr ⟨e'.1, e'.2.mono f.le⟩) := heq
  obtain ⟨p⟩ := ConnectedComponent.exact heq'
  have hs := eq_of_walk (fun _ _ => leafSide_adj haM hK) p
  have hI' : ∀ x ∈ ioo 0 c, x < a := fun x hx => hx.2.trans_le hca
  have hee : e.1 = e'.1 := by
    change ((0 : Fin 4) ∈ ((e.1 : mergeY.edgeSet) : Sym2 (Fin 4))) =
      ((0 : Fin 4) ∈ ((e'.1 : mergeY.edgeSet) : Sym2 (Fin 4))) at hs
    rcases leaf_of_edgeActive haM hI' e.2 with he | he <;>
      rcases leaf_of_edgeActive haM hI' e'.2 with he' | he' <;> rw [he, he'] at hs ⊢ <;>
      exact absurd hs (by decide)
  rw [Subtype.ext hee]

/-- The two height vectors are at product extended distance `b - a`. -/
theorem edist_mergeHeights {b : ℝ} (hab : a ≤ b) :
    edist (mergeHeights a M) (mergeHeights b M) = ENNReal.ofReal (b - a) := by
  have h2 : edist (mergeHeights a M 2) (mergeHeights b M 2) = ENNReal.ofReal (b - a) := by
    rw [edist_dist, Real.dist_eq, mergeHeights_two, mergeHeights_two, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 hab)]
  refine le_antisymm (edist_pi_le_iff.2 fun v => ?_) (h2.ge.trans (edist_le_pi_edist _ _ 2))
  fin_cases v
  · simp
  · simp
  · exact h2.le
  · simp

private theorem sup'_mergeHeights (ha : 0 ≤ a) (haM : a ≤ M) :
    Finset.univ.sup' Finset.univ_nonempty (mergeHeights a M) = M :=
  le_antisymm (Finset.sup'_le _ _ fun v _ => by fin_cases v <;> simp <;> linarith)
    (Finset.le_sup' (mergeHeights a M) (Finset.mem_univ 3))

private theorem inf'_mergeHeights (ha : 0 ≤ a) (haM : a ≤ M) :
    Finset.univ.inf' Finset.univ_nonempty (mergeHeights a M) = 0 :=
  le_antisymm (Finset.inf'_le (mergeHeights a M) (Finset.mem_univ 0))
    (Finset.le_inf' _ _ fun v _ => by fin_cases v <;> simp <;> linarith)

/-- Both extremal displacements of a merge-height change are `0`. -/
theorem max_ofReal_abs_sub_mergeHeights_eq_zero {b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbM : b ≤ M) :
    max (ENNReal.ofReal |Finset.univ.sup' Finset.univ_nonempty (mergeHeights a M) -
        Finset.univ.sup' Finset.univ_nonempty (mergeHeights b M)|)
      (ENNReal.ofReal |Finset.univ.inf' Finset.univ_nonempty (mergeHeights a M) -
        Finset.univ.inf' Finset.univ_nonempty (mergeHeights b M)|) = 0 := by
  rw [sup'_mergeHeights ha (hab.trans hbM), sup'_mergeHeights (ha.trans hab) hbM,
    inf'_mergeHeights ha (hab.trans hbM), inf'_mergeHeights (ha.trans hab) hbM]
  simp

/-- **Merge-height distance.** For `0 < a < b ≤ 2a` and `b ≤ M`, moving the apex of the merge
tree from height `a` to height `b` gives graph-PL Reeb quotients at geometric interleaving
distance exactly `b - a`. -/
theorem geometricInterleavingDistance_mergeY {b : ℝ} (ha : 0 < a) (hab : a < b)
    (hb : b ≤ 2 * a) (hbM : b ≤ M) :
    geometricInterleavingDistance (graphPLReebGraph mergeY (mergeHeights a M))
      (graphPLReebGraph mergeY (mergeHeights b M)) = ENNReal.ofReal (b - a) := by
  have hba : 0 ≤ b - a := sub_nonneg.2 hab.le
  apply le_antisymm
  · rw [ENNReal.ofReal_eq_coe_nnreal hba]
    refine geometricInterleavingDistance_graphPLReebGraph_le mergeY fun v => ?_
    change |mergeHeights a M v - mergeHeights b M v| ≤ b - a
    fin_cases v
    · simpa using hba
    · simpa using hba
    · change |a - b| ≤ b - a
      rw [abs_sub_comm, abs_of_nonneg hba]
    · simpa using hba
  rw [geometricInterleavingDistance_graphPLReebGraph,
    interleavingDistance_congr (intervalComponentsIso _ _) (intervalComponentsIso _ _)]
  refine le_interleavingDistance_of_forall_exists_card_lt_symm fun ε hε => ?_
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (by linarith)] at hε
  have hc : 0 < b - 2 * ε := by linarith
  have hthick (x : ℝ) : x ∈ thicken ε (ioo 0 (b - 2 * ε)) ↔ -ε < x ∧ x < b - ε := by
    rw [thicken_ioo hc, mem_ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hthick₂ (x : ℝ) (hx : x ∈ thicken ε (thicken ε (ioo 0 (b - 2 * ε)))) : x < b := by
    rw [thicken_ioo hc, thicken_ioo (by linarith), mem_ioo] at hx
    linarith [hx.2]
  refine ⟨ioo 0 (b - 2 * ε),
    injective_cellComponentFunctor_mergeHeights_map hc hbM _ hthick₂,
    by change Finite (cellGraph _ _ _).ConnectedComponent; infer_instance, ?_⟩
  change Nat.card (cellGraph mergeY (mergeHeights a M) _).ConnectedComponent <
    Nat.card (cellGraph mergeY (mergeHeights b M) _).ConnectedComponent
  have hε₀ : (0 : ℝ) ≤ ε := ε.coe_nonneg
  rw [card_cellComponents_mergeHeights_eq_one ((hthick a).2 ⟨by linarith, by linarith⟩),
    card_cellComponents_mergeHeights_ioo hc (by linarith) hbM]
  decide

end merge

end TDA.Mapper.GraphPL
