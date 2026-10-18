import TDA.Mapper.UniformCoverCells
import TDA.Reeb.RGraph
import Mathlib.Data.Finset.Sort

/-!
# Finite Reeb data of graph-PL input

For `V : Type u`, `G : SimpleGraph V` and vertex heights `h : V → ℝ`, this module builds finite
incidence data `graphPLReebData G h S : FiniteReebData n` over an arbitrary critical-value list
`S : CriticalValues n` with levels `a i = S.value i`, and identifies them with the extracted data
`S.extract (intervalComponents (plHeight G h))` of the path-component precosheaf whenever every
vertex height is a level of `S`.

## The data

* The vertices at level `i` are `LevelVertex G h (a i)`: the connected components of the graph
  induced on the vertices of height `a i`, together with the edges crossing `a i`, i.e. with
  endpoint heights strictly on both sides of `a i`. A crossing edge is a degree-two vertex over
  the level.
* The edges over gap `e` are `SpanEdge G h (a e) (a (e+1))`: the graph edges whose height interval
  contains `[a e, a (e+1)]`. A horizontal edge spans no gap.
* An endpoint map sends a spanning edge to the level component of its endpoint at the level when
  it has one (`levelEnd_of_mem`, for every such endpoint), and to itself as a crossing edge
  otherwise (`levelEnd_of_forall_ne`).

No covering hypothesis, decidability or minimality of `S` enters the construction; a level may
carry no vertex, and the list is a witness set in the sense of `TDA.Reeb.CriticalValues`. For a
finite nonempty vertex type, the sorted distinct vertex heights form the list
`vertexHeightLevels h`, with exactly the vertex heights as levels.

## The comparison

Under `CoversVertexHeights S h`, every vertex height is a level of `S`. Then the vertices with
height in the star `J i` are those of height `a i`, and no vertex height lies in a gap `K e`.
Through the incidence-graph comparison `preimageComponentsEquiv` and the splitting
`cellComponentsEquivSum`:

* the path components of `plHeight G h ⁻¹' J i` are the Reeb vertices at level `i`
  (`graphPLStarEquiv`);
* the path components of `plHeight G h ⁻¹' K e` are the Reeb edges over gap `e`
  (`graphPLGapEquiv`);
* under these bijections the inclusions `K e ≤ J e` and `K e ≤ J (e+1)` are the endpoint maps,
  for every element of the gap value (`graphPLStarEquiv_map_left`, `graphPLStarEquiv_map_right`).

Packaged, this is the isomorphism `graphPLExtractIso` of finite data. The comparison is at stars,
the vertex values of finite data, not at closed level sets. The covering hypothesis cannot be
dropped: without it a star may contain several vertex heights (see the fixtures). These are
elementary library results, not attributed to a source. Constructibility of the precosheaf and
the cosheaf identification are in `TDA.Mapper.GraphPLCosheaf`; the Reeb quotient is treated in
`TDA.Mapper.GraphPLReebQuotient`. See `docs/math/mapper.md`.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

universe u

/-! ## Height-covering lists -/

section covers

variable {V : Type u} {n : ℕ}

/-- Every vertex height is a level of `S`. -/
def CoversVertexHeights (S : CriticalValues n) (h : V → ℝ) : Prop := ∀ v, ∃ i, S.value i = h v

variable {S : CriticalValues n} {h : V → ℝ}

/-- Under covering, a vertex height in the star of level `i` is the level `a i`. -/
theorem CoversVertexHeights.eq_of_mem_J (hS : CoversVertexHeights S h) {v : V}
    {i : Fin (n + 1)} (hv : h v ∈ S.J i) : h v = S.value i := by
  obtain ⟨j, hj⟩ := hS v
  rw [← hj] at hv ⊢
  rw [S.value_mem_J_iff.1 hv]

/-- Under covering, the vertices with height in the star of level `i` are those of height `a i`. -/
theorem CoversVertexHeights.preimage_J (hS : CoversVertexHeights S h) (i : Fin (n + 1)) :
    h ⁻¹' (S.J i : Set ℝ) = {v | h v = S.value i} := by
  ext v
  refine ⟨fun hv => hS.eq_of_mem_J hv, fun hv => ?_⟩
  show h v ∈ S.J i
  rw [show h v = S.value i from hv]
  exact S.value_mem_J i

/-- Under covering, no vertex height lies in a gap. -/
theorem CoversVertexHeights.notMem_K (hS : CoversVertexHeights S h) (e : Fin n) (v : V) :
    h v ∉ S.K e := by
  obtain ⟨j, hj⟩ := hS v
  rw [← hj]
  exact S.value_notMem_K e j

end covers

/-! ## The canonical list -/

section levels

variable {V : Type u}

/-- The finite set of vertex heights. -/
def vertexHeightSet [Fintype V] (h : V → ℝ) : Finset ℝ := Finset.univ.image h

/-- The number of gaps between consecutive distinct vertex heights. -/
def vertexGapCount [Fintype V] (h : V → ℝ) : ℕ := (vertexHeightSet h).card - 1

/-- A nonempty vertex type has `vertexGapCount h + 1` distinct vertex heights. -/
theorem card_vertexHeightSet [Fintype V] [Nonempty V] (h : V → ℝ) :
    (vertexHeightSet h).card = vertexGapCount h + 1 :=
  (Nat.sub_add_cancel (Finset.card_pos.2 (Finset.univ_nonempty.image h))).symm

/-- The sorted distinct vertex heights. -/
def vertexHeightLevels [Fintype V] [Nonempty V] (h : V → ℝ) :
    CriticalValues (vertexGapCount h) where
  value := (vertexHeightSet h).orderEmbOfFin (card_vertexHeightSet h)
  strictMono := OrderEmbedding.strictMono _

/-- The levels of the canonical list are exactly the vertex heights. -/
theorem range_vertexHeightLevels [Fintype V] [Nonempty V] (h : V → ℝ) :
    Set.range (vertexHeightLevels h).value = Set.range h := by
  show Set.range ((vertexHeightSet h).orderEmbOfFin (card_vertexHeightSet h)) = _
  rw [Finset.range_orderEmbOfFin, vertexHeightSet, Finset.coe_image, Finset.coe_univ,
    Set.image_univ]

/-- The canonical list covers the vertex heights. -/
theorem coversVertexHeights_vertexHeightLevels [Fintype V] [Nonempty V] (h : V → ℝ) :
    CoversVertexHeights (vertexHeightLevels h) h := fun v => by
  have hv : h v ∈ Set.range (vertexHeightLevels h).value := by
    rw [range_vertexHeightLevels]
    exact ⟨v, rfl⟩
  exact hv

end levels

/-! ## Reeb vertices, Reeb edges and endpoints -/

section reeb

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- Reeb vertices at height `c`: components of the level graph and edges crossing `c`. -/
abbrev LevelVertex (c : ℝ) : Type u :=
  (G.induce {v | h v = c}).ConnectedComponent ⊕ {e : G.edgeSet // EdgeCrosses G h c e}

/-- Reeb edges over `[p, q]`. -/
abbrev SpanEdge (p q : ℝ) : Type u := {e : G.edgeSet // EdgeSpans G h p q e}

/-- Two endpoints of one edge in a vertex set lie in one component of the induced graph. -/
private theorem induce_mk_eq_of_mem_edge {A : Set V} {e : G.edgeSet} {u w : A}
    (hu : (u : V) ∈ (e : Sym2 V)) (hw : (w : V) ∈ (e : Sym2 V)) :
    (G.induce A).connectedComponentMk u = (G.induce A).connectedComponentMk w := by
  by_cases huw : (u : V) = w
  · rw [Subtype.ext huw]
  · have he : (e : Sym2 V) = s(u.1, w.1) := (Sym2.mem_and_mem_iff huw).1 ⟨hu, hw⟩
    have hadj : G.Adj u w := by
      have := e.2
      rw [he] at this
      exact this
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hadj

/-- The endpoint of an edge at the level `c`: the level component of an endpoint of height `c`
when one exists, and the edge itself as a crossing edge otherwise. The endpoint is chosen
classically; only its level component enters the laws (`levelEnd_of_mem`). -/
def levelEnd (c : ℝ) (e : G.edgeSet)
    (hx : (∀ v ∈ (e : Sym2 V), h v ≠ c) → EdgeCrosses G h c e) : LevelVertex G h c :=
  haveI := Classical.propDecidable (∃ v ∈ (e : Sym2 V), h v = c)
  if hv : ∃ v ∈ (e : Sym2 V), h v = c then
    Sum.inl ((G.induce {v | h v = c}).connectedComponentMk
      ⟨Classical.choose hv, (Classical.choose_spec hv).2⟩)
  else Sum.inr ⟨e, hx fun v hv' hvc => hv ⟨v, hv', hvc⟩⟩

/-- An edge with an endpoint of height `c` goes to the level component of that endpoint, for
every such endpoint. -/
theorem levelEnd_of_mem {c : ℝ} {e : G.edgeSet}
    (hx : (∀ v ∈ (e : Sym2 V), h v ≠ c) → EdgeCrosses G h c e) {v : V}
    (hv : v ∈ (e : Sym2 V)) (hvc : h v = c) :
    levelEnd G h c e hx = Sum.inl ((G.induce {v | h v = c}).connectedComponentMk ⟨v, hvc⟩) := by
  have hv' : ∃ v ∈ (e : Sym2 V), h v = c := ⟨v, hv, hvc⟩
  unfold levelEnd
  rw [dif_pos hv']
  exact congrArg Sum.inl (induce_mk_eq_of_mem_edge G (Classical.choose_spec hv').1 hv)

/-- An edge without an endpoint of height `c` goes to itself as a crossing edge. -/
theorem levelEnd_of_forall_ne {c : ℝ} {e : G.edgeSet}
    (hx : (∀ v ∈ (e : Sym2 V), h v ≠ c) → EdgeCrosses G h c e)
    (hne : ∀ v ∈ (e : Sym2 V), h v ≠ c) : levelEnd G h c e hx = Sum.inr ⟨e, hx hne⟩ := by
  unfold levelEnd
  rw [dif_neg fun ⟨w, hw, hwc⟩ => hne w hw hwc]

variable {G h}

/-- A spanning edge without an endpoint at the lower bound crosses it. -/
theorem EdgeSpans.crosses_left {p q : ℝ} (hpq : p < q) {e : G.edgeSet}
    (he : EdgeSpans G h p q e) (hne : ∀ v ∈ (e : Sym2 V), h v ≠ p) : EdgeCrosses G h p e := by
  obtain ⟨d, rfl, hmin, hmax⟩ := he
  refine ⟨d, rfl, lt_of_le_of_ne hmin ?_, hpq.trans_le hmax⟩
  rcases min_choice (h d.fst) (h d.snd) with hm | hm <;> rw [hm]
  · exact hne _ (fst_mem_dartEdge d)
  · exact hne _ (snd_mem_dartEdge d)

/-- A spanning edge without an endpoint at the upper bound crosses it. -/
theorem EdgeSpans.crosses_right {p q : ℝ} (hpq : p < q) {e : G.edgeSet}
    (he : EdgeSpans G h p q e) (hne : ∀ v ∈ (e : Sym2 V), h v ≠ q) : EdgeCrosses G h q e := by
  obtain ⟨d, rfl, hmin, hmax⟩ := he
  refine ⟨d, rfl, hmin.trans_lt hpq, lt_of_le_of_ne hmax ?_⟩
  rcases max_choice (h d.fst) (h d.snd) with hm | hm <;> rw [hm]
  · exact (hne _ (fst_mem_dartEdge d)).symm
  · exact (hne _ (snd_mem_dartEdge d)).symm

end reeb

/-! ## The data -/

section data

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) {n : ℕ} (S : CriticalValues n)

/-- **Finite Reeb data of graph-PL input** over an arbitrary critical list: level components and
crossing edges at the levels, spanning edges over the gaps, and `levelEnd` as endpoint maps. No
covering hypothesis enters. -/
def graphPLReebData [Finite V] : FiniteReebData.{u} n where
  V i := LevelVertex G h (S.value i)
  E e := SpanEdge G h (S.value e.castSucc) (S.value e.succ)
  finiteV _ := by
    classical
    have := Fintype.ofFinite V
    infer_instance
  finiteE _ := by
    classical
    have := Fintype.ofFinite V
    infer_instance
  left e y := levelEnd G h (S.value e.castSucc) y.1
    (y.2.crosses_left (S.value_castSucc_lt_succ e))
  right e y := levelEnd G h (S.value e.succ) y.1 (y.2.crosses_right (S.value_castSucc_lt_succ e))

@[simp] theorem graphPLReebData_V [Finite V] (i : Fin (n + 1)) :
    (graphPLReebData G h S).V i = LevelVertex G h (S.value i) := rfl

@[simp] theorem graphPLReebData_E [Finite V] (e : Fin n) :
    (graphPLReebData G h S).E e = SpanEdge G h (S.value e.castSucc) (S.value e.succ) := rfl

/-- The left endpoint of a spanning edge with an endpoint at the lower level. -/
theorem graphPLReebData_left_of_mem [Finite V] (e : Fin n)
    (y : SpanEdge G h (S.value e.castSucc) (S.value e.succ)) {v : V} (hv : v ∈ (y.1 : Sym2 V))
    (hvc : h v = S.value e.castSucc) :
    ((graphPLReebData G h S).left e y : LevelVertex G h (S.value e.castSucc)) =
      Sum.inl ((G.induce {v | h v = S.value e.castSucc}).connectedComponentMk ⟨v, hvc⟩) :=
  levelEnd_of_mem G h (y.2.crosses_left (S.value_castSucc_lt_succ e)) hv hvc

/-- The left endpoint of a spanning edge without an endpoint at the lower level. -/
theorem graphPLReebData_left_of_forall_ne [Finite V] (e : Fin n)
    (y : SpanEdge G h (S.value e.castSucc) (S.value e.succ))
    (hne : ∀ v ∈ (y.1 : Sym2 V), h v ≠ S.value e.castSucc) :
    ((graphPLReebData G h S).left e y : LevelVertex G h (S.value e.castSucc)) =
      Sum.inr ⟨y.1, y.2.crosses_left (S.value_castSucc_lt_succ e) hne⟩ :=
  levelEnd_of_forall_ne G h (y.2.crosses_left (S.value_castSucc_lt_succ e)) hne

/-- The right endpoint of a spanning edge with an endpoint at the upper level. -/
theorem graphPLReebData_right_of_mem [Finite V] (e : Fin n)
    (y : SpanEdge G h (S.value e.castSucc) (S.value e.succ)) {v : V} (hv : v ∈ (y.1 : Sym2 V))
    (hvc : h v = S.value e.succ) :
    ((graphPLReebData G h S).right e y : LevelVertex G h (S.value e.succ)) =
      Sum.inl ((G.induce {v | h v = S.value e.succ}).connectedComponentMk ⟨v, hvc⟩) :=
  levelEnd_of_mem G h (y.2.crosses_right (S.value_castSucc_lt_succ e)) hv hvc

/-- The right endpoint of a spanning edge without an endpoint at the upper level. -/
theorem graphPLReebData_right_of_forall_ne [Finite V] (e : Fin n)
    (y : SpanEdge G h (S.value e.castSucc) (S.value e.succ))
    (hne : ∀ v ∈ (y.1 : Sym2 V), h v ≠ S.value e.succ) :
    ((graphPLReebData G h S).right e y : LevelVertex G h (S.value e.succ)) =
      Sum.inr ⟨y.1, y.2.crosses_right (S.value_castSucc_lt_succ e) hne⟩ :=
  levelEnd_of_forall_ne G h (y.2.crosses_right (S.value_castSucc_lt_succ e)) hne

end data

/-! ## Uncovered edges at a level, and induced components of equal sets -/

section level

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- Strict bounds `min a b < c < max a b` exclude `c` at both values. -/
private theorem ne_of_min_lt_of_lt_max {a b c : ℝ} (h₁ : min a b < c) (h₂ : c < max a b) :
    a ≠ c ∧ b ≠ c := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab] at h₁
    rw [max_eq_right hab] at h₂
    exact ⟨h₁.ne, h₂.ne'⟩
  · rw [min_eq_right hab] at h₁
    rw [max_eq_left hab] at h₂
    exact ⟨h₂.ne', h₁.ne⟩

/-- A dart with endpoint heights strictly around `c ∈ I` is active over `I`, through the
parameter of height `c`. -/
private theorem edgeActive_of_fst_lt_of_lt_snd {I : OpenInterval} {c : ℝ} (hc : c ∈ I)
    {d : G.Dart} (h₁ : h d.fst < c) (h₂ : c < h d.snd) : EdgeActive G h I (dartEdge d) := by
  have hden : 0 < h d.snd - h d.fst := by linarith
  set s : ℝ := (c - h d.fst) / (h d.snd - h d.fst) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := (div_le_one hden).2 (by linarith)
  have hmul : s * (h d.snd - h d.fst) = c - h d.fst := div_mul_cancel₀ _ hden.ne'
  refine edgeActive_dartEdge_of_mem (t := ⟨s, hs0, hs1⟩) ?_
  have hval : dartHeight h d ⟨s, hs0, hs1⟩ = c := by
    show (1 - s) * h d.fst + s * h d.snd = c
    linear_combination hmul
  rw [hval]
  exact hc

/-- **Uncovered edges at a level.** If `c ∈ I` and every vertex height in `I` is `c`, the
uncovered edges over `I` are the edges crossing `c`. The interval is arbitrary, including rays
and `⊤`; the equivalence is the identity on the underlying edge. -/
def uncoveredEdgeEquivCrossesOfLevel {I : OpenInterval} {c : ℝ} (hc : c ∈ I)
    (hlev : ∀ v, h v ∈ I → h v = c) : UncoveredEdge G h I ≃ {e // EdgeCrosses G h c e} :=
  Equiv.subtypeEquivRight fun e => by
    obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
    rw [edgeCrosses_dartEdge_iff]
    constructor
    · rintro ⟨hact, hunc⟩
      obtain ⟨t, ht0, ht1, hx⟩ := (edgeActive_dartEdge_iff d).1 hact
      have hx' : (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ∈ I := hx
      have hmin : min (h d.fst) (h d.snd) ≤ (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd := by
        nlinarith [mul_nonneg (sub_nonneg.2 ht1.le)
            (sub_nonneg.2 (min_le_left (h d.fst) (h d.snd))),
          mul_nonneg ht0.le (sub_nonneg.2 (min_le_right (h d.fst) (h d.snd)))]
      have hmax : (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ≤ max (h d.fst) (h d.snd) := by
        nlinarith [mul_nonneg (sub_nonneg.2 ht1.le)
            (sub_nonneg.2 (le_max_left (h d.fst) (h d.snd))),
          mul_nonneg ht0.le (sub_nonneg.2 (le_max_right (h d.fst) (h d.snd)))]
      constructor
      · by_contra hle
        have hm := OpenInterval.mem_of_le_of_le hc hx' (not_lt.1 hle) hmin
        rcases min_choice (h d.fst) (h d.snd) with hm' | hm' <;> rw [hm'] at hm
        · exact hunc _ (fst_mem_dartEdge d) hm
        · exact hunc _ (snd_mem_dartEdge d) hm
      · by_contra hle
        have hm := OpenInterval.mem_of_le_of_le hx' hc hmax (not_lt.1 hle)
        rcases max_choice (h d.fst) (h d.snd) with hm' | hm' <;> rw [hm'] at hm
        · exact hunc _ (fst_mem_dartEdge d) hm
        · exact hunc _ (snd_mem_dartEdge d) hm
    · rintro ⟨hmin, hmax⟩
      obtain ⟨hne₁, hne₂⟩ := ne_of_min_lt_of_lt_max hmin hmax
      refine ⟨?_, fun v hv hvI => ?_⟩
      · rcases le_total (h d.fst) (h d.snd) with hab | hab
        · rw [min_eq_left hab] at hmin
          rw [max_eq_right hab] at hmax
          exact edgeActive_of_fst_lt_of_lt_snd G h hc hmin hmax
        · rw [min_eq_right hab] at hmin
          rw [max_eq_left hab] at hmax
          have := edgeActive_of_fst_lt_of_lt_snd G h hc (d := d.symm) hmin hmax
          rwa [dartEdge_symm] at this
      · rcases mem_dartEdge.1 hv with rfl | rfl
        · exact hne₁ (hlev _ hvI)
        · exact hne₂ (hlev _ hvI)

@[simp] theorem uncoveredEdgeEquivCrossesOfLevel_apply_coe {I : OpenInterval} {c : ℝ}
    (hc : c ∈ I) (hlev : ∀ v, h v ∈ I → h v = c) (e : UncoveredEdge G h I) :
    ((uncoveredEdgeEquivCrossesOfLevel G h hc hlev e : {e // EdgeCrosses G h c e}) :
      G.edgeSet) = e.1 := rfl

/-- Components of the graphs induced on equal vertex sets, computing on representatives. -/
def induceComponentsEquivOfEq {A B : Set V} (hAB : A = B) :
    (G.induce A).ConnectedComponent ≃ (G.induce B).ConnectedComponent where
  toFun := ConnectedComponent.map (G.induceHomOfLE hAB.le).toHom
  invFun := ConnectedComponent.map (G.induceHomOfLE hAB.ge).toHom
  left_inv c := by
    induction c using ConnectedComponent.ind with
    | h v => rfl
  right_inv c := by
    induction c using ConnectedComponent.ind with
    | h v => rfl

@[simp] theorem induceComponentsEquivOfEq_mk {A B : Set V} (hAB : A = B) (v : A) :
    induceComponentsEquivOfEq G hAB ((G.induce A).connectedComponentMk v) =
      (G.induce B).connectedComponentMk ⟨v.1, hAB ▸ v.2⟩ := rfl

end level

/-! ## Star and gap comparison -/

section comparison

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) {n : ℕ} (S : CriticalValues n)

/-- **(i) Stars.** Under covering, the path components over the star of level `i` are the Reeb
vertices at `a i`. No finiteness is assumed. -/
def graphPLStarEquiv (hS : CoversVertexHeights S h) (i : Fin (n + 1)) :
    (intervalComponents (plHeight G h)).obj (S.J i) ≃ LevelVertex G h (S.value i) :=
  (preimageComponentsEquiv G h (S.J i)).trans ((cellComponentsEquivSum G h (S.J i)).trans
    (Equiv.sumCongr (induceComponentsEquivOfEq G (hS.preimage_J i))
      (uncoveredEdgeEquivCrossesOfLevel G h (S.value_mem_J i) fun _ hv => hS.eq_of_mem_J hv)))

/-- **(ii) Gaps.** Under covering, the path components over the gap `e` are the Reeb edges over
it. No finiteness is assumed. -/
def graphPLGapEquiv (hS : CoversVertexHeights S h) (e : Fin n) :
    (intervalComponents (plHeight G h)).obj (S.K e) ≃
      SpanEdge G h (S.value e.castSucc) (S.value e.succ) :=
  (preimageComponentsEquiv G h (S.K e)).trans
    ((cellGraphComponentsEquivActiveEdges (G := G) (hS.notMem_K e)).trans
      (activeEdgeEquivSpans (G := G) (S.value_castSucc_lt_succ e) fun v => hS.notMem_K e v))

/-- The star bijection as the composite of its three steps. -/
private theorem graphPLStarEquiv_apply (hS : CoversVertexHeights S h) (i : Fin (n + 1))
    (x : (intervalComponents (plHeight G h)).obj (S.J i)) :
    graphPLStarEquiv G h S hS i x =
      Equiv.sumCongr (induceComponentsEquivOfEq G (hS.preimage_J i))
        (uncoveredEdgeEquivCrossesOfLevel G h (S.value_mem_J i) fun _ hv => hS.eq_of_mem_J hv)
        (cellComponentsEquivSum G h (S.J i) (preimageComponentsEquiv G h (S.J i) x)) := rfl

/-- The gap bijection as the composite of its three steps. -/
private theorem graphPLGapEquiv_apply (hS : CoversVertexHeights S h) (e : Fin n)
    (x : (intervalComponents (plHeight G h)).obj (S.K e)) :
    graphPLGapEquiv G h S hS e x =
      activeEdgeEquivSpans (G := G) (S.value_castSucc_lt_succ e) (fun v => hS.notMem_K e v)
        (cellGraphComponentsEquivActiveEdges (G := G) (hS.notMem_K e)
          (preimageComponentsEquiv G h (S.K e) x)) := rfl

/-- A vertex at the level goes to its level component. -/
theorem graphPLStarEquiv_mk_vertex (hS : CoversVertexHeights S h) {i : Fin (n + 1)} (v : V)
    (hv : h v = S.value i) :
    graphPLStarEquiv G h S hS i
        (ZerothHomotopy.mk (⟨vertex G v, by rw [plHeight_vertex, hv]; exact S.value_mem_J i⟩ :
          {p : Realization G // plHeight G h p ∈ S.J i})) =
      Sum.inl ((G.induce {v | h v = S.value i}).connectedComponentMk ⟨v, hv⟩) := by
  refine (graphPLStarEquiv_apply G h S hS i _).trans ?_
  exact congrArg (fun c => Equiv.sumCongr (induceComponentsEquivOfEq G (hS.preimage_J i))
    (uncoveredEdgeEquivCrossesOfLevel G h (S.value_mem_J i) fun _ hv => hS.eq_of_mem_J hv)
    (cellComponentsEquivSum G h (S.J i) c))
    (preimageComponentsEquiv_mk_vertex G h (S.J i) v (by rw [hv]; exact S.value_mem_J i))

/-- An edge node over the star goes to the endpoint of its edge at the level, for every admissible
crossing witness. -/
theorem graphPLStarEquiv_cell_inr (hS : CoversVertexHeights S h) {i : Fin (n + 1)}
    (e : {e : G.edgeSet // EdgeActive G h (S.J i) e})
    (hx : (∀ v ∈ (e.1 : Sym2 V), h v ≠ S.value i) → EdgeCrosses G h (S.value i) e.1) :
    graphPLStarEquiv G h S hS i ((preimageComponentsEquiv G h (S.J i)).symm
        ((cellGraph G h (S.J i)).connectedComponentMk (Sum.inr e))) =
      levelEnd G h (S.value i) e.1 hx := by
  refine (graphPLStarEquiv_apply G h S hS i _).trans ?_
  rw [Equiv.apply_symm_apply]
  by_cases hw : ∃ w ∈ (e.1 : Sym2 V), h w = S.value i
  · obtain ⟨w, hw, hwc⟩ := hw
    have hwJ : h w ∈ S.J i := by
      rw [hwc]
      exact S.value_mem_J i
    rw [cellComponentsEquivSum_inr_of_mem G h (S.J i) e (w := ⟨w, hwJ⟩) hw,
      levelEnd_of_mem G h hx hw hwc]
    rfl
  · replace hw : ∀ w ∈ (e.1 : Sym2 V), h w ≠ S.value i := fun w hw' hwc => hw ⟨w, hw', hwc⟩
    have hunc : ∀ v ∈ (e.1 : Sym2 V), h v ∉ S.J i := fun v hv hvJ =>
      hw v hv (hS.eq_of_mem_J hvJ)
    rw [cellComponentsEquivSum_inr_uncovered G h (S.J i) ⟨e.1, e.2, hunc⟩,
      levelEnd_of_forall_ne G h hx hw]
    rfl

/-- An edge point over the star goes to the endpoint of its edge at the level. -/
theorem graphPLStarEquiv_mk_edgePoint (hS : CoversVertexHeights S h) {i : Fin (n + 1)}
    (d : G.Dart) (t : unitInterval) (ht : dartHeight h d t ∈ S.J i)
    (hx : (∀ v ∈ (dartEdge d : Sym2 V), h v ≠ S.value i) →
      EdgeCrosses G h (S.value i) (dartEdge d)) :
    graphPLStarEquiv G h S hS i
        (ZerothHomotopy.mk (⟨edgePoint G d t, ht⟩ :
          {p : Realization G // plHeight G h p ∈ S.J i})) =
      levelEnd G h (S.value i) (dartEdge d) hx := by
  have key := graphPLStarEquiv_cell_inr G h S hS ⟨dartEdge d, edgeActive_dartEdge_of_mem ht⟩ hx
  rw [← preimageComponentsEquiv_mk_edgePoint G h (S.J i) d t ht, Equiv.symm_apply_apply] at key
  exact key

/-- An edge point over the gap goes to its edge. -/
theorem graphPLGapEquiv_mk_edgePoint (hS : CoversVertexHeights S h) {e : Fin n} (d : G.Dart)
    (t : unitInterval) (ht : dartHeight h d t ∈ S.K e)
    (hsp : EdgeSpans G h (S.value e.castSucc) (S.value e.succ) (dartEdge d)) :
    graphPLGapEquiv G h S hS e
        (ZerothHomotopy.mk (⟨edgePoint G d t, ht⟩ :
          {p : Realization G // plHeight G h p ∈ S.K e})) = ⟨dartEdge d, hsp⟩ := by
  refine (graphPLGapEquiv_apply G h S hS e _).trans ?_
  exact congrArg (fun c => activeEdgeEquivSpans (G := G) (S.value_castSucc_lt_succ e)
    (fun v => hS.notMem_K e v) (cellGraphComponentsEquivActiveEdges (G := G) (hS.notMem_K e) c))
    (preimageComponentsEquiv_mk_edgePoint G h (S.K e) d t ht)

/-- The inverse over the gap is the class of the edge node. -/
theorem graphPLGapEquiv_symm_apply (hS : CoversVertexHeights S h) {e : Fin n}
    (y : SpanEdge G h (S.value e.castSucc) (S.value e.succ))
    (hy : EdgeActive G h (S.K e) y.1) :
    (graphPLGapEquiv G h S hS e).symm y =
      (preimageComponentsEquiv G h (S.K e)).symm
        ((cellGraph G h (S.K e)).connectedComponentMk (Sum.inr ⟨y.1, hy⟩)) := rfl

/-- The inclusion of a gap into an incident star on an edge node over the gap. -/
private theorem map_symm_cell_inr {I J : OpenInterval} (hIJ : I ≤ J)
    (y : {e : G.edgeSet // EdgeActive G h I e}) :
    (intervalComponents (plHeight G h)).map (homOfLE hIJ)
        ((preimageComponentsEquiv G h I).symm
          ((cellGraph G h I).connectedComponentMk (Sum.inr y))) =
      (preimageComponentsEquiv G h J).symm
        ((cellGraph G h J).connectedComponentMk (Sum.inr ⟨y.1, y.2.mono hIJ⟩)) := by
  apply (preimageComponentsEquiv G h J).injective
  rw [Equiv.apply_symm_apply]
  have := preimageComponentsEquiv_componentMap G h hIJ
    ((preimageComponentsEquiv G h I).symm ((cellGraph G h I).connectedComponentMk (Sum.inr y)))
  rw [Equiv.apply_symm_apply] at this
  exact this

/-- **(iii) Left incidence.** Under the star and gap bijections, the inclusion of the gap `e`
into the star of `e` is the left endpoint map, on every element of the gap value. -/
theorem graphPLStarEquiv_map_left [Finite V] (hS : CoversVertexHeights S h) (e : Fin n)
    (x : (intervalComponents (plHeight G h)).obj (S.K e)) :
    graphPLStarEquiv G h S hS e.castSucc
        ((intervalComponents (plHeight G h)).map (homOfLE (S.K_le_J_castSucc e)) x) =
      (graphPLReebData G h S).left e (graphPLGapEquiv G h S hS e x) := by
  obtain ⟨y, rfl⟩ := (graphPLGapEquiv G h S hS e).symm.surjective x
  have hy : EdgeActive G h (S.K e) y.1 :=
    ((activeEdgeEquivSpans (G := G) (S.value_castSucc_lt_succ e) fun v => hS.notMem_K e v).symm
      y).2
  rw [Equiv.apply_symm_apply, graphPLGapEquiv_symm_apply G h S hS y hy, map_symm_cell_inr,
    graphPLStarEquiv_cell_inr G h S hS _ (y.2.crosses_left (S.value_castSucc_lt_succ e))]
  rfl

/-- **(iii) Right incidence.** Under the star and gap bijections, the inclusion of the gap `e`
into the star of `e + 1` is the right endpoint map, on every element of the gap value. -/
theorem graphPLStarEquiv_map_right [Finite V] (hS : CoversVertexHeights S h) (e : Fin n)
    (x : (intervalComponents (plHeight G h)).obj (S.K e)) :
    graphPLStarEquiv G h S hS e.succ
        ((intervalComponents (plHeight G h)).map (homOfLE (S.K_le_J_succ e)) x) =
      (graphPLReebData G h S).right e (graphPLGapEquiv G h S hS e x) := by
  obtain ⟨y, rfl⟩ := (graphPLGapEquiv G h S hS e).symm.surjective x
  have hy : EdgeActive G h (S.K e) y.1 :=
    ((activeEdgeEquivSpans (G := G) (S.value_castSucc_lt_succ e) fun v => hS.notMem_K e v).symm
      y).2
  rw [Equiv.apply_symm_apply, graphPLGapEquiv_symm_apply G h S hS y hy, map_symm_cell_inr,
    graphPLStarEquiv_cell_inr G h S hS _ (y.2.crosses_right (S.value_castSucc_lt_succ e))]
  rfl

/-- The extracted data of the graph-PL path-component precosheaf map to the combinatorial data,
by the star and gap bijections. -/
def graphPLExtractHom [Finite V] (hS : CoversVertexHeights S h) :
    (S.extract (intervalComponents (plHeight G h)) (fun I => finite_zerothHomotopy G h I)).Hom
      (graphPLReebData G h S) where
  v i := graphPLStarEquiv G h S hS i
  e k := graphPLGapEquiv G h S hS k
  left_comm k x := (graphPLStarEquiv_map_left G h S hS k x).symm
  right_comm k x := (graphPLStarEquiv_map_right G h S hS k x).symm

@[simp] theorem graphPLExtractHom_v [Finite V] (hS : CoversVertexHeights S h)
    (i : Fin (n + 1)) : (graphPLExtractHom G h S hS).v i = graphPLStarEquiv G h S hS i := rfl

@[simp] theorem graphPLExtractHom_e [Finite V] (hS : CoversVertexHeights S h) (k : Fin n) :
    (graphPLExtractHom G h S hS).e k = graphPLGapEquiv G h S hS k := rfl

/-- **The isomorphism of finite data** between the extracted star and gap components and the
combinatorial Reeb data of graph-PL input. -/
def graphPLExtractIso [Finite V] (hS : CoversVertexHeights S h) :
    S.extract (intervalComponents (plHeight G h)) (fun I => finite_zerothHomotopy G h I) ≅
      graphPLReebData G h S where
  hom := graphPLExtractHom G h S hS
  inv := (graphPLExtractHom G h S hS).inv (fun i => (graphPLStarEquiv G h S hS i).bijective)
    (fun k => (graphPLGapEquiv G h S hS k).bijective)
  hom_inv_id := (graphPLExtractHom G h S hS).comp_inv _ _
  inv_hom_id := (graphPLExtractHom G h S hS).inv_comp _ _

end comparison

end

end TDA.Mapper.GraphPL
