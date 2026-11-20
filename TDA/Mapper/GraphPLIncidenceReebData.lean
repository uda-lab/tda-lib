import TDA.Mapper.GraphPLIncidence
import TDA.Mapper.GraphPLReebQuotient

/-!
# The executed graph-PL incidence lists as finite Reeb data

For a valid `X : HeightGraph N`, the lists computed in `TDA.Mapper.GraphPLIncidence` are read as
finite Reeb data `X.reebData hX` over the computed covering list `X.criticalValues`, without
renumbering:

* the vertices at level `i` are the listed cells `{x // x ∈ X.cellList (X.level i)}`;
* the edges over gap `e` are the listed entries
  `{z // z ∈ X.edgeList (X.level e.castSucc) (X.level e.succ)}`, so two listed edges with the
  same endpoint cells are two edges;
* the endpoint maps read the endpoint cells stored in an entry (`reebData_left_coe`,
  `reebData_right_coe`), which are `leftEnd` and `rightEnd` of its edge
  (`reebData_left_eq_leftEnd`, `reebData_right_eq_rightEnd`).

By `incidence_cells_getElem?` and `incidence_edges_getElem?` these lists are the entries of the
computed value `X.incidence`.

## The comparison

`reebDataIso` is an isomorphism of finite data from `X.reebData hX` to
`graphPLReebData (X.graph hX) X.realHeight X.criticalValues`. Its forward map sends a component
cell to the connected component of its representative in the actual induced level graph
(`reebDataIso_hom_v_inl`), a crossing cell `(lo, hi)` to the edge `s(lo, hi)` as a crossing edge
(`reebDataIso_hom_v_inr`), and a listed edge to its edge as a spanning edge
(`reebDataIso_hom_e`). These three laws determine the forward map. Bijectivity uses
`label_eq_label_iff_reachable` and the strict order of the heights of the two ends; the
compatibility with the endpoint maps uses the endpoint laws of `graphPLReebData`.

Consequently the data extracted from the path-component precosheaf of the graph-PL height are
the executed lists (`extractReebDataIso`, through `graphPLExtractIso`), and the Reeb quotient of
the graph-PL height is, over `ℝ`, the realization of the executed lists (`reebQuotientIso`,
through `graphPLReebQuotientIsoOfIso`). With no vertex that realization is empty
(`isEmpty_realization`).

The comparison maps are noncomputable; nothing here is on the executable path. These are
elementary library results, not attributed to a source. See `docs/math/mapper.md`.
-/

set_option autoImplicit false

namespace TDA.Mapper.GraphPL

open SimpleGraph CategoryTheory TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.RGraph

namespace HeightGraph

variable {N : ℕ} (X : HeightGraph N)

/-- The executed incidence lists as finite Reeb data: the listed cells of each level, the listed
edges of each gap, and the listed endpoint cells. -/
def reebData (hX : X.Valid) : FiniteReebData.{0} X.gapCount where
  V i := {x : Cell N // x ∈ X.cellList (X.level i)}
  E e := {z : (Fin N × Fin N) × Cell N × Cell N //
    z ∈ X.edgeList (X.level e.castSucc) (X.level e.succ)}
  finiteV _ := inferInstance
  finiteE _ := inferInstance
  left _ z := ⟨z.1.2.1, X.leftEnd_mem_cellList hX
    (X.level_strictMono Fin.castSucc_lt_succ) z.2⟩
  right _ z := ⟨z.1.2.2, X.rightEnd_mem_cellList hX
    (X.level_strictMono Fin.castSucc_lt_succ) z.2⟩

@[simp] theorem reebData_left_coe (hX : X.Valid) (e : Fin X.gapCount)
    (z : (X.reebData hX).E e) :
    ((X.reebData hX).left e z).1 = z.1.2.1 := rfl

@[simp] theorem reebData_right_coe (hX : X.Valid) (e : Fin X.gapCount)
    (z : (X.reebData hX).E e) :
    ((X.reebData hX).right e z).1 = z.1.2.2 := rfl

theorem reebData_left_eq_leftEnd (hX : X.Valid) (e : Fin X.gapCount)
    (z : (X.reebData hX).E e) :
    ((X.reebData hX).left e z).1 = X.leftEnd (X.level e.castSucc) z.1.1 :=
  (X.mem_edgeList.1 z.2).2.1

theorem reebData_right_eq_rightEnd (hX : X.Valid) (e : Fin X.gapCount)
    (z : (X.reebData hX).E e) :
    ((X.reebData hX).right e z).1 = X.rightEnd (X.level e.succ) z.1.1 :=
  (X.mem_edgeList.1 z.2).2.2

private theorem crosses_of_lt (hX : X.Valid) {c : ℚ} {y : Fin N × Fin N}
    (hadj : X.adj y.1 y.2 = true) (h₁ : X.height y.1 < c) (h₂ : c < X.height y.2) :
    EdgeCrosses (X.graph hX) X.realHeight (c : ℝ) ⟨s(y.1, y.2), hadj⟩ := by
  refine ⟨⟨(y.1, y.2), hadj⟩, rfl, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (Rat.cast_lt.2 h₁)
  · exact (Rat.cast_lt.2 h₂).trans_le (le_max_right _ _)

private theorem spans_of_le (hX : X.Valid) {p q : ℚ} {y : Fin N × Fin N}
    (hadj : X.adj y.1 y.2 = true) (h₁ : X.height y.1 ≤ p) (h₂ : q ≤ X.height y.2) :
    EdgeSpans (X.graph hX) X.realHeight (p : ℝ) (q : ℝ) ⟨s(y.1, y.2), hadj⟩ := by
  refine ⟨⟨(y.1, y.2), hadj⟩, rfl, ?_, ?_⟩
  · exact (min_le_left _ _).trans (Rat.cast_le.2 h₁)
  · exact (Rat.cast_le.2 h₂).trans (le_max_right _ _)

/-- The Reeb vertex of a listed cell. -/
private noncomputable def levelVertexOf (hX : X.Valid) (c : ℚ) :
    (x : Cell N) → x ∈ X.cellList c → LevelVertex (X.graph hX) X.realHeight (c : ℝ)
  | .inl r, hr => .inl (((X.graph hX).induce {v | X.realHeight v = (c : ℝ)}).connectedComponentMk
      ⟨r, X.realHeight_eq_iff.2 (X.mem_cellList_inl.1 hr).2⟩)
  | .inr y, hy => .inr ⟨⟨s(y.1, y.2), (X.mem_cellList_inr.1 hy).1⟩,
      X.crosses_of_lt hX (X.mem_cellList_inr.1 hy).1 (X.mem_cellList_inr.1 hy).2.1
        (X.mem_cellList_inr.1 hy).2.2⟩

private theorem levelVertexOf_bijective (hX : X.Valid) (c : ℚ) :
    Function.Bijective fun x : {x : Cell N // x ∈ X.cellList c} =>
      X.levelVertexOf hX c x.1 x.2 := by
  constructor
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    apply Subtype.ext
    show x = x'
    rcases x with r | y <;> rcases x' with r' | y'
    · have h' := Sum.inl_injective h
      have hr := X.mem_cellList_inl.1 hx
      have hr' := X.mem_cellList_inl.1 hx'
      have := (X.label_eq_label_iff_reachable hX hr.2 hr'.2).2 (ConnectedComponent.exact h')
      rw [hr.1, hr'.1] at this
      rw [this]
    · exact absurd h Sum.inl_ne_inr
    · exact absurd h Sum.inr_ne_inl
    · have h' : s(y.1, y.2) = s(y'.1, y'.2) :=
        congrArg (fun e => ((e.1 : (X.graph hX).edgeSet) : Sym2 (Fin N))) (Sum.inr_injective h)
      have hy := X.mem_cellList_inr.1 hx
      have hy' := X.mem_cellList_inr.1 hx'
      rcases Sym2.eq_iff.1 h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact congrArg Sum.inr (Prod.ext h₁ h₂)
      · rw [h₁] at hy
        exact absurd hy.2.1 (not_lt.2 hy'.2.2.le)
  · rintro (κ | ⟨e, he⟩)
    · induction κ using ConnectedComponent.ind with
      | h v =>
        have hv : X.height v.1 = c := X.realHeight_eq_iff.1 v.2
        refine ⟨⟨.inl (X.label v.1), X.mem_cellList_inl.2
          ⟨X.label_label hX _, (X.height_label _).trans hv⟩⟩, ?_⟩
        refine congrArg Sum.inl (ConnectedComponent.sound ?_)
        exact (X.label_eq_label_iff_reachable hX ((X.height_label _).trans hv) hv).1
          (X.label_label hX _)
    · obtain ⟨d, rfl, h₁, h₂⟩ := he
      rcases le_total (X.realHeight d.fst) (X.realHeight d.snd) with hle | hle
      · rw [min_eq_left hle] at h₁
        rw [max_eq_right hle] at h₂
        refine ⟨⟨.inr (d.fst, d.snd), X.mem_cellList_inr.2
          ⟨d.adj, Rat.cast_lt.1 h₁, Rat.cast_lt.1 h₂⟩⟩, ?_⟩
        rfl
      · rw [min_eq_right hle] at h₁
        rw [max_eq_left hle] at h₂
        refine ⟨⟨.inr (d.snd, d.fst), X.mem_cellList_inr.2
          ⟨d.adj.symm, Rat.cast_lt.1 h₁, Rat.cast_lt.1 h₂⟩⟩, ?_⟩
        refine congrArg Sum.inr (Subtype.ext (Subtype.ext ?_))
        exact Sym2.eq_swap

/-- The Reeb edge of a listed edge. -/
private def spanEdgeOf (hX : X.Valid) (p q : ℚ)
    (z : {z : (Fin N × Fin N) × Cell N × Cell N // z ∈ X.edgeList p q}) :
    SpanEdge (X.graph hX) X.realHeight (p : ℝ) (q : ℝ) :=
  ⟨⟨s(z.1.1.1, z.1.1.2), (X.mem_edgeList.1 z.2).1.1⟩,
    X.spans_of_le hX (X.mem_edgeList.1 z.2).1.1 (X.mem_edgeList.1 z.2).1.2.1
      (X.mem_edgeList.1 z.2).1.2.2⟩

private theorem spanEdgeOf_bijective (hX : X.Valid) {p q : ℚ} (hpq : p < q) :
    Function.Bijective (X.spanEdgeOf hX p q) := by
  constructor
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' : s(z.1.1, z.1.2) = s(z'.1.1, z'.1.2) :=
      congrArg (fun e => ((e.1 : (X.graph hX).edgeSet) : Sym2 (Fin N))) h
    obtain ⟨⟨-, hlo, hhi⟩, hl, hr⟩ := X.mem_edgeList.1 hz
    obtain ⟨⟨-, hlo', hhi'⟩, hl', hr'⟩ := X.mem_edgeList.1 hz'
    have hfst : z.1 = z'.1 := by
      rcases Sym2.eq_iff.1 h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Prod.ext h₁ h₂
      · rw [h₁] at hlo
        exact absurd (hhi'.trans hlo) (not_le.2 hpq)
    apply Subtype.ext
    show z = z'
    refine Prod.ext hfst (Prod.ext ?_ ?_)
    · rw [hl, hl', hfst]
    · rw [hr, hr', hfst]
  · rintro ⟨e, he⟩
    obtain ⟨d, rfl, h₁, h₂⟩ := he
    rcases le_total (X.realHeight d.fst) (X.realHeight d.snd) with hle | hle
    · rw [min_eq_left hle] at h₁
      rw [max_eq_right hle] at h₂
      refine ⟨⟨((d.fst, d.snd), X.leftEnd p (d.fst, d.snd), X.rightEnd q (d.fst, d.snd)),
        X.mem_edgeList.2 ⟨⟨d.adj, Rat.cast_le.1 h₁, Rat.cast_le.1 h₂⟩, rfl, rfl⟩⟩,
        ?_⟩
      rfl
    · rw [min_eq_right hle] at h₁
      rw [max_eq_left hle] at h₂
      have hmem := (X.mem_edgeList
        (z := ((d.snd, d.fst), X.leftEnd p (d.snd, d.fst), X.rightEnd q (d.snd, d.fst)))).2
        ⟨⟨d.adj.symm, Rat.cast_le.1 h₁, Rat.cast_le.1 h₂⟩, rfl, rfl⟩
      refine ⟨⟨_, hmem⟩, ?_⟩
      refine Subtype.ext (Subtype.ext ?_)
      exact Sym2.eq_swap

/-- The map of finite data from the executed lists to the graph-PL Reeb data. -/
private noncomputable def reebDataHom (hX : X.Valid) :
    (X.reebData hX).Hom (graphPLReebData (X.graph hX) X.realHeight X.criticalValues) where
  v i x := X.levelVertexOf hX (X.level i) x.1 x.2
  e k := X.spanEdgeOf hX (X.level k.castSucc) (X.level k.succ)
  left_comm k z := by
    obtain ⟨⟨y, a, b⟩, hz⟩ := z
    have hpq : X.level k.castSucc < X.level k.succ := X.level_strictMono Fin.castSucc_lt_succ
    obtain ⟨⟨hadj, hlo, hhi⟩, hl, -⟩ := X.mem_edgeList.1 hz
    have key : ∀ (a' : Cell N) (ha' : a' ∈ X.cellList (X.level k.castSucc)),
        a' = X.leftEnd (X.level k.castSucc) y →
        (graphPLReebData (X.graph hX) X.realHeight X.criticalValues).left k
            (X.spanEdgeOf hX (X.level k.castSucc) (X.level k.succ) ⟨(y, a, b), hz⟩) =
          X.levelVertexOf hX (X.level k.castSucc) a' ha' := by
      intro a' ha' ha
      by_cases h : X.height y.1 = X.level k.castSucc
      · have ha₂ : a' = .inl (X.label y.1) := by
          rw [ha]; unfold leftEnd leftEndWith; simp only [h, ↓reduceIte]
        subst ha₂
        refine (graphPLReebData_left_of_mem (X.graph hX) X.realHeight X.criticalValues k _
          (v := y.1) (Sym2.mem_mk_left _ _) (X.realHeight_eq_iff.2 h)).trans ?_
        refine congrArg Sum.inl (ConnectedComponent.sound ?_)
        exact (X.label_eq_label_iff_reachable hX h ((X.height_label _).trans h)).1
          (X.label_label hX _).symm
      · have ha₂ : a' = .inr y := by
          rw [ha]; unfold leftEnd leftEndWith; simp only [h, ↓reduceIte]
        subst ha₂
        refine (graphPLReebData_left_of_forall_ne (X.graph hX) X.realHeight X.criticalValues k _
          ?_).trans rfl
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact fun hv' => h (X.realHeight_eq_iff.1 hv')
        · exact fun hv' => absurd (X.realHeight_eq_iff.1 hv' ▸ hhi) (not_le.2 hpq)
    exact key a _ hl
  right_comm k z := by
    obtain ⟨⟨y, a, b⟩, hz⟩ := z
    have hpq : X.level k.castSucc < X.level k.succ := X.level_strictMono Fin.castSucc_lt_succ
    obtain ⟨⟨hadj, hlo, hhi⟩, -, hr⟩ := X.mem_edgeList.1 hz
    have key : ∀ (b' : Cell N) (hb' : b' ∈ X.cellList (X.level k.succ)),
        b' = X.rightEnd (X.level k.succ) y →
        (graphPLReebData (X.graph hX) X.realHeight X.criticalValues).right k
            (X.spanEdgeOf hX (X.level k.castSucc) (X.level k.succ) ⟨(y, a, b), hz⟩) =
          X.levelVertexOf hX (X.level k.succ) b' hb' := by
      intro b' hb' hb
      by_cases h : X.height y.2 = X.level k.succ
      · have hb₂ : b' = .inl (X.label y.2) := by
          rw [hb]; unfold rightEnd rightEndWith; simp only [h, ↓reduceIte]
        subst hb₂
        refine (graphPLReebData_right_of_mem (X.graph hX) X.realHeight X.criticalValues k _
          (v := y.2) (Sym2.mem_mk_right _ _) (X.realHeight_eq_iff.2 h)).trans ?_
        refine congrArg Sum.inl (ConnectedComponent.sound ?_)
        exact (X.label_eq_label_iff_reachable hX h ((X.height_label _).trans h)).1
          (X.label_label hX _).symm
      · have hb₂ : b' = .inr y := by
          rw [hb]; unfold rightEnd rightEndWith; simp only [h, ↓reduceIte]
        subst hb₂
        refine (graphPLReebData_right_of_forall_ne (X.graph hX) X.realHeight X.criticalValues k _
          ?_).trans rfl
        intro v hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact fun hv' => absurd (X.realHeight_eq_iff.1 hv' ▸ hlo) (not_le.2 hpq)
        · exact fun hv' => h (X.realHeight_eq_iff.1 hv')
    exact key b _ hr

/-- **The executed incidence lists are the graph-PL Reeb data** at the computed covering list,
up to isomorphism of finite data. -/
noncomputable def reebDataIso (hX : X.Valid) :
    X.reebData hX ≅ graphPLReebData (X.graph hX) X.realHeight X.criticalValues where
  hom := X.reebDataHom hX
  inv := (X.reebDataHom hX).inv (fun i => X.levelVertexOf_bijective hX (X.level i))
    (fun _ => X.spanEdgeOf_bijective hX (X.level_strictMono Fin.castSucc_lt_succ))
  hom_inv_id := (X.reebDataHom hX).comp_inv _ _
  inv_hom_id := (X.reebDataHom hX).inv_comp _ _

/-- A component cell goes to the level component of its representative. -/
theorem reebDataIso_hom_v_inl (hX : X.Valid) (i : Fin (X.gapCount + 1)) (r : Fin N)
    (hr : Sum.inl r ∈ X.cellList (X.level i)) :
    ((X.reebDataIso hX).hom.v i ⟨Sum.inl r, hr⟩ :
        LevelVertex (X.graph hX) X.realHeight (X.level i : ℝ)) =
      Sum.inl (((X.graph hX).induce {v | X.realHeight v = (X.level i : ℝ)}).connectedComponentMk
        ⟨r, X.realHeight_eq_iff.2 (X.mem_cellList_inl.1 hr).2⟩) := rfl

/-- A crossing cell goes to its edge, as a crossing edge. -/
theorem reebDataIso_hom_v_inr (hX : X.Valid) (i : Fin (X.gapCount + 1)) (y : Fin N × Fin N)
    (hy : Sum.inr y ∈ X.cellList (X.level i)) :
    ∃ he hc, ((X.reebDataIso hX).hom.v i ⟨Sum.inr y, hy⟩ :
        LevelVertex (X.graph hX) X.realHeight (X.level i : ℝ)) =
      Sum.inr ⟨⟨s(y.1, y.2), he⟩, hc⟩ := ⟨_, _, rfl⟩

/-- A listed edge goes to its edge, as a spanning edge. -/
theorem reebDataIso_hom_e (hX : X.Valid) (k : Fin X.gapCount) (z : (X.reebData hX).E k) :
    ((((X.reebDataIso hX).hom.e k z :
        SpanEdge (X.graph hX) X.realHeight (X.level k.castSucc : ℝ) (X.level k.succ : ℝ)).1 :
          (X.graph hX).edgeSet) : Sym2 (Fin N)) = s(z.1.1.1, z.1.1.2) := rfl

/-- The finite data extracted from the path-component precosheaf of the graph-PL height at the
computed covering list are the executed incidence lists, through `graphPLExtractIso`. -/
noncomputable def extractReebDataIso (hX : X.Valid) :
    X.criticalValues.extract (intervalComponents (plHeight (X.graph hX) X.realHeight))
        (fun I => finite_zerothHomotopy (X.graph hX) X.realHeight I) ≅ X.reebData hX :=
  graphPLExtractIso (X.graph hX) X.realHeight X.criticalValues X.coversVertexHeights ≪≫
    (X.reebDataIso hX).symm

/-- **The Reeb quotient of the graph-PL height is the realization of the executed incidence
lists**, over `ℝ`. -/
noncomputable def reebQuotientIso (hX : X.Valid) :
    (ReebQuotient.quotientFunctor ℝ).obj (graphPLOver (X.graph hX) X.realHeight) ≅
      RGraph.toOver X.criticalValues (X.reebData hX) :=
  graphPLReebQuotientIsoOfIso (X.graph hX) X.realHeight X.coversVertexHeights (X.reebDataIso hX)

/-- With no vertex the realization of the executed lists is empty. -/
theorem isEmpty_realization (X : HeightGraph 0) (hX : X.Valid) :
    IsEmpty
      ((CylinderPresentation.ofFiniteData (X.reebData hX)).Realization X.criticalValues) := by
  refine ⟨fun q => ?_⟩
  rcases (CylinderPresentation.ofFiniteData (X.reebData hX)).exists_rep X.criticalValues q with
    ⟨i, v, -⟩ | ⟨e, -, -⟩
  · have v' : {x : Cell 0 // x ∈ X.cellList (X.level i)} := v
    rcases v' with ⟨r | y, -⟩
    · exact r.elim0
    · exact y.1.elim0
  · exact absurd e.2 (by simp [gapCount, levels])

end HeightGraph

end TDA.Mapper.GraphPL
