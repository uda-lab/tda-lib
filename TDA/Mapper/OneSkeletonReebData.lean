import TDA.Reeb.FiniteDataGraph
import TDA.Mapper.UniformMapperReebData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

universe u

/-!
# The ordinary Mapper one-skeleton and uniform Mapper finite Reeb data

The incidence graph of the uniform MultiNerve Mapper finite Reeb data is the ORDINARY Mapper
one-skeleton when 2 * g ≤ r (a genuine isomorphism, not a definitional one).  Parallel
MultiNerve edge cells are forgotten by the ordinary one-skeleton.  Composed with
uniformMapperIso, this compares the one-skeleton with the graph-PL finite Reeb data.

These are library results in the context of CO16-v3, and are not attributed to that source.  No
claim about a realization or about connectivity versus a realization is made here.
-/

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization
open TDA.Topology TDA.Topology.MultiNerveCell
open scoped Classical

noncomputable section

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) {a r g : ℝ} {n : ℕ} [Finite V]

private abbrev uniformMapperCover (a r g : ℝ) (n : ℕ) : Fin (n + 1) → Set ℝ :=
  fun i => (uniformCover a r g (n + 1) i : Set ℝ)

private abbrev uniformMapperIndex (a r g : ℝ) (n : ℕ) : Type u :=
  ComponentIndex (plHeight G h) (uniformMapperCover a r g n)

/-! ## Vertex cells -/

/-- The support of a one-label uniform MultiNerve cell is the corresponding Mapper vertex. -/
theorem support_eq_singleton_of_vertexCell (k : Fin (n + 1))
    (c : (uniformMapperData G h a r g n).V k) :
    c.1.support =
      {⟨k, vertexCellsEquiv (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) k c⟩} := by
  obtain ⟨b, hb⟩ := c.1.support_nonempty
  rcases b with ⟨j, b⟩
  have hj : j = k := by
    have hmem : j ∈ c.1.support.image Sigma.fst :=
      Finset.mem_image.2 ⟨⟨j, b⟩, hb, rfl⟩
    rw [c.2] at hmem
    exact Finset.mem_singleton.1 hmem
  subst j
  have hsupport : c.1.support = {⟨k, b⟩} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨hb, ?_⟩
    intro d hd
    have hdk : d.1 = k := by
      have hmem : d.1 ∈ c.1.support.image Sigma.fst :=
        Finset.mem_image.2 ⟨d, hd, rfl⟩
      rw [c.2] at hmem
      exact Finset.mem_singleton.1 hmem
    exact eq_of_mem_mapper_face_of_fst_eq
      (plHeight G h) (uniformMapperCover a r g n)
      c.1.support_mem_nerve hd hb hdk
  have hclass : b = vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) k c := by
    obtain ⟨x, hx⟩ := c.1.carrier_nonempty
    have hxb : x ∈ componentCover (plHeight G h) (uniformMapperCover a r g n)
        ⟨k, b⟩ := by
      exact (mem_interMember_iff _).1 (c.1.carrier_subset hx) ⟨k, b⟩ hb
    rcases hxb with ⟨hxU, hxb⟩
    refine hxb.symm.trans ?_
    exact (congrArg (zerothHomotopySetCongr (by rw [Finset.set_biInter_singleton]; rfl))
      (cellsOverLabelsEquiv_apply_of_mem (plHeight G h)
        (uniformMapperCover a r g n) {k} (Finset.singleton_nonempty k) c hx)).symm
  rw [hsupport, hclass]

private theorem uniformMapperVertexCell_eq (k : Fin (n + 1))
    (c : (uniformMapperData G h a r g n).V k) :
    c.1 = vertexCell (plHeight G h) (uniformMapperCover a r g n)
      ⟨k, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) k c⟩ := by
  exact eq_vertexCell_of_support_eq _ _ (support_eq_singleton_of_vertexCell G h k c)

private theorem uniformMapperLeft_eq_of_mem (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e)
    (v : (uniformMapperData G h a r g n).V e.castSucc)
    (hv : (⟨e.castSucc, vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) e.castSucc v⟩ :
        ComponentIndex (plHeight G h) (uniformMapperCover a r g n)) ∈ c.1.support) :
    (uniformMapperData G h a r g n).left e c = v := by
  let A : ComponentIndex (plHeight G h) (uniformMapperCover a r g n) :=
    ⟨e.castSucc, vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) e.castSucc v⟩
  let A' : ComponentIndex (plHeight G h) (uniformMapperCover a r g n) :=
    ⟨e.castSucc, vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) e.castSucc
        ((uniformMapperData G h a r g n).left e c)⟩
  have hA' : A' ∈ c.1.support := by
    have hmem : A' ∈ ((uniformMapperData G h a r g n).left e c).1.support := by
      rw [support_eq_singleton_of_vertexCell G h e.castSucc
        ((uniformMapperData G h a r g n).left e c)]
      exact Finset.mem_singleton_self _
    exact (support_mono (show
      (labelFace (plHeight G h) (uniformMapperCover a r g n) c
        e.castSucc (Finset.mem_insert_self _ _)).1 ≤ c.1 from
      labelFace_le (plHeight G h) (uniformMapperCover a r g n) c
        e.castSucc (Finset.mem_insert_self _ _))) hmem
  have hAA' : A' = A := by
    apply eq_of_mem_mapper_face_of_fst_eq
      (plHeight G h) (uniformMapperCover a r g n)
      c.1.support_mem_nerve hA' hv
    rfl
  apply Subtype.ext
  calc
    ((uniformMapperData G h a r g n).left e c).1 = vertexCell
        (plHeight G h) (uniformMapperCover a r g n) A' := by
          exact uniformMapperVertexCell_eq G h e.castSucc
            ((uniformMapperData G h a r g n).left e c)
    _ = vertexCell (plHeight G h) (uniformMapperCover a r g n) A :=
      congrArg (vertexCell (plHeight G h) (uniformMapperCover a r g n)) hAA'
    _ = v.1 := (uniformMapperVertexCell_eq G h e.castSucc v).symm

private theorem uniformMapperRight_eq_of_mem (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e)
    (v : (uniformMapperData G h a r g n).V e.succ)
    (hv : (⟨e.succ, vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) e.succ v⟩ :
        ComponentIndex (plHeight G h) (uniformMapperCover a r g n)) ∈ c.1.support) :
    (uniformMapperData G h a r g n).right e c = v := by
  let A : ComponentIndex (plHeight G h) (uniformMapperCover a r g n) :=
    ⟨e.succ, vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) e.succ v⟩
  let A' : ComponentIndex (plHeight G h) (uniformMapperCover a r g n) :=
    ⟨e.succ, vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) e.succ
        ((uniformMapperData G h a r g n).right e c)⟩
  have hA' : A' ∈ c.1.support := by
    have hmem : A' ∈ ((uniformMapperData G h a r g n).right e c).1.support := by
      rw [support_eq_singleton_of_vertexCell G h e.succ
        ((uniformMapperData G h a r g n).right e c)]
      exact Finset.mem_singleton_self _
    exact (support_mono (show
      (labelFace (plHeight G h) (uniformMapperCover a r g n) c
        e.succ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).1 ≤ c.1 from
      labelFace_le (plHeight G h) (uniformMapperCover a r g n) c
        e.succ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))) hmem
  have hAA' : A' = A := by
    apply eq_of_mem_mapper_face_of_fst_eq
      (plHeight G h) (uniformMapperCover a r g n)
      c.1.support_mem_nerve hA' hv
    rfl
  apply Subtype.ext
  calc
    ((uniformMapperData G h a r g n).right e c).1 = vertexCell
        (plHeight G h) (uniformMapperCover a r g n) A' := by
          exact uniformMapperVertexCell_eq G h e.succ
            ((uniformMapperData G h a r g n).right e c)
    _ = vertexCell (plHeight G h) (uniformMapperCover a r g n) A :=
      congrArg (vertexCell (plHeight G h) (uniformMapperCover a r g n)) hAA'
    _ = v.1 := (uniformMapperVertexCell_eq G h e.succ v).symm

/-! ## The vertex equivalence and adjacency -/

/-- The vertices of the uniform Mapper finite data are the ordinary Mapper vertices. -/
def uniformMapperIncidenceVertexEquiv :
    (uniformMapperData G h a r g n).IncidenceVertex ≃
      MapperVertex (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) := by
  let e₁ : (Σ k, (uniformMapperData G h a r g n).V k) ≃
      ComponentIndex (plHeight G h) (uniformMapperCover a r g n) :=
    Equiv.sigmaCongrRight (fun k => vertexCellsEquiv (plHeight G h)
      (uniformMapperCover a r g n) k)
  let e₂ : ComponentIndex (plHeight G h) (uniformMapperCover a r g n) ≃
      MapperVertex (plHeight G h) (uniformMapperCover a r g n) :=
    { toFun := toMapperVertex (plHeight G h) (uniformMapperCover a r g n)
      invFun := fun z => z.1
      left_inv := fun z => rfl
      right_inv := fun z => Subtype.ext rfl }
  exact e₁.trans e₂

private theorem uniformMapperIncidenceVertexEquiv_apply (k : Fin (n + 1))
    (c : (uniformMapperData G h a r g n).V k) :
    uniformMapperIncidenceVertexEquiv G h ⟨k, c⟩ =
      toMapperVertex (plHeight G h) (uniformMapperCover a r g n)
        ⟨k, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) k c⟩ := rfl

private theorem uniformMapperLeft_mem_support (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e) :
    (⟨e.castSucc, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) e.castSucc
        ((uniformMapperData G h a r g n).left e c)⟩ :
      uniformMapperIndex G h a r g n) ∈ c.1.support := by
  have hm : (⟨e.castSucc, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) e.castSucc
      ((uniformMapperData G h a r g n).left e c)⟩ :
      uniformMapperIndex G h a r g n) ∈
        ((uniformMapperData G h a r g n).left e c).1.support := by
    rw [support_eq_singleton_of_vertexCell G h e.castSucc
        ((uniformMapperData G h a r g n).left e c)]
    exact Finset.mem_singleton_self _
  exact (support_mono (show
    (labelFace (plHeight G h) (uniformMapperCover a r g n) c
      e.castSucc (Finset.mem_insert_self _ _)).1 ≤ c.1 from
    labelFace_le (plHeight G h) (uniformMapperCover a r g n) c
      e.castSucc (Finset.mem_insert_self _ _))) hm

private theorem uniformMapperRight_mem_support (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e) :
    (⟨e.succ, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) e.succ
        ((uniformMapperData G h a r g n).right e c)⟩ :
      uniformMapperIndex G h a r g n) ∈ c.1.support := by
  have hm : (⟨e.succ, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) e.succ
      ((uniformMapperData G h a r g n).right e c)⟩ :
      uniformMapperIndex G h a r g n) ∈
        ((uniformMapperData G h a r g n).right e c).1.support := by
    rw [support_eq_singleton_of_vertexCell G h e.succ
        ((uniformMapperData G h a r g n).right e c)]
    exact Finset.mem_singleton_self _
  exact (support_mono (show
    (labelFace (plHeight G h) (uniformMapperCover a r g n) c
      e.succ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).1 ≤ c.1 from
    labelFace_le (plHeight G h) (uniformMapperCover a r g n) c
      e.succ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))) hm

private theorem uniformMapperArrow_adj (e : Fin n) (c : (uniformMapperData G h a r g n).E e) :
    (mapperOneSkeleton (plHeight G h) (uniformMapperCover a r g n)).Adj
        (uniformMapperIncidenceVertexEquiv G h
            ⟨e.castSucc, (uniformMapperData G h a r g n).left e c⟩)
        (uniformMapperIncidenceVertexEquiv G h
            ⟨e.succ, (uniformMapperData G h a r g n).right e c⟩) := by
  rw [uniformMapperIncidenceVertexEquiv_apply, uniformMapperIncidenceVertexEquiv_apply]
  apply (mapperOneSkeleton_adj_iff (plHeight G h) (uniformMapperCover a r g n) _ _).2
  constructor
  · intro hab
    exact (Fin.castSucc_lt_succ (i := e)).ne
      (congrArg (fun z : MapperVertex (plHeight G h) (uniformMapperCover a r g n) => z.1.1) hab)
  · apply mem_nerve_of_nonempty_subset
      (componentCover (plHeight G h) (uniformMapperCover a r g n))
      c.1.support_mem_nerve
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact uniformMapperLeft_mem_support G h e c
      · obtain rfl := Finset.mem_singleton.1 hz
        exact uniformMapperRight_mem_support G h e c
    · exact Finset.insert_nonempty _ _

private theorem uniformMapperAdj_of_cell (hgr : 2 * g ≤ r) {k l : Fin (n + 1)}
    (c : (uniformMapperData G h a r g n).V k) (d : (uniformMapperData G h a r g n).V l)
    (z : MultiNerveCell (componentCover (plHeight G h) (uniformMapperCover a r g n)))
    (hz : z.support = {(⟨k, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n)
        k c⟩ : uniformMapperIndex G h a r g n),
      ⟨l, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) l d⟩})
    (hkl : k < l) :
    (uniformMapperData G h a r g n).incidenceGraph.Adj ⟨k, c⟩ ⟨l, d⟩ := by
  have hlabels : z.support.image Sigma.fst = {k, l} := by
    rw [hz]
    ext i
    constructor
    · intro hi
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hi
      rcases (Finset.mem_insert (α := uniformMapperIndex G h a r g n)).1 hy with rfl | hy
      · exact Finset.mem_insert_self _ _
      · obtain rfl := Finset.mem_singleton.1 hy
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · intro hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Finset.mem_image.2 ⟨_, Finset.mem_insert_self
          (α := uniformMapperIndex G h a r g n) _ _, rfl⟩
      · obtain rfl := Finset.mem_singleton.1 hi
        exact Finset.mem_image.2
          ⟨_, Finset.mem_insert_of_mem (α := uniformMapperIndex G h a r g n)
              (Finset.mem_singleton_self _), rfl⟩
  have hfar : ¬ (k : ℕ) + 2 ≤ l := fun hfar =>
    (isEmpty_uniformEdgeCells_of_far G h hgr hfar).false ⟨z, hlabels⟩
  have hkl' : (k : ℕ) < l := hkl
  have hl : (l : ℕ) < n + 1 := l.isLt
  obtain ⟨e, rfl, rfl⟩ : ∃ e : Fin n, e.castSucc = k ∧ e.succ = l :=
    ⟨⟨k, by omega⟩, Fin.ext rfl, Fin.ext (show (k : ℕ) + 1 = l by omega)⟩
  have hA : (⟨e.castSucc, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n)
      e.castSucc c⟩ : uniformMapperIndex G h a r g n) ∈ z.support := by
    rw [hz]
    exact Finset.mem_insert_self (α := uniformMapperIndex G h a r g n) _ _
  have hB : (⟨e.succ, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n)
      e.succ d⟩ : uniformMapperIndex G h a r g n) ∈ z.support := by
    rw [hz]
    exact Finset.mem_insert_of_mem (α := uniformMapperIndex G h a r g n)
        (Finset.mem_singleton_self _)
  exact ((uniformMapperData G h a r g n).incidenceGraph_adj_castSucc_succ_iff e c d).2
    ⟨⟨z, hlabels⟩, uniformMapperLeft_eq_of_mem G h e ⟨z, hlabels⟩ c hA,
      uniformMapperRight_eq_of_mem G h e ⟨z, hlabels⟩ d hB⟩

private theorem uniformMapperAdj_iff (hgr : 2 * g ≤ r)
    {x y : (uniformMapperData G h a r g n).IncidenceVertex} :
    (mapperOneSkeleton (plHeight G h) (uniformMapperCover a r g n)).Adj
        (uniformMapperIncidenceVertexEquiv G h x)
        (uniformMapperIncidenceVertexEquiv G h y) ↔
      (uniformMapperData G h a r g n).incidenceGraph.Adj x y := by
  rcases x with ⟨k, c⟩
  rcases y with ⟨l, d⟩
  rw [uniformMapperIncidenceVertexEquiv_apply, uniformMapperIncidenceVertexEquiv_apply]
  constructor
  · intro hab
    have hab' := (mapperOneSkeleton_adj_iff (plHeight G h)
      (uniformMapperCover a r g n) _ _).1 hab
    have hface : {(⟨k, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n)
        k c⟩ : uniformMapperIndex G h a r g n),
        ⟨l, vertexCellsEquiv (plHeight G h) (uniformMapperCover a r g n) l d⟩} ∈
        mapper (plHeight G h) (uniformMapperCover a r g n) := hab'.2
    have hkl : k ≠ l := by
      intro hkl
      apply hab'.1
      apply Subtype.ext
      exact eq_of_mem_mapper_face_of_fst_eq
        (plHeight G h) (uniformMapperCover a r g n) hface
        (Finset.mem_insert_self (α := uniformMapperIndex G h a r g n) _ _)
        (Finset.mem_insert_of_mem (α := uniformMapperIndex G h a r g n)
            (Finset.mem_singleton_self _)) hkl
    obtain ⟨z, hz⟩ := exists_cell_of_mem_nerve
      (V := componentCover (plHeight G h) (uniformMapperCover a r g n)) hface
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · exact uniformMapperAdj_of_cell G h hgr c d z hz hlt
    · exact (uniformMapperAdj_of_cell G h hgr d c z
        (hz.trans (Finset.pair_comm (α := uniformMapperIndex G h a r g n) _ _)) hgt).symm
  · intro hab
    rcases ((uniformMapperData G h a r g n).incidenceGraph_adj_iff).mp hab with hxy | hyx
    · obtain ⟨p⟩ := hxy
      rcases p with ⟨⟨e, q⟩, hs, ht⟩
      cases hs
      cases ht
      exact uniformMapperArrow_adj G h e q
    · obtain ⟨p⟩ := hyx
      rcases p with ⟨⟨e, q⟩, hs, ht⟩
      cases hs
      cases ht
      exact (uniformMapperArrow_adj G h e q).symm

/-! ## Graph comparison -/

/-- The incidence graph of the uniform Mapper data is the ordinary Mapper one-skeleton. -/
def incidenceGraphUniformMapperIso (hgr : 2 * g ≤ r) :
    (uniformMapperData G h a r g n).incidenceGraph ≃g
      mapperOneSkeleton (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) :=
  { toEquiv := uniformMapperIncidenceVertexEquiv (a := a) (r := r) (g := g) (n := n) G h
    map_rel_iff' := fun {_ _} =>
      uniformMapperAdj_iff (a := a) (r := r) (g := g) (n := n) G h hgr }

/-- The graph-isomorphism equivalence is the declared uniform Mapper vertex equivalence. -/
theorem incidenceGraphUniformMapperIso_toEquiv (hgr : 2 * g ≤ r) :
    (incidenceGraphUniformMapperIso (a := a) (r := r) (g := g) (n := n) G h hgr).toEquiv =
      uniformMapperIncidenceVertexEquiv (a := a) (r := r) (g := g) (n := n) G h := rfl

/-- The ordinary Mapper one-skeleton is graph-isomorphic to graph-PL finite Reeb data. -/
def mapperOneSkeletonGraphPLIso (T : CriticalValues n) (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) (hg : 0 < g) (hgr : 2 * g ≤ r) :
    mapperOneSkeleton (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) ≃g
      (graphPLReebData G h T).incidenceGraph :=
  (incidenceGraphUniformMapperIso G h hgr).symm.trans
    (TDA.Reeb.FiniteReebData.incidenceGraphIso
      (uniformMapperIso G h T hT hcov hg (by linarith)))

/-- Connectivity transfers across the Mapper--finite-Reeb graph isomorphism. -/
theorem mapperOneSkeleton_connected_iff (T : CriticalValues n) (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) (hg : 0 < g) (hgr : 2 * g ≤ r) :
    (mapperOneSkeleton (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ))).Connected ↔
      (graphPLReebData G h T).incidenceGraph.Connected :=
  (mapperOneSkeletonGraphPLIso G h T hT hcov hg hgr).connected_iff

/-- The ordinary Mapper one-skeleton edge count is bounded by the finite-data edge count. -/
theorem card_mapperOneSkeleton_edgeSet_le (hgr : 2 * g ≤ r) :
    Nat.card (mapperOneSkeleton (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ))).edgeSet ≤
      ∑ e, Nat.card ((uniformMapperData G h a r g n).E e) :=
  (Nat.card_congr (incidenceGraphUniformMapperIso G h hgr).mapEdgeSet.symm).trans_le
    (TDA.Reeb.FiniteReebData.card_incidenceGraph_edgeSet_le _)

end
end TDA.Mapper.GraphPL
