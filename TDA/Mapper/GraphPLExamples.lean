import TDA.Mapper.GraphPL
import TDA.Mapper.BasicExamples
import TDA.Reeb.GraphPLComponentsExamples
import TDA.Reeb.ComponentsDiscrete
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Exact fixtures for graph-PL Mapper

Concrete graph-realization fixtures for the graph-PL ordinary Mapper consumer.
-/

namespace TDA.Mapper.GraphPL.Examples

open Finset Set SimpleGraph
open TDA.Topology TDA.Reeb
open TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀ half)

noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-! ## A finite label type does not imply finite Mapper vertices -/

/-- The constant map from the discrete natural numbers to a point. -/
def natToUnit : C(ℕ, Unit) := ContinuousMap.const ℕ ()

private def natPoint (n : ℕ) :
    PullbackSpace natToUnit TDA.Mapper.Examples.unitCover () :=
  ⟨n, Set.mem_univ ()⟩

/-- The supported Mapper vertices for a one-member cover of a constant map on discrete `ℕ` are
explicitly equivalent to `ℕ`. -/
def natMapperVertexEquiv :
    MapperVertex natToUnit TDA.Mapper.Examples.unitCover ≃ ℕ where
  toFun a := (TDA.Reeb.zerothHomotopyEquivOfDiscrete _ a.1.2).1
  invFun n := toMapperVertex natToUnit TDA.Mapper.Examples.unitCover
    ⟨(), ZerothHomotopy.mk (natPoint n)⟩
  left_inv a := by
    apply Subtype.ext
    rcases a with ⟨⟨i, c⟩, ha⟩
    rcases i with ⟨⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    let e := TDA.Reeb.zerothHomotopyEquivOfDiscrete
      (PullbackSpace natToUnit TDA.Mapper.Examples.unitCover ())
    change ZerothHomotopy.mk
      (natPoint ((e c).1)) = c
    calc
      ZerothHomotopy.mk (natPoint ((e c).1)) = ZerothHomotopy.mk (e c) := by
        apply congrArg ZerothHomotopy.mk
        exact Subtype.ext rfl
      _ = c := e.symm_apply_apply c
  right_inv n := by
    let e := TDA.Reeb.zerothHomotopyEquivOfDiscrete
      (PullbackSpace natToUnit TDA.Mapper.Examples.unitCover ())
    have he := e.apply_symm_apply (natPoint n)
    exact congrArg Subtype.val he

/-! ## Shared interval cover and range bounds -/

/-- The two overlapping intervals `(-1, 3/2)` and `(1/2, 3)`. -/
def overlappingIntervals : Bool → OpenInterval
  | false => ioo (-1) (3 / 2)
  | true => ioo (1 / 2) 3

private theorem plHeight_mem_Icc_of_vertex_bounds {V : Type*} (G : SimpleGraph V)
    (h : V → ℝ) {a b : ℝ} (hh : ∀ v, h v ∈ Set.Icc a b) (p : Realization G) :
    plHeight G h p ∈ Set.Icc a b := by
  induction p using ind G with
  | vertex v => exact hh v
  | edgePoint d t =>
      have hf := hh d.fst
      have hs := hh d.snd
      have ht0 : (0 : ℝ) ≤ t := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      change a ≤ (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ∧
        (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ≤ b
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hf.1),
          mul_nonneg ht0 (sub_nonneg.2 hs.1)]
      · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hf.2),
          mul_nonneg ht0 (sub_nonneg.2 hs.2)]

private theorem overlappingIntervals_cover_of_bounds {V : Type*} (G : SimpleGraph V)
    (h : V → ℝ) (hh : ∀ v, h v ∈ Set.Icc (0 : ℝ) 2) :
    Covers (fun i => (overlappingIntervals i : Set ℝ)) (Set.range (plHeight G h)) := by
  rintro y ⟨p, rfl⟩
  obtain ⟨hp0, hp2⟩ := plHeight_mem_Icc_of_vertex_bounds G h hh p
  by_cases hy : plHeight G h p < 3 / 2
  · refine ⟨false, ?_⟩
    change (-1 : ℝ) < plHeight G h p ∧ plHeight G h p < 3 / 2
    exact ⟨by linarith, hy⟩
  · refine ⟨true, ?_⟩
    change (1 / 2 : ℝ) < plHeight G h p ∧ plHeight G h p < 3
    constructor <;> linarith

private theorem h02_mem_Icc (b : Bool) : h02 b ∈ Set.Icc (0 : ℝ) 2 := by
  cases b <;> norm_num [h02]

/-- The overlapping interval family covers the actual range of the single-edge PL height. -/
theorem overlappingIntervals_cover_edge_range :
    Covers (fun i => (overlappingIntervals i : Set ℝ))
      (Set.range (plHeight edgeGraph h02)) :=
  overlappingIntervals_cover_of_bounds edgeGraph h02 h02_mem_Icc

/-! ## One open arc and no surviving original vertex -/

/-- The one-member interval family whose member is `(0, 2)`. -/
def singleArcIntervals : Unit → OpenInterval := fun _ => ioo 0 2

/-- The `(0, 2)` single-edge Mapper has one component vertex although the interval contains no
original graph vertex. -/
theorem singleArc_mapper_exact :
    Nat.card (ComponentIndex (plHeight edgeGraph h02)
      (fun i => (singleArcIntervals i : Set ℝ))) = 1 ∧
    IsEmpty {v : Bool // h02 v ∈ singleArcIntervals ()} := by
  constructor
  · change Nat.card (Σ _ : Unit, ZerothHomotopy
      {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ ioo 0 2}) = 1
    exact (Nat.card_congr (Equiv.uniqueSigma fun _ : Unit =>
      ZerothHomotopy {p : Realization edgeGraph //
        plHeight edgeGraph h02 p ∈ ioo 0 2})).trans zeroTwo_card_preimage
  · exact zeroTwo_no_vertex

/-! ## Two overlapping labels on one edge -/

private theorem bool_mem_singleEdge (b : Bool) : b ∈ (dartEdge d₀ : Sym2 Bool) := by
  cases b
  · exact fst_mem_dartEdge d₀
  · exact snd_mem_dartEdge d₀

private theorem edgeCell_class_of_vertex_mem {K : OpenInterval} (b : Bool) (hb : h02 b ∈ K)
    (x : Cell edgeGraph h02 K) :
    (cellGraph edgeGraph h02 K).connectedComponentMk x =
      (cellGraph edgeGraph h02 K).connectedComponentMk (Sum.inl ⟨b, hb⟩) := by
  let e : {e : edgeGraph.edgeSet // EdgeActive edgeGraph h02 K e} :=
    ⟨dartEdge d₀, edgeActive_of_mem (bool_mem_singleEdge b) hb⟩
  rcases x with v | e'
  · calc
      (cellGraph edgeGraph h02 K).connectedComponentMk (Sum.inl v) =
          (cellGraph edgeGraph h02 K).connectedComponentMk (Sum.inr e) :=
        connectedComponentMk_inl_eq_inr edgeGraph h02 K (bool_mem_singleEdge v.1)
      _ = (cellGraph edgeGraph h02 K).connectedComponentMk (Sum.inl ⟨b, hb⟩) :=
        (connectedComponentMk_inl_eq_inr edgeGraph h02 K
          (bool_mem_singleEdge b)).symm
  · have he : e' = e := Subtype.ext (edgeGraph_edge_eq e'.1)
    subst e'
    exact (connectedComponentMk_inl_eq_inr edgeGraph h02 K
      (bool_mem_singleEdge b)).symm

private theorem edgeCellComponents_subsingleton {K : OpenInterval} (b : Bool)
    (hb : h02 b ∈ K) : Subsingleton (cellGraph edgeGraph h02 K).ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun x y => by
    rw [edgeCell_class_of_vertex_mem b hb x, edgeCell_class_of_vertex_mem b hb y]⟩

private theorem overlap_endpoint_mem (i : Bool) : h02 i ∈ overlappingIntervals i := by
  cases i <;> norm_num [h02, overlappingIntervals, mem_ioo]

private theorem overlap_components_subsingleton (i : Bool) :
    Subsingleton (ZerothHomotopy
      {p : Realization edgeGraph // plHeight edgeGraph h02 p ∈ overlappingIntervals i}) :=
  ⟨fun _c _d => (preimageComponentsEquiv edgeGraph h02 (overlappingIntervals i)).injective
    (@Subsingleton.elim _
      (edgeCellComponents_subsingleton i (overlap_endpoint_mem i)) _ _)⟩

private def edgeOverlapPoint (i : Bool) :
    PullbackSpace (plHeight edgeGraph h02) (fun i => (overlappingIntervals i : Set ℝ)) i :=
  ⟨edgePoint edgeGraph d₀ half, by
    rw [plHeight_edgePoint, dartHeight_d₀, coe_half]
    cases i <;> norm_num [overlappingIntervals, mem_ioo]⟩

/-- The component-cover vertex for the interval label `i`, represented by the common midpoint. -/
def edgeOverlapIndex (i : Bool) :
    ComponentIndex (plHeight edgeGraph h02) (fun i => (overlappingIntervals i : Set ℝ)) :=
  ⟨i, ZerothHomotopy.mk (edgeOverlapPoint i)⟩

private theorem edgeOverlapIndex_ne : edgeOverlapIndex false ≠ edgeOverlapIndex true :=
  componentIndex_ne_of_index_ne (plHeight edgeGraph h02)
    (fun i => (overlappingIntervals i : Set ℝ)) Bool.false_ne_true _ _

private theorem edgeOverlapIndex_exhaustive
    (a : ComponentIndex (plHeight edgeGraph h02)
      (fun i => (overlappingIntervals i : Set ℝ))) :
    a = edgeOverlapIndex false ∨ a = edgeOverlapIndex true := by
  rcases a with ⟨i, c⟩
  cases i with
  | false =>
      left
      refine Sigma.ext rfl (heq_of_eq ?_)
      exact @Subsingleton.elim _ (overlap_components_subsingleton false) _ _
  | true =>
      right
      refine Sigma.ext rfl (heq_of_eq ?_)
      exact @Subsingleton.elim _ (overlap_components_subsingleton true) _ _

private theorem edgeOverlap_pair_face :
    ({edgeOverlapIndex false, edgeOverlapIndex true} :
      Finset (ComponentIndex (plHeight edgeGraph h02)
        (fun i => (overlappingIntervals i : Set ℝ)))) ∈
      mapper (plHeight edgeGraph h02) (fun i => (overlappingIntervals i : Set ℝ)) := by
  apply (mem_mapper_iff _ _ _).2
  refine ⟨by simp, edgePoint edgeGraph d₀ half, ?_⟩
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨(edgeOverlapPoint false).2, rfl⟩
  · exact ⟨(edgeOverlapPoint true).2, rfl⟩

private theorem overlappingIntervals_multiplicity_two {V : Type*} (G : SimpleGraph V)
    (h : V → ℝ) :
    CoverMultiplicityAtMost (plHeight G h) (fun i => (overlappingIntervals i : Set ℝ)) 2 := by
  intro _ _ t _
  simpa using Finset.card_le_univ t

/-- The two overlapping intervals give exactly two Mapper vertices, their common edge, and no
face with more than two vertices. -/
theorem singleEdge_overlap_exact :
    Nat.card (ComponentIndex (plHeight edgeGraph h02)
      (fun i => (overlappingIntervals i : Set ℝ))) = 2 ∧
    ({edgeOverlapIndex false, edgeOverlapIndex true} :
      Finset (ComponentIndex (plHeight edgeGraph h02)
        (fun i => (overlappingIntervals i : Set ℝ)))) ∈
      mapper (plHeight edgeGraph h02) (fun i => (overlappingIntervals i : Set ℝ)) ∧
    ∀ s, s ∈ mapper (plHeight edgeGraph h02)
      (fun i => (overlappingIntervals i : Set ℝ)) → s.card ≤ 2 := by
  refine ⟨?_, edgeOverlap_pair_face, ?_⟩
  · exact Nat.card_eq_two_iff.2 ⟨edgeOverlapIndex false, edgeOverlapIndex true,
      edgeOverlapIndex_ne, Set.eq_univ_of_forall fun a => edgeOverlapIndex_exhaustive a⟩
  · intro s hs
    exact mapper_face_card_le_of_multiplicity _ _
      (overlappingIntervals_multiplicity_two edgeGraph h02) hs

/-! ## Two disjoint edges -/

/-- Two disjoint copies of the single-edge graph. -/
abbrev twoEdgeGraph : SimpleGraph (Bool ⊕ Bool) := edgeGraph ⊕g edgeGraph

/-- Matching endpoint heights `0` and `2` on both copies. -/
def twoEdgeHeight : Bool ⊕ Bool → ℝ
  | Sum.inl b => h02 b
  | Sum.inr b => h02 b

/-- The oriented edge in the selected copy. -/
def twoEdgeDart : Bool → twoEdgeGraph.Dart
  | false => ⟨(Sum.inl false, Sum.inl true), by simp [twoEdgeGraph]⟩
  | true => ⟨(Sum.inr false, Sum.inr true), by simp [twoEdgeGraph]⟩

private theorem twoEdgeHeight_mem_Icc (v : Bool ⊕ Bool) :
    twoEdgeHeight v ∈ Set.Icc (0 : ℝ) 2 := by
  rcases v with b | b <;> exact h02_mem_Icc b

/-- The overlapping interval family covers the actual range of the two-edge PL height. -/
theorem overlappingIntervals_cover_twoEdge_range :
    Covers (fun i => (overlappingIntervals i : Set ℝ))
      (Set.range (plHeight twoEdgeGraph twoEdgeHeight)) :=
  overlappingIntervals_cover_of_bounds twoEdgeGraph twoEdgeHeight twoEdgeHeight_mem_Icc

private theorem edgeSetSumEquiv_left :
    SimpleGraph.edgeSetSumEquiv (dartEdge (twoEdgeDart false)) =
      Sum.inl (dartEdge d₀) := rfl

private theorem edgeSetSumEquiv_right :
    SimpleGraph.edgeSetSumEquiv (dartEdge (twoEdgeDart true)) =
      Sum.inr (dartEdge d₀) := rfl

private theorem twoEdge_edge_eq (e : twoEdgeGraph.edgeSet) :
    e = dartEdge (twoEdgeDart false) ∨ e = dartEdge (twoEdgeDart true) := by
  let E := SimpleGraph.edgeSetSumEquiv (G := edgeGraph) (H := edgeGraph)
  rcases hE : E e with eL | eR
  · left
    apply E.injective
    rw [hE, edgeSetSumEquiv_left]
    exact congrArg Sum.inl (edgeGraph_edge_eq eL)
  · right
    apply E.injective
    rw [hE, edgeSetSumEquiv_right]
    exact congrArg Sum.inr (edgeGraph_edge_eq eR)

private theorem twoEdge_edges_ne :
    dartEdge (twoEdgeDart false) ≠ dartEdge (twoEdgeDart true) := by
  intro h
  have h' := congrArg SimpleGraph.edgeSetSumEquiv h
  rw [edgeSetSumEquiv_left, edgeSetSumEquiv_right] at h'
  exact Sum.inl_ne_inr h'

private def twoEdgeCellSide (K : OpenInterval) : Cell twoEdgeGraph twoEdgeHeight K → Bool
  | Sum.inl v => match v.1 with
    | Sum.inl _ => false
    | Sum.inr _ => true
  | Sum.inr e => if e.1 = dartEdge (twoEdgeDart false) then false else true

private theorem twoEdgeCellSide_adj {K : OpenInterval}
    {x y : Cell twoEdgeGraph twoEdgeHeight K}
    (hxy : (cellGraph twoEdgeGraph twoEdgeHeight K).Adj x y) :
    twoEdgeCellSide K x = twoEdgeCellSide K y := by
  have hinc : ∀ (v : {v : Bool ⊕ Bool // twoEdgeHeight v ∈ K})
      (e : {e : twoEdgeGraph.edgeSet // EdgeActive twoEdgeGraph twoEdgeHeight K e}),
      (v : Bool ⊕ Bool) ∈ (e.1 : Sym2 (Bool ⊕ Bool)) →
        twoEdgeCellSide K (Sum.inl v) = twoEdgeCellSide K (Sum.inr e) := by
    intro v e hve
    rcases twoEdge_edge_eq e.1 with he | he
    · rw [he] at hve
      rcases mem_dartEdge.mp hve with hv | hv
      · rcases v with ⟨v, hvK⟩
        change v = _ at hv
        subst v
        simp [twoEdgeCellSide, he, twoEdgeDart]
      · rcases v with ⟨v, hvK⟩
        change v = _ at hv
        subst v
        simp [twoEdgeCellSide, he, twoEdgeDart]
    · rw [he] at hve
      rcases mem_dartEdge.mp hve with hv | hv
      · rcases v with ⟨v, hvK⟩
        change v = _ at hv
        subst v
        change true = if e.1 = dartEdge (twoEdgeDart false) then false else true
        rw [if_neg]
        intro hEq
        exact (Ne.symm twoEdge_edges_ne) (he.symm.trans hEq)
      · rcases v with ⟨v, hvK⟩
        change v = _ at hv
        subst v
        change true = if e.1 = dartEdge (twoEdgeDart false) then false else true
        rw [if_neg]
        intro hEq
        exact (Ne.symm twoEdge_edges_ne) (he.symm.trans hEq)
  rcases x with v | e <;> rcases y with w | e'
  · exact (hxy : False).elim
  · exact hinc v e' hxy
  · exact (hinc w e hxy).symm
  · exact (hxy : False).elim

private def twoEdgeVertex (side i : Bool) :
    {v : Bool ⊕ Bool // twoEdgeHeight v ∈ overlappingIntervals i} :=
  match side with
  | false => ⟨Sum.inl i, overlap_endpoint_mem i⟩
  | true => ⟨Sum.inr i, overlap_endpoint_mem i⟩

private theorem twoEdgeVertex_mem_dart (side i : Bool) :
    (twoEdgeVertex side i : Bool ⊕ Bool) ∈
      (dartEdge (twoEdgeDart side) : Sym2 (Bool ⊕ Bool)) := by
  cases side <;> cases i
  · exact fst_mem_dartEdge (twoEdgeDart false)
  · exact snd_mem_dartEdge (twoEdgeDart false)
  · exact fst_mem_dartEdge (twoEdgeDart true)
  · exact snd_mem_dartEdge (twoEdgeDart true)

private theorem twoEdge_cell_classification (i : Bool)
    (c : (cellGraph twoEdgeGraph twoEdgeHeight (overlappingIntervals i)).ConnectedComponent) :
    c = (cellGraph twoEdgeGraph twoEdgeHeight (overlappingIntervals i)).connectedComponentMk
        (Sum.inl (twoEdgeVertex false i)) ∨
      c = (cellGraph twoEdgeGraph twoEdgeHeight (overlappingIntervals i)).connectedComponentMk
        (Sum.inl (twoEdgeVertex true i)) := by
  induction c using ConnectedComponent.ind with
  | h x =>
      rcases x with ⟨v, hv⟩ | e
      · rcases v with b | b
        · left
          apply congrArg
          apply congrArg Sum.inl
          apply Subtype.ext
          cases i <;> cases b
          · rfl
          · norm_num [twoEdgeHeight, h02, overlappingIntervals, mem_ioo] at hv
          · norm_num [twoEdgeHeight, h02, overlappingIntervals, mem_ioo] at hv
          · rfl
        · right
          apply congrArg
          apply congrArg Sum.inl
          apply Subtype.ext
          cases i <;> cases b
          · rfl
          · norm_num [twoEdgeHeight, h02, overlappingIntervals, mem_ioo] at hv
          · norm_num [twoEdgeHeight, h02, overlappingIntervals, mem_ioo] at hv
          · rfl
      · rcases twoEdge_edge_eq e.1 with he | he
        · left
          exact (connectedComponentMk_inl_eq_inr twoEdgeGraph twoEdgeHeight
            (overlappingIntervals i) (e := e) (by
              rw [he]
              exact twoEdgeVertex_mem_dart false i)).symm
        · right
          exact (connectedComponentMk_inl_eq_inr twoEdgeGraph twoEdgeHeight
            (overlappingIntervals i) (e := e) (by
              rw [he]
              exact twoEdgeVertex_mem_dart true i)).symm

private theorem twoEdge_cell_anchors_ne (i : Bool) :
    (cellGraph twoEdgeGraph twoEdgeHeight (overlappingIntervals i)).connectedComponentMk
        (Sum.inl (twoEdgeVertex false i)) ≠
      (cellGraph twoEdgeGraph twoEdgeHeight (overlappingIntervals i)).connectedComponentMk
        (Sum.inl (twoEdgeVertex true i)) := by
  intro h
  obtain ⟨p⟩ := ConnectedComponent.exact h
  have hs := eq_of_walk (fun _ _ => twoEdgeCellSide_adj) p
  simp [twoEdgeCellSide, twoEdgeVertex] at hs

private theorem twoEdge_midpoint_height (side : Bool) :
    dartHeight twoEdgeHeight (twoEdgeDart side) half = 1 := by
  cases side <;> norm_num [dartHeight, twoEdgeDart, twoEdgeHeight, h02, coe_half]

private theorem twoEdge_midpoint_mem (side i : Bool) :
    dartHeight twoEdgeHeight (twoEdgeDart side) half ∈ overlappingIntervals i := by
  rw [twoEdge_midpoint_height]
  cases i <;> norm_num [overlappingIntervals, mem_ioo]

private def twoEdgeOverlapPoint (side i : Bool) :
    PullbackSpace (plHeight twoEdgeGraph twoEdgeHeight)
      (fun i => (overlappingIntervals i : Set ℝ)) i :=
  ⟨edgePoint twoEdgeGraph (twoEdgeDart side) half, twoEdge_midpoint_mem side i⟩

/-- The component-cover vertex at a graph copy and an interval label, represented by their
midpoint. -/
def twoEdgeOverlapIndex (side i : Bool) :
    ComponentIndex (plHeight twoEdgeGraph twoEdgeHeight)
      (fun i => (overlappingIntervals i : Set ℝ)) :=
  ⟨i, ZerothHomotopy.mk (twoEdgeOverlapPoint side i)⟩

private theorem twoEdge_overlap_equiv (side i : Bool) :
    preimageComponentsEquiv twoEdgeGraph twoEdgeHeight (overlappingIntervals i)
        (ZerothHomotopy.mk (twoEdgeOverlapPoint side i)) =
      (cellGraph twoEdgeGraph twoEdgeHeight (overlappingIntervals i)).connectedComponentMk
        (Sum.inl (twoEdgeVertex side i) :
          Cell twoEdgeGraph twoEdgeHeight (overlappingIntervals i)) := by
  change preimageComponentsEquiv twoEdgeGraph twoEdgeHeight (overlappingIntervals i)
      (ZerothHomotopy.mk ⟨edgePoint twoEdgeGraph (twoEdgeDart side) half,
        twoEdge_midpoint_mem side i⟩) = _
  calc
    _ = (cellGraph twoEdgeGraph twoEdgeHeight
        (overlappingIntervals i)).connectedComponentMk
        (Sum.inr ⟨dartEdge (twoEdgeDart side),
          edgeActive_dartEdge_of_mem (twoEdge_midpoint_mem side i)⟩) :=
      preimageComponentsEquiv_mk_edgePoint twoEdgeGraph twoEdgeHeight
        (overlappingIntervals i) (twoEdgeDart side) half (twoEdge_midpoint_mem side i)
    _ = _ := (connectedComponentMk_inl_eq_inr twoEdgeGraph twoEdgeHeight
      (overlappingIntervals i) (twoEdgeVertex_mem_dart side i)).symm

private theorem twoEdge_componentIndexEquiv (side i : Bool) :
    componentIndexEquiv twoEdgeGraph twoEdgeHeight overlappingIntervals
        (twoEdgeOverlapIndex side i) =
      ⟨i, (cellGraph twoEdgeGraph twoEdgeHeight (overlappingIntervals i)).connectedComponentMk
        (Sum.inl (twoEdgeVertex side i) :
          Cell twoEdgeGraph twoEdgeHeight (overlappingIntervals i))⟩ := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact twoEdge_overlap_equiv side i

private theorem twoEdge_preimage_classification (i : Bool)
    (c : ZerothHomotopy
      {p : Realization twoEdgeGraph //
        plHeight twoEdgeGraph twoEdgeHeight p ∈ overlappingIntervals i}) :
    c = ZerothHomotopy.mk (twoEdgeOverlapPoint false i) ∨
      c = ZerothHomotopy.mk (twoEdgeOverlapPoint true i) := by
  rcases twoEdge_cell_classification i
      (preimageComponentsEquiv twoEdgeGraph twoEdgeHeight (overlappingIntervals i) c) with hc | hc
  · left
    apply (preimageComponentsEquiv twoEdgeGraph twoEdgeHeight
      (overlappingIntervals i)).injective
    exact hc.trans (twoEdge_overlap_equiv false i).symm
  · right
    apply (preimageComponentsEquiv twoEdgeGraph twoEdgeHeight
      (overlappingIntervals i)).injective
    exact hc.trans (twoEdge_overlap_equiv true i).symm

private theorem twoEdgeOverlapIndex_pair_injective :
    Function.Injective (fun p : Bool × Bool => twoEdgeOverlapIndex p.1 p.2) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ hst
  have hij : i = j := congrArg Sigma.fst hst
  subst j
  have hc : ZerothHomotopy.mk (twoEdgeOverlapPoint s i) =
      ZerothHomotopy.mk (twoEdgeOverlapPoint t i) :=
    eq_of_heq (Sigma.ext_iff.mp hst).2
  have hcell := congrArg
    (preimageComponentsEquiv twoEdgeGraph twoEdgeHeight (overlappingIntervals i)) hc
  rw [twoEdge_overlap_equiv, twoEdge_overlap_equiv] at hcell
  have hside : s = t := by
    cases s <;> cases t
    · rfl
    · exact (twoEdge_cell_anchors_ne i hcell).elim
    · exact (twoEdge_cell_anchors_ne i hcell.symm).elim
    · rfl
  exact Prod.ext hside rfl

private theorem twoEdgeOverlapIndex_pair_surjective :
    Function.Surjective (fun p : Bool × Bool => twoEdgeOverlapIndex p.1 p.2) := by
  rintro ⟨i, c⟩
  rcases twoEdge_preimage_classification i c with hc | hc
  · exact ⟨(false, i), Sigma.ext rfl (heq_of_eq hc.symm)⟩
  · exact ⟨(true, i), Sigma.ext rfl (heq_of_eq hc.symm)⟩

/-- The four actual component-cover indices are exactly the graph-copy/interval-label pairs. -/
def twoEdgeIndexEquiv :
    Bool × Bool ≃ ComponentIndex (plHeight twoEdgeGraph twoEdgeHeight)
      (fun i => (overlappingIntervals i : Set ℝ)) :=
  Equiv.ofBijective (fun p => twoEdgeOverlapIndex p.1 p.2)
    ⟨twoEdgeOverlapIndex_pair_injective, twoEdgeOverlapIndex_pair_surjective⟩

private theorem twoEdge_pair_face (side : Bool) :
    ({twoEdgeOverlapIndex side false, twoEdgeOverlapIndex side true} :
      Finset (ComponentIndex (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ)))) ∈
      mapper (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ)) := by
  apply (mem_mapper_iff _ _ _).2
  refine ⟨by simp, edgePoint twoEdgeGraph (twoEdgeDart side) half, ?_⟩
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨(twoEdgeOverlapPoint side false).2, rfl⟩
  · exact ⟨(twoEdgeOverlapPoint side true).2, rfl⟩

/-! ## Refinement to one wide interval -/

/-- The one-member interval family `(-1, 3)`. -/
def wideIntervals : Unit → OpenInterval := fun _ => ioo (-1) 3

/-- Both overlapping source intervals select the one wide target interval. -/
def overlapToWide : Refinement (fun i => (overlappingIntervals i : Set ℝ))
    (fun j => (wideIntervals j : Set ℝ)) where
  selector _ := ()
  subset i x hx := by
    cases i <;> rcases hx with ⟨hx₁, hx₂⟩ <;> constructor <;> linarith

/-- The wide interval covers the actual range of the two-edge PL height. -/
theorem wideIntervals_cover_twoEdge_range :
    Covers (fun i => (wideIntervals i : Set ℝ))
      (Set.range (plHeight twoEdgeGraph twoEdgeHeight)) := by
  rintro y ⟨p, rfl⟩
  obtain ⟨hp0, hp2⟩ := plHeight_mem_Icc_of_vertex_bounds twoEdgeGraph
    twoEdgeHeight twoEdgeHeight_mem_Icc p
  exact ⟨(), by
    change (-1 : ℝ) < plHeight twoEdgeGraph twoEdgeHeight p ∧
      plHeight twoEdgeGraph twoEdgeHeight p < 3
    constructor <;> linarith⟩

private def twoEdgeWideEdge (side : Bool) :
    {e : twoEdgeGraph.edgeSet // EdgeActive twoEdgeGraph twoEdgeHeight (wideIntervals ()) e} :=
  ⟨dartEdge (twoEdgeDart side), edgeActive_dartEdge_of_mem (t := half) (by
    rw [twoEdge_midpoint_height]
    norm_num [wideIntervals, mem_ioo])⟩

/-- For every displayed source vertex, the general transport square identifies its actual Mapper
image with the corresponding incidence-graph edge-node component in the wide interval. -/
theorem twoEdge_wide_refinement_incidence (side i : Bool) :
    componentIndexEquiv twoEdgeGraph twoEdgeHeight wideIntervals
        (mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
          (twoEdgeOverlapIndex side i)) =
      ⟨(), (cellGraph twoEdgeGraph twoEdgeHeight (wideIntervals ())).connectedComponentMk
        (Sum.inr (twoEdgeWideEdge side) :
          Cell twoEdgeGraph twoEdgeHeight (wideIntervals ()))⟩ := by
  rw [componentIndexEquiv_mapperMap, twoEdge_componentIndexEquiv]
  refine Sigma.ext rfl (heq_of_eq ?_)
  change (cellGraph twoEdgeGraph twoEdgeHeight (wideIntervals ())).connectedComponentMk
      (Sum.inl ⟨(twoEdgeVertex side i).1, overlapToWide.subset i
        (twoEdgeVertex side i).2⟩) = _
  exact connectedComponentMk_inl_eq_inr twoEdgeGraph twoEdgeHeight (wideIntervals ())
    (twoEdgeVertex_mem_dart side i)

private theorem twoEdge_wide_edge_components_ne :
    (cellGraph twoEdgeGraph twoEdgeHeight (wideIntervals ())).connectedComponentMk
        (Sum.inr (twoEdgeWideEdge false) :
          Cell twoEdgeGraph twoEdgeHeight (wideIntervals ())) ≠
      (cellGraph twoEdgeGraph twoEdgeHeight (wideIntervals ())).connectedComponentMk
        (Sum.inr (twoEdgeWideEdge true) :
          Cell twoEdgeGraph twoEdgeHeight (wideIntervals ())) := by
  intro h
  obtain ⟨p⟩ := ConnectedComponent.exact h
  have hs := eq_of_walk (fun _ _ => twoEdgeCellSide_adj) p
  simp [twoEdgeCellSide, twoEdgeWideEdge, Ne.symm twoEdge_edges_ne] at hs

private theorem twoEdge_wide_same_side (side : Bool) :
    mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
        (twoEdgeOverlapIndex side false) =
      mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
        (twoEdgeOverlapIndex side true) := by
  rw [show twoEdgeOverlapIndex side false =
      ⟨false, ZerothHomotopy.mk (twoEdgeOverlapPoint side false)⟩ by rfl,
    show twoEdgeOverlapIndex side true =
      ⟨true, ZerothHomotopy.mk (twoEdgeOverlapPoint side true)⟩ by rfl,
    mapperMap_mk, mapperMap_mk]
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply congrArg ZerothHomotopy.mk
  exact Subtype.ext rfl

private theorem twoEdge_wide_cross_ne (i j : Bool) :
    mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
        (twoEdgeOverlapIndex false i) ≠
      mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
        (twoEdgeOverlapIndex true j) := by
  intro h
  have hc := congrArg (componentIndexEquiv twoEdgeGraph twoEdgeHeight wideIntervals) h
  rw [twoEdge_wide_refinement_incidence, twoEdge_wide_refinement_incidence] at hc
  exact twoEdge_wide_edge_components_ne (eq_of_heq (Sigma.ext_iff.mp hc).2)

/-- Component members from different graph copies do not intersect, even when their interval
labels differ. -/
theorem twoEdge_cross_componentCover_disjoint (i j : Bool) :
    Disjoint
      (componentCover (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ)) (twoEdgeOverlapIndex false i))
      (componentCover (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ)) (twoEdgeOverlapIndex true j)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := (componentRefinement (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide).subset
    (twoEdgeOverlapIndex false i) hp
  have hq' := (componentRefinement (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide).subset
    (twoEdgeOverlapIndex true j) hq
  let a := mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
    (twoEdgeOverlapIndex false i)
  let b := mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
    (twoEdgeOverlapIndex true j)
  have hab : a.2 ≠ b.2 := by
    intro hab'
    apply twoEdge_wide_cross_ne i j
    exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq hab')
  exact (Set.disjoint_left.mp (componentCover_disjoint
    (plHeight twoEdgeGraph twoEdgeHeight) (fun _ : Unit => (wideIntervals () : Set ℝ)) hab))
      hp' hq'

/-- The two-edge Mapper is exactly two disconnected copies of the single Mapper edge and has no
higher face. -/
theorem twoEdge_mapper_two_disjoint_edges :
    Nat.card (ComponentIndex (plHeight twoEdgeGraph twoEdgeHeight)
      (fun i => (overlappingIntervals i : Set ℝ))) = 4 ∧
    (∀ side, ({twoEdgeOverlapIndex side false, twoEdgeOverlapIndex side true} :
      Finset (ComponentIndex (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ)))) ∈
      mapper (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ))) ∧
    (∀ i j, ({twoEdgeOverlapIndex false i, twoEdgeOverlapIndex true j} :
      Finset (ComponentIndex (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ)))) ∉
      mapper (plHeight twoEdgeGraph twoEdgeHeight)
        (fun i => (overlappingIntervals i : Set ℝ))) ∧
    ∀ s, s ∈ mapper (plHeight twoEdgeGraph twoEdgeHeight)
      (fun i => (overlappingIntervals i : Set ℝ)) → s.card ≤ 2 := by
  refine ⟨?_, twoEdge_pair_face, ?_, ?_⟩
  · calc
      Nat.card (ComponentIndex (plHeight twoEdgeGraph twoEdgeHeight)
          (fun i => (overlappingIntervals i : Set ℝ))) = Nat.card (Bool × Bool) :=
        Nat.card_congr twoEdgeIndexEquiv.symm
      _ = 4 := by simp [Nat.card_eq_fintype_card, Fintype.card_bool]
  · intro i j hs
    obtain ⟨_, p, hp⟩ := (mem_mapper_iff _ _ _).1 hs
    exact (Set.disjoint_left.mp (twoEdge_cross_componentCover_disjoint i j))
      (hp _ (by simp)) (hp _ (by simp))
  · intro s hs
    exact mapper_face_card_le_of_multiplicity _ _
      (overlappingIntervals_multiplicity_two twoEdgeGraph twoEdgeHeight) hs

/-- Refining to one wide label is noninjective by label merging, while the two graph components
remain distinct; the final conjunct records the incidence comparison for every displayed vertex. -/
theorem twoEdge_wide_refinement_behavior :
    ¬ Function.Injective
      (mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide) ∧
    (∀ side,
      mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
          (twoEdgeOverlapIndex side false) =
        mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
          (twoEdgeOverlapIndex side true)) ∧
    (∀ i j,
      mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
          (twoEdgeOverlapIndex false i) ≠
        mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
          (twoEdgeOverlapIndex true j)) ∧
    ∀ side i,
      componentIndexEquiv twoEdgeGraph twoEdgeHeight wideIntervals
          (mapperMap (plHeight twoEdgeGraph twoEdgeHeight) overlapToWide
            (twoEdgeOverlapIndex side i)) =
        ⟨(), (cellGraph twoEdgeGraph twoEdgeHeight (wideIntervals ())).connectedComponentMk
          (Sum.inr (twoEdgeWideEdge side) :
            Cell twoEdgeGraph twoEdgeHeight (wideIntervals ()))⟩ := by
  refine ⟨?_, twoEdge_wide_same_side, twoEdge_wide_cross_ne,
    twoEdge_wide_refinement_incidence⟩
  intro hinj
  have hsource : twoEdgeOverlapIndex false false ≠ twoEdgeOverlapIndex false true :=
    componentIndex_ne_of_index_ne (plHeight twoEdgeGraph twoEdgeHeight)
      (fun i => (overlappingIntervals i : Set ℝ)) Bool.false_ne_true _ _
  exact hsource (hinj (twoEdge_wide_same_side false))

end

end TDA.Mapper.GraphPL.Examples
