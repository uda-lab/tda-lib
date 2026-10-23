import TDA.Reeb.GraphRealization
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples

/-!
# Cycle obstructions to simply connected graph realizations

For `V : Type u`, `G : SimpleGraph V` and a dart `d₀ : G.Dart`, the one-edge winding map
`edgeWinding G d₀ : C(Realization G, AddCircle (1 : ℝ))` sends every vertex to `0`, the point of
`d₀` at `t` to the class of `t`, the point of `d₀.symm` at `t` to the class of `1 - t` and every
point of every other dart to `0`. It is the continuous lift of the realization
(`TDA.Reeb.GraphRealization.continuousLift`); the two selected cases agree under reversal, and all
endpoint values are `0` because `0` and `1` have the same class in the circle. It winds the edge of
`d₀` once around the circle; it is not induced by a graph homomorphism.

## The return loop

A walk `q` from `d₀.snd` back to `d₀.fst` in `G.deleteEdges {d₀.edge}` avoids the unoriented edge
of `d₀`, hence both `d₀` and `d₀.symm`, and need not be simple. Mapped into `G`, it closes the
edge path of `d₀` to the loop

```lean
returnLoop G d₀ q = (edgePath G d₀).trans (walkPath G (q.mapLe (G.deleteEdges_le {d₀.edge})))
```

at `vertex G d₀.fst`. The winding map vanishes on the mapped return walk
(`edgeWinding_walkPath_deleteEdges`), so along the loop it is the class of
`returnLift s = min (2 * s) 1` (`edgeWinding_returnLoop`), and `returnLift` is the lift of the
winding of the loop through the covering `ℝ → AddCircle (1 : ℝ)` starting at `0`
(`returnLift_eq_liftPath`). Its final value is `1`, while the constant loop lifts to the constant
path at `0`. An endpoint-fixed homotopy from the loop to the constant loop would map along the
winding map to one of the circle paths, and homotopic paths with the same initial lift have the
same final lift (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`); this gives `1 = 0`. Hence
the loop is not homotopic to the constant loop (`not_homotopic_returnLoop`).

## Graph consequences

In a simply connected realization every loop is homotopic to the constant loop, so no edge has a
return walk avoiding it: every edge is a bridge and the graph is acyclic
(`isAcyclic_of_simplyConnectedSpace`). A simply connected space is path connected, so the graph is
connected by `connected_iff_pathConnectedSpace`, including nonemptiness, and is a tree
(`isTree_of_simplyConnectedSpace`, contrapositive `not_simplyConnectedSpace_of_not_isTree`). No
finiteness, local finiteness, decidable adjacency, vertex topology or nonemptiness hypothesis is
used. The converse, that the realization of a tree is simply connected, is not proved here.

## Source

The winding map, the vanishing on deleted-edge walks and the proof of acyclicity are adapted from
`uda-lab/reeb-ordering`, `ReebOrdering/GraphRealisation.lean` at commit
`aa7d10f4f7dc0474b76f17ea81afcab5a230d521` (blob `6b79160f368a9d6fd63f2d52f1db4d9c5697cfa8`),
Copyright 2026 Tomoki Uda, licensed under the Apache License, Version 2.0. The adapted
declarations, with source names and lines, are `edgeWindingCell` with `edgeWindingCell_symm`,
`edgeWindingCell_zero` (`windEdge`, `windEdge_symm`, `windEdge_zero` and `continuous_windEdge`,
223–261), `edgeWinding` with `edgeWinding_vertex`, `edgeWinding_edgePoint_self` and
`edgeWinding_edgePoint_of_ne` (`windMap` and its evaluation lemmas, 262–279),
`edgeWinding_walkPath_deleteEdges` (`windMap_walkPath_deleteEdges`, 281–307) and the lift
argument of `isAcyclic_of_simplyConnectedSpace` (309–364), split here into `returnLoop`,
`returnLift`, `edgeWinding_returnLoop`, `returnLift_eq_liftPath` and `not_homotopic_returnLoop`.
Changes: the names; public visibility; bundled edge data through `continuousLift`; the return
loop, its lift and its non-null-homotopy as separate public declarations; the reversed-dart
formula and the endpoint values as statements; and graph connectedness from the merged
`connected_iff_pathConnectedSpace` in place of the source's private connectedness lemma. Every
other declaration is new. The source is not imported.
-/

open SimpleGraph unitInterval Topology

namespace TDA.Reeb.GraphCycleObstruction

open TDA.Reeb.GraphRealization

universe u

noncomputable section

variable {V : Type u} (G : SimpleGraph V)

/-! ### The one-edge winding map -/

open Classical in
/-- The edge data of the winding map: the class of `t` on `d₀`, the class of `1 - t` on
`d₀.symm` and `0` on every other dart. -/
def edgeWindingCell (d₀ d : G.Dart) : C(unitInterval, AddCircle (1 : ℝ)) :=
  if d = d₀ then
    ⟨fun t => ((t : ℝ) : AddCircle (1 : ℝ)),
      (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val⟩
  else if d = d₀.symm then
    ⟨fun t => ((1 - (t : ℝ) : ℝ) : AddCircle (1 : ℝ)),
      (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.sub continuous_subtype_val)⟩
  else ContinuousMap.const _ 0

theorem edgeWindingCell_self (d₀ : G.Dart) (t : unitInterval) :
    edgeWindingCell G d₀ d₀ t = ((t : ℝ) : AddCircle (1 : ℝ)) := by
  unfold edgeWindingCell
  rw [if_pos rfl]
  rfl

theorem edgeWindingCell_symm_self (d₀ : G.Dart) (t : unitInterval) :
    edgeWindingCell G d₀ d₀.symm t = ((1 - (t : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
  unfold edgeWindingCell
  rw [if_neg d₀.symm_ne, if_pos rfl]
  rfl

theorem edgeWindingCell_of_ne (d₀ d : G.Dart) (hd : d ≠ d₀) (hd' : d ≠ d₀.symm)
    (t : unitInterval) : edgeWindingCell G d₀ d t = 0 := by
  unfold edgeWindingCell
  rw [if_neg hd, if_neg hd']
  rfl

/-- Reversal: the two selected cases agree, since `1 - (1 - t) = t`. -/
theorem edgeWindingCell_symm (d₀ d : G.Dart) (t : unitInterval) :
    edgeWindingCell G d₀ d.symm (σ t) = edgeWindingCell G d₀ d t := by
  by_cases h₁ : d = d₀
  · subst h₁
    rw [edgeWindingCell_symm_self, edgeWindingCell_self, coe_symm_eq, sub_sub_cancel]
  · by_cases h₂ : d = d₀.symm
    · subst h₂
      rw [Dart.symm_symm, edgeWindingCell_self, edgeWindingCell_symm_self, coe_symm_eq]
    · have h₁' : d.symm ≠ d₀ := fun h => h₂ (by rw [← h, Dart.symm_symm])
      have h₂' : d.symm ≠ d₀.symm := fun h => h₁ (by rw [← Dart.symm_symm d, h, Dart.symm_symm])
      rw [edgeWindingCell_of_ne G d₀ _ h₁' h₂', edgeWindingCell_of_ne G d₀ _ h₁ h₂]

/-- Start compatibility: every dart starts at `0`. -/
theorem edgeWindingCell_zero (d₀ d : G.Dart) : edgeWindingCell G d₀ d 0 = 0 := by
  by_cases h₁ : d = d₀
  · subst h₁
    rw [edgeWindingCell_self, Set.Icc.coe_zero, AddCircle.coe_zero]
  · by_cases h₂ : d = d₀.symm
    · subst h₂
      rw [edgeWindingCell_symm_self, Set.Icc.coe_zero, sub_zero]
      exact AddCircle.coe_period (1 : ℝ)
    · exact edgeWindingCell_of_ne G d₀ d h₁ h₂ 0

/-- The map winding the edge of `d₀` once around the circle and sending everything else to `0`. -/
def edgeWinding (d₀ : G.Dart) : C(Realization G, AddCircle (1 : ℝ)) :=
  continuousLift G (fun _ => 0) (edgeWindingCell G d₀) (edgeWindingCell_symm G d₀)
    (edgeWindingCell_zero G d₀)

@[simp] theorem edgeWinding_vertex (d₀ : G.Dart) (v : V) :
    edgeWinding G d₀ (vertex G v) = 0 := rfl

theorem edgeWinding_edgePoint (d₀ d : G.Dart) (t : unitInterval) :
    edgeWinding G d₀ (edgePoint G d t) = edgeWindingCell G d₀ d t := rfl

/-- On the selected dart, the winding map is the class of the parameter. -/
theorem edgeWinding_edgePoint_self (d₀ : G.Dart) (t : unitInterval) :
    edgeWinding G d₀ (edgePoint G d₀ t) = ((t : ℝ) : AddCircle (1 : ℝ)) :=
  edgeWindingCell_self G d₀ t

/-- On the reversed dart, the winding map is the class of the reversed parameter. -/
theorem edgeWinding_edgePoint_symm_self (d₀ : G.Dart) (t : unitInterval) :
    edgeWinding G d₀ (edgePoint G d₀.symm t) = ((1 - (t : ℝ) : ℝ) : AddCircle (1 : ℝ)) :=
  edgeWindingCell_symm_self G d₀ t

/-- On every dart other than `d₀` and `d₀.symm`, the winding map is `0`. -/
theorem edgeWinding_edgePoint_of_ne (d₀ d : G.Dart) (hd : d ≠ d₀) (hd' : d ≠ d₀.symm)
    (t : unitInterval) : edgeWinding G d₀ (edgePoint G d t) = 0 :=
  edgeWindingCell_of_ne G d₀ d hd hd' t

/-- On every dart whose unoriented edge differs from that of `d₀`, the winding map is `0`. -/
theorem edgeWinding_edgePoint_of_edge_ne (d₀ d : G.Dart) (hd : d.edge ≠ d₀.edge)
    (t : unitInterval) : edgeWinding G d₀ (edgePoint G d t) = 0 :=
  edgeWinding_edgePoint_of_ne G d₀ d (fun h => hd (by rw [h]))
    (fun h => hd (by rw [h, Dart.edge_symm])) t

/-- Endpoint compatibility at the start of the selected dart. -/
theorem edgeWinding_edgePoint_self_zero (d₀ : G.Dart) :
    edgeWinding G d₀ (edgePoint G d₀ 0) = 0 :=
  edgeWindingCell_zero G d₀ d₀

/-- Endpoint compatibility at the end of the selected dart: the class of `1` is `0`. -/
theorem edgeWinding_edgePoint_self_one (d₀ : G.Dart) :
    edgeWinding G d₀ (edgePoint G d₀ 1) = 0 := by
  rw [edgeWinding_edgePoint_self, Set.Icc.coe_one]
  exact AddCircle.coe_period (1 : ℝ)

/-- Endpoint compatibility at the start of the reversed dart: the class of `1 - 0` is `0`. -/
theorem edgeWinding_edgePoint_symm_self_zero (d₀ : G.Dart) :
    edgeWinding G d₀ (edgePoint G d₀.symm 0) = 0 :=
  edgeWindingCell_zero G d₀ d₀.symm

/-- Endpoint compatibility at the end of the reversed dart. -/
theorem edgeWinding_edgePoint_symm_self_one (d₀ : G.Dart) :
    edgeWinding G d₀ (edgePoint G d₀.symm 1) = 0 := by
  rw [edgeWinding_edgePoint_symm_self, Set.Icc.coe_one, sub_self, AddCircle.coe_zero]

/-! ### Deleted-edge return walks -/

/-- The winding map vanishes along every walk of `G.deleteEdges {d₀.edge}` mapped into `G`: each
traversed dart has unoriented edge different from that of `d₀`. -/
theorem edgeWinding_walkPath_deleteEdges (d₀ : G.Dart) {a b : V}
    (q : (G.deleteEdges {d₀.edge}).Walk a b) (t : unitInterval) :
    edgeWinding G d₀ (walkPath G (q.mapLe (G.deleteEdges_le {d₀.edge})) t) = 0 := by
  induction q generalizing t with
  | nil => exact edgeWinding_vertex G d₀ _
  | @cons a c b hac p ih =>
    change edgeWinding G d₀
      ((edgePath G ⟨(a, c), G.deleteEdges_le _ hac⟩).trans
        (walkPath G (p.mapLe (G.deleteEdges_le _))) t) = 0
    rw [Path.trans_apply]
    split_ifs
    · have hne : s(a, c) ≠ d₀.edge := by
        simpa only [Set.mem_singleton_iff] using (deleteEdges_adj.mp hac).2
      exact edgeWinding_edgePoint_of_edge_ne G d₀ ⟨(a, c), G.deleteEdges_le _ hac⟩ hne _
    · exact ih _

/-- The loop at `vertex G d₀.fst` running along `d₀` and back along a deleted-edge walk. -/
def returnLoop (d₀ : G.Dart) (q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst) :
    Path (vertex G d₀.fst) (vertex G d₀.fst) :=
  (edgePath G d₀).trans (walkPath G (q.mapLe (G.deleteEdges_le {d₀.edge})))

theorem returnLoop_eq (d₀ : G.Dart) (q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst) :
    returnLoop G d₀ q =
      (edgePath G d₀).trans (walkPath G (q.mapLe (G.deleteEdges_le {d₀.edge}))) := rfl

/-- The lift of the winding of a return loop: `s ↦ min (2 * s) 1`. -/
def returnLift : C(unitInterval, ℝ) := ⟨fun s => min (2 * (s : ℝ)) 1, by fun_prop⟩

theorem returnLift_apply (s : unitInterval) : returnLift s = min (2 * (s : ℝ)) 1 := rfl

theorem returnLift_of_le {s : unitInterval} (hs : (s : ℝ) ≤ 1 / 2) :
    returnLift s = 2 * (s : ℝ) :=
  min_eq_left (by linarith)

theorem returnLift_of_ge {s : unitInterval} (hs : 1 / 2 ≤ (s : ℝ)) : returnLift s = 1 :=
  min_eq_right (by linarith)

theorem returnLift_zero : returnLift 0 = 0 := by
  rw [returnLift_of_le (by norm_num)]
  simp

theorem returnLift_one : returnLift 1 = 1 :=
  returnLift_of_ge (by norm_num)

/-- Along the return loop, the winding map is the class of `min (2 * s) 1`: one full turn along
`d₀`, then constant along the return walk. -/
theorem edgeWinding_returnLoop (d₀ : G.Dart) (q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst)
    (s : unitInterval) :
    edgeWinding G d₀ (returnLoop G d₀ q s) = ((returnLift s : ℝ) : AddCircle (1 : ℝ)) := by
  rw [returnLoop, Path.trans_apply]
  split_ifs with hs
  · rw [returnLift_of_le hs]
    exact edgeWinding_edgePoint_self G d₀ _
  · rw [returnLift_of_ge (not_le.mp hs).le, edgeWinding_walkPath_deleteEdges]
    exact (AddCircle.coe_period (1 : ℝ)).symm

theorem edgeWinding_returnLoop_zero (d₀ : G.Dart)
    (q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst) :
    ((returnLoop G d₀ q).map (edgeWinding G d₀).continuous) 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) :=
  ((returnLoop G d₀ q).map (edgeWinding G d₀).continuous).source.trans (edgeWinding_vertex G d₀ _)

/-- `returnLift` is the lift, through the covering `ℝ → AddCircle (1 : ℝ)` and starting at `0`,
of the winding of the return loop. -/
theorem returnLift_eq_liftPath (d₀ : G.Dart)
    (q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst) :
    returnLift = (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath
      ((returnLoop G d₀ q).map (edgeWinding G d₀).continuous).toContinuousMap 0
      (edgeWinding_returnLoop_zero G d₀ q) :=
  ((AddCircle.isCoveringMap_coe (1 : ℝ)).eq_liftPath_iff' _).2
    ⟨_root_.funext fun s => (edgeWinding_returnLoop G d₀ q s).symm, returnLift_zero⟩

/-- **The return loop is not null-homotopic.** It is not homotopic, with fixed endpoints, to the
constant loop: lifted through the winding map, it ends at `1` and the constant loop at `0`. -/
theorem not_homotopic_returnLoop (d₀ : G.Dart)
    (q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst) :
    ¬ (returnLoop G d₀ q).Homotopic (Path.refl (vertex G d₀.fst)) := by
  intro hh
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let pγ := (returnLoop G d₀ q).map (edgeWinding G d₀).continuous
  let pγ₀ := (Path.refl (vertex G d₀.fst)).map (edgeWinding G d₀).continuous
  have h0 : pγ 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := edgeWinding_returnLoop_zero G d₀ q
  have h0' : pγ₀ 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := edgeWinding_vertex G d₀ d₀.fst
  have hhom : pγ.toContinuousMap.HomotopicRel pγ₀.toContinuousMap {0, 1} :=
    hh.map (edgeWinding G d₀)
  have hend : cov.liftPath pγ.toContinuousMap 0 h0 1 = cov.liftPath pγ₀.toContinuousMap 0 h0' 1 :=
    cov.liftPath_apply_one_eq_of_homotopicRel hhom 0 h0 h0'
  have hleft : cov.liftPath pγ.toContinuousMap 0 h0 1 = 1 := by
    rw [← returnLift_eq_liftPath G d₀ q]
    exact returnLift_one
  have hright : cov.liftPath pγ₀.toContinuousMap 0 h0' 1 = 0 := by
    have hc : ContinuousMap.const unitInterval (0 : ℝ) = cov.liftPath pγ₀.toContinuousMap 0 h0' :=
      (cov.eq_liftPath_iff' _).2
        ⟨_root_.funext fun _ => (edgeWinding_vertex G d₀ d₀.fst).symm, rfl⟩
    rw [← hc]
    rfl
  exact one_ne_zero (hleft.symm.trans (hend.trans hright))

/-! ### Graph consequences -/

/-- A deleted-edge return walk obstructs simple connectivity of the realization. -/
theorem not_simplyConnectedSpace_of_returnWalk (d₀ : G.Dart)
    (q : (G.deleteEdges {d₀.edge}).Walk d₀.snd d₀.fst) :
    ¬ SimplyConnectedSpace (Realization G) := fun _ =>
  not_homotopic_returnLoop G d₀ q (SimplyConnectedSpace.paths_homotopic _ _)

/-- **Cycle obstruction.** A graph with simply connected realization is acyclic: every edge is a
bridge, since a return walk avoiding it would give a loop that is not null-homotopic. -/
theorem isAcyclic_of_simplyConnectedSpace (h : SimplyConnectedSpace (Realization G)) :
    G.IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [isBridge_iff]
  intro hreach
  let d₀ : G.Dart := ⟨(u, v), huv⟩
  obtain ⟨q⟩ : (G.deleteEdges {d₀.edge}).Reachable d₀.snd d₀.fst := hreach.symm
  exact not_simplyConnectedSpace_of_returnWalk G d₀ q h

/-- **Necessary tree condition.** A graph with simply connected realization is a tree. Its
connectedness, including nonemptiness, comes from path connectedness of the realization. -/
theorem isTree_of_simplyConnectedSpace (h : SimplyConnectedSpace (Realization G)) :
    G.IsTree :=
  ⟨(connected_iff_pathConnectedSpace G).2 inferInstance, isAcyclic_of_simplyConnectedSpace G h⟩

/-- A graph that is not a tree has a realization that is not simply connected. -/
theorem not_simplyConnectedSpace_of_not_isTree (hG : ¬ G.IsTree) :
    ¬ SimplyConnectedSpace (Realization G) := fun h =>
  hG (isTree_of_simplyConnectedSpace G h)

end

end TDA.Reeb.GraphCycleObstruction
