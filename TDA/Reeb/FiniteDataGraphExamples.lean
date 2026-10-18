import TDA.Reeb.FiniteDataGraph
import TDA.Reeb.RGraphExamples

/-!
# Fixtures for incidence quivers and graphs of finite Reeb data

These fixtures cover a single edge, parallel edges, isolated vertices, the four-edge cycle,
and empty finite Reeb data.  They record both the information retained by the incidence graph
and the information lost when parallel incidence arrows are forgotten.
-/

open CategoryTheory

namespace TDA.Reeb.Examples.FiniteDataGraph

open TDA.Reeb TDA.Reeb.RGraph.Examples TDA.Reeb.Examples.Cylinder

/-! ### G1: a single edge -/

/-- The two vertices of `singleEdge` are adjacent in its incidence graph. -/
theorem single_adj :
    singleEdge.incidenceGraph.Adj
      (⟨0, ()⟩ : singleEdge.IncidenceVertex) ⟨1, ()⟩ := by
  change singleEdge.incidenceGraph.Adj
    (⟨(0 : Fin 1).castSucc, ()⟩ : singleEdge.IncidenceVertex)
    ⟨(0 : Fin 1).succ, ()⟩
  exact (singleEdge.incidenceGraph_adj_castSucc_succ_iff 0 () ()).2 ⟨(), rfl, rfl⟩

/-- The single-edge incidence graph has one simple-graph edge. -/
theorem single_edgeCard : Nat.card singleEdge.incidenceGraph.edgeSet = 1 := by
  calc
    Nat.card singleEdge.incidenceGraph.edgeSet =
        ∑ e, Nat.card (singleEdge.E e) :=
      singleEdge.card_incidenceGraph_edgeSet_eq (by
        rw [singleEdge.incidenceEdgeSet_injective_iff]
        intro e x y _ _
        change Unit at x y
        exact Subsingleton.elim x y)
    _ = 1 := by simp [singleEdge]

/-- The single edge gives one arrow over the unique gap. -/
theorem single_homCard :
    Nat.card (Quiver.Hom (V := singleEdge.IncidenceVertex)
      ⟨0, ()⟩ ⟨1, ()⟩) = 1 := by
  have h := Nat.card_congr (singleEdge.homCastSuccSuccEquiv (0 : Fin 1) () ())
  simpa [singleEdge, Nat.card_eq_fintype_card] using h

/-! ### G2: parallel edges -/

/-- The two parallel arrows over the unique gap have cardinality two. -/
theorem parallel_homCard :
    Nat.card (Quiver.Hom (V := parallelData.IncidenceVertex)
      ⟨0, ()⟩ ⟨1, ()⟩) = 2 := by
  have h := Nat.card_congr (parallelData.homCastSuccSuccEquiv (0 : Fin 1) () ())
  simpa [parallelData, Nat.card_eq_fintype_card] using h

/-- The parallel-edge incidence graph forgets the multiplicity and has one edge. -/
theorem parallel_edgeCard : Nat.card parallelData.incidenceGraph.edgeSet = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨parallelData.incidenceEdgeSet ⟨0, false⟩, ?_⟩
  intro q
  obtain ⟨⟨e, x⟩, rfl⟩ := parallelData.incidenceEdgeSet_surjective q
  have he : e = 0 := Fin.eq_zero e
  subst e
  cases x <;> rfl

/-- The forgetful edge map is not injective for parallel edges. -/
theorem parallel_not_injective :
    ¬Function.Injective parallelData.incidenceEdgeSet := by
  intro h
  have heq : parallelData.incidenceEdgeSet
      ⟨(0 : Fin 1), false⟩ = parallelData.incidenceEdgeSet
      ⟨(0 : Fin 1), true⟩ := by
    apply Subtype.ext
    rfl
  have hp : (⟨(0 : Fin 1), false⟩ : parallelData.IncidenceEdge) =
      ⟨(0 : Fin 1), true⟩ := h heq
  exact Bool.false_ne_true (eq_of_heq (Sigma.mk.inj_iff.mp hp).2)

/-- The edge-count inequality is strict for parallel edges. -/
theorem parallel_card_lt :
    Nat.card parallelData.incidenceGraph.edgeSet <
      ∑ e, Nat.card (parallelData.E e) := by
  rw [parallel_edgeCard]
  simp [parallelData]

/-! ### G3: the graph is not a complete invariant -/

/-- The incidence graphs of the parallel-edge and single-edge data are isomorphic. -/
theorem parallel_graphIso :
    Nonempty (parallelData.incidenceGraph ≃g singleEdge.incidenceGraph) := by
  refine ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩
  intro x y
  change singleEdge.incidenceGraph.Adj x y ↔ parallelData.incidenceGraph.Adj x y
  rcases x with ⟨x, ⟨⟩⟩
  rcases y with ⟨y, ⟨⟩⟩
  have hsingle : singleEdge.incidenceGraph.Adj
      (⟨(0 : Fin 2), ()⟩ : singleEdge.IncidenceVertex) ⟨(1 : Fin 2), ()⟩ := by
    exact single_adj
  have hparallel : parallelData.incidenceGraph.Adj
      (⟨(0 : Fin 2), ()⟩ : parallelData.IncidenceVertex) ⟨(1 : Fin 2), ()⟩ := by
    change parallelData.incidenceGraph.Adj
      (⟨(0 : Fin 1).castSucc, ()⟩ : parallelData.IncidenceVertex)
      ⟨(0 : Fin 1).succ, ()⟩
    exact (parallelData.incidenceGraph_adj_castSucc_succ_iff 0 () ()).2
      ⟨false, rfl, rfl⟩
  fin_cases x <;> fin_cases y
  · constructor <;> intro h
    · exact (singleEdge.incidenceGraph.irrefl h).elim
    · exact (parallelData.incidenceGraph.irrefl h).elim
  · exact ⟨fun _ => hparallel, fun _ => hsingle⟩
  · exact ⟨fun h => (parallelData.incidenceGraph.adj_comm _ _).mp hparallel,
      fun h => (singleEdge.incidenceGraph.adj_comm _ _).mp hsingle⟩
  · constructor <;> intro h
    · exact (singleEdge.incidenceGraph.irrefl h).elim
    · exact (parallelData.incidenceGraph.irrefl h).elim

/-- The parallel and single-edge finite Reeb data are not isomorphic. -/
theorem parallel_not_iso_single : IsEmpty (parallelData ≅ singleEdge) :=
  ⟨fun i => Bool.false_ne_true
    (TDA.Reeb.RGraph.e_injective_of_iso i 0 (a₁ := false) (a₂ := true) rfl)⟩

/-! ### G4: the four-edge cycle -/

/-- The four edge cells of `cycleData` have pairwise distinct endpoint pairs. -/
theorem cycle_injective : Function.Injective cycleData.incidenceEdgeSet := by
  rw [cycleData.incidenceEdgeSet_injective_iff]
  intro e x y hleft hright
  fin_cases e
  · apply Fin.ext
    simpa [cycleData] using congrArg Fin.val hright
  · apply Fin.ext
    simpa [cycleData] using congrArg Fin.val hleft

/-- The cycle incidence graph has four simple-graph edges. -/
theorem cycle_edgeCard : Nat.card cycleData.incidenceGraph.edgeSet = 4 := by
  calc
    Nat.card cycleData.incidenceGraph.edgeSet =
        ∑ e, Nat.card (cycleData.E e) :=
      cycleData.card_incidenceGraph_edgeSet_eq cycle_injective
    _ = 4 := by simp [cycleData]

/-- Incidence vertices at levels two apart are not adjacent in the cycle. -/
theorem cycle_not_adj_02 :
    ¬cycleData.incidenceGraph.Adj
      (⟨0, (0 : Fin 1)⟩ : cycleData.IncidenceVertex)
      (⟨2, (0 : Fin 1)⟩ : cycleData.IncidenceVertex) := by
  intro h
  rcases cycleData.incidenceGraph_adj_level h with h | h
  · change ((0 : Fin 3) : ℕ) + 1 = ((2 : Fin 3) : ℕ) at h
    omega
  · change ((2 : Fin 3) : ℕ) + 1 = ((0 : Fin 3) : ℕ) at h
    omega

/-! ### G5: isolated vertices -/

/-- The `true` vertex at level zero of `isoData` is isolated. -/
theorem iso_isolated :
    ∀ y, ¬isoData.incidenceGraph.Adj
      (⟨0, true⟩ : isoData.IncidenceVertex) y := by
  intro y h
  rcases (isoData.incidenceGraph_adj_iff).mp h with hxy | hyx
  · obtain ⟨p⟩ := hxy
    have hs := congrArg (fun z : isoData.IncidenceVertex => z.2) p.2.1
    change false = true at hs
    exact Bool.false_ne_true hs
  · obtain ⟨p⟩ := hyx
    have ht := congrArg (fun z : isoData.IncidenceVertex => z.2) p.2.2
    change false = true at ht
    exact Bool.false_ne_true ht

/-! ### G6: empty finite Reeb data -/

/-- Every incidence vertex of `emptyData` is impossible. -/
theorem empty_isEmpty_vertex (n : ℕ) : IsEmpty (emptyData n).IncidenceVertex := by
  constructor
  intro x
  exact (show Empty from x.2).elim

/-- The incidence graph of empty finite Reeb data has no edges. -/
theorem empty_edgeCard (n : ℕ) :
    Nat.card (emptyData n).incidenceGraph.edgeSet = 0 := by
  apply (Nat.card_eq_zero).2
  left
  constructor
  intro q
  obtain ⟨p, _⟩ := (emptyData n).incidenceEdgeSet_surjective q
  exact (show Empty from p.2).elim

end TDA.Reeb.Examples.FiniteDataGraph
