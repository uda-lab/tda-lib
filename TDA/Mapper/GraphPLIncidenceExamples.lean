import TDA.Mapper.GraphPLIncidence
import Mathlib.Data.Fin.VecNotation

/-!
# Executed graph-PL incidence extraction

Each fixture states the complete value of `HeightGraph.incidence?`.

* `empty`: no vertex; the dummy level `0`, no cell and no edge.
* `single`, `apart`: one vertex; two isolated vertices at different heights.
* `flat`: a horizontal edge; one level, one component, no spanning edge.
* `vee`: two vertices of the same height that are not joined at their level, both joined to a
  lower vertex.
* `crossing`: an edge crossing an intermediate level that carries an isolated vertex.
* `diamond`: a cycle.
* `triangle`: two distinct edges over one gap with the same two endpoint cells; both entries are
  present.
* `bent`: a level component of three vertices whose least index is not adjacent to all of them,
  so that one propagation round does not suffice; its label equality is transferred to
  reachability in the actual induced level graph.
* `oneWay`, `loop`: invalid adjacency, reported as `none`.
-/

set_option autoImplicit false

namespace TDA.Mapper.GraphPL.GraphPLIncidenceExamples

open HeightGraph

/-- Symmetric adjacency on vertex numbers from a list of edges. -/
def edgeAdj {N : ℕ} (E : List (ℕ × ℕ)) (u w : Fin N) : Bool :=
  E.contains (u.1, w.1) || E.contains (w.1, u.1)

/-- No vertex. -/
def empty : HeightGraph 0 := ⟨fun _ _ => false, fun i => i.elim0⟩

theorem empty_incidence : empty.incidence? = some ⟨[0], [[]], []⟩ := by decide +kernel

/-- One vertex. -/
def single : HeightGraph 1 := ⟨fun _ _ => false, fun _ => 3⟩

theorem single_incidence : single.incidence? = some ⟨[3], [[.inl 0]], []⟩ := by decide +kernel

/-- Two isolated vertices at different heights. -/
def apart : HeightGraph 2 := ⟨fun _ _ => false, ![0, 1]⟩

theorem apart_incidence : apart.incidence? = some ⟨[0, 1], [[.inl 0], [.inl 1]], [[]]⟩ := by
  decide +kernel

/-- A horizontal edge. -/
def flat : HeightGraph 2 := ⟨edgeAdj [(0, 1)], ![0, 0]⟩

theorem flat_incidence : flat.incidence? = some ⟨[0], [[.inl 0]], []⟩ := by decide +kernel

/-- Vertices `0` and `1` at height `1`, not joined; both joined to vertex `2` at height `0`. -/
def vee : HeightGraph 3 := ⟨edgeAdj [(0, 2), (1, 2)], ![1, 1, 0]⟩

theorem vee_incidence :
    vee.incidence? = some ⟨[0, 1], [[.inl 2], [.inl 0, .inl 1]],
      [[((2, 0), .inl 2, .inl 0), ((2, 1), .inl 2, .inl 1)]]⟩ := by
  decide +kernel

/-- An edge from height `0` to height `2`, and an isolated vertex at height `1`. -/
def crossing : HeightGraph 3 := ⟨edgeAdj [(0, 1)], ![0, 2, 1]⟩

theorem crossing_incidence :
    crossing.incidence? = some ⟨[0, 1, 2], [[.inl 0], [.inl 2, .inr (0, 1)], [.inl 1]],
      [[((0, 1), .inl 0, .inr (0, 1))], [((0, 1), .inr (0, 1), .inl 1)]]⟩ := by
  decide +kernel

/-- A four-cycle with heights `0, 1, 1, 2`. -/
def diamond : HeightGraph 4 := ⟨edgeAdj [(0, 1), (0, 2), (1, 3), (2, 3)], ![0, 1, 1, 2]⟩

theorem diamond_incidence :
    diamond.incidence? = some ⟨[0, 1, 2], [[.inl 0], [.inl 1, .inl 2], [.inl 3]],
      [[((0, 1), .inl 0, .inl 1), ((0, 2), .inl 0, .inl 2)],
        [((1, 3), .inl 1, .inl 3), ((2, 3), .inl 2, .inl 3)]]⟩ := by
  decide +kernel

/-- A triangle with one vertex at height `0` and a horizontal edge at height `1`. -/
def triangle : HeightGraph 3 := ⟨edgeAdj [(0, 1), (0, 2), (1, 2)], ![0, 1, 1]⟩

theorem triangle_incidence :
    triangle.incidence? = some ⟨[0, 1], [[.inl 0], [.inl 1]],
      [[((0, 1), .inl 0, .inl 1), ((0, 2), .inl 0, .inl 1)]]⟩ := by
  decide +kernel

/-- Both edges of the triangle over the gap are listed. -/
theorem triangle_edgeList :
    triangle.edgeList 0 1 = [((0, 1), .inl 0, .inl 1), ((0, 2), .inl 0, .inl 1)] := by
  decide +kernel

/-- The two listed edges have the same two endpoint cells. -/
theorem triangle_parallel :
    (triangle.edgeList 0 1).map Prod.snd = [(.inl 0, .inl 1), (.inl 0, .inl 1)] := by
  decide +kernel

/-- Vertices `0, 1, 2` at height `0` joined as the path `0 — 2 — 1`, and vertex `3` above. -/
def bent : HeightGraph 4 := ⟨edgeAdj [(0, 2), (2, 1), (1, 3)], ![0, 0, 0, 5]⟩

theorem bent_valid : bent.Valid := by decide +kernel

theorem bent_incidence :
    bent.incidence? = some ⟨[0, 5], [[.inl 0], [.inl 3]], [[((1, 3), .inl 0, .inl 3)]]⟩ := by
  decide +kernel

/-- One propagation round leaves vertex `1` with its own label. -/
theorem bent_one_round : (bent.relax (Vector.ofFn id)).toList = [0, 1, 0, 3] := by decide +kernel

theorem bent_labels : bent.labels.toList = [0, 0, 0, 3] := by decide +kernel

theorem bent_height_zero : bent.height 0 = 0 := by decide +kernel

theorem bent_height_one : bent.height 1 = 0 := by decide +kernel

/-- Vertices `0` and `1` are joined in the actual graph induced on the height-`0` vertices. -/
theorem bent_reachable :
    ((bent.graph bent_valid).induce {v | bent.realHeight v = ((0 : ℚ) : ℝ)}).Reachable
      ⟨0, bent.realHeight_eq_iff.2 bent_height_zero⟩
      ⟨1, bent.realHeight_eq_iff.2 bent_height_one⟩ :=
  (bent.label_eq_label_iff_reachable bent_valid bent_height_zero bent_height_one).1
    (by decide +kernel)

/-- An asymmetric adjacency. -/
def oneWay : HeightGraph 2 := ⟨fun u w => decide (u.1 = 0 ∧ w.1 = 1), ![0, 1]⟩

theorem oneWay_incidence : oneWay.incidence? = none := by decide +kernel

/-- A loop. -/
def loop : HeightGraph 1 := ⟨fun _ _ => true, ![0]⟩

theorem loop_incidence : loop.incidence? = none := by decide +kernel

end TDA.Mapper.GraphPL.GraphPLIncidenceExamples
