import TDA.Reeb.RGraph
import Mathlib.Combinatorics.Quiver.Prefunctor
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Incidence quivers and graphs of finite Reeb data

For finite Reeb data, `IncidenceVertex` collects all level vertices and the incidence quiver
has one arrow for each edge, with its prescribed endpoints.  `incidenceGraph` is the simple
graph obtained by forgetting arrow orientation and parallel edges.  The constructions and their
properties below are library constructions; no source theorem is attributed to them.
-/

universe u

namespace TDA.Reeb.FiniteReebData

open CategoryTheory

variable {n : ℕ} (D : FiniteReebData.{u} n)

/-- Vertices of the incidence quiver: all level vertices. -/
def IncidenceVertex : Type u := Σ k : Fin (n + 1), D.V k

/-- All edges, over all gaps. -/
abbrev IncidenceEdge : Type u := Σ e : Fin n, D.E e

/-- The source vertex of an edge in the incidence quiver. -/
def incidenceSource (p : D.IncidenceEdge) : D.IncidenceVertex :=
  ⟨p.1.castSucc, D.left p.1 p.2⟩

/-- The target vertex of an edge in the incidence quiver. -/
def incidenceTarget (p : D.IncidenceEdge) : D.IncidenceVertex :=
  ⟨p.1.succ, D.right p.1 p.2⟩

/-- The incidence quiver: arrows are edges with prescribed source and target. -/
@[instance_reducible]
def incidenceQuiver : Quiver.{u} D.IncidenceVertex where
  Hom x y := {p : D.IncidenceEdge // D.incidenceSource p = x ∧ D.incidenceTarget p = y}

/-- The quiver instance carried by the incidence-vertex type synonym. -/
instance instQuiverIncidenceVertex : Quiver.{u} D.IncidenceVertex := D.incidenceQuiver

/-- The incidence-vertex type is finite. -/
instance instFiniteIncidenceVertex : Finite D.IncidenceVertex :=
  inferInstanceAs (Finite (Σ k : Fin (n + 1), D.V k))

/-- Every incidence hom type is finite. -/
instance instFiniteHom (x y : D.IncidenceVertex) : Finite (x ⟶ y) := by
  change Finite {p : D.IncidenceEdge // D.incidenceSource p = x ∧ D.incidenceTarget p = y}
  exact Subtype.finite

private theorem sigma_mk_castSucc_eq_iff {β : Fin (n + 1) → Type u} {i j : Fin n}
    {x : β i.castSucc} {y : β j.castSucc} :
    (⟨i.castSucc, x⟩ : Σ k, β k) = ⟨j.castSucc, y⟩ ↔ i = j ∧ HEq x y := by
  constructor
  · intro h
    have h' := Sigma.mk.inj_iff.mp h
    exact ⟨Fin.castSucc_injective _ h'.1, h'.2⟩
  · rintro ⟨rfl, h⟩
    exact Sigma.ext rfl h

private theorem sigma_mk_succ_eq_iff {β : Fin (n + 1) → Type u} {i j : Fin n}
    {x : β i.succ} {y : β j.succ} :
    (⟨i.succ, x⟩ : Σ k, β k) = ⟨j.succ, y⟩ ↔ i = j ∧ HEq x y := by
  constructor
  · intro h
    have h' := Sigma.mk.inj_iff.mp h
    exact ⟨Fin.succ_injective _ h'.1, h'.2⟩
  · rintro ⟨rfl, h⟩
    exact Sigma.ext rfl h

/-- Every arrow, over all source and target vertices, is one incidence edge. -/
def arrowTotalEquiv : (Σ x y : D.IncidenceVertex, x ⟶ y) ≃ D.IncidenceEdge where
  toFun p := p.2.2.1
  invFun p := ⟨D.incidenceSource p, D.incidenceTarget p, ⟨p, rfl, rfl⟩⟩
  left_inv := by
    rintro ⟨x, y, p⟩
    rcases p with ⟨p, hs, ht⟩
    cases hs
    cases ht
    rfl
  right_inv _ := rfl

/-- Arrows across a fixed gap are equivalent to edges with the indicated endpoints. -/
def homCastSuccSuccEquiv (e : Fin n) (v : D.V e.castSucc) (w : D.V e.succ) :
    Quiver.Hom (V := D.IncidenceVertex) ⟨e.castSucc, v⟩ ⟨e.succ, w⟩ ≃
      {x : D.E e // D.left e x = v ∧ D.right e x = w} where
  toFun p := by
    rcases p with ⟨⟨e', x⟩, hs, ht⟩
    change (⟨e'.castSucc, D.left e' x⟩ : D.IncidenceVertex) =
      ⟨e.castSucc, v⟩ at hs
    change (⟨e'.succ, D.right e' x⟩ : D.IncidenceVertex) =
      ⟨e.succ, w⟩ at ht
    have hs' : e' = e ∧ HEq (D.left e' x) v := by
      apply (sigma_mk_castSucc_eq_iff (β := D.V)).mp
      exact hs
    have ht' : e' = e ∧ HEq (D.right e' x) w := by
      apply (sigma_mk_succ_eq_iff (β := D.V)).mp
      exact ht
    have he : e' = e := hs'.1
    subst e'
    exact ⟨x, eq_of_heq hs'.2, eq_of_heq ht'.2⟩
  invFun x := ⟨⟨e, x.1⟩,
    congrArg (fun z => (⟨e.castSucc, z⟩ : D.IncidenceVertex)) x.2.1,
    congrArg (fun z => (⟨e.succ, z⟩ : D.IncidenceVertex)) x.2.2⟩
  left_inv := by
    rintro ⟨⟨e', x⟩, hs, ht⟩
    change (⟨e'.castSucc, D.left e' x⟩ : D.IncidenceVertex) =
      ⟨e.castSucc, v⟩ at hs
    have hs' : e' = e ∧ HEq (D.left e' x) v := by
      apply (sigma_mk_castSucc_eq_iff (β := D.V)).mp
      exact hs
    have he : e' = e := hs'.1
    subst e'
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨x, hx, hy⟩
    apply Subtype.ext
    rfl

/-- There are no arrows whose levels are not consecutive in the forward direction. -/
theorem isEmpty_hom_of_ne {x y : D.IncidenceVertex} (h : (x.1 : ℕ) + 1 ≠ y.1) :
    IsEmpty (x ⟶ y) := by
  constructor
  intro p
  apply h
  have hs := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) p.2.1
  have ht := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) p.2.2
  change (p.1.1.castSucc : ℕ) = (x.1 : ℕ) at hs
  change (p.1.1.succ : ℕ) = (y.1 : ℕ) at ht
  calc
    (x.1 : ℕ) + 1 = (p.1.1.castSucc : ℕ) + 1 := by rw [hs]
    _ = (p.1.1.succ : ℕ) := by simp only [Fin.val_castSucc, Fin.val_succ]
    _ = (y.1 : ℕ) := ht

/-- The incidence graph: distinct vertices joined by at least one edge. -/
def incidenceGraph : SimpleGraph D.IncidenceVertex :=
  SimpleGraph.fromRel fun x y => Nonempty (x ⟶ y)

/-- Adjacency in the incidence graph is witnessed by an arrow in either direction. -/
theorem incidenceGraph_adj_iff {x y : D.IncidenceVertex} :
    D.incidenceGraph.Adj x y ↔ Nonempty (x ⟶ y) ∨ Nonempty (y ⟶ x) := by
  rw [incidenceGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hxy⟩
    exact hxy
  · intro hxy
    refine ⟨?_, hxy⟩
    intro h
    subst y
    rcases hxy with hx | hx
    · obtain ⟨p⟩ := hx
      exact (isEmpty_hom_of_ne D (by omega) : IsEmpty (x ⟶ x)).false p
    · obtain ⟨p⟩ := hx
      exact (isEmpty_hom_of_ne D (by omega) : IsEmpty (x ⟶ x)).false p

/-- Adjacency across one gap is exactly the existence of an edge with those endpoints. -/
theorem incidenceGraph_adj_castSucc_succ_iff (e : Fin n) (v : D.V e.castSucc)
    (w : D.V e.succ) :
    D.incidenceGraph.Adj ⟨e.castSucc, v⟩ ⟨e.succ, w⟩ ↔
      ∃ x : D.E e, D.left e x = v ∧ D.right e x = w := by
  refine (D.incidenceGraph_adj_iff
    (x := (⟨e.castSucc, v⟩ : D.IncidenceVertex))
    (y := (⟨e.succ, w⟩ : D.IncidenceVertex))).trans ?_
  constructor
  · intro h
    rcases h with hxy | hyx
    · obtain ⟨p⟩ := hxy
      exact ⟨(D.homCastSuccSuccEquiv e v w p).1,
        (D.homCastSuccSuccEquiv e v w p).2⟩
    · obtain ⟨p⟩ := hyx
      exact ((isEmpty_hom_of_ne D (by
          change (e.succ : ℕ) + 1 ≠ (e.castSucc : ℕ)
          rw [Fin.val_succ, Fin.val_castSucc]
          omega) :
        IsEmpty (Quiver.Hom (V := D.IncidenceVertex) ⟨e.succ, w⟩ ⟨e.castSucc, v⟩)).false p).elim
  · rintro ⟨x, hx, hy⟩
    exact Or.inl ⟨(D.homCastSuccSuccEquiv e v w).symm ⟨x, hx, hy⟩⟩

/-- Adjacent incidence vertices have consecutive levels. -/
theorem incidenceGraph_adj_level {x y : D.IncidenceVertex} (h : D.incidenceGraph.Adj x y) :
    (x.1 : ℕ) + 1 = y.1 ∨ (y.1 : ℕ) + 1 = x.1 := by
  rcases (D.incidenceGraph_adj_iff).mp h with hxy | hyx
  · left
    obtain ⟨p⟩ := hxy
    have hs := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) p.2.1
    have ht := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) p.2.2
    change (p.1.1.castSucc : ℕ) = (x.1 : ℕ) at hs
    change (p.1.1.succ : ℕ) = (y.1 : ℕ) at ht
    calc
      (x.1 : ℕ) + 1 = (p.1.1.castSucc : ℕ) + 1 := by rw [hs]
      _ = (p.1.1.succ : ℕ) := by simp only [Fin.val_castSucc, Fin.val_succ]
      _ = (y.1 : ℕ) := ht
  · right
    obtain ⟨p⟩ := hyx
    have hs := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) p.2.1
    have ht := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) p.2.2
    change (p.1.1.castSucc : ℕ) = (y.1 : ℕ) at hs
    change (p.1.1.succ : ℕ) = (x.1 : ℕ) at ht
    calc
      (y.1 : ℕ) + 1 = (p.1.1.castSucc : ℕ) + 1 := by rw [hs]
      _ = (p.1.1.succ : ℕ) := by simp only [Fin.val_castSucc, Fin.val_succ]
      _ = (x.1 : ℕ) := ht

section Functoriality

variable {D D' D'' : FiniteReebData.{u} n}

/-- The level-preserving map on incidence vertices induced by a finite-data map. -/
def incidenceVertexMap (φ : D ⟶ D') : D.IncidenceVertex → D'.IncidenceVertex :=
  fun x => ⟨x.1, φ.v x.1 x.2⟩

/-- The quiver prefunctor induced by a finite-data map. -/
def incidencePrefunctor (φ : D ⟶ D') : D.IncidenceVertex ⥤q D'.IncidenceVertex where
  obj := incidenceVertexMap φ
  map := by
    intro x y p
    refine ⟨⟨p.1.1, φ.e p.1.1 p.1.2⟩, ?_, ?_⟩
    · calc
        D'.incidenceSource ⟨p.1.1, φ.e p.1.1 p.1.2⟩ =
            incidenceVertexMap φ (D.incidenceSource p.1) := by
              change (⟨p.1.1.castSucc, D'.left p.1.1 (φ.e p.1.1 p.1.2)⟩ :
                D'.IncidenceVertex) =
                ⟨p.1.1.castSucc, φ.v p.1.1.castSucc (D.left p.1.1 p.1.2)⟩
              exact congrArg
                (fun z => (⟨p.1.1.castSucc, z⟩ : D'.IncidenceVertex))
                (φ.left_comm p.1.1 p.1.2)
        _ = incidenceVertexMap φ x := congrArg (incidenceVertexMap φ) p.2.1
    · calc
        D'.incidenceTarget ⟨p.1.1, φ.e p.1.1 p.1.2⟩ =
            incidenceVertexMap φ (D.incidenceTarget p.1) := by
              change (⟨p.1.1.succ, D'.right p.1.1 (φ.e p.1.1 p.1.2)⟩ :
                D'.IncidenceVertex) =
                ⟨p.1.1.succ, φ.v p.1.1.succ (D.right p.1.1 p.1.2)⟩
              exact congrArg
                (fun z => (⟨p.1.1.succ, z⟩ : D'.IncidenceVertex))
                (φ.right_comm p.1.1 p.1.2)
        _ = incidenceVertexMap φ y := congrArg (incidenceVertexMap φ) p.2.2

/-- The simple-graph homomorphism induced by a finite-data map. -/
def incidenceGraphHom (φ : D ⟶ D') : D.incidenceGraph →g D'.incidenceGraph where
  toFun := incidenceVertexMap φ
  map_rel' := by
    intro x y hxy
    have hxy' := (D.incidenceGraph_adj_iff (x := x) (y := y)).mp hxy
    apply (D'.incidenceGraph_adj_iff
      (x := incidenceVertexMap φ x) (y := incidenceVertexMap φ y)).mpr
    rcases hxy' with hxy | hyx
    · obtain ⟨p⟩ := hxy
      exact Or.inl ⟨(D.incidencePrefunctor φ).map p⟩
    · obtain ⟨p⟩ := hyx
      exact Or.inr ⟨(D.incidencePrefunctor φ).map p⟩

/-- The incidence graph hom induced by an identity finite-data map is the identity. -/
theorem incidenceGraphHom_id : incidenceGraphHom (𝟙 D) = SimpleGraph.Hom.id := by
  ext x
  rfl

/-- Incidence graph homomorphisms compose covariantly with finite-data maps. -/
theorem incidenceGraphHom_comp (φ : D ⟶ D') (ψ : D' ⟶ D'') :
    incidenceGraphHom (φ ≫ ψ) = (incidenceGraphHom ψ).comp (incidenceGraphHom φ) := by
  ext x
  rfl

/-- The incidence graphs of isomorphic finite Reeb data are graph-isomorphic. -/
def incidenceGraphIso (i : D ≅ D') : D.incidenceGraph ≃g D'.incidenceGraph := by
  let e : D.IncidenceVertex ≃ D'.IncidenceVertex :=
    { toFun := incidenceVertexMap i.hom
      invFun := incidenceVertexMap i.inv
      left_inv := by
        intro z
        cases z with
        | mk k x =>
          change (⟨k, i.inv.v k (i.hom.v k x)⟩ : D.IncidenceVertex) = ⟨k, x⟩
          have hc := congrArg (fun φ : D ⟶ D => φ.v k) i.hom_inv_id
          exact congrArg (fun y => (⟨k, y⟩ : D.IncidenceVertex)) (congrFun hc x)
      right_inv := by
        intro z
        cases z with
        | mk k x =>
          change (⟨k, i.hom.v k (i.inv.v k x)⟩ : D'.IncidenceVertex) = ⟨k, x⟩
          have hc := congrArg (fun φ : D' ⟶ D' => φ.v k) i.inv_hom_id
          exact congrArg (fun y => (⟨k, y⟩ : D'.IncidenceVertex)) (congrFun hc x) }
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro x y
  change D'.incidenceGraph.Adj (incidenceVertexMap i.hom x) (incidenceVertexMap i.hom y) ↔
    D.incidenceGraph.Adj x y
  constructor
  · intro hxy
    have hxy' := (incidenceGraphHom i.inv).map_rel' hxy
    change D.incidenceGraph.Adj
      (incidenceVertexMap i.inv (incidenceVertexMap i.hom x))
      (incidenceVertexMap i.inv (incidenceVertexMap i.hom y)) at hxy'
    have hx : incidenceVertexMap i.inv (incidenceVertexMap i.hom x) = x := e.symm_apply_apply x
    have hy : incidenceVertexMap i.inv (incidenceVertexMap i.hom y) = y := e.symm_apply_apply y
    simpa only [hx, hy] using hxy'
  · intro hxy
    exact (incidenceGraphHom i.hom).map_rel' hxy

end Functoriality

/-- The simple-graph edge represented by an incidence edge. -/
def incidenceEdgeSet (p : D.IncidenceEdge) : D.incidenceGraph.edgeSet :=
  ⟨s(D.incidenceSource p, D.incidenceTarget p), by
    rw [SimpleGraph.mem_edgeSet]
    exact (D.incidenceGraph_adj_iff).2 (Or.inl ⟨⟨p, rfl, rfl⟩⟩)⟩

/-- Every simple-graph edge is represented by an incidence edge. -/
theorem incidenceEdgeSet_surjective : Function.Surjective D.incidenceEdgeSet := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    rcases (D.incidenceGraph_adj_iff).mp he with hxy | hyx
    · obtain ⟨p⟩ := hxy
      refine ⟨p.1, ?_⟩
      apply Subtype.ext
      exact congrArg₂ (fun a b => s(a, b)) p.2.1 p.2.2
    · obtain ⟨p⟩ := hyx
      refine ⟨p.1, ?_⟩
      apply Subtype.ext
      exact (congrArg₂ (fun a b => s(a, b)) p.2.1 p.2.2).trans Sym2.eq_swap

/-- Injectivity of the forgetful edge map is equivalent to absence of parallel endpoints. -/
theorem incidenceEdgeSet_injective_iff :
    Function.Injective D.incidenceEdgeSet ↔
      ∀ e (x y : D.E e), D.left e x = D.left e y → D.right e x = D.right e y → x = y := by
  constructor
  · intro hinj e x y hleft hright
    have hs : D.incidenceSource ⟨e, x⟩ = D.incidenceSource ⟨e, y⟩ := by
      change (⟨e.castSucc, D.left e x⟩ : D.IncidenceVertex) =
        ⟨e.castSucc, D.left e y⟩
      exact congrArg (fun z => (⟨e.castSucc, z⟩ : D.IncidenceVertex)) hleft
    have ht : D.incidenceTarget ⟨e, x⟩ = D.incidenceTarget ⟨e, y⟩ := by
      change (⟨e.succ, D.right e x⟩ : D.IncidenceVertex) =
        ⟨e.succ, D.right e y⟩
      exact congrArg (fun z => (⟨e.succ, z⟩ : D.IncidenceVertex)) hright
    have hp : D.incidenceEdgeSet ⟨e, x⟩ = D.incidenceEdgeSet ⟨e, y⟩ := by
      apply Subtype.ext
      exact congrArg₂ (fun a b => s(a, b)) hs ht
    exact eq_of_heq (Sigma.mk.inj_iff.mp (hinj hp)).2
  · intro hcond p q hpq
    rcases p with ⟨e, x⟩
    rcases q with ⟨e', y⟩
    have hpq' : s(D.incidenceSource ⟨e, x⟩, D.incidenceTarget ⟨e, x⟩) =
        s(D.incidenceSource ⟨e', y⟩, D.incidenceTarget ⟨e', y⟩) :=
      congrArg Subtype.val hpq
    rw [Sym2.eq_iff] at hpq'
    rcases hpq' with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · change (⟨e.castSucc, D.left e x⟩ : D.IncidenceVertex) =
        ⟨e'.castSucc, D.left e' y⟩ at hs
      change (⟨e.succ, D.right e x⟩ : D.IncidenceVertex) =
        ⟨e'.succ, D.right e' y⟩ at ht
      have he : e = e' := Fin.castSucc_injective _
        (congrArg (fun z : D.IncidenceVertex => z.1) hs)
      subst e'
      have hleft : D.left e x = D.left e y := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      have hright : D.right e x = D.right e y := eq_of_heq (Sigma.mk.inj_iff.mp ht).2
      exact congrArg (fun z => (⟨e, z⟩ : D.IncidenceEdge)) (hcond e x y hleft hright)
    · change (⟨e.castSucc, D.left e x⟩ : D.IncidenceVertex) =
        ⟨e'.succ, D.right e' y⟩ at hs
      change (⟨e.succ, D.right e x⟩ : D.IncidenceVertex) =
        ⟨e'.castSucc, D.left e' y⟩ at ht
      have hlevel := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) hs
      have hlevel' := congrArg (fun z : D.IncidenceVertex => (z.1 : ℕ)) ht
      simp only [Fin.val_succ, Fin.val_castSucc] at hlevel hlevel'
      omega

/-- The incidence graph edge set is finite. -/
instance instFiniteEdgeSet : Finite D.incidenceGraph.edgeSet :=
  Finite.of_surjective D.incidenceEdgeSet (incidenceEdgeSet_surjective D)

/-- The simple-graph edge count is bounded by the total number of incidence edges. -/
theorem card_incidenceGraph_edgeSet_le :
    Nat.card D.incidenceGraph.edgeSet ≤ ∑ e, Nat.card (D.E e) := by
  have h := Nat.card_le_card_of_surjective D.incidenceEdgeSet
    (incidenceEdgeSet_surjective D)
  simpa only [Nat.card_sigma] using h

/-- If no parallel incidence edges are present, the simple-graph edge count is exact. -/
theorem card_incidenceGraph_edgeSet_eq (h : Function.Injective D.incidenceEdgeSet) :
    Nat.card D.incidenceGraph.edgeSet = ∑ e, Nat.card (D.E e) := by
  calc
    Nat.card D.incidenceGraph.edgeSet = Nat.card D.IncidenceEdge :=
      (Nat.card_congr (Equiv.ofBijective D.incidenceEdgeSet
        ⟨h, incidenceEdgeSet_surjective D⟩)).symm
    _ = ∑ e, Nat.card (D.E e) := Nat.card_sigma

end TDA.Reeb.FiniteReebData
