import Mathlib.Data.Fintype.Basic

/-!
# Finite incidence data over critical levels

`FiniteReebData n` is the finite combinatorial data of de Silva–Munch–Patel, Notation 3.11, over
`n + 1` levels: finite vertex types `V i` for `i : Fin (n + 1)`, finite edge types `E e` for
`e : Fin n`, and endpoint functions `left e : E e → V e.castSucc` and
`right e : E e → V e.succ`. The direction is from edges to vertices. Empty types, isolated
vertices, parallel edges and noninjective endpoint functions are all allowed. Finiteness is
recorded by `Finite` fields; no enumeration is chosen.

A map of finite data (`Hom`, DMP Proposition 3.12) consists of functions on vertices and edges
commuting with both endpoint functions. Maps compose (`Hom.comp`) with identities (`Hom.id`).
A map whose vertex and edge functions are all bijective has an inverse map (`Hom.inv`), whose
incidence equations follow from those of the map (`Hom.comp_inv`, `Hom.inv_comp`).

The data are indexed by the number of gaps `n`, not by the levels themselves; the heights enter
only where the data are compared with a cosheaf or a space. See
`docs/math/reeb-constructible-cosheaf.md`.
-/

universe u

namespace TDA.Reeb

/-- Finite incidence data over `n + 1` levels: finite vertex types `V i`, finite edge types
`E e`, and endpoint functions `E e → V e.castSucc`, `E e → V e.succ` (direction `E → V`).
Empty types, isolated vertices, parallel edges and noninjective endpoints are all permitted. -/
structure FiniteReebData (n : ℕ) : Type (u + 1) where
  /-- Vertex types, one per level. -/
  V : Fin (n + 1) → Type u
  /-- Edge types, one per regular gap. -/
  E : Fin n → Type u
  /-- Every vertex type is finite. -/
  finiteV : ∀ i, Finite (V i)
  /-- Every edge type is finite. -/
  finiteE : ∀ e, Finite (E e)
  /-- Left endpoint of an edge. -/
  left : ∀ e, E e → V e.castSucc
  /-- Right endpoint of an edge. -/
  right : ∀ e, E e → V e.succ

namespace FiniteReebData

variable {n : ℕ}

/-- Finiteness of the vertex types as an instance. -/
instance instFiniteV (D : FiniteReebData.{u} n) (i : Fin (n + 1)) : Finite (D.V i) :=
  D.finiteV i

/-- Finiteness of the edge types as an instance. -/
instance instFiniteE (D : FiniteReebData.{u} n) (e : Fin n) : Finite (D.E e) :=
  D.finiteE e

/-- Maps of finite data: functions on vertices and edges commuting with both endpoint maps. -/
@[ext]
structure Hom (D D' : FiniteReebData.{u} n) where
  /-- Vertex components. -/
  v : ∀ i, D.V i → D'.V i
  /-- Edge components. -/
  e : ∀ i, D.E i → D'.E i
  /-- Compatibility with the left endpoints. -/
  left_comm : ∀ i x, D'.left i (e i x) = v i.castSucc (D.left i x)
  /-- Compatibility with the right endpoints. -/
  right_comm : ∀ i x, D'.right i (e i x) = v i.succ (D.right i x)

namespace Hom

variable {D D' D'' : FiniteReebData.{u} n}

/-- The identity map of finite data. -/
def id (D : FiniteReebData.{u} n) : Hom D D :=
  ⟨fun _ => _root_.id, fun _ => _root_.id, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Composition of maps of finite data, `φ` first. -/
def comp (φ : Hom D D') (ψ : Hom D' D'') : Hom D D'' where
  v i := ψ.v i ∘ φ.v i
  e i := ψ.e i ∘ φ.e i
  left_comm i x := (ψ.left_comm i _).trans (congrArg _ (φ.left_comm i x))
  right_comm i x := (ψ.right_comm i _).trans (congrArg _ (φ.right_comm i x))

/-- Inverse finite map from componentwise bijections; both incidence equations are proved
algebraically from those of `φ`. -/
noncomputable def inv (φ : Hom D D') (hv : ∀ i, Function.Bijective (φ.v i))
    (he : ∀ i, Function.Bijective (φ.e i)) : Hom D' D where
  v i := (Equiv.ofBijective _ (hv i)).symm
  e i := (Equiv.ofBijective _ (he i)).symm
  left_comm i y := (hv i.castSucc).injective (by
    rw [← φ.left_comm, Equiv.ofBijective_apply_symm_apply _ (he i),
      Equiv.ofBijective_apply_symm_apply _ (hv i.castSucc)])
  right_comm i y := (hv i.succ).injective (by
    rw [← φ.right_comm, Equiv.ofBijective_apply_symm_apply _ (he i),
      Equiv.ofBijective_apply_symm_apply _ (hv i.succ)])

theorem comp_inv (φ : Hom D D') (hv : ∀ i, Function.Bijective (φ.v i))
    (he : ∀ i, Function.Bijective (φ.e i)) : φ.comp (φ.inv hv he) = Hom.id D :=
  Hom.ext (funext fun i => funext fun x => Equiv.ofBijective_symm_apply_apply _ (hv i) x)
    (funext fun i => funext fun x => Equiv.ofBijective_symm_apply_apply _ (he i) x)

theorem inv_comp (φ : Hom D D') (hv : ∀ i, Function.Bijective (φ.v i))
    (he : ∀ i, Function.Bijective (φ.e i)) : (φ.inv hv he).comp φ = Hom.id D' :=
  Hom.ext (funext fun i => funext fun x => Equiv.ofBijective_apply_symm_apply _ (hv i) x)
    (funext fun i => funext fun x => Equiv.ofBijective_apply_symm_apply _ (he i) x)

end Hom

end FiniteReebData

end TDA.Reeb
