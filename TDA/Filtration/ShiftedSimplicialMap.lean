import TDA.Filtration.Basic
import TDA.Simplicial.Contiguity
import Mathlib.Data.Rel
import Mathlib.Logic.Relator
import Mathlib.Data.Real.Basic

/-!
# Shifted simplicial functions and multivalued maps

A global function preserves faces with shift ε when its image of every face at t is a face
at t + ε. A native set relation is simplicial with that shift when every nonempty finite
subset of the relational image of a face is a target face. Totality on all ambient vertices
is kept separate from this face condition, including vertices outside the filtration support.
The shift ε is any real number; relational images need not be finite.

Faces here are nonempty. Adjoining only the empty simplex to both face collections recovers
the empty-subset convention of CDSO Definition 3.2, without inserting any ghost singleton.
-/

universe u v

namespace TDA.Filtration

open TDA.Simplicial

noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

variable {X : Type u} {Y : Type v}
variable {F : SimplicialFiltration ℝ X} {G : SimplicialFiltration ℝ Y} {ε : ℝ}

/-- A single global function sends each actual face at t to a face at t + ε. -/
def IsShiftedSimplicial (F : SimplicialFiltration ℝ X) (G : SimplicialFiltration ℝ Y)
    (ε : ℝ) (f : X → Y) : Prop :=
  ∀ t σ, σ ∈ F t → σ.image f ∈ G (t + ε)

/-- Each nonempty finite subset of a relational face image is a target face.
Totality of the relation on ambient vertices is a separate premise. -/
def IsShiftedSimplicialRelation (F : SimplicialFiltration ℝ X)
    (G : SimplicialFiltration ℝ Y) (ε : ℝ) (C : SetRel X Y) : Prop :=
  ∀ t σ, σ ∈ F t → ∀ τ : Finset Y, τ.Nonempty →
    (↑τ : Set Y) ⊆ C.image (↑σ) → τ ∈ G (t + ε)

/-- The actual vertex map supplied by a shifted simplicial function at a level. -/
def IsShiftedSimplicial.vertexMap {f : X → Y} (hf : IsShiftedSimplicial F G ε f)
    (t : ℝ) : VertexMap (F t) (G (t + ε)) where
  toFun := f
  map_face := hf t

/-- The stage vertex map uses the given global function. -/
@[simp] theorem IsShiftedSimplicial.vertexMap_apply {f : X → Y}
    (hf : IsShiftedSimplicial F G ε f) (t : ℝ) (x : X) : hf.vertexMap t x = f x := rfl

/-- Every subordinate function preserves shifted faces. -/
theorem IsShiftedSimplicialRelation.of_subordinate {C : SetRel X Y}
    (hC : IsShiftedSimplicialRelation F G ε C) {f : X → Y}
    (hf : Function.graph f ⊆ C) : IsShiftedSimplicial F G ε f := by
  intro t σ hσ
  apply hC t σ hσ (σ.image f)
  · exact Finset.image_nonempty.mpr ((F t).isRelLowerSet_faces hσ).1
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx, hf rfl⟩

/-- Two subordinate functions are contiguous on every actual stage. -/
theorem IsShiftedSimplicialRelation.contiguous {C : SetRel X Y}
    (hC : IsShiftedSimplicialRelation F G ε C) {f g : X → Y}
    (hf : Function.graph f ⊆ C) (hg : Function.graph g ⊆ C) (t : ℝ) :
    Contiguous ((hC.of_subordinate hf).vertexMap t) ((hC.of_subordinate hg).vertexMap t) := by
  intro σ hσ
  apply hC t σ hσ
  · exact (Finset.image_nonempty.mpr ((F t).isRelLowerSet_faces hσ).1).mono
      Finset.subset_union_left
  · intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hf rfl⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, hx, hg rfl⟩

/-- A function graph satisfies the relation condition exactly when the function preserves
shifted faces. -/
theorem isShiftedSimplicialRelation_graph_iff (f : X → Y) :
    IsShiftedSimplicialRelation F G ε (Function.graph f) ↔ IsShiftedSimplicial F G ε f := by
  constructor
  · intro h
    exact h.of_subordinate (Set.Subset.refl _)
  · intro hf t σ hσ τ hτ hsub
    apply ((G (t + ε)).isRelLowerSet_faces (hf t σ hσ)).2 _ hτ
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsub hy
    exact Finset.mem_image.mpr ⟨x, hx, hxy⟩

/-- Identity preserves a filtration at zero shift. -/
theorem isShiftedSimplicial_id (F : SimplicialFiltration ℝ X) :
    IsShiftedSimplicial F F 0 id := by
  intro t σ hσ
  simpa using hσ

end
end TDA.Filtration
