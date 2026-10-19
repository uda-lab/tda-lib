import TDA.Filtration.Basic
import TDA.Simplicial.Contiguity
import TDA.Simplicial.VertexChainMap
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


section Composition

variable {Z : Type*} {H : SimplicialFiltration ℝ Z} {δ : ℝ}

/-- Shifted simplicial functions compose by adding their real degrees. -/
theorem IsShiftedSimplicial.comp {f : X → Y} {g : Y → Z}
    (hf : IsShiftedSimplicial F G ε f) (hg : IsShiftedSimplicial G H δ g) :
    IsShiftedSimplicial F H (ε + δ) (g ∘ f) := by
  intro t σ hσ
  simpa only [Finset.image_image, add_assoc] using hg (t + ε) _ (hf t σ hσ)

/-- The stage composite includes the index transport from `(t+ε)+δ` to `t+(ε+δ)`. -/
theorem IsShiftedSimplicial.comp_vertexMap {f : X → Y} {g : Y → Z}
    (hf : IsShiftedSimplicial F G ε f) (hg : IsShiftedSimplicial G H δ g) (t : ℝ) :
    (hf.comp hg).vertexMap t = VertexMap.comp (VertexMap.comp (hf.vertexMap t)
      (hg.vertexMap (t + ε)))
      (inclusionVertexMap (H.monotone (le_of_eq (add_assoc t ε δ)))) :=
  VertexMap.ext (fun _ => rfl)

/-- Every finite part of a composite relational image has a finite intermediate witness.
The image itself can be infinite. Choosing only on `τ.attach` avoids a default vertex. -/
private theorem finite_intermediate {C : SetRel X Y} {D : SetRel Y Z}
    {σ : Finset X} {τ : Finset Z} (hτ : τ.Nonempty)
    (hsub : (↑τ : Set Z) ⊆ (C.comp D).image ↑σ) :
    ∃ ρ : Finset Y, ρ.Nonempty ∧ (↑ρ : Set Y) ⊆ C.image ↑σ ∧
      (↑τ : Set Z) ⊆ D.image ↑ρ := by
  have hex (z : {z // z ∈ τ}) : ∃ y, y ∈ C.image ↑σ ∧ (y, z.1) ∈ D := by
    obtain ⟨x, hx, y, hxy, hyz⟩ := hsub z.2
    exact ⟨y, ⟨x, hx, hxy⟩, hyz⟩
  let w (z : {z // z ∈ τ}) : Y := Classical.choose (hex z)
  have hw (z : {z // z ∈ τ}) := Classical.choose_spec (hex z)
  refine ⟨τ.attach.image w, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hτ
    exact ⟨w ⟨z, hz⟩, Finset.mem_image.mpr ⟨⟨z,hz⟩, Finset.mem_attach _ _, rfl⟩⟩
  · intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hw z).1
  · intro z hz
    exact ⟨w ⟨z,hz⟩, Finset.mem_image.mpr ⟨⟨z,hz⟩, Finset.mem_attach _ _, rfl⟩,
      (hw ⟨z,hz⟩).2⟩

/-- Native relation composition is first `C`, then `D`; its shift is `ε+δ`.
This geometric fact requires no ambient totality or finite relational image. -/
theorem IsShiftedSimplicialRelation.comp {C : SetRel X Y} {D : SetRel Y Z}
    (hC : IsShiftedSimplicialRelation F G ε C)
    (hD : IsShiftedSimplicialRelation G H δ D) :
    IsShiftedSimplicialRelation F H (ε + δ) (C.comp D) := by
  intro t σ hσ τ hτ hsub
  obtain ⟨ρ, hρ, hρC, hτD⟩ := finite_intermediate hτ hsub
  simpa only [add_assoc] using hD (t + ε) ρ (hC t σ hσ ρ hρ hρC) τ hτ hτD

end Composition

end
end TDA.Filtration
