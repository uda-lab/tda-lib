import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Noninjective simplicial vertex maps

A vertex map between preabstract simplicial complexes is a total function on the
ambient vertex types whose finite images preserve faces.  The definition does
not require injectivity, order, or preservation of face cardinality.
-/

universe u v w z

namespace TDA.Simplicial

open Finset

noncomputable section

variable {I : Type u} {J : Type v} {P : Type w} {Q : Type z}

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- A simplicial vertex map between preabstract simplicial complexes. -/
structure VertexMap (K : PreAbstractSimplicialComplex I)
    (L : PreAbstractSimplicialComplex J) where
  /-- The total map on ambient vertices. -/
  toFun : I → J
  /-- The image of every source face is a target face. -/
  map_face : ∀ s, s ∈ K →
    @Finset.image I J (Classical.decEq J) toFun s ∈ L

instance (K : PreAbstractSimplicialComplex I) (L : PreAbstractSimplicialComplex J) :
    CoeFun (VertexMap K L) (fun _ => I → J) := ⟨VertexMap.toFun⟩

/-- Two vertex maps are equal when their ambient functions are pointwise equal. -/
@[ext] theorem VertexMap.ext {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {f g : VertexMap K L}
    (h : ∀ i, f i = g i) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      cases funext h
      rfl

/-- The identity vertex map. -/
def VertexMap.id (K : PreAbstractSimplicialComplex I) : VertexMap K K :=
  { toFun := fun i => i
    map_face := by
      intro s hs
      simpa using hs }

/-- Vertex maps compose by composing their ambient functions. -/
def VertexMap.comp {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {M : PreAbstractSimplicialComplex P}
    (f : VertexMap K L) (g : VertexMap L M) : VertexMap K M :=
  { toFun := g.toFun ∘ f.toFun
    map_face := by
      intro s hs
      have hf : @Finset.image I J (Classical.decEq J) f.toFun s ∈ L :=
        f.map_face s hs
      have hg := g.map_face (@Finset.image I J (Classical.decEq J) f.toFun s) hf
      simpa only [Finset.image_image, Function.comp_apply] using hg }

@[simp] theorem VertexMap.comp_apply {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {M : PreAbstractSimplicialComplex P}
    (f : VertexMap K L) (g : VertexMap L M) (i : I) : VertexMap.comp f g i = g (f i) := rfl

@[simp] theorem VertexMap.id_apply (K : PreAbstractSimplicialComplex I) (i : I) :
    VertexMap.id K i = i := rfl

/-! Extensional identity and associativity laws. -/

theorem VertexMap.id_comp {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (f : VertexMap K L) :
    VertexMap.comp (VertexMap.id K) f = f := by
  apply VertexMap.ext
  intro i
  simp [VertexMap.comp, VertexMap.id]

theorem VertexMap.comp_id {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (f : VertexMap K L) :
    VertexMap.comp f (VertexMap.id L) = f := by
  apply VertexMap.ext
  intro i
  simp [VertexMap.comp, VertexMap.id]

theorem VertexMap.comp_assoc {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {M : PreAbstractSimplicialComplex P}
    {N : PreAbstractSimplicialComplex Q} (f : VertexMap K L) (g : VertexMap L M)
    (h : VertexMap M N) :
    VertexMap.comp (VertexMap.comp f g) h = VertexMap.comp f (VertexMap.comp g h) := by
  apply VertexMap.ext
  intro i
  rfl

/-- The pointwise face condition is equivalent to image-complex containment.

The local classical equality decision is used only by the finite-image
operation in the pinned mathlib definition of `PreAbstractSimplicialComplex.map`.
-/
theorem map_le_iff {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (r : I → J) :
    PreAbstractSimplicialComplex.map K r ≤ L ↔ ∀ s ∈ K, s.image r ∈ L := by
  constructor
  · intro h s hs
    exact h (by
      change s.image r ∈ PreAbstractSimplicialComplex.map K r
      exact ⟨s, hs, rfl⟩)
  · intro h s hs
    change s ∈ K.faces.image (fun t => t.image r) at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact h t ht

/-- A vertex map's field is exactly the image-complex containment condition. -/
theorem VertexMap.map_le_iff {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (f : VertexMap K L) :
    PreAbstractSimplicialComplex.map K f ≤ L ↔ ∀ s ∈ K, s.image f ∈ L := by
  exact TDA.Simplicial.map_le_iff f

end
end TDA.Simplicial
