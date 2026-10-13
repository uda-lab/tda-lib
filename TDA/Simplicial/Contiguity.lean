import TDA.Simplicial.VertexMap

/-!
# Contiguity of simplicial vertex maps

Two vertex maps are contiguous when the union of their images of every source
face is a target face.  Contiguity is reflexive and symmetric, and it is
preserved by pre- and postcomposition.  It is not asserted to be transitive.
-/

namespace TDA.Simplicial

open Finset

noncomputable section

universe u v w z

variable {I : Type u} {J : Type v} {P : Type w} {Q : Type z}

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- Two simplicial vertex maps are contiguous when the union of their images
of every source face is a target face. -/
def Contiguous {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (a b : VertexMap K L) : Prop :=
  ∀ s, s ∈ K → s.image a ∪ s.image b ∈ L

/-- Every simplicial vertex map is contiguous to itself. -/
theorem contiguous_refl {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} (a : VertexMap K L) :
    Contiguous a a := by
  intro s hs
  simpa using a.map_face s hs

/-- Contiguity is symmetric. -/
theorem Contiguous.symm {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {a b : VertexMap K L}
    (h : Contiguous a b) : Contiguous b a := by
  intro s hs
  simpa [Finset.union_comm] using h s hs

/-- Precomposing two contiguous maps by the same simplicial map preserves
contiguity. -/
theorem Contiguous.precomp {H : PreAbstractSimplicialComplex P}
    {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J} {a b : VertexMap K L}
    (h : Contiguous a b) (e : VertexMap H K) :
    Contiguous (VertexMap.comp e a) (VertexMap.comp e b) := by
  intro s hs
  change s.image (a.toFun ∘ e.toFun) ∪ s.image (b.toFun ∘ e.toFun) ∈ L
  simpa only [Finset.image_image, Function.comp_apply] using
    h (s.image e) (e.map_face s hs)

/-- Postcomposing two contiguous maps by the same simplicial map preserves
contiguity. -/
theorem Contiguous.postcomp {K : PreAbstractSimplicialComplex I}
    {L : PreAbstractSimplicialComplex J}
    {M : PreAbstractSimplicialComplex Q} {a b : VertexMap K L}
    (h : Contiguous a b) (e : VertexMap L M) :
    Contiguous (VertexMap.comp a e) (VertexMap.comp b e) := by
  intro s hs
  change s.image (e.toFun ∘ a.toFun) ∪ s.image (e.toFun ∘ b.toFun) ∈ M
  have himage := e.map_face (s.image a ∪ s.image b) (h s hs)
  simpa only [Finset.image_union, Finset.image_image, Function.comp_apply] using himage

end

end TDA.Simplicial
