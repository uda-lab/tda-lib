import TDA.Simplicial.Bridge

set_option autoImplicit false

/-!
# Finite support-aware simplicial complexes

A `FiniteComplex n` records exactly a finite collection of nonempty, downward-closed faces
on `Fin n`. Its conversion to mathlib's preabstract complex preserves that collection, and
its face subtype has a computable enumeration directly from the stored `Finset`.
-/

namespace TDA.Simplicial

/-- A finite list of nonempty faces on the ambient vertex type `Fin n`. -/
structure FiniteComplex (n : ℕ) where
  faces : Finset (Finset (Fin n))
  nonempty : ∀ s ∈ faces, s.Nonempty
  downClosed : ∀ {s t : Finset (Fin n)},
    s ∈ faces → t.Nonempty → t ⊆ s → t ∈ faces

namespace FiniteComplex

variable {n : ℕ}

/-- The support-aware preabstract complex with exactly the stored faces. -/
def toPre (C : FiniteComplex n) : PreAbstractSimplicialComplex (Fin n) where
  faces := {s | s ∈ C.faces}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨C.nonempty s hs, fun t hts ht => C.downClosed hs ht hts⟩

/-- Membership in the converted complex is decided by the stored finite collection. -/
instance instDecidableMemToPre (C : FiniteComplex n) :
    DecidablePred (fun s : Finset (Fin n) => s ∈ C.toPre) :=
  fun s => inferInstanceAs (Decidable (s ∈ C.faces))

/-- Enumerate faces by attaching membership proofs to the stored faces. -/
instance instFintypeTotalFace (C : FiniteComplex n) :
    Fintype (TDA.Simplicial.TotalFace C.toPre) :=
  Fintype.subtype C.faces (fun _ => Iff.rfl)

/-- The converted complex has precisely the stored membership predicate. -/
theorem mem_toPre (C : FiniteComplex n) (s : Finset (Fin n)) :
    s ∈ C.toPre ↔ s ∈ C.faces := Iff.rfl

/-- A valid presentation cannot list the empty face. -/
theorem empty_not_mem_faces (C : FiniteComplex n) :
    (∅ : Finset (Fin n)) ∉ C.faces := by
  intro h
  exact (C.nonempty ∅ h).ne_empty rfl

/-- Erasing membership proofs from the face enumeration recovers exactly `faces`. -/
theorem image_univ_totalFace_val (C : FiniteComplex n) :
    (Finset.univ : Finset (TDA.Simplicial.TotalFace C.toPre)).image
      (fun s => s.val) = C.faces := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    exact t.property
  · intro hs
    exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩

/-- The executable face enumeration has one element per stored face. -/
theorem card_totalFace (C : FiniteComplex n) :
    Fintype.card (TDA.Simplicial.TotalFace C.toPre) = C.faces.card := by
  exact Fintype.subtype_card C.faces (fun _ => Iff.rfl)

/-- Conversion to the preabstract complex faithfully determines the presentation. -/
theorem toPre_injective :
    Function.Injective (toPre : FiniteComplex n →
      PreAbstractSimplicialComplex (Fin n)) := by
  intro C D h
  have hf : C.faces = D.faces := by
    ext s
    have hm := congrArg (fun K : PreAbstractSimplicialComplex (Fin n) => s ∈ K) h
    change (s ∈ C.faces) = (s ∈ D.faces) at hm
    exact Iff.of_eq hm
  cases C with
  | mk fc nc dc =>
    cases D with
    | mk fd nd dd =>
      cases hf
      rfl

end FiniteComplex
end TDA.Simplicial
