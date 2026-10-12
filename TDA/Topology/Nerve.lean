import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import TDA.Topology.IndexedCover

/-!
# The ordinary support-aware nerve of an indexed family

The nerve retains the index labels of an indexed family and records exactly the
nonempty finite collections of members with a common point.  In particular,
empty members do not create vertices and no ambient singleton completion is
performed.
-/

universe u v w

namespace TDA.Topology

open Finset Set

variable {X : Type u} {I : Type v} {J : Type w}

/-- The ordinary nerve of an indexed family of sets.

Its faces are the nonempty finite sets of indices whose corresponding members
have a common point.  The index type is retained, so equal members at distinct
indices give distinct vertices.
-/
def nerve (U : CoverFamily X I) : PreAbstractSimplicialComplex I where
  faces := {s | s.Nonempty ∧ ∃ x, ∀ i ∈ s, x ∈ U i}
  isRelLowerSet_faces := by
    intro s hs
    constructor
    · exact hs.1
    · intro t hts ht
      obtain ⟨x, hx⟩ := hs.2
      exact ⟨ht, x, fun i hi => hx i (hts hi)⟩

/-- Face membership in the ordinary nerve, including the nonempty-face guard. -/
theorem mem_nerve_iff (U : CoverFamily X I) (s : Finset I) :
    s ∈ nerve U ↔ s.Nonempty ∧ ∃ x, ∀ i ∈ s, x ∈ U i := Iff.rfl

/-- A singleton is a nerve face exactly when its indexed member is nonempty. -/
theorem mem_nerve_singleton_iff (U : CoverFamily X I) (i : I) :
    ({i} : Finset I) ∈ nerve U ↔ (U i).Nonempty := by
  rw [mem_nerve_iff]
  constructor
  · rintro ⟨_, x, hx⟩
    exact ⟨x, hx i (Finset.mem_singleton_self i)⟩
  · rintro ⟨x, hx⟩
    exact ⟨Finset.singleton_nonempty i, x, fun j hj =>
      (Finset.mem_singleton.mp hj) ▸ hx⟩

/-- Every nonempty subface of a nerve face is again a nerve face. -/
theorem mem_nerve_of_nonempty_subset (U : CoverFamily X I) {s t : Finset I}
    (hs : s ∈ nerve U) (hts : t ⊆ s) (ht : t.Nonempty) : t ∈ nerve U := by
  exact (nerve U).isRelLowerSet_faces hs |>.2 hts ht

/-- Enlarging every member of a family enlarges its nerve on the same index type. -/
theorem nerve_mono {U V : CoverFamily X I} (hUV : ∀ i, U i ⊆ V i) :
    nerve U ≤ nerve V := by
  intro s hs
  obtain ⟨hsn, x, hx⟩ := (mem_nerve_iff U s).1 hs
  exact (mem_nerve_iff V s).2 ⟨hsn, x, fun i hi => hUV i (hx i hi)⟩

/-- An empty ambient space has no nerve faces. -/
theorem nerve_eq_bot_of_isEmpty (U : CoverFamily X I) [IsEmpty X] :
    nerve U = ⊥ := by
  apply PreAbstractSimplicialComplex.ext
  ext s
  constructor
  · intro hs
    exact isEmptyElim hs.2.choose
  · intro hs
    exact hs.elim

section Relabel

noncomputable section

local instance : DecidableEq J := Classical.decEq J

/-- Faces are transported through a bijective relabelling of indices.

The reindexed family is `fun i => U (e i)`, and finite faces are transported
by `Finset.image e`.
-/
theorem mem_nerve_relabel_iff (e : I ≃ J) (U : CoverFamily X J) (s : Finset I) :
    s ∈ nerve (fun i => U (e i)) ↔ s.image e ∈ nerve U := by
  constructor
  · intro hs'
    obtain ⟨hs, x, hx⟩ := (mem_nerve_iff _ s).1 hs'
    refine (mem_nerve_iff _ _).2 ⟨hs.image e, x, ?_⟩
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact hx i hi
  · intro hs'
    obtain ⟨hs, x, hx⟩ := (mem_nerve_iff _ _).1 hs'
    refine (mem_nerve_iff _ s).2 ⟨Finset.image_nonempty.mp hs, x, ?_⟩
    intro i hi
    exact hx (e i) (mem_image.mpr ⟨i, hi, rfl⟩)

end

end Relabel

/-- A witness-level description of the nerve of a pulled-back family. -/
theorem mem_nerve_pullback_iff {Y : Type w} (f : X → Y) (U : CoverFamily Y I)
    (s : Finset I) :
    s ∈ nerve (pullback f U) ↔
      s.Nonempty ∧ ∃ y ∈ Set.range f, ∀ i ∈ s, y ∈ U i := by
  constructor
  · intro hs'
    obtain ⟨hs, x, hx⟩ := (mem_nerve_iff _ s).1 hs'
    refine ⟨hs, f x, ⟨x, rfl⟩, ?_⟩
    intro i hi
    exact hx i hi
  · rintro ⟨hs, y, ⟨x, rfl⟩, hy⟩
    exact (mem_nerve_iff _ s).2 ⟨hs, x, hy⟩

/-- Pullback can only remove faces from the target-family nerve. -/
theorem nerve_pullback_le {Y : Type w} (f : X → Y) (U : CoverFamily Y I) :
    nerve (pullback f U) ≤ nerve U := by
  intro s hs
  obtain ⟨hsn, y, hy, hface⟩ := (mem_nerve_pullback_iff f U s).1 hs
  exact (mem_nerve_iff U s).2 ⟨hsn, y, fun i hi => hface i hi⟩

/-- Pullback preserves the target-family nerve exactly when the map is surjective. -/
theorem nerve_pullback_eq_of_surjective {Y : Type w} (f : X → Y)
    (U : CoverFamily Y I) (hf : Function.Surjective f) :
    nerve (pullback f U) = nerve U := by
  apply le_antisymm
  · exact nerve_pullback_le f U
  · intro s hs
    obtain ⟨hsn, y, hy⟩ := (mem_nerve_iff U s).1 hs
    obtain ⟨x, rfl⟩ := hf y
    exact (mem_nerve_pullback_iff f U s).2 ⟨hsn, f x, ⟨x, rfl⟩, hy⟩

end TDA.Topology
