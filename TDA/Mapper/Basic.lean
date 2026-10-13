import TDA.Mapper.PullbackCover
import TDA.Topology.Nerve
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Ordinary Mapper and its one-skeleton

Ordinary Mapper is the support-aware nerve of the path-component pullback
cover.  Faces therefore have a common domain witness.  The original cover
label is injective on every face, which turns a target-cover multiplicity
bound into a face-cardinality bound.
-/

namespace TDA.Mapper

open Finset Set
open TDA.Topology

noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {I : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- Ordinary Mapper is the nerve of the path-component pullback cover. -/
def mapper (f : C(X, Y)) (U : I → Set Y) :
    PreAbstractSimplicialComplex (ComponentIndex f U) :=
  nerve (componentCover f U)

/-- A Mapper face is a nonempty finite collection of component members with a
common point in the domain. -/
theorem mem_mapper_iff (f : C(X, Y)) (U : I → Set Y)
    (s : Finset (ComponentIndex f U)) :
    s ∈ mapper f U ↔
      s.Nonempty ∧ ∃ x : X, ∀ a ∈ s, x ∈ componentCover f U a :=
  Iff.rfl

/-- Every component-cover index is a supported Mapper vertex. -/
theorem componentIndex_supported (f : C(X, Y)) (U : I → Set Y)
    (a : ComponentIndex f U) :
    ({a} : Finset (ComponentIndex f U)) ∈ mapper f U :=
  (mem_nerve_singleton_iff (componentCover f U) a).2
    (componentCover_nonempty f U a)

/-- Two vertices of one Mapper face with the same original cover label are equal. -/
theorem eq_of_mem_mapper_face_of_fst_eq (f : C(X, Y)) (U : I → Set Y)
    {s : Finset (ComponentIndex f U)} (hs : s ∈ mapper f U)
    {a b : ComponentIndex f U} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a.1 = b.1) : a = b := by
  obtain ⟨_, x, hx⟩ := (mem_mapper_iff f U s).1 hs
  rcases a with ⟨i, c⟩
  rcases b with ⟨j, d⟩
  change i = j at hab
  subst j
  rcases hx ⟨i, c⟩ ha with ⟨hxi, hc⟩
  rcases hx ⟨i, d⟩ hb with ⟨hxi', hd⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact hc.symm.trans ((componentClass_proof_irrel f U hxi hxi').trans hd)

/-- The projection to original cover labels is injective on every Mapper face. -/
theorem componentLabel_injOn_face (f : C(X, Y)) (U : I → Set Y)
    {s : Finset (ComponentIndex f U)} (hs : s ∈ mapper f U) :
    Set.InjOn Sigma.fst (s : Set (ComponentIndex f U)) := by
  intro a ha b hb hab
  exact eq_of_mem_mapper_face_of_fst_eq f U hs ha hb hab

/-- Every attained target value belongs to at most `m` distinct indices of `U`. -/
def CoverMultiplicityAtMost (f : C(X, Y)) (U : I → Set Y) (m : ℕ) : Prop :=
  ∀ y ∈ Set.range f, ∀ t : Finset I,
    (∀ i ∈ t, y ∈ U i) → t.card ≤ m

/-- Target-cover multiplicity bounds the cardinality of every Mapper face. -/
theorem mapper_face_card_le_of_multiplicity (f : C(X, Y)) (U : I → Set Y)
    {m : ℕ} (hmult : CoverMultiplicityAtMost f U m)
    {s : Finset (ComponentIndex f U)} (hs : s ∈ mapper f U) :
    s.card ≤ m := by
  obtain ⟨_, x, hx⟩ := (mem_mapper_iff f U s).1 hs
  let labels : Finset I := s.image Sigma.fst
  have hlabels : labels.card ≤ m := hmult (f x) ⟨x, rfl⟩ labels (by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact (hx a ha).1)
  have hcard : labels.card = s.card :=
    Finset.card_image_of_injOn (componentLabel_injOn_face f U hs)
  rw [← hcard]
  exact hlabels

/-- Supported vertices of a Mapper complex.  For ordinary Mapper every ambient
component index has this property, by `componentIndex_supported`. -/
def MapperVertex (f : C(X, Y)) (U : I → Set Y) :=
  {a : ComponentIndex f U // ({a} : Finset (ComponentIndex f U)) ∈ mapper f U}

/-- Regard any component-cover index as a supported Mapper vertex. -/
def toMapperVertex (f : C(X, Y)) (U : I → Set Y) (a : ComponentIndex f U) :
    MapperVertex f U :=
  ⟨a, componentIndex_supported f U a⟩

/-- The simple-graph one-skeleton on supported Mapper vertices.  Distinct
vertices are adjacent exactly when their underlying pair is a Mapper face. -/
def mapperOneSkeleton (f : C(X, Y)) (U : I → Set Y) :
    SimpleGraph (MapperVertex f U) where
  Adj a b := a ≠ b ∧
    ({a.1, b.1} : Finset (ComponentIndex f U)) ∈ mapper f U
  symm.symm a b h := by
    refine ⟨h.1.symm, ?_⟩
    simpa [Finset.pair_comm] using h.2
  loopless.irrefl a h := by
    exact h.1 rfl

/-- Adjacency in the Mapper one-skeleton is exactly distinctness together with
membership of the underlying two-vertex face. -/
theorem mapperOneSkeleton_adj_iff (f : C(X, Y)) (U : I → Set Y)
    (a b : MapperVertex f U) :
    (mapperOneSkeleton f U).Adj a b ↔
      a ≠ b ∧ ({a.1, b.1} : Finset (ComponentIndex f U)) ∈ mapper f U :=
  Iff.rfl

/-- Under multiplicity at most two, every Mapper face is exactly a supported
singleton or the underlying pair of two adjacent supported vertices. -/
theorem mem_mapper_iff_supported_singleton_or_adjacent_pair
    (f : C(X, Y)) (U : I → Set Y)
    (hmult : CoverMultiplicityAtMost f U 2)
    (s : Finset (ComponentIndex f U)) :
    s ∈ mapper f U ↔
      (∃ a : MapperVertex f U, s = {a.1}) ∨
        ∃ a b : MapperVertex f U,
          (mapperOneSkeleton f U).Adj a b ∧ s = {a.1, b.1} := by
  constructor
  · intro hs
    have hcard := mapper_face_card_le_of_multiplicity f U hmult hs
    have hpos : 0 < s.card := Finset.card_pos.mpr ((mem_mapper_iff f U s).1 hs).1
    have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hcases with hcard_one | hcard_two
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard_one
      exact Or.inl ⟨toMapperVertex f U a, rfl⟩
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard_two
      let va := toMapperVertex f U a
      let vb := toMapperVertex f U b
      refine Or.inr ⟨va, vb, ?_, rfl⟩
      exact ⟨fun hv => hab (congrArg Subtype.val hv), hs⟩
  · rintro (⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩)
    · exact a.2
    · exact hab.2

end

end TDA.Mapper
