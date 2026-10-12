import Mathlib.Data.Set.Lattice

/-!
# Indexed set covers

An indexed family of arbitrary sets is kept separate from the support that it covers.
Selected refinements retain their index maps, and pullbacks retain all family labels.
-/

universe u v w z t s r

namespace TDA.Topology

variable {X : Type u} {I : Type v} {J : Type w} {K : Type r} {L : Type t}

/-! An indexed family of sets retains the index type and all of its labelled members. -/
abbrev CoverFamily (X : Type u) (I : Type v) := I → Set X

/-! `Covers U A` says that every point of the specified support belongs to a family member. -/
def Covers (U : CoverFamily X I) (A : Set X) : Prop :=
  ∀ x ∈ A, ∃ i, x ∈ U i

/-! A selected refinement supplies an index selector and containment into the selected member. -/
structure Refinement (U : CoverFamily X I) (V : CoverFamily X J) where
  selector : I → J
  subset : ∀ i, U i ⊆ V (selector i)

namespace Refinement

/-! The identity refinement selects each index itself. -/
def id (U : CoverFamily X I) : Refinement U U :=
  { selector := fun i => i
    subset := fun _ => subset_rfl }

/-! Refinements compose by composing their selected index functions. -/
def comp {U : CoverFamily X I} {V : CoverFamily X J} {W : CoverFamily X K}
    (R : Refinement U V) (S : Refinement V W) : Refinement U W :=
  { selector := fun i => S.selector (R.selector i)
    subset := fun i => (R.subset i).trans (S.subset (R.selector i)) }

@[simp] theorem id_selector (U : CoverFamily X I) : (id U).selector = fun i => i := rfl

@[simp] theorem comp_selector {U : CoverFamily X I} {V : CoverFamily X J}
    {W : CoverFamily X K} (R : Refinement U V) (S : Refinement V W) :
    (comp R S).selector = fun i => S.selector (R.selector i) := rfl

/-! Two refinements are equal when their selected index functions are pointwise equal. -/
@[ext] theorem ext {U : CoverFamily X I} {V : CoverFamily X J}
    {R S : Refinement U V} (h : ∀ i, R.selector i = S.selector i) : R = S := by
  cases R with
  | mk r hr =>
    cases S with
    | mk s hs =>
      cases funext h
      rfl

/-! Composition with the identity refinement on the right is the original refinement. -/
theorem comp_id {U : CoverFamily X I} {V : CoverFamily X J} (R : Refinement U V) :
    comp R (id V) = R := by
  apply ext
  intro i
  rfl

/-! Composition with the identity refinement on the left is the original refinement. -/
theorem id_comp {U : CoverFamily X I} {V : CoverFamily X J} (R : Refinement U V) :
    comp (id U) R = R := by
  apply ext
  intro i
  rfl

/-! Refinement composition is associative at the level of selected index functions. -/
theorem comp_assoc {U : CoverFamily X I} {V : CoverFamily X J} {W : CoverFamily X K}
    {Z : CoverFamily X L} (R : Refinement U V) (S : Refinement V W)
    (T : Refinement W Z) : comp (comp R S) T = comp R (comp S T) := by
  apply ext
  intro i
  rfl

end Refinement

/-! Pulling back an indexed family applies the inverse image to every member and retains its index. -/
def pullback {Y : Type z} (f : X → Y) (U : CoverFamily Y I) : CoverFamily X I :=
  fun i => f ⁻¹' U i

/-! Pulling back a refinement retains its selector and pulls back each containment. -/
def pullbackRefinement {Y : Type z} (f : X → Y) {U : CoverFamily Y I}
    {V : CoverFamily Y J} (R : Refinement U V) :
    Refinement (pullback f U) (pullback f V) :=
  { selector := R.selector
    subset := fun i => Set.preimage_mono (R.subset i) }

/-! Coverage of a support pulls back to coverage of its inverse image. -/
theorem covers_pullback {Y : Type z} (f : X → Y) {U : CoverFamily Y I} {A : Set Y}
    (hU : Covers U A) : Covers (pullback f U) (f ⁻¹' A) := by
  intro x hx
  change f x ∈ A at hx
  obtain ⟨i, hi⟩ := hU (f x) hx
  refine ⟨i, ?_⟩
  exact hi

/-! Coverage of the range of a map pulls back to full coverage of its domain. -/
theorem covers_range_pullback {Y : Type z} (f : X → Y) {U : CoverFamily Y I}
    (hU : Covers U (Set.range f)) : Covers (pullback f U) Set.univ := by
  intro x _
  obtain ⟨i, hi⟩ := hU (f x) ⟨x, rfl⟩
  refine ⟨i, ?_⟩
  exact hi

/-! Pullback along the identity has the original indexed family as an explicit family equality. -/
theorem pullback_id (U : CoverFamily X I) : pullback (id : X → X) U = U := by
  rfl

/-! Pullback along a composition has the corresponding explicit family equality. -/
theorem pullback_comp {Y : Type z} {Z : Type s} (f : X → Y) (g : Y → Z)
    (U : CoverFamily Z I) : pullback f (pullback g U) = pullback (g ∘ f) U := by
  funext i
  ext x
  rfl

/-! Pulling back a refinement along the identity map leaves its selected map unchanged. -/
theorem pullbackRefinement_id {Y : Type z} {U : CoverFamily Y I} {V : CoverFamily Y J}
    (R : Refinement U V) :
    (pullbackRefinement (fun y => y) R).selector = R.selector := rfl

/-! Pulling back a refinement along a composition has the same selector as one pullback. -/
theorem pullbackRefinement_comp {Y : Type z} {Z : Type s}
    (f : X → Y) (g : Y → Z) {U : CoverFamily Z I} {V : CoverFamily Z J}
    (R : Refinement U V) :
    (pullbackRefinement f (pullbackRefinement g R)).selector =
      (pullbackRefinement (g ∘ f) R).selector := rfl

/-! Pullback preserves the identity refinement. -/
theorem pullbackRefinement_refinement_id {Y : Type z} (U : CoverFamily Y I) (f : X → Y) :
    pullbackRefinement f (Refinement.id U) = Refinement.id (pullback f U) := by
  apply Refinement.ext
  intro i
  rfl

/-! Pullback preserves composition of selected refinements. -/
theorem pullbackRefinement_refinement_comp {Y : Type z}
    {U : CoverFamily Y I} {V : CoverFamily Y J} {W : CoverFamily Y K} (f : X → Y)
    (R : Refinement U V) (S : Refinement V W) :
    pullbackRefinement f (Refinement.comp R S) =
      Refinement.comp (pullbackRefinement f R) (pullbackRefinement f S) := by
  apply Refinement.ext
  intro i
  rfl

end TDA.Topology
