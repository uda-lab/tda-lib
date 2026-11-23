import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Grade
import Mathlib.Logic.Relation

set_option autoImplicit false

/-!
# Elementary collapses of simplicial complexes

A pair `(σ, τ)` of faces of a preabstract simplicial complex `K` is free when `σ` is a
codimension-one face of `τ` and `τ` is the only face of `K` that strictly contains `σ`.
Deleting the free face `σ` together with `τ` is an elementary collapse; `deletion K σ` keeps the
faces of `K` that do not contain `σ`, and on a free pair these are exactly the faces other than
`σ` and `τ` (`IsFreePair.mem_deletion_iff`). `CollapsesTo K L` is the reflexive transitive closure
of `ElementaryCollapsesTo`: a finite, possibly empty, sequence of elementary collapses from `K`
to `L`. An elementary collapse ends in a proper subcomplex (`ElementaryCollapsesTo.lt`), and a
collapse ends in a subcomplex on the same labels (`CollapsesTo.le`).

The complexes are `PreAbstractSimplicialComplex`, so deleting a free vertex is allowed. These
are library definitions; no source theorem is attributed to them, and no homotopy or homology
statement is made here.
-/

namespace TDA.Simplicial

variable {V : Type*}

/-- The pair `(σ, τ)` is free in `K`: both are faces, `σ` is a codimension-one face of `τ`,
and `τ` is the only face of `K` that strictly contains `σ`. -/
structure IsFreePair (K : PreAbstractSimplicialComplex V) (σ τ : Finset V) : Prop where
  /-- The free face belongs to `K`. -/
  lower_mem : σ ∈ K
  /-- Its coface belongs to `K`. -/
  upper_mem : τ ∈ K
  /-- The free face has codimension one in its coface. -/
  covBy : σ ⋖ τ
  /-- Every face of `K` strictly containing the free face is the coface. -/
  eq_upper : ∀ ⦃ω : Finset V⦄, ω ∈ K → σ ⊂ ω → ω = τ

/-- The faces of `K` that do not contain `σ` (the anti-star of `σ`). -/
def deletion (K : PreAbstractSimplicialComplex V) (σ : Finset V) :
    PreAbstractSimplicialComplex V where
  faces := {ω | ω ∈ K ∧ ¬ σ ⊆ ω}
  isRelLowerSet_faces := by
    rintro ω ⟨hω, hσ⟩
    exact ⟨(K.isRelLowerSet_faces hω).1, fun ρ hρ hne =>
      ⟨(K.isRelLowerSet_faces hω).2 hρ hne, fun h => hσ (h.trans hρ)⟩⟩

/-- Membership in the deletion: a face of `K` not containing `σ`. -/
@[simp] theorem mem_deletion {K : PreAbstractSimplicialComplex V} {σ ω : Finset V} :
    ω ∈ deletion K σ ↔ ω ∈ K ∧ ¬ σ ⊆ ω :=
  Iff.rfl

/-- The deletion is a subcomplex. -/
theorem deletion_le (K : PreAbstractSimplicialComplex V) (σ : Finset V) : deletion K σ ≤ K :=
  fun _ h => h.1

/-- Deleting the free face of a free pair removes exactly the free face and its coface. -/
theorem IsFreePair.mem_deletion_iff {K : PreAbstractSimplicialComplex V} {σ τ : Finset V}
    (h : IsFreePair K σ τ) {ω : Finset V} :
    ω ∈ deletion K σ ↔ ω ∈ K ∧ ω ≠ σ ∧ ω ≠ τ := by
  rw [mem_deletion]
  constructor
  · rintro ⟨hω, hσ⟩
    exact ⟨hω, fun e => hσ e.ge, fun e => hσ (e ▸ h.covBy.1.subset)⟩
  · rintro ⟨hω, hne, hne'⟩
    refine ⟨hω, fun hσω => hne' (h.eq_upper hω ?_)⟩
    exact lt_of_le_of_ne hσω (Ne.symm hne)

/-- `K` collapses to `L` in one step: `L` is the deletion of the free face of a free pair. -/
def ElementaryCollapsesTo (K L : PreAbstractSimplicialComplex V) : Prop :=
  ∃ σ τ, IsFreePair K σ τ ∧ L = deletion K σ

/-- A free pair gives an elementary collapse to the deletion of its free face. -/
theorem IsFreePair.elementaryCollapsesTo {K : PreAbstractSimplicialComplex V} {σ τ : Finset V}
    (h : IsFreePair K σ τ) : ElementaryCollapsesTo K (deletion K σ) :=
  ⟨σ, τ, h, rfl⟩

/-- An elementary collapse ends in a proper subcomplex: the free face is lost. -/
theorem ElementaryCollapsesTo.lt {K L : PreAbstractSimplicialComplex V}
    (h : ElementaryCollapsesTo K L) : L < K := by
  obtain ⟨σ, _, hσ, rfl⟩ := h
  refine lt_of_le_of_ne (deletion_le K σ) fun e => ?_
  have h' : σ ∈ deletion K σ := by rw [e]; exact hσ.lower_mem
  exact h'.2 subset_rfl

/-- `K` collapses to `L` by a finite, possibly empty, sequence of elementary collapses. -/
def CollapsesTo : PreAbstractSimplicialComplex V → PreAbstractSimplicialComplex V → Prop :=
  Relation.ReflTransGen ElementaryCollapsesTo

/-- A collapse ends in a subcomplex on the same labels. -/
theorem CollapsesTo.le {K L : PreAbstractSimplicialComplex V} (h : CollapsesTo K L) : L ≤ K := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    obtain ⟨σ, _, _, rfl⟩ := hstep
    exact (deletion_le _ σ).trans ih

end TDA.Simplicial
