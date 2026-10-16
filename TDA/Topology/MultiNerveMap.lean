import TDA.Topology.MultiNerve
import TDA.Topology.NerveMap

/-!
# Refinement-induced maps of multinerves

A selected refinement `R : Refinement U V` of indexed families on one topological space sends
the intersection over a finite index set `σ` into the intersection over its image
`σ.image R.selector`. The induced map on path components sends a multinerve cell `(σ, C)` to
`(R.selector '' σ, C')`, where `C'` is the path component containing `C`. Like the ordinary
`nerveMap`, the map may lower the support cardinality, because selectors need not be injective.

The cell map is monotone for the face order, commutes with taking faces, preserves the identity
and composition of selected refinements, and lies over `nerveMap R` under the projection onto
the ordinary nerve. The selected refinement is supplied data, as in Dey–Mémoli–Wang
(DMW16-v2 §2–3); the laws stated here are elementary library results, not attributed to a
source.

No openness, local path connectedness, finiteness, coverage or nonemptiness is assumed. No
category structure, contiguity, selector-independence, geometric realization or homology is
constructed.
-/

namespace TDA.Topology

open Finset Set

noncomputable section

universe u v w z

variable {X : Type u} {I : Type v} {J : Type w} {K : Type z}

local instance multiNerveMapDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- A finite intersection is contained in the intersection over the selected image indices. -/
theorem interMember_image_subset {U : CoverFamily X I} {V : CoverFamily X J}
    (R : Refinement U V) (σ : Finset I) :
    interMember U σ ⊆ interMember V (σ.image R.selector) := by
  intro x hx
  rw [mem_interMember_iff]
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
  exact R.subset i ((mem_interMember_iff U).1 hx i hi)

variable [TopologicalSpace X]

section refinementFaceMap

variable {U : CoverFamily X I} {V : CoverFamily X J}

/-- The map on path components induced by the inclusion
`interMember U σ ⊆ interMember V (σ.image R.selector)`. -/
def refinementFaceMap (R : Refinement U V) (σ : Finset I) :
    ZerothHomotopy (interMember U σ) → ZerothHomotopy (interMember V (σ.image R.selector)) :=
  componentMap (preimageSetInclusion (ContinuousMap.id X) (interMember_image_subset R σ))

/-- Representative formula for refinement face maps. -/
@[simp]
theorem refinementFaceMap_mk (R : Refinement U V) (σ : Finset I) (x : interMember U σ) :
    refinementFaceMap R σ (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk
        (⟨x.1, interMember_image_subset R σ x.2⟩ : interMember V (σ.image R.selector)) :=
  rfl

/-- Refinement face maps commute with face maps. -/
theorem refinementFaceMap_faceMap (R : Refinement U V) {σ τ : Finset I} (h : τ ⊆ σ)
    (c : ZerothHomotopy (interMember U σ)) :
    faceMap V (Finset.image_subset_image h) (refinementFaceMap R σ c) =
      refinementFaceMap R τ (faceMap U h c) := by
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

end refinementFaceMap

open MultiNerveCell

/-- The map of multinerve cells induced by a selected refinement: a cell over `σ` goes to the
cell over `σ.image R.selector` whose path component contains it. -/
def multiNerveMap {U : CoverFamily X I} {V : CoverFamily X J} (R : Refinement U V) :
    MultiNerveCell U → MultiNerveCell V := fun a =>
  MultiNerveCell.mk (a.support.image R.selector) (a.support_nonempty.image R.selector)
    (refinementFaceMap R a.support a.component)

section multiNerveMap

variable {U : CoverFamily X I} {V : CoverFamily X J} {W : CoverFamily X K}

@[simp] theorem support_multiNerveMap (R : Refinement U V) (a : MultiNerveCell U) :
    (multiNerveMap R a).support = a.support.image R.selector := rfl

/-- The image of a represented cell. -/
theorem multiNerveMap_mk (R : Refinement U V) (σ : Finset I) (hσ : σ.Nonempty)
    (c : ZerothHomotopy (interMember U σ)) :
    multiNerveMap R (MultiNerveCell.mk σ hσ c) =
      MultiNerveCell.mk (σ.image R.selector) (hσ.image R.selector) (refinementFaceMap R σ c) :=
  rfl

/-- Refinement maps of multinerves are monotone for the face order. -/
theorem multiNerveMap_monotone (R : Refinement U V) : Monotone (multiNerveMap R) := by
  intro b a hba
  obtain ⟨hs, hc⟩ := le_def.1 hba
  refine le_def.2 ⟨Finset.image_subset_image hs, ?_⟩
  change faceMap V (Finset.image_subset_image hs) (refinementFaceMap R a.support a.component) =
    refinementFaceMap R b.support b.component
  rw [refinementFaceMap_faceMap R hs, hc]

/-- Refinement maps of multinerves send the face over `τ` to the face over `τ.image R.selector`. -/
theorem multiNerveMap_face (R : Refinement U V) (a : MultiNerveCell U) (τ : Finset I)
    (hτ : τ.Nonempty) (hτa : τ ⊆ a.support) :
    multiNerveMap R (a.face τ hτ hτa) =
      (multiNerveMap R a).face (τ.image R.selector) (hτ.image _)
        (Finset.image_subset_image hτa) :=
  congrArg (MultiNerveCell.mk (τ.image R.selector) (hτ.image _))
    (refinementFaceMap_faceMap R hτa a.component).symm

/-- The identity refinement induces the identity map of multinerve cells. -/
theorem multiNerveMap_id : multiNerveMap (Refinement.id U) = id := by
  funext a
  refine ext_of_support_eq (a := a) (b := multiNerveMap (Refinement.id U) a)
    Finset.image_id' ?_
  rcases a with ⟨⟨σ, hσ⟩, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Composition of refinements induces composition of multinerve maps. -/
theorem multiNerveMap_comp (R : Refinement U V) (S : Refinement V W) :
    multiNerveMap (Refinement.comp R S) = multiNerveMap S ∘ multiNerveMap R := by
  funext a
  refine (ext_of_support_eq (a := multiNerveMap S (multiNerveMap R a))
    (b := multiNerveMap (Refinement.comp R S) a)
    (Finset.image_image (s := a.support) (f := R.selector) (g := S.selector)).symm ?_)
  rcases a with ⟨⟨σ, hσ⟩, c⟩
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- The square with the ordinary nerve map: projecting the image cell gives the image of the
projected nerve face under `nerveMap R`. -/
theorem projection_multiNerveMap (R : Refinement U V) (a : MultiNerveCell U) :
    (projection V (multiNerveMap R a)).1 = (projection U a).1.image (nerveMap R) :=
  rfl

end multiNerveMap

end

end TDA.Topology
