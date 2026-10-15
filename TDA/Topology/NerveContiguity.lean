import TDA.Topology.NerveMap
import TDA.Simplicial.Contiguity

/-!
# Contiguity of refinement-induced nerve maps

Any two selected refinements between the same indexed families induce contiguous
vertex maps: a common point of the source face lies in every target member
selected by either refinement. This is a nerve theorem, using the generic
simplicial contiguity relation.
-/

namespace TDA.Topology

open TDA.Simplicial

noncomputable section

universe u v z

variable {I : Type u} {J : Type v}

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- Any two selected refinements between the same indexed families induce
contiguous maps of ordinary nerves. -/
theorem nerveMap_contiguous {X : Type z}
    {U : TDA.Topology.CoverFamily X I}
    {V : TDA.Topology.CoverFamily X J}
    (R S : TDA.Topology.Refinement U V) :
    Contiguous (TDA.Topology.nerveMap R) (TDA.Topology.nerveMap S) := by
  intro s hs
  obtain ⟨hsn, x, hx⟩ := (TDA.Topology.mem_nerve_iff U s).1 hs
  refine (TDA.Topology.mem_nerve_iff V _).2 ⟨?_, x, ?_⟩
  · obtain ⟨i, hi⟩ := hsn
    exact ⟨R.selector i, Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact R.subset i (hx i hi)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact S.subset i (hx i hi)

end

end TDA.Topology
