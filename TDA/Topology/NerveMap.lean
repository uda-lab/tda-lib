import TDA.Simplicial.VertexMap
import TDA.Topology.Nerve

/-!
# Refinement-induced maps of ordinary nerves

A selected refinement sends every nerve face to a face of the target nerve by
using the same ambient witness and the refinement containments.  The resulting
vertex map can identify vertices and therefore can lower face cardinality.
-/

universe u v w z

namespace TDA.Topology

open Finset
open TDA.Simplicial

noncomputable section

variable {X : Type u} {I : Type v} {J : Type w} {K : Type z}

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- The vertex map of a selected refinement on ordinary nerves. -/
def nerveMap {U : CoverFamily X I} {V : CoverFamily X J} (R : Refinement U V) :
    VertexMap (nerve U) (nerve V) :=
  { toFun := R.selector
    map_face := by
      intro s hs
      obtain ⟨hsn, x, hx⟩ := (mem_nerve_iff U s).1 hs
      refine (mem_nerve_iff V _).2 ⟨Finset.image_nonempty.mpr hsn, x, ?_⟩
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact R.subset i (hx i hi) }

@[simp] theorem nerveMap_apply {U : CoverFamily X I} {V : CoverFamily X J}
    (R : Refinement U V) (i : I) : nerveMap R i = R.selector i := rfl

/-- Refinement identity induces vertex-map identity. -/
theorem nerveMap_id (U : CoverFamily X I) :
    nerveMap (Refinement.id U) = VertexMap.id (nerve U) := by
  apply VertexMap.ext
  intro i
  rfl

/-- Refinement composition induces vertex-map composition. -/
theorem nerveMap_comp {U : CoverFamily X I} {V : CoverFamily X J}
    {W : CoverFamily X K} (R : Refinement U V) (S : Refinement V W) :
    nerveMap (Refinement.comp R S) = VertexMap.comp (nerveMap R) (nerveMap S) := by
  apply VertexMap.ext
  intro i
  rfl

/-- The refinement associated with a bijective relabelling of a family. -/
def reindexRefinement (e : I ≃ J) (U : CoverFamily X J) :
    Refinement (fun i => U (e i)) U :=
  { selector := e
    subset := fun _ => subset_rfl }

/-- The inverse refinement associated with a bijective relabelling. -/
def reindexRefinement_symm (e : I ≃ J) (U : CoverFamily X J) :
    Refinement U (fun i => U (e i)) :=
  { selector := e.symm
    subset := fun j => by
      simp }

/-- Relabelling followed by its inverse gives the identity on the reindexed nerve. -/
theorem nerveMap_reindex_comp (e : I ≃ J) (U : CoverFamily X J) :
    VertexMap.comp (nerveMap (reindexRefinement e U))
        (nerveMap (reindexRefinement_symm e U)) =
      VertexMap.id (nerve (fun i => U (e i))) := by
  apply VertexMap.ext
  intro i
  simp [reindexRefinement, reindexRefinement_symm]

/-- The inverse relabelling followed by the relabelling gives the target identity. -/
theorem nerveMap_reindex_symm_comp (e : I ≃ J) (U : CoverFamily X J) :
    VertexMap.comp (nerveMap (reindexRefinement_symm e U))
        (nerveMap (reindexRefinement e U)) =
      VertexMap.id (nerve U) := by
  apply VertexMap.ext
  intro j
  simp [reindexRefinement, reindexRefinement_symm]

end
end TDA.Topology
