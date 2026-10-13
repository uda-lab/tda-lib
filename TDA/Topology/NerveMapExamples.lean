import TDA.Topology.IndexedCoverExamples
import TDA.Topology.NerveExamples
import TDA.Topology.NerveMap

/-!
# Concrete refinement-induced nerve-map fixtures

These examples connect selected refinements to the vertex-map API: duplicate
members can collapse an edge, bijective relabellings are invertible, and
composable selectors have the direct composite on every ambient index.
-/

namespace TDA.Topology.NerveMapExamples

open Finset
open TDA.Simplicial

noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- A refinement can collapse the edge from two duplicate members to one vertex. -/
theorem duplicate_edge_maps_to_singleton :
    ({false, true} : Finset Bool).image
          (nerveMap ProbeFixtures.mergeDuplicated : Bool → Unit) =
        ({()} : Finset Unit) ∧
      ({false, true} : Finset Bool) ∈ nerve ProbeFixtures.duplicatedFamily ∧
      ({()} : Finset Unit) ∈ nerve ProbeFixtures.singletonFamily := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    constructor
    · intro hi
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hi
      simpa using hb
    · intro hi
      have : i = () := Finset.mem_singleton.mp hi
      subst i
      exact Finset.mem_image.mpr ⟨false, by simp, rfl⟩
  · simp [mem_nerve_iff, ProbeFixtures.duplicatedFamily]
  · simp [mem_nerve_iff, ProbeFixtures.singletonFamily]

private def swapEquiv : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- A nontrivial relabelling and its inverse induce inverse vertex maps. -/
theorem permutation_reindex_inverse_fixture :
    swapEquiv 0 = 1 ∧
      VertexMap.comp
          (nerveMap (reindexRefinement swapEquiv NerveExamples.disjointFamily))
          (nerveMap (reindexRefinement_symm swapEquiv NerveExamples.disjointFamily)) =
        VertexMap.id
          (nerve (fun i => NerveExamples.disjointFamily (swapEquiv i))) ∧
      VertexMap.comp
          (nerveMap (reindexRefinement_symm swapEquiv NerveExamples.disjointFamily))
          (nerveMap (reindexRefinement swapEquiv NerveExamples.disjointFamily)) =
        VertexMap.id (nerve NerveExamples.disjointFamily) := by
  refine ⟨by decide, ?_, ?_⟩
  · exact nerveMap_reindex_comp swapEquiv NerveExamples.disjointFamily
  · exact nerveMap_reindex_symm_comp swapEquiv NerveExamples.disjointFamily

private def firstFamily : CoverFamily Unit (Fin 2) := fun _ => Set.univ

private def secondFamily : CoverFamily Unit (Fin 3) := fun _ => Set.univ

private def thirdFamily : CoverFamily Unit (Fin 1) := fun _ => Set.univ

private def firstRefinement : Refinement firstFamily secondFamily :=
  { selector := fun i => i.succ
    subset := by simp [firstFamily, secondFamily] }

private def secondRefinement : Refinement secondFamily thirdFamily :=
  { selector := fun _ => 0
    subset := by simp [secondFamily, thirdFamily] }

/-- Two nonidentity composable refinements have the asserted direct selector. -/
theorem composable_refinements_have_direct_composite :
    firstRefinement.selector 0 = 1 ∧
      secondRefinement.selector 0 = 0 ∧
      (∀ i : Fin 2, (Refinement.comp firstRefinement secondRefinement).selector i = 0) ∧
      nerveMap (Refinement.comp firstRefinement secondRefinement) =
        VertexMap.comp (nerveMap firstRefinement) (nerveMap secondRefinement) := by
  refine ⟨rfl, rfl, ?_, nerveMap_comp firstRefinement secondRefinement⟩
  intro i
  rfl

end
end TDA.Topology.NerveMapExamples
