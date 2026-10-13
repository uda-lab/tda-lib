import TDA.Mapper.Basic
import TDA.Topology.NerveMap

/-!
# Refinement maps of ordinary Mapper complexes

Selected target-cover refinements act on path components and then on the
ordinary nerve.  The resulting vertex maps preserve identity and composition
and may identify Mapper vertices.
-/

namespace TDA.Mapper

open TDA.Topology
open TDA.Simplicial

noncomputable section

universe u v w z

variable {X : Type u} {Y : Type v} {I : Type w} {J : Type z}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The Mapper vertex map induced by a selected refinement of target covers. -/
def mapperMap (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) : VertexMap (mapper f U) (mapper f V) :=
  nerveMap (componentRefinement f R)

@[simp]
theorem mapperMap_apply (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) (a : ComponentIndex f U) :
    mapperMap f R a = (componentRefinement f R).selector a :=
  rfl

/-- A represented component is sent to the class of the same point in the
selected larger inverse image. -/
@[simp]
theorem mapperMap_mk (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) (i : I) (x : PullbackSpace f U i) :
    mapperMap f R ⟨i, ZerothHomotopy.mk x⟩ =
      ⟨R.selector i, ZerothHomotopy.mk (refinementInclusion f R i x)⟩ :=
  rfl

/-- The identity selected refinement induces the identity Mapper vertex map. -/
theorem mapperMap_id (f : C(X, Y)) (U : I → Set Y) :
    mapperMap f (Refinement.id U) = VertexMap.id (mapper f U) := by
  unfold mapperMap
  rw [componentRefinement_id, nerveMap_id]
  rfl

/-- Composition of selected refinements induces composition of Mapper maps. -/
theorem mapperMap_comp {K : Type*} (f : C(X, Y))
    {U : I → Set Y} {V : J → Set Y} {W : K → Set Y}
    (R : Refinement U V) (S : Refinement V W) :
    mapperMap f (Refinement.comp R S) =
      VertexMap.comp (mapperMap f R) (mapperMap f S) := by
  unfold mapperMap
  rw [componentRefinement_comp, nerveMap_comp]
  rfl

/-- A bijective relabelling followed by its inverse induces the identity on
the reindexed Mapper complex. -/
theorem mapperMap_reindex_comp (f : C(X, Y)) (e : I ≃ J) (U : J → Set Y) :
    VertexMap.comp
        (mapperMap f (reindexRefinement e U))
        (mapperMap f (reindexRefinement_symm e U)) =
      VertexMap.id (mapper f (fun i => U (e i))) := by
  rw [← mapperMap_comp]
  have h : Refinement.comp (reindexRefinement e U)
      (reindexRefinement_symm e U) = Refinement.id (fun i => U (e i)) := by
    apply Refinement.ext
    intro i
    simp [reindexRefinement, reindexRefinement_symm]
  rw [h, mapperMap_id]

/-- The inverse relabelling followed by a bijective relabelling induces the
identity on the original Mapper complex. -/
theorem mapperMap_reindex_symm_comp (f : C(X, Y)) (e : I ≃ J) (U : J → Set Y) :
    VertexMap.comp
        (mapperMap f (reindexRefinement_symm e U))
        (mapperMap f (reindexRefinement e U)) =
      VertexMap.id (mapper f U) := by
  rw [← mapperMap_comp]
  have h : Refinement.comp (reindexRefinement_symm e U)
      (reindexRefinement e U) = Refinement.id U := by
    apply Refinement.ext
    intro j
    simp [reindexRefinement, reindexRefinement_symm]
  rw [h, mapperMap_id]

end

end TDA.Mapper
