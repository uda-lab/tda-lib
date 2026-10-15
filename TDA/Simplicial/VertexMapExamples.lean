import TDA.Filtration.Basic
import TDA.Simplicial.VertexMap

/-!
# Concrete noninjective vertex-map fixtures

The fixtures record edge collapse, a nontrivial permutation, and the fact that
ambient vertices absent from a target complex are not silently added.
-/

namespace TDA.Simplicial.VertexMapExamples

open Finset

noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

private def swapVertex (i : Fin 3) : Fin 3 :=
  if i = 0 then 1 else if i = 1 then 0 else 2

private def swapMap : VertexMap (⊤ : PreAbstractSimplicialComplex (Fin 3))
    (⊤ : PreAbstractSimplicialComplex (Fin 3)) :=
  { toFun := swapVertex
    map_face := by
      intro s hs
      change s.Nonempty at hs
      have hne : (@Finset.image (Fin 3) (Fin 3) (Classical.decEq (Fin 3))
          swapVertex s).Nonempty :=
        (@Finset.image_nonempty (Fin 3) (Fin 3) (Classical.decEq (Fin 3))
          swapVertex s).2 hs
      change (@Finset.image (Fin 3) (Fin 3) (Classical.decEq (Fin 3))
        swapVertex s).Nonempty
      exact hne }

/-- A noninjective simplicial map sends the source edge to one target vertex. -/
theorem edge_collapse_fixture :
    ({0, 1} : Finset (Fin 2)).image (fun _ : Fin 2 => (0 : Fin 2)) =
        ({0} : Finset (Fin 2)) ∧
      ({0} : Finset (Fin 2)) ∈ TDA.Filtration.singletonFace (0 : Fin 2) := by
  constructor
  · decide
  · simp [TDA.Filtration.mem_singletonFace_iff]

/-- A nontrivial permutation and its inverse compose to the identity map. -/
theorem permutation_inverse_fixture :
    swapMap 0 = 1 ∧ swapMap 1 = 0 ∧
      VertexMap.comp swapMap swapMap = VertexMap.id (⊤ : PreAbstractSimplicialComplex (Fin 3)) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rfl
  · apply VertexMap.ext
    intro i
    fin_cases i <;> simp [swapMap, swapVertex]

/-- A proper target complex need not contain singleton faces for ghost vertices. -/
theorem ghost_vertices_are_not_forced :
    ¬ ({1} : Finset (Fin 2)) ∈ TDA.Filtration.singletonFace (0 : Fin 2) ∧
      @PreAbstractSimplicialComplex.map (Fin 2) (Fin 2) (Classical.decEq (Fin 2))
          (⊤ : PreAbstractSimplicialComplex (Fin 2))
          (fun _ : Fin 2 => (0 : Fin 2)) ≤
        TDA.Filtration.singletonFace (0 : Fin 2) := by
  constructor
  · simp [TDA.Filtration.mem_singletonFace_iff]
  · intro s hs
    have hs' : s ∈
        (fun t : Finset (Fin 2) =>
          @Finset.image (Fin 2) (Fin 2) (Classical.decEq (Fin 2))
            (fun _ : Fin 2 => (0 : Fin 2)) t) ''
          (⊤ : PreAbstractSimplicialComplex (Fin 2)).faces := by
      simpa only [PreAbstractSimplicialComplex.map] using hs
    obtain ⟨t, ht, rfl⟩ := hs'
    change t.Nonempty at ht
    apply (TDA.Filtration.mem_singletonFace_iff 0 _).2
    ext i
    constructor
    · intro hi
      have hi' := hi
      simp only [Finset.mem_image] at hi'
      obtain ⟨j, _, hj⟩ := hi'
      simpa using hj.symm
    · intro hi
      have hi0 : i = (0 : Fin 2) := by simpa using hi
      subst i
      obtain ⟨j, hj⟩ := ht
      change (0 : Fin 2) ∈
        @Finset.image (Fin 2) (Fin 2) (Classical.decEq (Fin 2))
          (fun _ : Fin 2 => (0 : Fin 2)) t
      exact (@Finset.mem_image (Fin 2) (Fin 2) (Classical.decEq (Fin 2))
        (fun _ : Fin 2 => (0 : Fin 2)) t 0).2 ⟨j, hj, rfl⟩

end
end TDA.Simplicial.VertexMapExamples
