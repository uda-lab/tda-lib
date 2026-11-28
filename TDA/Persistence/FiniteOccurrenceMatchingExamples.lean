import TDA.Persistence.FiniteOccurrenceMatching

/-! A bipartite graph with two prescribed source vertices and one prescribed target vertex. -/

set_option autoImplicit false

namespace TDA.Persistence.FiniteOccurrenceMatching.Examples

open scoped Classical

private def edge (i j : Fin 3) : Prop :=
  (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)

private theorem edge_symm {i j : Fin 3} (h : edge i j) : edge j i := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [edge]

example : ∃ σ : OccurrenceMatching (Fin 3) (Fin 3) PEmpty.{1} PEmpty.{1},
    σ.finite 0 = some 1 ∧ σ.finite 1 = some 0 := by
  let L : Finset (Fin 3) := {0, 1}
  let e := (Equiv.swap (0 : Fin 3) 1).toEmbedding
  have hall (S : Finset (Fin 3)) (hS : S ⊆ L) :
      S.card ≤ (neighbors edge S).card := by
    rw [← Finset.card_map e]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    refine mem_neighbors.mpr ⟨i, hi, ?_⟩
    rcases (show i = 0 ∨ i = 1 from by simpa [L] using hS hi) with rfl | rfl
    · simp [e, edge]
    · simp [e, edge]
  have hright (S : Finset (Fin 3)) (hS : S ⊆ ({1} : Finset (Fin 3))) :
      S.card ≤ (neighbors (fun j i => edge i j) S).card :=
    (hall S (hS.trans (by simp [L]))).trans (Finset.card_le_card (by
      intro i hi
      obtain ⟨j, hj, he⟩ := mem_neighbors.mp hi
      exact mem_neighbors.mpr ⟨j, hj, edge_symm he⟩))
  obtain ⟨σ, hσ, hL, hM⟩ := exists_two_sided_of_hall edge L {1} hall hright
  obtain ⟨i, hi⟩ := hM 1 (by simp)
  obtain ⟨j, hj⟩ := hL 1 (by simp [L])
  have hi' : i = 0 := by simpa [edge] using hσ i 1 hi
  have hj' : j = 0 := by simpa [edge] using hσ 1 j hj
  exact ⟨σ, hi' ▸ hi, hj' ▸ hj⟩

end TDA.Persistence.FiniteOccurrenceMatching.Examples
