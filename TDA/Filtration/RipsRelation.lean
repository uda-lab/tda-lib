import TDA.Filtration.Rips
import TDA.Filtration.ShiftedSimplicialMap

/-!
# Rips face images under a distance-distortion bound

An absolute bound on every pair in a native relation gives the shifted finite-face
condition. It includes pairs with the same source vertex, so multivalued fibers
are controlled too. No totality or finiteness of the relational image is needed.
Rips time is diameter; singleton birth is zero and negative stages are empty.
-/

universe u v

namespace TDA.Filtration.Rips

open scoped NNReal

variable {X : Type u} {Y : Type v}

/-- A pairwise distortion bound sends every finite part of a relational face image
to the closed Rips sublevel at the shifted diameter threshold. -/
theorem isShiftedSimplicialRelation_of_distortion (dX : MetricSpace X) (dY : MetricSpace Y)
    {C : SetRel X Y} {ε : ℝ≥0}
    (h : ∀ x x' y y', (x,y) ∈ C → (x',y') ∈ C →
      |dX.dist x x' - dY.dist y y'| ≤ (ε : ℝ)) :
    IsShiftedSimplicialRelation (filter dX).sublevelFiltration
      (filter dY).sublevelFiltration (ε : ℝ) C := by
  intro t σ hσ τ hτ hsub
  apply (mem_sublevel_iff dY _ _).mpr
  refine ⟨hτ, ?_⟩
  intro y hy y' hy'
  obtain ⟨x, hx, hxy⟩ := hsub hy
  obtain ⟨x', hx', hxy'⟩ := hsub hy'
  have hd := ((mem_sublevel_iff dX t σ).mp hσ).2 x hx x' hx'
  have hb := (abs_sub_le_iff.mp (h x x' y y' hxy hxy')).2
  linarith

end TDA.Filtration.Rips
