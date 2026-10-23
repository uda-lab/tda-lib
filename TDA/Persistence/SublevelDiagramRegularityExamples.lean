import TDA.Persistence.SublevelDiagramRegularity
import TDA.Persistence.SublevelDiagramExamples

/-! A moving, persistently tied face template. -/

set_option autoImplicit false

namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration
open scoped ContDiff

/-- A finite full-template slot has two equal, moving real endpoints. -/
theorem moving_tied_edge_full_pair
    (e : CompatibleOrder (Examples.movingTiedEdgeFilter (0 : ℝ)))
    (t : ℝ) (i : Fin (faceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1) :
    (fixedFaceLift (ZMod 2) Examples.movingTiedEdgeFilter e 0 t).1 i = (t, t) := rfl

/-- Essential births stay as real coordinates in the reduced template,
including when multiple selected births have the same value. -/
theorem moving_tied_edge_strict_essential_birth
    (e : CompatibleOrder (Examples.movingTiedEdgeFilter (0 : ℝ)))
    (t : ℝ) (i : Fin (strictFaceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).2) :
    (strictFaceLift (ZMod 2) Examples.movingTiedEdgeFilter e 0 t).2 i = t := rfl

/-- The tied edge has a nonempty full finite template but no strict
finite slots. Both fixed lifts represent the same diagram for every
parameter, including repeated face values and essential real births. -/
theorem moving_tied_edge_full_strict_cr (r : ℕ∞ω) :
    ∃ e : CompatibleOrder (Examples.movingTiedEdgeFilter (0 : ℝ)),
      0 < (faceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1 ∧
      (strictFaceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1 = 0 ∧
      ContDiffOn ℝ r
        (fixedFaceLift (ZMod 2) Examples.movingTiedEdgeFilter e 0) Set.univ ∧
      ContDiffOn ℝ r
        (strictFaceLift (ZMod 2) Examples.movingTiedEdgeFilter e 0) Set.univ ∧
      ∀ t : ℝ,
        orderedQ (faceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1
          (faceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).2
          (fixedFaceLift (ZMod 2) Examples.movingTiedEdgeFilter e 0 t) =
        orderedQ (strictFaceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1
          (strictFaceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).2
          (strictFaceLift (ZMod 2) Examples.movingTiedEdgeFilter e 0 t) := by
  obtain ⟨e, hpos⟩ := Examples.moving_tied_edge_has_finite_slot
  refine ⟨e, hpos, ?_, ?_, ?_, ?_⟩
  · simp [strictFaceLiftCounts, strictFacePairList, Examples.movingTiedEdgeFilter]
  · apply fixedFaceLift_contDiffOn_cr
    intro s
    change ContDiffOn ℝ r (fun x : ℝ => x) Set.univ
    exact contDiffOn_id
  · apply strictFaceLift_contDiffOn_cr
    intro s
    change ContDiffOn ℝ r (fun x : ℝ => x) Set.univ
    exact contDiffOn_id
  · intro t
    have horder : ∀ x : ℝ, x ∈ (Set.univ : Set ℝ) →
        OrderingEquivalent (Examples.movingTiedEdgeFilter 0)
          (Examples.movingTiedEdgeFilter x) := by
      intro x _ _ _
      simp [Examples.movingTiedEdgeFilter]
    rw [← fixedFaceLift_factorization (ZMod 2) Examples.movingTiedEdgeFilter
      e 0 horder t (Set.mem_univ t)]
    exact strictFaceLift_factorization (ZMod 2) Examples.movingTiedEdgeFilter
      e 0 horder t (Set.mem_univ t)

end TDA.Persistence
