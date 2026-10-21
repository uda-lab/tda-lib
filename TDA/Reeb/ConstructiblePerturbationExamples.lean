import TDA.Reeb.ConstructiblePerturbation
import TDA.Reeb.ConstructibleSpaceExamples

/-!
# Carrier-level fixtures for changes of levels

The pinch presentation has a noninjective attachment map. Stretching its single
gap changes the midpoint height, preserves the endpoint identifications and has
the inverse supplied by the level homeomorphism. These fixtures concern the
carrier-level API; they make no interleaving-distance claim.
-/

set_option autoImplicit false

namespace TDA.Reeb.Examples.ConstructiblePerturbation

noncomputable section

open CylinderPresentation Examples.Cylinder

/-- Levels `0 < 2`. -/
def S02 : CriticalValues 1 where
  value i := 2 * ((i : ℕ) : ℝ)
  strictMono _ _ h := mul_lt_mul_of_pos_left (Nat.cast_lt.mpr h) (by norm_num)

/-- Stretching moves an actual interior point even when the attachment is noninjective. -/
theorem pinch_midpoint_height_change :
    ¬ Function.Injective (pinch.left 0) ∧
    |pinch.height S01 (pinch.ofCylinder S01 0 (false, gapIncl S01 0 half)) -
      pinch.height S02 (pinch.levelMap S01 S02
        (pinch.ofCylinder S01 0 (false, gapIncl S01 0 half)))| = 1 / 2 := by
  refine ⟨pinch_left_not_injective, ?_⟩
  simp only [levelMap_ofCylinder, height_ofCylinder]
  norm_num [segMap, gapIncl, half, S01, S02]

/-- Both glued bottom ends still map to the same vertex after stretching. -/
theorem pinch_levelMap_glued_bottom :
    pinch.levelMap S01 S02 (pinch.ofCylinder S01 0 (false, segBot S01 0)) =
      pinch.levelMap S01 S02 (pinch.ofCylinder S01 0 (true, segBot S01 0)) :=
  congrArg (pinch.levelMap S01 S02) pinch_segBot_glued

/-- Reversing the level change fixes every point of the noninjective-attachment quotient. -/
theorem pinch_levelHomeomorph_roundTrip (q : pinch.Realization S01) :
    pinch.levelHomeomorph S02 S01 (pinch.levelHomeomorph S01 S02 q) = q := by
  simp only [levelHomeomorph_apply, levelMap_levelMap]

/-- With no level change, the induced continuous map is the identity. -/
theorem pinch_levelMap_self : pinch.levelMap S01 S01 = ContinuousMap.id _ :=
  pinch.levelMap_self S01

end

end TDA.Reeb.Examples.ConstructiblePerturbation
