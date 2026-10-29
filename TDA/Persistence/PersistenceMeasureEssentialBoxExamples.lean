import TDA.Persistence.PersistenceMeasureEssentialBox
import TDA.Persistence.PersistenceMeasureExamples

/-! Nonzero essential boundary mass transported by a displaced interval interleaving. -/

universe u

namespace TDA.Persistence.PersistenceMeasureEssentialBoxExamples

open scoped NNReal

variable {k : Type u} [Field k]

private theorem interval_qTame (p : ℝ × WithTop ℝ) :
    (RealBarcode.intervalModule (k := k) p).QTame := by
  apply PModule.qTame_of_finiteDimensional
  intro t
  change FiniteDimensional k (RealBarcode.fiber (k := k) p t)
  infer_instance

/-- The `1/4`-interleaving of `[0,∞)` and `[1/4,∞)` transports essential mass to a
strip whose upper birth edge is the shifted birth. Finite-death rectangles miss it. -/
theorem displaced_essential_interval_box_nonzero :
    1 ≤ essentialMeasureValue (RealBarcode.intervalModule (k := k) (1 / 4, ⊤))
      (show (-5 / 4 : ℝ) ≤ 1 / 4 by norm_num) := by
  let i := RealBarcode.interleavingOfBounds (k := k) (1 / 4 : ℝ≥0)
    (0, ⊤) (1 / 4, ⊤) (by norm_num) (by norm_num) (by simp) (by simp)
  have h := i.essentialMeasureValue_box_le_of_qTame (interval_qTame _)
    (show (-1 : ℝ) ≤ 0 by norm_num)
  rw [PersistenceMeasureExamples.essential_interval_count_one] at h
  norm_num at h ⊢
  exact h

end TDA.Persistence.PersistenceMeasureEssentialBoxExamples
