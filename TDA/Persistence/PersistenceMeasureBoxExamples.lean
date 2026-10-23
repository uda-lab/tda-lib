import TDA.Persistence.PersistenceMeasureBox
import TDA.Persistence.PersistenceMeasureExamples

/-!
# A nonzero box inequality with displaced intervals

The intervals `[0,2)` and `[1/4,9/4)` are `1/4`-interleaved. The first has
one occurrence in `[-1,0] × [1,2]`; the box inequality forces an occurrence
in `[-5/4,1/4] × [3/4,9/4]` for the second. Both its birth and death lie
on the expanded rectangle's upper edges.
-/

universe u

namespace TDA.Persistence.PersistenceMeasureBoxExamples

open scoped NNReal

variable {k : Type u} [Field k]

private theorem interval_qTame (p : ℝ × WithTop ℝ) :
    (RealBarcode.intervalModule (k := k) p).QTame := by
  apply PModule.qTame_of_finiteDimensional
  intro t
  change FiniteDimensional k (RealBarcode.fiber (k := k) p t)
  infer_instance

/-- Positive-parameter interleaving transports a nonzero rectangle count, including
birth and death on the upper edges of the expanded rectangle. -/
theorem displaced_interval_box_nonzero :
    1 ≤ persistenceMeasureValue
      (RealBarcode.intervalModule (k := k) (1 / 4, (9 / 4 : ℝ)))
      (show (-5 / 4 : ℝ) ≤ 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num)
      (show (3 / 4 : ℝ) ≤ 9 / 4 by norm_num) := by
  let i := RealBarcode.interleavingOfBounds (k := k) (1 / 4 : ℝ≥0)
    (0, (2 : WithTop ℝ)) (1 / 4, (9 / 4 : ℝ))
    (by norm_num) (by norm_num)
    (by rw [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe]; norm_num)
    (by rw [← WithTop.coe_ofNat, ← WithTop.coe_add, WithTop.coe_le_coe]; norm_num)
  have h := i.persistenceMeasureValue_box_le_of_qTame (interval_qTame _)
    (show (-1 : ℝ) ≤ 0 by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
    (by norm_num)
  rw [PersistenceMeasureExamples.upper_edges_count_one] at h
  norm_num at h ⊢
  exact h

end TDA.Persistence.PersistenceMeasureBoxExamples
