import TDA.Sheaf.BandIntervalMaps
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Degree-zero band map fixtures

Over `ℚ`, the radius map from `2` to `1` is nonzero for the singleton at `0`.
For `[0, 1)` it is zero because the two output intervals
`[-2, -1)` and `[-1, 0)` have empty intersection.
-/

open CategoryTheory TDA.Sheaf TDA.Sheaf.AlternatingDiagram TDA.Sheaf.BandConvolution
  TDA.Sheaf.ClientExamples TDA.Sheaf.RealConstructible TDA.Sheaf.RealIntervalSectionsExamples
  TDA.Sheaf.RealIntervalSetsExamples TDA.Sheaf.RealStratification
  TDA.Sheaf.RealConstructibleExamples TDA.Sheaf.RealStratificationExamples

attribute [local instance] HasDerivedCategory.standard

example : H0Restr ℚ (show (1 : ℝ) ≤ 2 by norm_num) (pointSheaf ℚ) ≠ 0 := by
  apply (H0Restr_interval_ne_zero_iff (k := ℚ) zero_le_one (by norm_num : (1 : ℝ) ≤ 2)
    p₁_strictMono pointSegment).2
  rw [intervalSet_pointSegment, outSet0_singleton (by norm_num : (0 : ℝ) ≤ 2),
    outSet0_singleton zero_le_one]
  exact ⟨0, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

example : H0Restr ℚ (show (1 : ℝ) ≤ 2 by norm_num)
    ((extension ℚ q2_strictMono).obj (interval (orient 2) Jco)) = 0 := by
  by_contra h
  obtain ⟨x, h₂, h₁⟩ :=
    (H0Restr_interval_ne_zero_iff (k := ℚ) zero_le_one (by norm_num : (1 : ℝ) ≤ 2)
      q2_strictMono Jco).1 h
  rw [intervalSet_q2_Jco, outSet0_Ico (by norm_num) zero_lt_one, Set.mem_Ico] at h₂
  rw [intervalSet_q2_Jco, outSet0_Ico zero_le_one zero_lt_one, Set.mem_Ico] at h₁
  linarith [h₂.2, h₁.1]
