import TDA.Sheaf.BandIntervalConvolution
import TDA.Sheaf.BandIntervalMaps
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Real interval convolution fixtures

Over the rationals, the open unit interval shrinks at radius one quarter, gives the
midpoint in degree one at radius one half, and gives the closed unit interval in degree
one at radius one. Closed and half-open intervals exercise degree zero. The augmentation
at radius one is nonzero for the point at zero and zero for the right-open unit interval.
-/

open CategoryTheory DerivedCategory TDA.Sheaf TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.BandConvolution TDA.Sheaf.RealConstructible TDA.Sheaf.RealIntervalSectionsExamples
  TDA.Sheaf.RealIntervalSetsExamples TDA.Sheaf.RealStratification
  TDA.Sheaf.RealConstructibleExamples TDA.Sheaf.RealStratificationExamples TDA.Persistence
open TDA.Sheaf.ClientExamples (q2 q2_strictMono Jc Jco intervalSet_q2_Jc)

attribute [local instance] HasDerivedCategory.standard

local notation "QInterval[" J "]" =>
  Functor.obj (extension ℚ q2_strictMono) (interval (orient 2) J)
local notation "Conv[" ε "," J "]" =>
  Functor.obj (T ℚ ε) (Functor.obj (Plus.singleFunctor _ 0) QInterval[J])
local notation "Output[" ε "," i "," K "]" =>
  Functor.obj (Plus.singleFunctor _ i)
    (Functor.obj (extension ℚ (strictMono_sortedBreakpoints (bandBreakpoints q2 ε)))
      (interval _ K))
local notation "Breaks[" ε "]" => sortedBreakpoints (bandBreakpoints q2 ε)

example : ∃ K, intervalSet Breaks[1 / 4] K = Set.Ioo (1 / 4) (3 / 4) ∧
    Nonempty (Conv[1 / 4,Joo] ≅ Output[1 / 4,0,K]) := by
  simpa only [zero_add, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] using
    exists_intervalSheaf_T_Ioo_below (k := ℚ) q2_strictMono Joo (ε := 1 / 4)
      (by norm_num) zero_lt_one (by norm_num) intervalSet_q2_Joo

example : ∃ K, intervalSet Breaks[1 / 2] K = {1 / 2} ∧
    Nonempty (Conv[1 / 2,Joo] ≅ Output[1 / 2,1,K]) := by
  simpa only [zero_add] using
    exists_intervalSheaf_T_Ioo_threshold (k := ℚ) q2_strictMono Joo (ε := 1 / 2)
      (by norm_num) zero_lt_one (by norm_num) intervalSet_q2_Joo

example : ∃ K, intervalSet Breaks[1] K = Set.Icc 0 1 ∧
    Nonempty (Conv[1,Joo] ≅ Output[1,1,K]) := by
  simpa only [sub_self, zero_add] using
    exists_intervalSheaf_T_Ioo_above (k := ℚ) q2_strictMono Joo zero_le_one
      zero_lt_one (by norm_num) intervalSet_q2_Joo

example : ∃ K, intervalSet Breaks[1] K = Set.Icc (-1) 2 ∧
    Nonempty (Conv[1,Jc] ≅ Output[1,0,K]) := by
  simpa only [zero_sub, one_add_one_eq_two] using
    exists_intervalSheaf_T_Icc (k := ℚ) q2_strictMono Jc zero_le_one zero_le_one
      intervalSet_q2_Jc

example : ∃ K, intervalSet Breaks[1] K = Set.Ico (-1) 0 ∧
    Nonempty (Conv[1,Jco] ≅ Output[1,0,K]) := by
  simpa only [zero_sub, sub_self] using
    exists_intervalSheaf_T_Ico (k := ℚ) q2_strictMono Jco zero_le_one zero_lt_one
      intervalSet_q2_Jco

example : H0Aug ℚ zero_le_one (pointSheaf ℚ) ≠ 0 := by
  apply (H0Aug_interval_ne_zero_iff (k := ℚ) zero_le_one p₁_strictMono pointSegment).2
  rw [intervalSet_pointSegment, outSet0_singleton zero_le_one]
  exact ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩

example : H0Aug ℚ zero_le_one QInterval[Jco] = 0 := by
  by_contra h
  obtain ⟨x, hx, hx'⟩ :=
    (H0Aug_interval_ne_zero_iff (k := ℚ) zero_le_one q2_strictMono Jco).mp h
  rw [intervalSet_q2_Jco, outSet0_Ico zero_le_one zero_lt_one, Set.mem_Ico] at hx
  rw [intervalSet_q2_Jco, Set.mem_Ico] at hx'
  linarith [hx.2, hx'.1]
