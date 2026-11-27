import TDA.Sheaf.BandIntervalDegreeOne
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Degree-one band convolution fixtures

The open unit interval is tested below, at and above the threshold. The coefficient module
at the threshold is nonzero. A closed-point input exercises the empty degree-one output.
-/

open CategoryTheory CategoryTheory.Limits DerivedCategory TDA.Sheaf
  TDA.Sheaf.AlternatingDiagram TDA.Sheaf.BandConvolution TDA.Sheaf.RealConstructible
  TDA.Sheaf.RealIntervalSectionsExamples TDA.Sheaf.RealIntervalSetsExamples
  TDA.Sheaf.RealStratification TDA.Sheaf.RealConstructibleExamples
  TDA.Sheaf.RealStratificationExamples
open TDA.Sheaf.ClientExamples (q2 q2_strictMono)

attribute [local instance] HasDerivedCategory.standard

local notation "OpenUnit" =>
  Functor.obj (extension ℚ q2_strictMono) (interval (orient 2) Joo)


example : IsZero ((Plus.singleFunctor _ 0 ⋙ T ℚ (1 / 4) ⋙
    Plus.homologyFunctor _ 1).obj OpenUnit) := by
  apply isZero_H1T_interval q2_strictMono Joo (by norm_num)
  rw [intervalSet_q2_Joo, outSet1_Ioo (by norm_num) zero_lt_one]
  exact Set.Icc_eq_empty (by norm_num)

example : outSet1 (1 / 2) (intervalSet q2 Joo) = ({1 / 2} : Set ℝ) := by
  rw [intervalSet_q2_Joo, outSet1_Ioo_threshold (by norm_num) zero_lt_one (by norm_num)]
  norm_num

example : outSet1 1 (intervalSet q2 Joo) = Set.Icc 0 1 := by
  rw [intervalSet_q2_Joo, outSet1_Ioo zero_le_one zero_lt_one]
  norm_num

example : IsZero ((Plus.singleFunctor _ 0 ⋙ T ℚ 1 ⋙ Plus.homologyFunctor _ 1).obj
    (pointSheaf ℚ)) := by
  apply isZero_H1T_interval p₁_strictMono pointSegment zero_le_one
  rw [intervalSet_pointSegment, outSet1_singleton zero_le_one]

example : ¬ IsZero (fibreCohomology ℚ (1 / 2) (1 / 2) OpenUnit 1) := by
  intro hz
  obtain ⟨e⟩ := nonempty_iso_fibreCohomology_one_interval (k := ℚ) q2_strictMono Joo
    (ε := 1 / 2) (y := 1 / 2) (by norm_num) (by
      rw [intervalSet_q2_Joo, outSet1_Ioo_threshold (by norm_num) zero_lt_one (by norm_num)]
      norm_num)
  have hst := (TopCat.Sheaf.forget (ModuleCat ℚ) pt ⋙
    TopCat.Presheaf.stalkFunctor (X := pt) (ModuleCat ℚ) PUnit.unit).map_isZero hz
  exact zero_ne_one ((ModuleCat.isZero_iff_subsingleton.1 (hst.of_iso e.symm)).elim
    (0 : ℚ) (1 : ℚ))

example : Nonempty (((Plus.singleFunctor _ 0 ⋙ T ℚ 1 ⋙ Plus.homologyFunctor _ 1).obj
    OpenUnit).presheaf.stalk (1 : realLine) ≅ ModuleCat.of ℚ ℚ) := by
  apply nonempty_iso_stalk_H1T_interval q2_strictMono Joo zero_le_one
  rw [intervalSet_q2_Joo, outSet1_Ioo zero_le_one zero_lt_one]
  exact ⟨by norm_num, by norm_num⟩
