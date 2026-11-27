import TDA.Sheaf.BandIntervalDegreeZero
import TDA.Sheaf.RealIntervalSectionsExamples

/-!
# Degree-zero band convolution fixtures

The endpoint formulas are exercised at radius `1`. Over `ℚ`, the closed band about the
singleton at `0` has a nonzero stalk at its right endpoint, and the degree-zero convolution
of the open unit interval vanishes at radius `1/2`.
-/

open CategoryTheory CategoryTheory.Limits DerivedCategory
  TDA.Sheaf TDA.Sheaf.AlternatingDiagram TDA.Sheaf.BandConvolution
  TDA.Sheaf.ClientExamples TDA.Sheaf.RealConstructible TDA.Sheaf.RealIntervalSectionsExamples
  TDA.Sheaf.RealIntervalSetsExamples TDA.Sheaf.RealStratification
  TDA.Sheaf.RealConstructibleExamples TDA.Sheaf.RealStratificationExamples

attribute [local instance] HasDerivedCategory.standard

example : outSet0 1 (Set.Icc 0 3) = Set.Icc (-1) 4 ∧
    outSet0 1 (Set.Ico 0 3) = Set.Ico (-1) 2 ∧
    outSet0 1 (Set.Ioc 0 3) = Set.Ioc 1 4 ∧
    outSet0 1 (Set.Ioo 0 3) = Set.Ioo 1 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [outSet0_Icc zero_le_one (by norm_num)]
    norm_num
  · rw [outSet0_Ico zero_le_one (by norm_num)]
    norm_num
  · rw [outSet0_Ioc zero_le_one (by norm_num)]
    norm_num
  · rw [outSet0_Ioo zero_le_one (by norm_num)]
    norm_num

example : outSet0 1 (Set.Ici 0) = Set.Ici (-1) ∧ outSet0 1 (Set.Ioi 0) = Set.Ioi 1 ∧
    outSet0 1 (Set.Iic 0) = Set.Iic 1 ∧ outSet0 1 (Set.Iio 0) = Set.Iio (-1) ∧
    outSet0 1 (Set.univ : Set ℝ) = Set.univ := by
  exact ⟨by simpa using outSet0_Ici zero_le_one 0, by simpa using outSet0_Ioi zero_le_one 0,
    by simpa using outSet0_Iic zero_le_one 0, by simpa using outSet0_Iio zero_le_one 0,
    outSet0_univ zero_le_one⟩

example : Nonempty (((Plus.homologyFunctor _ 0).obj
    ((T ℚ 1).obj ((Plus.singleFunctor _ 0).obj (pointSheaf ℚ)))).presheaf.stalk (1 : ℝ) ≅
    ModuleCat.of ℚ ℚ) := by
  have hset : outSet0 1 (intervalSet p₁ pointSegment) = Set.Icc (-1) 1 := by
    rw [intervalSet_pointSegment]
    simpa using outSet0_singleton zero_le_one 0
  have hx : (1 : ℝ) ∈ outSet0 1 (intervalSet p₁ pointSegment) := by
    rw [hset]
    exact ⟨by norm_num, le_rfl⟩
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_H0T (k := ℚ) p₁_strictMono pointSegment
    zero_le_one ⟨1, hx⟩
  obtain ⟨s⟩ := nonempty_stalk_extension_interval_iso ℚ (strictMono_sortedBreakpoints _)
    (J := K) (hK.symm ▸ hx)
  exact ⟨(TopCat.Sheaf.forget _ _ ⋙ TopCat.Presheaf.stalkFunctor _ (1 : realLine)).mapIso e ≪≫ s⟩

example : IsZero ((Plus.homologyFunctor _ 0).obj ((T ℚ (1 / 2)).obj
    ((Plus.singleFunctor _ 0).obj
      ((extension ℚ q2_strictMono).obj (interval (orient 2) Joo))))) := by
  apply isZero_H0T_interval q2_strictMono Joo (by norm_num)
  rw [intervalSet_q2_Joo, outSet0_Ioo (by norm_num) zero_lt_one]
  exact Set.Ioo_eq_empty (by norm_num)
