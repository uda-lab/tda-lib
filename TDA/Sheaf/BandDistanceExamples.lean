import TDA.Sheaf.BandSkyscraperDistance

/-!
# Exact rational skyscraper distances

The skyscrapers at zero and one admit a witness at radius one and have no witness
at radius one half. The skyscraper at zero has infinite distance from the zero object.
-/

open CategoryTheory TDA.Sheaf.BandConvolution
open scoped ENNReal ZeroObject

attribute [local instance] HasDerivedCategory.standard

example : distance (skyscraper ℚ 0) (skyscraper ℚ 1) = 1 := by
  rw [distance_skyscraper]
  norm_num

example : Nonempty (Witness ℚ (zero_le_one : (0 : ℝ) ≤ 1)
    (skyscraper ℚ 0) (skyscraper ℚ 1)) := by
  apply (nonempty_witness_skyscraper_iff ℚ 0 1 _).2
  norm_num

example : ¬ Nonempty (Witness ℚ (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (skyscraper ℚ 0) (skyscraper ℚ 1)) := by
  rw [nonempty_witness_skyscraper_iff]
  norm_num

example : distance (skyscraper ℚ 0) 0 = ⊤ := distance_skyscraper_zero ℚ 0
