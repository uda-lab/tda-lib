import TDA.Sheaf.BandCompositionAssociativity
import TDA.Sheaf.BandCompositionExamples

/-!
# Associativity and bounded augmentation of band composition: fixtures

Over `ℚ`, the composition law is associative at radii `(1, 2, 3)` on `D⁺` and `(0, 1, 2)` on
`Dᵇ`. The source of the first law has nonzero zeroth stalk cohomology on the constant sheaf.
The bounded augmentations compose at radii `(1, 1)`.
-/

noncomputable section

open CategoryTheory Limits TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandCompositionAssociativityExamples

open TDA.Sheaf.BandCompositionExamples (not_isZero_H0_stalk_TT)
open TDA.Sheaf.IntervalFibrationExamples (constOn)

attribute [local instance] HasDerivedCategory.standard

/-- Associativity at radii `(1, 2, 3)` over `ℚ`. -/
theorem TComp_assoc_one_two_three :
    Functor.whiskerRight (TComp ℚ zero_le_one zero_le_two).hom (T ℚ 3) ≫
        (TComp ℚ (add_nonneg zero_le_one zero_le_two) zero_le_three).hom =
      (Functor.associator (T ℚ 1) (T ℚ 2) (T ℚ 3)).hom ≫
        Functor.whiskerLeft (T ℚ 1) (TComp ℚ zero_le_two zero_le_three).hom ≫
        (TCompOfEq ℚ zero_le_one (add_nonneg zero_le_two zero_le_three)
          (add_assoc (1 : ℝ) 2 3).symm).hom :=
  TComp_assoc_hom ℚ zero_le_one zero_le_two zero_le_three

/-- Every stalk of the source of the triple law on the constant sheaf has nonzero `H⁰`. -/
theorem not_isZero_H0_stalk_TTT_one_two_three (y : realLine) :
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((pullbackPlus ℚ (ptOf y)).obj (((T ℚ 1 ⋙ T ℚ 2) ⋙ T ℚ 3).obj (constOn realLine)))) := by
  let e := (Functor.isoWhiskerRight (TComp ℚ zero_le_one zero_le_two) (T ℚ 3)).app
    (constOn realLine)
  let eH := (pullbackPlus ℚ (ptOf y) ⋙ DerivedCategory.Plus.homologyFunctor _ 0).mapIso e
  exact fun h => not_isZero_H0_stalk_TT (add_nonneg zero_le_one zero_le_two) zero_le_three y
    (h.of_iso eH.symm)

/-- Bounded associativity at radii `(0, 1, 2)` over `ℚ`. -/
theorem TCompB_assoc_zero_one_two :
    Functor.whiskerRight (TCompB ℚ le_rfl zero_le_one).hom (TB ℚ 2) ≫
        (TCompB ℚ (add_nonneg le_rfl zero_le_one) zero_le_two).hom =
      (Functor.associator (TB ℚ 0) (TB ℚ 1) (TB ℚ 2)).hom ≫
        Functor.whiskerLeft (TB ℚ 0) (TCompB ℚ zero_le_one zero_le_two).hom ≫
        (compIsoB ℚ (TCompOfEq ℚ le_rfl (add_nonneg zero_le_one zero_le_two)
          (add_assoc (0 : ℝ) 1 2).symm)).hom :=
  TCompB_assoc_hom ℚ le_rfl zero_le_one zero_le_two

/-- Bounded augmentation at radii `(1, 1)` over `ℚ`. -/
theorem hcomp_augB_TCompB_one_one :
    (augB ℚ zero_le_one ◫ augB ℚ zero_le_one) ≫ (Functor.leftUnitor (𝟭 _)).hom =
      (TCompB ℚ zero_le_one zero_le_one).hom ≫ augB ℚ (add_nonneg zero_le_one zero_le_one) :=
  hcomp_augB_TCompB_hom ℚ zero_le_one zero_le_one

end TDA.Sheaf.BandCompositionAssociativityExamples
