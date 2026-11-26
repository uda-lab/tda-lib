import TDA.Sheaf.BandConvolution
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Rat

/-!
# Closed-band functors on `D⁺(Sh(ℝ; k))`: fixtures

These fixtures consume `TDA.Sheaf.BandConvolution` with Mathlib's standard derived category
`HasDerivedCategory.standard`, installed as a local instance in this file only; the library
statements take the derived category structure as an instance argument.

* `a = 0`: `T0Iso` identifies `T 0` with the identity functor, and the augmentation at radius
  zero is that isomorphism (`aug_zero`), over `ℚ` and over `ZMod 2`.
* `a = b`: the radius map of `a ≤ a` is the identity (`restr_refl`), at radius `0` and at a
  positive radius.
* A nondegenerate chain `0 ≤ 1 ≤ 2`: the radius maps compose (`restr_trans`), and the
  augmentations are compatible with them (`restr_comp_aug`).
* The zero band is special: `q 0` is a homeomorphism (`isIso_q_zero`), while `q 1` identifies
  the two points `(0, 0)` and `(1, 0)` of `D 1`, so it is not an isomorphism. The projections
  of every band are proper, and the shear sends `(0, 1)` to `(1, 0)`.
-/

noncomputable section

open CategoryTheory TDA.Sheaf TDA.Sheaf.BandConvolution

namespace TDA.Sheaf.BandConvolutionExamples

attribute [local instance] HasDerivedCategory.standard

/-! ## `a = 0` -/

example : T ℚ 0 ≅ 𝟭 _ := T0Iso ℚ

example : aug ℚ (le_refl (0 : ℝ)) = (T0Iso ℚ).hom := aug_zero ℚ

example : T (ZMod 2) 0 ≅ 𝟭 _ := T0Iso (ZMod 2)

example : (T0Iso ℚ).inv = derivedUnit ℚ (q 0) ≫
    Functor.whiskerRight (eqToHom (congrArg (pullbackPlus ℚ) p_zero_eq_q_zero.symm))
      (pushforwardPlus ℚ (q 0)) := T0Iso_inv ℚ

/-! ## `a = b` -/

example : restr ℚ (le_refl (0 : ℝ)) = 𝟙 (T ℚ 0) := restr_refl ℚ 0

example : restr ℚ (le_refl (1 : ℝ)) = 𝟙 (T ℚ 1) := restr_refl ℚ 1

example (a : ℝ) : restr (ZMod 2) (le_refl a) = 𝟙 (T (ZMod 2) a) := restr_refl (ZMod 2) a

/-! ## A chain of radii -/

private lemma zero_le_one' : (0 : ℝ) ≤ 1 := zero_le_one
private lemma one_le_two' : (1 : ℝ) ≤ 2 := one_le_two

example : restr ℚ one_le_two' ≫ restr ℚ zero_le_one' =
    restr ℚ (zero_le_one'.trans one_le_two') :=
  restr_trans ℚ zero_le_one' one_le_two'

example : restr ℚ one_le_two' ≫ aug ℚ zero_le_one' = aug ℚ (zero_le_one'.trans one_le_two') :=
  restr_comp_aug ℚ one_le_two' zero_le_one'

example : (T ℚ 1).IsTriangulated := inferInstance

/-! ## Geometry -/

/-- The points `(0, 0)` and `(1, 0)` of the band of radius `1`. -/
def origin : D 1 := ⟨(0, 0), by norm_num [band, Real.dist_eq]⟩

/-- The point `(1, 0)` of the band of radius `1`. -/
def unitPoint : D 1 := ⟨(1, 0), by norm_num [band, Real.dist_eq]⟩

/-- `q 1` is not injective: it sends `(0, 0)` and `(1, 0)` to `0`. -/
lemma q_one_not_injective : ¬ Function.Injective (q 1) := by
  intro h
  have := congrArg (fun z : D 1 => (z : ℝ × ℝ).1) (h (a₁ := origin) (a₂ := unitPoint) rfl)
  norm_num [origin, unitPoint] at this

/-- Unlike `q 0`, the projection `q 1` is not an isomorphism. -/
lemma not_isIso_q_one : ¬ IsIso (q 1) := by
  intro h
  exact q_one_not_injective ((TopCat.homeoOfIso (asIso (q 1))).injective)

example : IsIso (q 0) := inferInstance

example : IsProperMap (p 1) := isProperMap_p 1

example : IsProperMap (q 1) := isProperMap_q 1

example : Topology.IsClosedEmbedding (incl zero_le_one') := isClosedEmbedding_incl _

example : (shear 1 ⟨(0, 1), by norm_num [band, Real.dist_eq]⟩ : Set.Icc (-1 : ℝ) 1 × ℝ).2 = 0 := rfl

example : ((shear 1 ⟨(0, 1), by norm_num [band, Real.dist_eq]⟩).1 : ℝ) = 1 := by simp [shear]

end TDA.Sheaf.BandConvolutionExamples
