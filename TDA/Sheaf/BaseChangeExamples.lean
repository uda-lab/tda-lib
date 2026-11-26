import Mathlib.Algebra.Field.Rat
import TDA.Sheaf.BaseChange
import TDA.Sheaf.RealLine

/-!
# The derived base-change morphism: fixtures

These fixtures consume `TDA.Sheaf.BaseChange` over `ℚ`, with Mathlib's standard derived category
`HasDerivedCategory.standard` installed as a local instance in this file only.

* `isIso_baseChange_id`: the base-change morphism of the identity square on the real line is an
  isomorphism.
* `isIso_baseChange_ι`: for the square `ι ≫ 𝟙 = 𝟙 ≫ ι` with identity direct images and the
  inclusion `ι : [0, 1] ⟶ ℝ` as base change, `ι⁻¹ ⟶ ι⁻¹` is an isomorphism.
-/

noncomputable section

open CategoryTheory Limits TDA.Sheaf

namespace TDA.Sheaf.BaseChangeExamples

attribute [local instance] HasDerivedCategory.standard

/-- The unit interval `[0, 1]` in `TopCat`. -/
abbrev I01 : TopCat.{0} := TopCat.of (Set.Icc (0 : ℝ) 1)

/-- The inclusion `[0, 1] ⟶ ℝ`. -/
def ι : I01 ⟶ realLine := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The base-change morphism of the identity square on `ℝ` is an isomorphism. -/
theorem isIso_baseChange_id :
    IsIso (baseChange ℚ (rfl : 𝟙 realLine ≫ 𝟙 realLine = 𝟙 realLine ≫ 𝟙 realLine)) :=
  isIso_baseChange_of_isIso ℚ _

/-- The square `ι ≫ 𝟙 ℝ = 𝟙 [0, 1] ≫ ι`. -/
theorem ι_square : ι ≫ 𝟙 realLine = 𝟙 I01 ≫ ι := by
  rw [Category.comp_id, Category.id_comp]

/-- Base change along `ι : [0, 1] ⟶ ℝ` of the identity direct image is an isomorphism. -/
theorem isIso_baseChange_ι : IsIso (baseChange ℚ ι_square) :=
  isIso_baseChange_of_isIso ℚ _

end TDA.Sheaf.BaseChangeExamples
