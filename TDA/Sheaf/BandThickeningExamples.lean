import TDA.Sheaf.BandThickening
import TDA.Sheaf.RealIntervalSetsExamples
import Mathlib.Algebra.Field.Rat

/-!
# The thickening formula: fixtures

Coefficients `ℚ`; Mathlib's `HasDerivedCategory.standard` is a local instance in this file only.
Opens are `RealStratificationExamples.ioo a b = (a, b)`, order-connected by `ordConnected_ioo`.

* Thickened opens: at radius `1` the interval `(0, 1)` thickens to `(-1, 2)`
  (`bandOpen_one_ioo`), at radius `0` it stays `(0, 1)` (`bandOpen_zero_ioo`), and
  `(1/4, 1/2)` thickens to `(-3/4, 3/2)` (`bandOpen_one_ioo_quarter`).
* The thickening formula at radius `1`: for every sheaf `F`, the sections of
  `(q 1)_* (p 1)⁻¹ F` over `(0, 1)` are `F((-1, 2))` (`thickeningSectionsIoo`), and so are
  the sections of `H⁰ (T ℚ 1 (F[0]))` (`H0TSectionsIoo`, through `H0TIso`).
* Restriction from `(0, 1)` to `(1/4, 1/2)` is, through the formula, restriction from `(-1, 2)` to
  `(-3/4, 3/2)` (`thickeningSectionsIoo_map`), and the formula is natural in `F`
  (`thickeningSectionsIoo_naturality`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TDA.Sheaf TDA.Sheaf.BandConvolution
  TDA.Sheaf.RealStratificationExamples

namespace TDA.Sheaf.BandThickeningExamples

attribute [local instance] HasDerivedCategory.standard

/-- The open `ioo a b` is order-connected. -/
theorem ordConnected_ioo (a b : ℝ) : ((ioo a b : Opens realLine) : Set ℝ).OrdConnected :=
  Set.ordConnected_Ioo

/-- At radius `1`, `(0, 1)` thickens to `(-1, 2)`. -/
theorem bandOpen_one_ioo : bandOpen 1 (ioo 0 1) = ioo (-1) 2 :=
  Opens.ext ((coe_bandOpen_Ioo zero_le_one (by norm_num)).trans (by norm_num [ioo]))

/-- At radius `0`, `(0, 1)` does not change. -/
theorem bandOpen_zero_ioo : bandOpen 0 (ioo 0 1) = ioo 0 1 :=
  Opens.ext ((coe_bandOpen_Ioo le_rfl (by norm_num)).trans (by norm_num [ioo]))

/-- At radius `1`, `(1/4, 1/2)` thickens to `(-3/4, 3/2)`. -/
theorem bandOpen_one_ioo_quarter : bandOpen 1 (ioo (1 / 4) (1 / 2)) = ioo (-3 / 4) (3 / 2) :=
  Opens.ext ((coe_bandOpen_Ioo zero_le_one (by norm_num)).trans (by norm_num [ioo]))

/-- **The thickening formula at radius `1` over `(0, 1)`**: the sections of `(q 1)_* (p 1)⁻¹ F`
over `(0, 1)` are the sections of `F` over `(-1, 2)`. -/
def thickeningSectionsIoo (F : realLine.Sheaf (ModuleCat.{0} ℚ)) :
    ((thickening ℚ 1).obj F).presheaf.obj (op (ioo 0 1)) ≅ F.presheaf.obj (op (ioo (-1) 2)) :=
  thickeningSectionsIso ℚ 1 F (ioo 0 1) (ordConnected_ioo 0 1) ≪≫
    F.presheaf.mapIso (eqToIso (congrArg op bandOpen_one_ioo))

/-- **Degree zero of `T ℚ 1` over `(0, 1)`**: the sections of `H⁰ (T ℚ 1 (F[0]))` over `(0, 1)`
are the sections of `F` over `(-1, 2)`, through `H0TSectionsIso`. -/
def H0TSectionsIoo (F : realLine.Sheaf (ModuleCat.{0} ℚ)) :
    ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((T ℚ 1).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).presheaf.obj
        (op (ioo 0 1)) ≅
      F.presheaf.obj (op (ioo (-1) 2)) :=
  H0TSectionsIso ℚ 1 F (ioo 0 1) (ordConnected_ioo 0 1) ≪≫
    F.presheaf.mapIso (eqToIso (congrArg op bandOpen_one_ioo))

/-- `(1/4, 1/2) ≤ (0, 1)`. -/
theorem ioo_quarter_le : ioo (1 / 4) (1 / 2) ≤ ioo 0 1 :=
  fun _ hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **Restriction through the formula**: restricting from `(0, 1)` to `(1/4, 1/2)` in
`(q 1)_* (p 1)⁻¹ F` is restricting from the thickened `(-1, 2)` to the thickened `(-3/4, 3/2)`
in `F`. -/
theorem thickeningSectionsIoo_map (F : realLine.Sheaf (ModuleCat.{0} ℚ)) :
    ((thickening ℚ 1).obj F).presheaf.map (homOfLE ioo_quarter_le).op ≫
        (thickeningSectionsIso ℚ 1 F _ (ordConnected_ioo (1 / 4) (1 / 2))).hom =
      (thickeningSectionsIso ℚ 1 F _ (ordConnected_ioo 0 1)).hom ≫
        F.presheaf.map (homOfLE (bandOpen_mono_right 1 ioo_quarter_le)).op :=
  thickeningSectionsIso_hom_map ℚ 1 F ioo_quarter_le _ _

/-- **Naturality through the formula**: a morphism of sheaves acts on the sections of the
thickenings over `(0, 1)` as on the sections over `(-1, 2)`. -/
theorem thickeningSectionsIoo_naturality {F G : realLine.Sheaf (ModuleCat.{0} ℚ)} (φ : F ⟶ G) :
    ((thickening ℚ 1).map φ).hom.app (op (ioo 0 1)) ≫ (thickeningSectionsIoo G).hom =
      (thickeningSectionsIoo F).hom ≫ φ.hom.app (op (ioo (-1) 2)) := by
  simp only [thickeningSectionsIoo, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [← Category.assoc, thickeningSectionsIso_hom_naturality, Category.assoc, Category.assoc]
  congr 1
  exact (φ.hom.naturality _).symm

/-- The thickening formula applies to the interval sheaf of the whole line: its thickening has
sections over `(0, 1)` equal to its sections over `(-1, 2)`. -/
example : ((thickening ℚ 1).obj RealIntervalSetsExamples.wholeLineSheaf).presheaf.obj
      (op (ioo 0 1)) ≅
    RealIntervalSetsExamples.wholeLineSheaf.presheaf.obj (op (ioo (-1) 2)) :=
  thickeningSectionsIoo _

/-- `H⁰ T_1` on sheaves in degree `0` is the thickening functor. -/
example : DerivedCategory.Plus.singleFunctor _ 0 ⋙ T ℚ 1 ⋙
    DerivedCategory.Plus.homologyFunctor _ 0 ≅ thickening ℚ 1 :=
  H0TIso ℚ 1

end TDA.Sheaf.BandThickeningExamples
