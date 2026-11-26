import TDA.Sheaf.HereditarySplitting
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.Double
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Fixtures for hereditary splitting

Over the field `ℚ`, every `ℚ`-module is projective, so `Ext^n` between `ℚ`-modules vanishes for
`n ≥ 1` (`ext_rat_eq_zero`), and every bounded object of the derived category of `ℚ`-modules is
the direct sum of its shifted cohomology objects (`exists_iso_biproduct_homology_rat`).

The two-term complex `twoTerm : ℚ ⟶ ℚ` (zero differential, degrees `0` and `1`) has cohomology
`ℚ` in degrees `0` and `1` (`nonempty_homology_twoTerm_iso`, `not_isZero_homology_twoTerm`), and
its image in the derived category is `ℚ[0] ⊕ ℚ[-1]`, indexed by `Finset.Icc 0 1`
(`nonempty_iso_twoTerm`).

The derived category of `ℚ`-modules is any instance `HasDerivedCategory (ModuleCat.{0} ℚ)`.
-/

namespace TDA.Sheaf.HereditarySplittingExamples

open CategoryTheory Limits DerivedCategory Abelian

universe w

/-- The relation `0 → 1` of cochain complexes indexed by `ℤ`. -/
theorem rel_zero_one : (ComplexShape.up ℤ).Rel 0 1 := by simp

/-- The two-term complex `ℚ ⟶ ℚ` with zero differential, in degrees `0` and `1`. -/
noncomputable def twoTerm : CochainComplex (ModuleCat.{0} ℚ) ℤ :=
  HomologicalComplex.double (0 : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) rel_zero_one

/-- All differentials of `twoTerm` vanish. -/
theorem twoTerm_d (i j : ℤ) : twoTerm.d i j = 0 := by
  by_cases hi : i = 0
  · by_cases hj : j = 1
    · subst hi hj
      rw [twoTerm, HomologicalComplex.double_d _ _ (by decide), zero_comp, comp_zero]
    · exact HomologicalComplex.double_d_eq_zero₁ _ _ _ _ hj
  · exact HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hi

/-- `twoTerm` vanishes in negative degrees. -/
instance twoTerm_isStrictlyGE : twoTerm.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact HomologicalComplex.isZero_double_X _ _ i (by lia) (by lia)

/-- `twoTerm` vanishes in degrees above `1`. -/
instance twoTerm_isStrictlyLE : twoTerm.IsStrictlyLE 1 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact HomologicalComplex.isZero_double_X _ _ i (by lia) (by lia)

/-- The terms of `twoTerm` in degrees `0` and `1` are `ℚ`. -/
noncomputable def twoTermXIso (i : ℤ) (hi : i ∈ Finset.Icc (0 : ℤ) 1) :
    twoTerm.X i ≅ ModuleCat.of ℚ ℚ :=
  if h : i = 0 then eqToIso (congrArg twoTerm.X h) ≪≫ HomologicalComplex.doubleXIso₀ _ _
  else eqToIso (congrArg twoTerm.X (show i = 1 by have := Finset.mem_Icc.1 hi; lia)) ≪≫
    HomologicalComplex.doubleXIso₁ _ _ (by decide)

/-- `Ext^n` between `ℚ`-modules vanishes for `n ≥ 1`: every `ℚ`-module is projective. -/
theorem ext_rat_eq_zero [HasExt.{w} (ModuleCat.{0} ℚ)] (X Y : ModuleCat.{0} ℚ) {n : ℕ}
    (hn : 1 ≤ n) (e : Ext X Y n) : e = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have : Module.Projective ℚ X := Module.Projective.of_free
  have : Projective X := ModuleCat.projective_of_categoryTheory_projective X
  exact Ext.eq_zero_of_projective e

variable [HasDerivedCategory (ModuleCat.{0} ℚ)]

/-- **Every bounded complex of `ℚ`-vector spaces splits**: an object `K` of the derived category
of `ℚ`-modules with cohomology in `[a, b]` is `⨁_{i ∈ [a, b]} (Hⁱ K)[-i]`. -/
theorem exists_iso_biproduct_homology_rat (K : DerivedCategory (ModuleCat.{0} ℚ)) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] :
    Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
      (singleFunctor _ i).obj ((homologyFunctor _ i).obj K)) := by
  have := HasExt.standard (ModuleCat.{0} ℚ)
  exact exists_iso_biproduct_homology_of_two_le K a b fun _ _ _ hn e =>
    ext_rat_eq_zero _ _ (by lia) e

/-- **The cohomology of `twoTerm` is `ℚ` in degrees `0` and `1`.** -/
theorem nonempty_homology_twoTerm_iso (i : ℤ) (hi : i ∈ Finset.Icc (0 : ℤ) 1) :
    Nonempty ((homologyFunctor _ i).obj (Q.obj twoTerm) ≅ ModuleCat.of ℚ ℚ) :=
  ⟨(homologyFunctorFactors _ i).app twoTerm ≪≫
    (twoTerm.isoHomologyπ (i - 1) i (by simp) (twoTerm_d _ _)).symm ≪≫
    twoTerm.iCyclesIso i (i + 1) (by simp) (twoTerm_d _ _) ≪≫ twoTermXIso i hi⟩

/-- The cohomology of `twoTerm` in degrees `0` and `1` is nonzero. -/
theorem not_isZero_homology_twoTerm (i : ℤ) (hi : i ∈ Finset.Icc (0 : ℤ) 1) :
    ¬IsZero ((homologyFunctor _ i).obj (Q.obj twoTerm)) := fun h => by
  obtain ⟨e⟩ := nonempty_homology_twoTerm_iso i hi
  have := ModuleCat.subsingleton_of_isZero (h.of_iso e.symm)
  exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

/-- **`twoTerm` splits**: in the derived category it is `ℚ[0] ⊕ ℚ[-1]`, the sum over
`Finset.Icc 0 1` of `ℚ` placed in each degree. -/
theorem nonempty_iso_twoTerm :
    Nonempty (Q.obj twoTerm ≅
      ⨁ fun i : Finset.Icc (0 : ℤ) 1 => (singleFunctor _ i).obj (ModuleCat.of ℚ ℚ)) := by
  obtain ⟨e⟩ := exists_iso_biproduct_homology_rat (Q.obj twoTerm) 0 1
  exact ⟨e ≪≫ biproduct.mapIso fun i =>
    (singleFunctor _ i).mapIso (nonempty_homology_twoTerm_iso i i.2).some⟩

end TDA.Sheaf.HereditarySplittingExamples
