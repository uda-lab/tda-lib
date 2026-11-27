import TDA.Sheaf.RealConstructibleDerived
import TDA.Sheaf.RealConstructibleExamples

/-!
# Fixtures for graded barcodes on the real line

One breakpoint at `0` (`p₁`), strata `0 ← 1 → 2` with stars `(-∞, 0)`, `ℝ` and `(0, ∞)`,
coefficients `ℚ`, and any instance `HasDerivedCategory` for sheaves of `ℚ`-modules on `ℝ`.

* `gradedBarcode_pointSheaf_one`: the field at the point `0` (`pointSheaf`, the interval
  `[1, 1]`) placed in degree `1` has the barcode `{[1, 1]}` in degree `1` and the empty barcode in
  every other degree.
* `twoDegree`: the sum of `Φ [0, 1]` (the field on `(-∞, 0]`, `segLeft`) in degree `0` and of the
  field at `0` in degree `1`, an object with cohomology in two degrees. Its graded barcode is
  `{[0, 1]}` in degree `0` (`gradedBarcode_twoDegree_zero`), `{[1, 1]}` in degree `1`
  (`gradedBarcode_twoDegree_one`) and empty elsewhere (`gradedBarcode_twoDegree_of_ne`).
-/

namespace TDA.Sheaf.RealConstructibleDerivedExamples

open CategoryTheory Limits DerivedCategory TDA.Persistence TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratificationExamples
  TDA.Sheaf.RealConstructibleExamples

variable [HasDerivedCategory (TopCat.Sheaf (ModuleCat.{0} ℚ) realLine)]

/-- **A constructible sheaf placed in degree `1`.** The field at `0` placed in degree `1` has
the barcode `{[1, 1]}` in degree `1` and the empty barcode in every other degree. -/
theorem gradedBarcode_pointSheaf_one (i : ℤ) :
    gradedBarcode ℚ p₁_strictMono ((singleFunctor _ 1).obj (pointSheaf ℚ))
        (hasConstructibleCohomology_singleFunctor ℚ p₁_strictMono
          (isConstructible_intervalSheaf ℚ pointSegment) 1) i =
      if i = 1 then {pointSegment} else 0 := by
  rw [gradedBarcode_singleFunctor ℚ p₁_strictMono
    (isConstructible_intervalSheaf ℚ pointSegment)]
  split_ifs
  · exact barcode_sections_extension_interval ℚ p₁_strictMono pointSegment
  · rfl

/-- The barcodes of `twoDegree`: `{[0, 1]}` in degree `0`, `{[1, 1]}` in the other degrees. -/
def twoDegreeBarcode (x : ℤ) : Multiset (FiniteInterval 3) :=
  if x = 0 then {segLeft} else {pointSegment}

/-- The field on `(-∞, 0]` in degree `0` plus the field at `0` in degree `1`:
`⨁_{x ∈ [0, 1]} (barcodeSheaf (twoDegreeBarcode x))[-x]`. -/
noncomputable def twoDegree : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} ℚ) realLine) :=
  ⨁ fun x : Finset.Icc (0 : ℤ) 1 =>
    (singleFunctor _ x).obj (barcodeSheaf ℚ p₁_strictMono (twoDegreeBarcode x))

/-- `twoDegree` has constructible cohomology. -/
theorem hasConstructibleCohomology_twoDegree :
    HasConstructibleCohomology ℚ p₁ twoDegree :=
  hasConstructibleCohomology_biproduct ℚ p₁_strictMono _ _

/-- The graded barcode of `twoDegree` in degree `0` is `{[0, 1]}`. -/
theorem gradedBarcode_twoDegree_zero :
    gradedBarcode ℚ p₁_strictMono twoDegree hasConstructibleCohomology_twoDegree 0 =
      {segLeft} :=
  (gradedBarcode_biproduct ℚ p₁_strictMono _ twoDegreeBarcode 0).trans (by simp [twoDegreeBarcode])

/-- The graded barcode of `twoDegree` in degree `1` is `{[1, 1]}`. -/
theorem gradedBarcode_twoDegree_one :
    gradedBarcode ℚ p₁_strictMono twoDegree hasConstructibleCohomology_twoDegree 1 =
      {pointSegment} :=
  (gradedBarcode_biproduct ℚ p₁_strictMono _ twoDegreeBarcode 1).trans (by simp [twoDegreeBarcode])

/-- The graded barcode of `twoDegree` is empty outside the degrees `0` and `1`. -/
theorem gradedBarcode_twoDegree_of_ne {i : ℤ} (h₀ : i ≠ 0) (h₁ : i ≠ 1) :
    gradedBarcode ℚ p₁_strictMono twoDegree hasConstructibleCohomology_twoDegree i = 0 :=
  (gradedBarcode_biproduct ℚ p₁_strictMono _ twoDegreeBarcode i).trans
    (ite_eq_right_iff.2 fun h => by simp only [Finset.mem_Icc] at h; lia)

end TDA.Sheaf.RealConstructibleDerivedExamples
