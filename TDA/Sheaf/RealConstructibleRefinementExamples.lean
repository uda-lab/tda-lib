import TDA.Sheaf.RealConstructibleRefinement
import TDA.Sheaf.RealIntervalSetsExamples

/-!
# Fixtures for refinement of the breakpoints on the real line

Coefficients `ℚ`. The breakpoint-free family `p₀` is refined by the single breakpoint `0`
(`p₁`, strata `0 ← 1 → 2`): `breakpoints_p₀_subset_p₁`.

* Bisecting a constant cell, sheaf level: the constant sheaf `constSheaf₀` (the interval sheaf of
  the single vertex for no breakpoints) has the single bar `[0, 0]`, with interval set `ℝ`
  (`barcode_sections_p₀_constSheaf₀`, `map_intervalSet_barcode_sections_p₀_constSheaf₀`). The
  breakpoint `0` bisects the cell `ℝ`: the refined interval of `[0, 0]` is the whole path
  `[0, 2]` (`refineInterval_p₀_p₁`), and for `p₁` the constant sheaf still has the single bar
  `[0, 2]`, with interval set `ℝ` (`barcode_sections_p₁_constSheaf₀`,
  `map_intervalSet_barcode_sections_p₁_constSheaf₀`).
* Bisecting a constant cell, graded: the constant sheaf placed in degree `n`
  (`hasConstructibleCohomology_constSheaf₀`) has, for the breakpoint `0`, the graded barcode
  `{[0, 2]}` in degree `n` and the empty barcode elsewhere (`gradedBarcode_p₁_constSheaf₀`), and
  as subsets of `ℝ` the single bar `ℝ` in degree `n` (`gradedBarcodeSets_p₁_constSheaf₀`).
-/

namespace TDA.Sheaf.RealConstructibleRefinementExamples

open CategoryTheory Limits DerivedCategory TDA.Persistence TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratificationExamples
  TDA.Sheaf.RealConstructibleExamples TDA.Sheaf.RealIntervalSetsExamples

/-- No breakpoints are among the breakpoint `0`. -/
theorem breakpoints_p₀_subset_p₁ : breakpoints p₀ ⊆ breakpoints p₁ := by
  rw [breakpoints_p₀]
  exact Finset.empty_subset _

/-- Without breakpoints, the constant sheaf has the single bar `[0, 0]`. -/
theorem barcode_sections_p₀_constSheaf₀ :
    haveI := finiteDimensional_sections ℚ p₀_strictMono (isConstructible_constSheaf₀ ℚ)
    barcode ((sections ℚ p₀).obj (constSheaf₀ ℚ)) = {⟨0, 1, by decide, by decide⟩} :=
  barcode_sections_extension_interval ℚ p₀_strictMono _

/-- Without breakpoints, the single bar of the constant sheaf is `ℝ`. -/
theorem map_intervalSet_barcode_sections_p₀_constSheaf₀ :
    haveI := finiteDimensional_sections ℚ p₀_strictMono (isConstructible_constSheaf₀ ℚ)
    (barcode ((sections ℚ p₀).obj (constSheaf₀ ℚ))).map (intervalSet p₀) = {Set.univ} := by
  rw [barcode_sections_p₀_constSheaf₀, Multiset.map_singleton, intervalSet_p₀]

/-- **The breakpoint `0` bisects the cell `ℝ`**: the refined interval of the single vertex is the
whole path `[0, 2]`. -/
theorem refineInterval_p₀_p₁ :
    refineInterval p₀_strictMono p₁_strictMono breakpoints_p₀_subset_p₁
      ⟨0, 1, by decide, by decide⟩ = wholeLine := by
  unfold refineInterval wholeLine
  congr 1
  · simp

/-- **Bisecting a constant cell.** For the breakpoint `0`, the constant sheaf still has a single
bar, the whole path `[0, 2]`. -/
theorem barcode_sections_p₁_constSheaf₀ :
    haveI := finiteDimensional_sections ℚ p₁_strictMono
      ((isConstructible_constSheaf₀ ℚ).mono breakpoints_p₀_subset_p₁)
    barcode ((sections ℚ p₁).obj (constSheaf₀ ℚ)) = {wholeLine} := by
  rw [barcode_sections_eq_map_refineInterval ℚ p₀_strictMono p₁_strictMono
    breakpoints_p₀_subset_p₁ (isConstructible_constSheaf₀ ℚ), barcode_sections_p₀_constSheaf₀,
    Multiset.map_singleton, refineInterval_p₀_p₁]

/-- **Bisecting a constant cell, as subsets of `ℝ`.** For the breakpoint `0`, the single bar of the
constant sheaf is still `ℝ`. -/
theorem map_intervalSet_barcode_sections_p₁_constSheaf₀ :
    haveI := finiteDimensional_sections ℚ p₁_strictMono
      ((isConstructible_constSheaf₀ ℚ).mono breakpoints_p₀_subset_p₁)
    (barcode ((sections ℚ p₁).obj (constSheaf₀ ℚ))).map (intervalSet p₁) = {Set.univ} := by
  rw [barcode_sections_map_intervalSet_refine ℚ p₀_strictMono p₁_strictMono
    breakpoints_p₀_subset_p₁ (isConstructible_constSheaf₀ ℚ)]
  exact map_intervalSet_barcode_sections_p₀_constSheaf₀

variable [HasDerivedCategory (TopCat.Sheaf (ModuleCat.{0} ℚ) realLine)]

/-- The constant sheaf placed in degree `n` has constructible cohomology without breakpoints. -/
theorem hasConstructibleCohomology_constSheaf₀ (n : ℤ) :
    HasConstructibleCohomology ℚ p₀ ((singleFunctor _ n).obj (constSheaf₀ ℚ)) :=
  hasConstructibleCohomology_singleFunctor ℚ p₀_strictMono (isConstructible_constSheaf₀ ℚ) n

/-- **Bisecting a constant cell, graded.** For the breakpoint `0`, the constant sheaf placed in
degree `n` has the graded barcode `{[0, 2]}` in degree `n` and the empty barcode elsewhere. -/
theorem gradedBarcode_p₁_constSheaf₀ (n i : ℤ) :
    gradedBarcode ℚ p₁_strictMono ((singleFunctor _ n).obj (constSheaf₀ ℚ))
        ((hasConstructibleCohomology_constSheaf₀ n).mono breakpoints_p₀_subset_p₁) i =
      if i = n then {wholeLine} else 0 := by
  rw [gradedBarcode_eq_map_refineInterval ℚ p₀_strictMono p₁_strictMono breakpoints_p₀_subset_p₁
    _ (hasConstructibleCohomology_constSheaf₀ n),
    gradedBarcode_singleFunctor ℚ p₀_strictMono (isConstructible_constSheaf₀ ℚ)]
  split_ifs
  · rw [barcode_sections_p₀_constSheaf₀, Multiset.map_singleton, refineInterval_p₀_p₁]
  · rfl

/-- **Bisecting a constant cell, graded, as subsets of `ℝ`.** For the breakpoint `0`, the constant
sheaf placed in degree `n` has the single bar `ℝ` in degree `n` and no bar elsewhere. -/
theorem gradedBarcodeSets_p₁_constSheaf₀ (n i : ℤ) :
    gradedBarcodeSets ℚ p₁_strictMono ((singleFunctor _ n).obj (constSheaf₀ ℚ))
        ((hasConstructibleCohomology_constSheaf₀ n).mono breakpoints_p₀_subset_p₁) i =
      if i = n then {Set.univ} else 0 := by
  rw [gradedBarcodeSets, gradedBarcode_p₁_constSheaf₀]
  split_ifs
  · rw [Multiset.map_singleton, intervalSet_wholeLine]
  · rfl

end TDA.Sheaf.RealConstructibleRefinementExamples
