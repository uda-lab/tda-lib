import TDA.Sheaf.RealConstructibleAdjunction
import TDA.Sheaf.RealStratificationExamples
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Fixtures for the extension–sections adjunction

One breakpoint at `0` (`p₁`), strata `0 ← 1 → 2` with stars `(-∞, 0)`, `ℝ` and `(0, ∞)`.

* The skyscraper sheaf `skyOne` at `1` with value `k` is **not** constructible for the
  breakpoint `0` (`not_isConstructible_skyOne`): the restriction from `(1/2, 2)` to `(1/2, 3/4)`
  goes from `k` to `0`, although neither open contains a breakpoint.
* The universal property of `Φ P_v` holds for it all the same: `Hom(Φ P_2, skyOne)` is
  nontrivial (`nontrivial_hom_extension_skyOne`, the star `(0, ∞)` contains `1`) and
  `Hom(Φ P_0, skyOne)` is trivial (`subsingleton_hom_extension_skyOne`, the star `(-∞, 0)`
  misses `1`). This uses `extensionAdjunction` on a sheaf outside D1's equivalence.
-/

namespace TDA.Sheaf.RealConstructibleAdjunctionExamples

open CategoryTheory Limits TopologicalSpace Opposite TDA.Sheaf.AlternatingDiagram
  TDA.Sheaf.RealStratification TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratificationExamples

variable (k : Type) [Field k]

open Classical in
/-- Mathlib's skyscraper sheaf at `1` with value `k`. -/
noncomputable def skyOne : TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  skyscraperSheaf (1 : ℝ) (ModuleCat.of k k)

open Classical in
/-- Sections of `skyOne` over an open containing `1` are the field. -/
noncomputable def skyOneObjIso {U : Opens realLine} (h : (1 : ℝ) ∈ U) :
    (skyOne k).presheaf.obj (op U) ≅ ModuleCat.of k k :=
  eqToIso (ite_eq_left h)

open Classical in
/-- Sections of `skyOne` over an open missing `1` vanish. -/
theorem isZero_skyOne_obj {U : Opens realLine} (h : (1 : ℝ) ∉ U) :
    IsZero ((skyOne k).presheaf.obj (op U)) := by
  change IsZero ((skyscraperPresheaf (X := realLine) (1 : ℝ) (ModuleCat.of k k)).obj (op U))
  rw [skyscraperPresheaf_obj, ite_eq_right h]
  exact IsZero.of_iso (isZero_zero _)
    (terminalIsTerminal.uniqueUpToIso (isZero_zero _).isTerminal)

/-- **`skyOne` is not constructible for the breakpoint `0`.** -/
theorem not_isConstructible_skyOne : ¬ IsConstructible (breakpoints p₁) (skyOne k) := by
  intro hc
  have hUV : ioo (1 / 2) (3 / 4) ≤ ioo (1 / 2) 2 :=
    fun x hx => ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hS : (ioo (1 / 2) (3 / 4) : Set ℝ) ∩ breakpoints p₁ =
      (ioo (1 / 2) 2 : Set ℝ) ∩ breakpoints p₁ := by
    rw [breakpoints_p₁, Finset.coe_singleton]
    ext x
    simp only [ioo, Opens.coe_mk, Set.mem_inter_iff, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor <;> rintro ⟨⟨h₁, -⟩, rfl⟩ <;> norm_num at h₁
  have hiso := (isConstructible_iff.1 hc).1 hUV (isBasicOpen_ioo (by norm_num))
    (isBasicOpen_ioo (by norm_num)) hS
  have hz : IsZero (ModuleCat.of k k) :=
    ((isZero_skyOne_obj k (U := ioo (1 / 2) (3 / 4)) fun h => by
      have := h.2
      norm_num at this).of_iso (asIso ((skyOne k).presheaf.map (homOfLE hUV).op))).of_iso
      (skyOneObjIso k (U := ioo (1 / 2) 2) ⟨by norm_num, by norm_num⟩).symm
  have := ModuleCat.subsingleton_of_isZero hz
  exact one_ne_zero (Subsingleton.elim (1 : k) 0)

/-- **The universal property beyond constructible sheaves: a nonzero morphism.** The star
`(0, ∞)` of the right cell contains `1`, so `Hom(Φ P_2, skyOne) ≃ skyOne((0, ∞)) = k`. -/
theorem nontrivial_hom_extension_skyOne :
    Nontrivial ((extension k p₁_strictMono).obj (representable k (orient 1) 2) ⟶ skyOne k) := by
  have h1 : (1 : ℝ) ∈ star p₁ 2 := by
    change (1 : ℝ) ∈ (star p₁ 2 : Set ℝ)
    rw [coe_star_p₁_two]
    norm_num
  have : Nontrivial ((skyOne k).presheaf.obj (op (star p₁ 2))) :=
    (skyOneObjIso k h1).toLinearEquiv.toEquiv.nontrivial
  exact (homExtensionRepresentableEquiv k p₁_strictMono 2 (skyOne k)).nontrivial

/-- **The universal property beyond constructible sheaves: no nonzero morphism.** The star
`(-∞, 0)` of the left cell misses `1`, so `Hom(Φ P_0, skyOne) ≃ skyOne((-∞, 0)) = 0`. -/
theorem subsingleton_hom_extension_skyOne :
    Subsingleton ((extension k p₁_strictMono).obj (representable k (orient 1) 0) ⟶ skyOne k) := by
  have h1 : (1 : ℝ) ∉ star p₁ 0 := by
    change (1 : ℝ) ∉ (star p₁ 0 : Set ℝ)
    rw [coe_star_p₁_zero]
    norm_num
  have := ModuleCat.subsingleton_of_isZero (isZero_skyOne_obj k h1)
  exact (homExtensionRepresentableEquiv k p₁_strictMono 0 (skyOne k)).subsingleton

end TDA.Sheaf.RealConstructibleAdjunctionExamples
