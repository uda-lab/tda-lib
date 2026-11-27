import TDA.Sheaf.BandGradedBarcode
import TDA.Sheaf.BandSkyscraperDistance

/-!
# Two interval costs for real-band matching

A bounded open interval in degree zero matches the midpoint skyscraper in degree
one at the radius equal to half its length. A skyscraper in any degree has infinite
deletion cost.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory
open TDA.Persistence TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealStratification
open scoped ENNReal ZeroObject

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Field k] {m : ℕ} {p : Fin m → ℝ}

local notation "Sh[" k "]" => realLine.Sheaf (ModuleCat k)
local notation "D⁺[" k "]" => DerivedCategory.Plus (Sh[k])
local notation "Single[" i "," F "]" => Functor.obj (Plus.singleFunctor _ i) F

variable [HasDerivedCategory (Sh[k])]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem aug_singleFunctor_skyscraper_ne_zero (a : ℝ) (i : ℤ)
    {ε : ℝ} (hε : 0 ≤ ε) : (aug k hε).app (Single[i, skyscraperSheaf k a]) ≠ 0 := by
  let S := shiftFunctor (D⁺[k]) (-i)
  let X := skyscraper k a
  let e : S.obj X ≅ Single[i, skyscraperSheaf k a] :=
    ((Plus.singleFunctors _).shiftIso (-i) i 0 (neg_add_cancel i)).app _
  intro hz
  have h := (aug k hε).naturality e.hom
  change (T k ε).map e.hom ≫ (aug k hε).app (Single[i, skyscraperSheaf k a]) =
    (aug k hε).app (S.obj X) ≫ e.hom at h
  have hshift : (aug k hε).app (S.obj X) = 0 :=
    (cancel_mono e.hom).mp (by simpa only [hz, comp_zero, zero_comp] using h.symm)
  have hm := (aug k hε).shift_app (-i) X
  change S.map ((aug k hε).app X) = ((T k ε).commShiftIso (-i)).inv.app X ≫
    (aug k hε).app (S.obj X) ≫ ((𝟭 (D⁺[k])).commShiftIso (-i)).hom.app X at hm
  rw [hshift, zero_comp, comp_zero] at hm
  apply aug_skyscraper_ne_zero k a hε
  apply S.map_injective
  rw [S.map_zero]
  exact hm

/-- A skyscraper in any cohomological degree has infinite distance from zero. -/
theorem distance_singleFunctor_skyscraper_zero (a : ℝ) (i : ℤ) :
    distance (Single[i, skyscraperSheaf k a]) 0 = ⊤ := by
  refine distance_eq_top_iff.mpr fun ε => ⟨fun w => ?_⟩
  exact aug_singleFunctor_skyscraper_ne_zero k a i _ (nonempty_witness_zero_iff.mp ⟨w⟩)

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))] in
/-- At half the length of the open interval, its convolution is the midpoint skyscraper
in degree one. -/
theorem nonempty_iso_T_interval_Ioo_shifted_skyscraper
    (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) {a b ε : ℝ}
    (hε : 0 ≤ ε) (hab : a < b) (h : 2 * ε = b - a) (hJ : intervalSet p J = Set.Ioo a b) :
    Nonempty ((T k ε).obj ((GradedInterval.mk J 0).obj k hp) ≅
      Single[1, skyscraperSheaf k ((a + b) / 2)]) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_T_Ioo_threshold (k := k) hp J hε hab h hJ
  obtain ⟨f⟩ := nonempty_iso_skyscraperSheaf_interval k _ K hK
  exact ⟨e ≪≫ (Plus.singleFunctor (Sh[k]) 1).mapIso f.symm⟩

/-- The degree-zero open interval and the midpoint in degree one admit a witness
exactly at the radii at least half the interval length. -/
theorem nonempty_witness_interval_Ioo_shifted_skyscraper_iff
    (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) {a b ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hab : a < b) (h : 2 * ε = b - a)
    (hJ : intervalSet p J = Set.Ioo a b) :
    Nonempty (Witness k hδ ((GradedInterval.mk J 0).obj k hp)
      (Single[1, skyscraperSheaf k ((a + b) / 2)])) ↔ ε ≤ δ := by
  let F := (GradedInterval.mk J 0).obj k hp
  constructor
  · rintro ⟨w⟩
    by_contra! hlt
    obtain ⟨K, _, ⟨e⟩⟩ := exists_intervalSheaf_T_Ioo_below
      (k := k) hp J hδ hab (by linarith : 2 * δ < b - a) hJ
    have hz : e.inv ≫ w.hom = 0 :=
      Plus.TStructure.t.zero_of_isLE_of_isGE _ 0 1 (by decide) inferInstance inferInstance
    have hw : w.hom = 0 := (cancel_epi e.inv).mp (hz.trans (comp_zero (f := e.inv)).symm)
    exact aug_singleFunctor_skyscraper_ne_zero k ((a + b) / 2) 1 _ (by
      simpa only [hw, comp_zero] using w.inv_hom.symm)
  · intro hd
    obtain ⟨e⟩ := nonempty_iso_T_interval_Ioo_shifted_skyscraper k hp J hε hab h hJ
    exact ⟨((Witness.toConvolution F hε).congr (Iso.refl _) e).mono hd⟩

/-- The pair cost of the degree-zero open interval and its midpoint in degree one
is half the interval length. -/
theorem distance_interval_Ioo_shifted_skyscraper (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {a b ε : ℝ}
    (hε : 0 ≤ ε) (hab : a < b) (h : 2 * ε = b - a) (hJ : intervalSet p J = Set.Ioo a b) :
    distance ((GradedInterval.mk J 0).obj k hp) (Single[1, skyscraperSheaf k ((a + b) / 2)]) =
      ENNReal.ofReal ε := by
  obtain ⟨w⟩ :=
    (nonempty_witness_interval_Ioo_shifted_skyscraper_iff k hp J hε hε hab h hJ).mpr le_rfl
  refine le_antisymm w.distance_le (le_distance_iff.mpr fun δ wδ => ?_)
  rw [ENNReal.ofReal_eq_coe_nnreal hε, ENNReal.coe_le_coe]
  exact (nonempty_witness_interval_Ioo_shifted_skyscraper_iff k hp J hε
    δ.coe_nonneg hab h hJ).mp wδ

end TDA.Sheaf.BandConvolution
