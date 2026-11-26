import TDA.Topology.MayerVietorisSequence
import TDA.Topology.SmallChainsQuasiIsoExamples
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Examples for the Mayer–Vietoris connecting map

The fixtures use the open rays `(-∞, 1)` and `(0, ∞)` of
`TDA.Topology.SingularMayerVietorisExamples`, which cover the real line.

* **The sign lemma on a loop.** The path `lowerPath` runs from `1/4` to `3/4` inside the lower
  ray, and `upperPath` runs back from `3/4` to `1/4` inside the upper ray, through the point `2`,
  which is not in the lower ray (`upperPath_half`). With `pathChain` and `pointChain` the
  generators of the singular chains of a path and of a point, the sum of the two path chains,
  pushed into the line, is a cycle (`loop_isCycle`). The boundary of the lower piece is
  `[3/4] - [1/4]`, which comes from the intersection `(0, 1)` (`loop_boundary`), so
  `mayerVietorisδ_liftCycles` sends the class of the loop to the class of `[3/4] - [1/4]` in
  `H₀((0, 1))` (`mayerVietorisδ_loop`).
* **Naturality for the halving map.** `halfMap : x ↦ x / 2` is not the identity
  (`halfMap_ne_id`) and maps each ray into itself, so the three maps of the Mayer–Vietoris
  sequence of the rays commute with the maps it induces (`mayerVietoris_naturality_halfMap`).
-/

namespace TDA.Topology.MayerVietorisSequenceExamples

open CategoryTheory Limits AlgebraicTopology Opposite HomologicalComplex
open TDA.Topology.SingularMayerVietorisExamples TDA.Topology.SmallChainsQuasiIsoExamples
open scoped Simplicial

noncomputable section

/-- The path `τ ↦ 1/4 + τ/2` from `1/4` to `3/4`, inside the lower ray `(-∞, 1)`. -/
def lowerPath : TopCat.I ⟶ TopCat.of lowerRay :=
  TopCat.ofHom ⟨fun τ => ⟨1 / 4 + (TopCat.I.homeomorph τ : ℝ) / 2, by
      have := (TopCat.I.homeomorph τ).2.2
      change _ < (1 : ℝ)
      linarith⟩,
    (continuous_const.add ((continuous_subtype_val.comp
      TopCat.I.homeomorph.continuous).div_const 2)).subtype_mk fun τ => by
      have := (TopCat.I.homeomorph τ).2.2
      show 1 / 4 + (TopCat.I.homeomorph τ : ℝ) / 2 < 1
      linarith⟩

/-- The path `τ ↦ 3/4 - τ/2 + 6 τ (1 - τ)` from `3/4` to `1/4`, inside the upper ray `(0, ∞)`;
it passes through `2`, outside the lower ray. -/
def upperPath : TopCat.I ⟶ TopCat.of upperRay :=
  TopCat.ofHom ⟨fun τ => ⟨3 / 4 - (TopCat.I.homeomorph τ : ℝ) / 2 +
      6 * (TopCat.I.homeomorph τ : ℝ) * (1 - (TopCat.I.homeomorph τ : ℝ)), by
      have h₀ := (TopCat.I.homeomorph τ).2.1
      have h₁ := (TopCat.I.homeomorph τ).2.2
      change (0 : ℝ) < _
      nlinarith⟩, by
    have hc : Continuous fun τ : TopCat.I => (TopCat.I.homeomorph τ : ℝ) :=
      continuous_subtype_val.comp TopCat.I.homeomorph.continuous
    exact ((continuous_const.sub (hc.div_const 2)).add
      ((continuous_const.mul hc).mul (continuous_const.sub hc))).subtype_mk fun τ => by
      have h₀ := (TopCat.I.homeomorph τ).2.1
      have h₁ := (TopCat.I.homeomorph τ).2.2
      show (0 : ℝ) < 3 / 4 - (TopCat.I.homeomorph τ : ℝ) / 2 +
        6 * (TopCat.I.homeomorph τ : ℝ) * (1 - (TopCat.I.homeomorph τ : ℝ))
      nlinarith⟩

/-- The point `1/4` of the intersection `(0, 1)` of the rays. -/
def quarterPoint : TopCat.of ↥(lowerRay ∩ upperRay) :=
  ⟨1 / 4, by norm_num [lowerRay, upperRay]⟩

/-- The point `3/4` of the intersection `(0, 1)` of the rays. -/
def threeQuarterPoint : TopCat.of ↥(lowerRay ∩ upperRay) :=
  ⟨3 / 4, by norm_num [lowerRay, upperRay]⟩

/-- The upper path leaves the lower ray: it passes through `2`. -/
theorem upperPath_half :
    (upperPath (TopCat.I.homeomorph.symm ⟨1 / 2, by norm_num, by norm_num⟩)).1 = 2 := by
  simp [upperPath]
  norm_num

section Chains

variable {k : Type} [Ring k] (M : ModuleCat.{0} k)

/-- The singular `1`-chain `1 · γ` of a path `γ`, with coefficients `M`. -/
def pathChain {Y : TopCat.{0}} (γ : TopCat.I ⟶ Y) :
    M ⟶ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj Y).X 1 :=
  (TopCat.toSSet.obj Y).ιChainComplex (R := M) (TopCat.toSSetObj₁Equiv.symm γ)

/-- The singular `0`-chain `1 · y` of a point `y`, with coefficients `M`. -/
def pointChain {Y : TopCat.{0}} (y : Y) :
    M ⟶ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj Y).X 0 :=
  (TopCat.toSSet.obj Y).ιChainComplex (R := M) (TopCat.toSSetObj₀Equiv.symm y)

/-- The boundary of a path chain is its endpoint minus its starting point. -/
theorem pathChain_d {Y : TopCat.{0}} (γ : TopCat.I ⟶ Y) :
    pathChain M γ ≫ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj Y).d 1 0 =
      pointChain M (γ 1) - pointChain M (γ 0) := by
  have e := SSet.ιChainComplex_d (TopCat.toSSet.obj Y) (R := M) (TopCat.toSSetObj₁Equiv.symm γ)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, pow_zero,
    one_smul, add_zero, zero_add, pow_one, neg_smul, ← sub_eq_add_neg, Fin.succ_zero_eq_one] at e
  rw [TopCat.δ_zero_toSSetObj₁Equiv.symm, TopCat.δ_one_toSSetObj₁Equiv.symm] at e
  exact e

/-- A continuous map sends the chain of a path to the chain of the composite path. -/
theorem pathChain_map {Y Z : TopCat.{0}} (γ : TopCat.I ⟶ Y) (g : Y ⟶ Z) :
    pathChain M γ ≫ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map g).f 1 =
      pathChain M (γ ≫ g) :=
  SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map g) M (TopCat.toSSetObj₁Equiv.symm γ)

/-- The boundary of the image of a path under a continuous map is the image of its endpoint
minus the image of its starting point. -/
theorem pathChain_map_d {Y Z : TopCat.{0}} (γ : TopCat.I ⟶ Y) (g : Y ⟶ Z) :
    pathChain M γ ≫ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map g).f 1 ≫
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj Z).d 1 0 =
      pointChain M (g (γ 1)) - pointChain M (g (γ 0)) := by
  rw [← Category.assoc, pathChain_map, pathChain_d]
  rfl

/-- The image of a point chain under a continuous map is the point chain of the image. -/
theorem pointChain_map {Y Z : TopCat.{0}} (y : Y) (g : Y ⟶ Z) :
    pointChain M y ≫ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map g).f 0 =
      pointChain M (g y) :=
  SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map g) M (TopCat.toSSetObj₀Equiv.symm y)

/-- The `1`-chain of the lower path, in the lower ray. -/
abbrev lowerChain : M ⟶ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj
    (TopCat.of lowerRay)).X 1 :=
  pathChain M lowerPath

/-- The `1`-chain of the upper path, in the upper ray. -/
abbrev upperChain : M ⟶ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj
    (TopCat.of upperRay)).X 1 :=
  pathChain M upperPath

/-- The `0`-chain `[3/4] - [1/4]` of the intersection `(0, 1)` of the rays. -/
abbrev interChain : M ⟶ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj
    (TopCat.of ↥(lowerRay ∩ upperRay))).X 0 :=
  pointChain M threeQuarterPoint - pointChain M quarterPoint

/-- **The loop is a cycle.** The two paths, pushed into the line, form a singular `1`-cycle. -/
theorem loop_isCycle :
    (lowerChain M ≫
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map (subsetIncl lowerRay)).f 1 +
      upperChain M ≫
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map (subsetIncl upperRay)).f 1) ≫
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj lineSpace).d 1 0 = 0 := by
  have h₁ : subsetIncl lowerRay (lowerPath 1) = subsetIncl upperRay (upperPath 0) := by
    simp [lowerPath, upperPath, subsetIncl]
    norm_num
  have h₀ : subsetIncl lowerRay (lowerPath 0) = subsetIncl upperRay (upperPath 1) := by
    simp [lowerPath, upperPath, subsetIncl]
    norm_num
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, pathChain_map_d, pathChain_map_d, h₁,
    h₀]
  abel

/-- **The boundary of the lower piece comes from the intersection.** The image of
`[3/4] - [1/4]` in the lower ray is the boundary of the lower path. -/
theorem loop_boundary :
    interChain M ≫ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map
        (TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left))).f 0 =
      lowerChain M ≫
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj
          (TopCat.of lowerRay)).d 1 0 := by
  have h₁ : TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left) threeQuarterPoint =
      lowerPath 1 := by
    apply Subtype.ext
    simp [lowerPath, threeQuarterPoint]
    norm_num
  have h₀ : TopCat.ofHom (ContinuousMap.inclusion Set.inter_subset_left) quarterPoint =
      lowerPath 0 := by
    apply Subtype.ext
    simp [lowerPath, quarterPoint]
  rw [Preadditive.sub_comp, pointChain_map, pointChain_map, h₁, h₀, pathChain_d]

/-- **The sign lemma on the loop.** The connecting map of the two rays sends the class of the loop
`lowerPath + upperPath` to the class of `[3/4] - [1/4]` in `H₀((0, 1))`: the boundary of the
piece in the first ray, read in the intersection. -/
theorem mayerVietorisδ_loop :
    (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj lineSpace).liftCycles
        (lowerChain M ≫ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map
            (subsetIncl lowerRay)).f 1 +
          upperChain M ≫ (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).map
            (subsetIncl upperRay)).f 1) 0 (by simp) (loop_isCycle M) ≫
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj lineSpace).homologyπ 1 ≫
          mayerVietorisδ lowerRay upperRay M interior_lowerRay_union_interior_upperRay 0 =
      (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj
          (TopCat.of ↥(lowerRay ∩ upperRay))).liftCycles (interChain M) 0 (by simp)
          (by rw [HomologicalComplex.shape _ _ _ (by simp), Limits.comp_zero]) ≫
        (((singularChainComplexFunctor (ModuleCat.{0} k)).obj M).obj
          (TopCat.of ↥(lowerRay ∩ upperRay))).homologyπ 0 :=
  mayerVietorisδ_liftCycles lowerRay upperRay M interior_lowerRay_union_interior_upperRay 0
    (lowerChain M) (upperChain M) (loop_isCycle M) (interChain M) (loop_boundary M) 0 (by simp)

end Chains

/-! ### Naturality for the halving map -/

/-- The halving map `x ↦ x / 2` of the line. -/
def halfMap : lineSpace ⟶ lineSpace :=
  TopCat.ofHom ⟨fun x : ℝ => x / 2, by fun_prop⟩

/-- The halving map is not the identity. -/
theorem halfMap_ne_id : halfMap ≠ 𝟙 lineSpace := by
  intro h
  have := congrArg (fun g : lineSpace ⟶ lineSpace => g (2 : ℝ)) h
  norm_num [halfMap] at this

/-- The halving map sends the lower ray into itself. -/
theorem halfMap_mapsTo_lowerRay : Set.MapsTo halfMap lowerRay lowerRay := by
  intro x hx
  simp only [lowerRay, Set.mem_Iio] at hx ⊢
  change x / 2 < 1
  linarith

/-- The halving map sends the upper ray into itself. -/
theorem halfMap_mapsTo_upperRay : Set.MapsTo halfMap upperRay upperRay := by
  intro x hx
  simp only [upperRay, Set.mem_Ioi] at hx ⊢
  change 0 < x / 2
  linarith

/-- **Naturality for the halving map.** The three maps of the Mayer–Vietoris sequence of the two
rays commute with the maps induced by `halfMap` and its restrictions to the rays and to their
intersection. -/
theorem mayerVietoris_naturality_halfMap {k : Type} [Ring k] (M : ModuleCat.{0} k) (n : ℕ) :
    mayerVietorisδ lowerRay upperRay M interior_lowerRay_union_interior_upperRay n ≫
        ((singularHomologyFunctor (ModuleCat.{0} k) n).obj M).map
          (subsetRestrict halfMap (halfMap_mapsTo_lowerRay.inter_inter halfMap_mapsTo_upperRay)) =
      ((singularHomologyFunctor (ModuleCat.{0} k) (n + 1)).obj M).map halfMap ≫
        mayerVietorisδ lowerRay upperRay M interior_lowerRay_union_interior_upperRay n ∧
    mayerVietorisInterMap lowerRay upperRay M n ≫
        biprod.map (((singularHomologyFunctor (ModuleCat.{0} k) n).obj M).map
            (subsetRestrict halfMap halfMap_mapsTo_lowerRay))
          (((singularHomologyFunctor (ModuleCat.{0} k) n).obj M).map
            (subsetRestrict halfMap halfMap_mapsTo_upperRay)) =
      ((singularHomologyFunctor (ModuleCat.{0} k) n).obj M).map
          (subsetRestrict halfMap (halfMap_mapsTo_lowerRay.inter_inter halfMap_mapsTo_upperRay)) ≫
        mayerVietorisInterMap lowerRay upperRay M n ∧
    mayerVietorisSumMap lowerRay upperRay M n ≫
        ((singularHomologyFunctor (ModuleCat.{0} k) n).obj M).map halfMap =
      biprod.map (((singularHomologyFunctor (ModuleCat.{0} k) n).obj M).map
            (subsetRestrict halfMap halfMap_mapsTo_lowerRay))
          (((singularHomologyFunctor (ModuleCat.{0} k) n).obj M).map
            (subsetRestrict halfMap halfMap_mapsTo_upperRay)) ≫
        mayerVietorisSumMap lowerRay upperRay M n :=
  ⟨mayerVietorisδ_naturality M halfMap halfMap_mapsTo_lowerRay halfMap_mapsTo_upperRay _ _ n,
    mayerVietorisInterMap_naturality M halfMap halfMap_mapsTo_lowerRay halfMap_mapsTo_upperRay n,
    mayerVietorisSumMap_naturality M halfMap halfMap_mapsTo_lowerRay halfMap_mapsTo_upperRay n⟩


end

end TDA.Topology.MayerVietorisSequenceExamples
