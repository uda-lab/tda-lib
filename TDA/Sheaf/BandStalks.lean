import TDA.Sheaf.IntervalFibration
import TDA.Sheaf.IntervalFibre

/-!
# Stalks of the derived direct image along a band projection

Let `k` be a ring and `a y : ℝ`. The fibre `(q a)⁻¹ {y}` of the second projection of the closed
band `D a` is parametrised by `[y - a, y + a]` through `fibreEmb a y : x ↦ (x, y)`
(`mem_range_fibreEmb`; `fibreEmb_eq` relates it to `fibreIso a y`). The stalk at `y` is read
through the inverse image along `ptAt y : pt ⟶ ℝ` (which is `ptOf y`, `ptAt_eq`), and
`fibreEmb a y ≫ q a = toPt _ ≫ ptAt y` (`fibreEmb_comp_q`).

The band projection is an interval fibration (`TDA.Sheaf.IntervalFibration`):

* `fibreCoordinate_q a`: the first coordinate `p a` is a fibre coordinate of `q a`, since
  `z ↦ (q a z, p a z)` is the inclusion of the band into `ℝ²` up to the swap and `q a` is proper
  (`isProperMap_q`).
* `isFibreParam_fibreEmb a y`: `fibreEmb a y` is a fibre parametrisation of `q a` at `y`, and
  `intervalFibration_q a` is the interval fibration with `lo y = y - a`, `hi y = y + a` and
  `e = fibreEmb a`.

The general results specialise to the band:

* `exists_preimage_q_le`, `exists_preimage_q_le_of_fibreEmb`: tubes `(q a)⁻¹ U`, `U ∋ y` open,
  are cofinal among the open neighbourhoods of the fibre.
* `exists_unit_eq_fibreEmb`: every section of `(fibreEmb a y)⁻¹ G` over the fibre comes from a
  section of `G` over an open neighbourhood of the fibre.
* `stalkComparison a y G : (ptAt y)⁻¹ (q a)_* G ⟶ Γ([y - a, y + a]; (fibreEmb a y)⁻¹ G)`, the
  adjoint of `(q a)_*` applied to the unit; it is the underived base change of the fibre square
  (`baseChangeSheaf_fibreEmb_app`), is described on sections by `stalkComparison_app_top`, is
  natural (`stalkComparison_naturality`) and is an isomorphism (`isIso_stalkComparison`).
  `stalkIso a y` is the natural isomorphism
  `(q a)_* ⋙ (ptAt y)⁻¹ ≅ (fibreEmb a y)⁻¹ ⋙ Γ([y - a, y + a]; -)`, and `stalkSectionsIso` reads
  it as `((q a)_* G)_y ≅ Γ([y - a, y + a]; (fibreEmb a y)⁻¹ G)`.
* `nonempty_stalkFormula`, `nonempty_stalkFormula_homology`: for `F ∈ D⁺(Sh(D a))`,
  `(ptAt y)⁻¹ R(q a)_* F ≅ RΓ([y - a, y + a]; (fibreEmb a y)⁻¹ F)`, by proper base change on
  the fibre (`FibreCoordinate.IsFibreParam.isIso_baseChange`).
* `isZero_H_stalk_pushforwardPlus_q`: for a sheaf `G` placed in degree `0`, these stalks vanish in
  degrees `i ≥ 2`.

Derived categories are instance arguments for exactly the spaces each statement mentions.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable {k : Type} [Ring k]

namespace BandConvolution

/-- The point `y` of the real line, as a map from the one-point space. -/
def ptAt (y : ℝ) : pt ⟶ realLine := TopCat.ofHom (ContinuousMap.const _ y)

/-- `ptAt y` is the inclusion `ptOf y` of the point `y`. -/
theorem ptAt_eq (y : ℝ) : ptAt y = ptOf y := rfl

/-- The fibre `(q a)⁻¹ {y}` parametrised by `[y - a, y + a]`: `x ↦ (x, y)`. -/
def fibreEmb (a y : ℝ) : TopCat.of (Set.Icc (y - a) (y + a)) ⟶ D a :=
  TopCat.ofHom ⟨fun x => ⟨(x.1, y), by
      change dist x.1 y ≤ a
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [x.2.1, x.2.2], by linarith [x.2.1, x.2.2]⟩⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩

/-- `fibreEmb a y` sends `x` to `(x, y)`. -/
@[simp]
theorem coe_fibreEmb_apply (a y : ℝ) (x : TopCat.of (Set.Icc (y - a) (y + a))) :
    ((fibreEmb a y x : band a) : ℝ × ℝ) = (x.1, y) := rfl

/-- `fibreEmb a y` is the inverse of `fibreIso a y` followed by the inclusion of the fibre. -/
theorem fibreEmb_eq (a y : ℝ) :
    fibreEmb a y = (fibreIso a y).inv ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :=
  rfl

/-- The image of `fibreEmb a y` is the fibre `(q a)⁻¹ {y}`. -/
theorem mem_range_fibreEmb {a y : ℝ} {z : D a} : z ∈ Set.range (fibreEmb a y) ↔ q a z = y := by
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro h
    refine ⟨fibreHomeo a y ⟨z, h⟩, Subtype.ext (Prod.ext rfl ?_)⟩
    exact h.symm

/-- The fibre square: `fibreEmb a y ≫ q a = toPt _ ≫ ptAt y`. -/
theorem fibreEmb_comp_q (a y : ℝ) : fibreEmb a y ≫ q a = toPt _ ≫ ptAt y := rfl

/-- **The first coordinate is a fibre coordinate of the band projection `q a`**: `q a` is proper
(`isProperMap_q`) and `z ↦ (q a z, p a z)` is the inclusion of the band into `ℝ²` followed by the
swap of the factors. -/
def fibreCoordinate_q (a : ℝ) : FibreCoordinate (q a) where
  t := (p a).hom
  isInducing := (Homeomorph.prodComm ℝ ℝ).isInducing.comp Topology.IsInducing.subtypeVal
  isClosedMap := (isProperMap_q a).isClosedMap

/-- The fibre coordinate of `q a` is the first projection `p a`. -/
@[simp]
theorem fibreCoordinate_q_t (a : ℝ) (z : D a) : (fibreCoordinate_q a).t z = p a z := rfl

/-- `fibreEmb a y` is a fibre parametrisation of `q a` at `y` in the coordinate `p a`. -/
theorem isFibreParam_fibreEmb (a y : ℝ) : (fibreCoordinate_q a).IsFibreParam y (fibreEmb a y) where
  comp_eq := fibreEmb_comp_q a y
  t_apply _ := rfl
  mem_range _ hz := mem_range_fibreEmb.2 hz

/-- **The band projection is an interval fibration**, with fibre coordinate `p a`, fibre
intervals `[y - a, y + a]` and fibre parametrisations `fibreEmb a y`. -/
def intervalFibration_q (a : ℝ) : IntervalFibration (q a) where
  toFibreCoordinate := fibreCoordinate_q a
  lo y := y - a
  hi y := y + a
  e := fibreEmb a
  isFibreParam := isFibreParam_fibreEmb a

/-- The fibre parametrisations of `intervalFibration_q a` are `fibreEmb a`. -/
@[simp]
theorem intervalFibration_q_e (a y : ℝ) : (intervalFibration_q a).e y = fibreEmb a y := rfl

/-- **Tubes are cofinal.** An open subset of the band containing the fibre `(q a)⁻¹ {y}`
contains `(q a)⁻¹ U` for an open `U ∋ y`, because `q a` is a closed map (`isProperMap_q`). -/
theorem exists_preimage_q_le (a y : ℝ) (W : Opens (D a)) (hW : ∀ z : D a, q a z = y → z ∈ W) :
    ∃ U : Opens realLine, y ∈ U ∧ (Opens.map (q a)).obj U ≤ W :=
  exists_preimage_le_of_isClosedMap (isProperMap_q a).isClosedMap y W hW

/-- An open subset of the band whose preimage under `fibreEmb a y` is everything contains
`(q a)⁻¹ U` for an open `U ∋ y`. -/
theorem exists_preimage_q_le_of_fibreEmb (a y : ℝ) (W : Opens (D a))
    (hW : ⊤ ≤ (Opens.map (fibreEmb a y)).obj W) :
    ∃ U : Opens realLine, y ∈ U ∧ (Opens.map (q a)).obj U ≤ W :=
  (isFibreParam_fibreEmb a y).exists_preimage_le W hW

variable (k)

/-- **Sections over the fibre come from a neighbourhood (degree-0 tautness, surjectivity).** Every
section of `(fibreEmb a y)⁻¹ G` over `[y - a, y + a]` is the restriction of the image under the
adjunction unit of a section of `G` over an open neighbourhood `W` of the fibre. -/
theorem exists_unit_eq_fibreEmb {a y : ℝ} (G : (D a).Sheaf (ModuleCat.{0} k))
    (t : ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.obj (op ⊤)) :
    ∃ (W : Opens (D a)) (hW : ⊤ ≤ (Opens.map (fibreEmb a y)).obj W) (s : G.presheaf.obj (op W)),
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.map (homOfLE hW).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app
          G).hom.app (op W) s) = t :=
  (isFibreParam_fibreEmb a y).exists_unit_eq G t

section stalk

variable (a y : ℝ)

/-- **The stalk comparison.** For a sheaf `G` of `k`-modules on the band `D a`, the morphism
`(ptAt y)⁻¹ (q a)_* G ⟶ Γ([y - a, y + a]; (fibreEmb a y)⁻¹ G)` of sheaves on the point adjoint to
`(q a)_*` applied to the unit `G ⟶ (fibreEmb a y)_* (fibreEmb a y)⁻¹ G`; the composite
`fibreEmb a y ≫ q a` is `toPt _ ≫ ptAt y` (`fibreEmb_comp_q`). -/
def stalkComparison (G : (D a).Sheaf (ModuleCat.{0} k)) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G) ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (ptAt y)).homEquiv _ _).symm
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app G))

/-- **The underived base change of the fibre square is the stalk comparison.** For a sheaf `G`
of `k`-modules on `D a`, `baseChangeSheaf` of `fibreEmb a y ≫ q a = toPt _ ≫ ptAt y` at `G` is
`stalkComparison k a y G`. -/
theorem baseChangeSheaf_fibreEmb_app (G : (D a).Sheaf (ModuleCat.{0} k)) :
    (baseChangeSheaf k (fibreEmb_comp_q a y)).app G = stalkComparison k a y G := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k)
    (ptAt y)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, unit_baseChangeSheaf, stalkComparison]
  exact (Category.comp_id _).trans (Equiv.apply_symm_apply _ _).symm

/-- **The stalk comparison on sections.** For an open `U ∋ y` and a section `s` of `G` over
`(q a)⁻¹ U`, the comparison sends the restriction to the point of the unit image of `s` to the
restriction to `[y - a, y + a]` of the unit image of `s` in `(fibreEmb a y)⁻¹ G`. -/
theorem stalkComparison_app_top (G : (D a).Sheaf (ModuleCat.{0} k)) {U : Opens realLine}
    (hU : ⊤ ≤ (Opens.map (ptAt y)).obj U)
    (hU' : ⊤ ≤ (Opens.map (fibreEmb a y)).obj ((Opens.map (q a)).obj U))
    (s : G.presheaf.obj (op ((Opens.map (q a)).obj U))) :
    (stalkComparison k a y G).hom.app (op ⊤)
        (((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
            ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)).presheaf.map
          (homOfLE hU).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (ptAt y)).unit.app
            ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)).hom.app (op U) s)) =
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.map
        (homOfLE hU').op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (fibreEmb a y)).unit.app
          G).hom.app (op ((Opens.map (q a)).obj U)) s) := by
  rw [← baseChangeSheaf_fibreEmb_app]
  exact baseChangeSheaf_app_hom_app_top k (fibreEmb_comp_q a y) G hU hU' s

/-- The stalk comparison is natural in `G`. -/
theorem stalkComparison_naturality {G G' : (D a).Sheaf (ModuleCat.{0} k)} (φ : G ⟶ G') :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).map φ) ≫ stalkComparison k a y G' =
      stalkComparison k a y G ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt _)).map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).map φ) := by
  rw [← baseChangeSheaf_fibreEmb_app, ← baseChangeSheaf_fibreEmb_app]
  exact (baseChangeSheaf k (fibreEmb_comp_q a y)).naturality φ

/-- **The stalk comparison is an isomorphism** (degree-0 tautness of the fibre). -/
instance isIso_stalkComparison (G : (D a).Sheaf (ModuleCat.{0} k)) :
    IsIso (stalkComparison k a y G) := by
  rw [← baseChangeSheaf_fibreEmb_app]
  exact (isFibreParam_fibreEmb a y).isIso_baseChangeSheaf_app G

/-- **The stalk of `(q a)_* G` at `y` is the sections of `G` over the fibre.** The stalk
comparison as a natural isomorphism `(q a)_* ⋙ (ptAt y)⁻¹ ≅ (fibreEmb a y)⁻¹ ⋙ Γ([y - a, y + a]; -)`
of functors from sheaves of `k`-modules on `D a` to sheaves on the point. -/
def stalkIso :
    TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y) ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y) ⋙
        TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt (TopCat.of (Set.Icc (y - a) (y + a)))) :=
  NatIso.ofComponents (fun G => asIso (stalkComparison k a y G))
    (fun φ => stalkComparison_naturality k a y φ)

/-- The components of `stalkIso` are the stalk comparisons. -/
@[simp]
theorem stalkIso_hom_app (G : (D a).Sheaf (ModuleCat.{0} k)) :
    (stalkIso k a y).hom.app G = stalkComparison k a y G := rfl

/-- **The stalk of `(q a)_* G` at `y` as sections over the fibre.** The stalk at `y` of the direct
image `(q a)_* G` is the module of sections of `(fibreEmb a y)⁻¹ G` over `[y - a, y + a]`
(`stalkPullbackSheafIso`, `germ_top_bijective` and `stalkComparison` on global sections). -/
def stalkSectionsIso (G : (D a).Sheaf (ModuleCat.{0} k)) :
    ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G).presheaf.stalk y ≅
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).obj G).presheaf.obj (op ⊤) :=
  have := (ConcreteCategory.isIso_iff_bijective _).2 (germ_top_bijective
    ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)) PUnit.unit)
  stalkPullbackSheafIso k (ptAt y) _ PUnit.unit ≪≫
    (asIso (((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).obj G)).presheaf.germ ⊤ PUnit.unit
        trivial)).symm ≪≫
    ((TopCat.Sheaf.forget (ModuleCat.{0} k) pt).mapIso (asIso (stalkComparison k a y G))).app
      (op ⊤)

end stalk

section formula

variable (a y : ℝ) [HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory ((TopCat.of (Set.Icc (y - a) (y + a))).Sheaf (ModuleCat.{0} k))]

/-- **The stalk formula for the band projections exists.** For `F ∈ D⁺(Sh(D a))`, the stalk at
`y` of `R(q a)_* F` (its inverse image `(ptAt y)⁻¹` to the point) is isomorphic in `D⁺(Sh pt)` to
`RΓ` of the fibre `(q a)⁻¹ {y} ≅ [y - a, y + a]` with coefficients in `(fibreEmb a y)⁻¹ F`; in
particular so are their `Hⁱ`. -/
theorem nonempty_stalkFormula (F : DerivedCategory.Plus ((D a).Sheaf (ModuleCat.{0} k))) :
    Nonempty ((pullbackPlus k (ptAt y)).obj ((pushforwardPlus k (q a)).obj F) ≅
      (pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).obj
        ((pullbackPlus k (fibreEmb a y)).obj F)) :=
  have := (isFibreParam_fibreEmb a y).isIso_baseChange k
  ⟨(asIso (baseChange k (isFibreParam_fibreEmb a y).comp_eq)).app F⟩

/-- **The stalk formula for the band projections, on cohomology.** For `F ∈ D⁺(Sh(D a))` and
every degree `i`, `Hⁱ` of the stalk at `y` of `R(q a)_* F` (read through `(ptAt y)⁻¹`) is
isomorphic to `Hⁱ((q a)⁻¹ {y}; (fibreEmb a y)⁻¹ F)`, the fibre parametrised by
`[y - a, y + a]`. -/
theorem nonempty_stalkFormula_homology
    (F : DerivedCategory.Plus ((D a).Sheaf (ModuleCat.{0} k))) (i : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((pullbackPlus k (ptAt y)).obj ((pushforwardPlus k (q a)).obj F)) ≅
      (DerivedCategory.Plus.homologyFunctor _ i).obj
        ((pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).obj
          ((pullbackPlus k (fibreEmb a y)).obj F))) :=
  ⟨(DerivedCategory.Plus.homologyFunctor _ i).mapIso (nonempty_stalkFormula k a y F).some⟩

/-- **Stalks of `R(q a)_*` of a sheaf vanish above degree one.** For a sheaf `G` of `k`-modules on
`D a` placed in degree `0`, `Hⁱ` of the stalk at `y` of `R(q a)_* G` vanishes for `2 ≤ i`. -/
theorem isZero_H_stalk_pushforwardPlus_q (G : (D a).Sheaf (ModuleCat.{0} k)) {i : ℤ}
    (hi : 2 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pullbackPlus k (ptAt y)).obj ((pushforwardPlus k (q a)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) :=
  (isFibreParam_fibreEmb a y).isZero_H_stalk_pushforwardPlus k G hi

end formula

end BandConvolution

end TDA.Sheaf
