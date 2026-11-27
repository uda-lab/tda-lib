import TDA.Sheaf.BandConvolution
import TDA.Sheaf.RightDerivedHomology
import TDA.Sheaf.StalkPullback

/-!
# The degree-zero part of the band functors: the thickening formula

Fix a ring `k : Type` and `ε : ℝ`. The band functor `T k ε = R(q ε)_* (p ε)⁻¹` on
`D⁺(Sh(ℝ; k))` (`TDA.Sheaf.BandConvolution`) has, on a sheaf placed in degree `0`, the
underived degree-zero part

`thickening k ε F = (q ε)_* (p ε)⁻¹ F`.

* `H0TIso k ε : H⁰ ∘ T k ε ∘ (-)[0] ≅ thickening k ε`, naturally in `F`. The inverse image
  `(p ε)⁻¹` is exact, so its derived functor commutes with placing in degree `0`
  (`singleRightDerivedFunctorPlusIso`), and `(q ε)_*` is left exact, so `H⁰` of its derived
  functor on a sheaf in degree `0` is the underived direct image
  (`homologyZeroRightDerivedSingleIso`). `H0TIso_inv_app` writes the inverse at `F` through
  the two derived-functor comparisons. `H0TSectionsIso` combines it with the thickening formula
  below: `H⁰ (T k ε (F[0]))(U) ≅ F(bandOpen ε U)` for an order-connected open `U`.
* `bandOpen ε U = {x | ∃ y ∈ U, dist x y ≤ ε}` is the closed `ε`-thickening of an open `U`, an
  open set (`mem_bandOpen`). It is `U` for `ε = 0` (`bandOpen_zero`), contains `U` for
  `0 ≤ ε` (`le_bandOpen`), is monotone in `ε` (`bandOpen_mono`) and in `U`
  (`bandOpen_mono_right`), keeps order-connected opens order-connected
  (`ordConnected_bandOpen`), and thickens `(a, b)` to `(a - ε, b + ε)` for `0 ≤ ε`
  (`coe_bandOpen_Ioo`). It uses the closed condition `dist x y ≤ ε` at one point `y`, which
  at `ε = 0` gives `U` itself.
* The band geometry: `bandOpen ε U` is the image under `p ε` of the tube `(q ε)⁻¹ U`
  (`tube_le_bandOpen`, `exists_mem_tube`), `p ε` is an open map (`isOpenMap_p`, through `shear`),
  and the fibres of `p ε` on the tube over an order-connected `U` are preconnected
  (`isPreconnected_tube_fibre`).
* **The thickening formula.** `thickeningSectionsIso k ε F U hU`: for an order-connected open
  `U`, `(thickening k ε F)(U) ≅ F(bandOpen ε U)`. Its inverse is the unit
  `F(bandOpen ε U) ⟶ ((p ε)⁻¹ F)((q ε)⁻¹ U)` of `(p ε)⁻¹ ⊣ (p ε)_*` followed by restriction
  (`thickeningSectionsIso_inv`), invertible by `isIso_pullbackUnitRes`. It is natural in `F`
  (`thickeningSectionsIso_inv_naturality`, `thickeningSectionsIso_hom_naturality`,
  `thickeningSectionsNatIso`) and compatible with restriction along an inclusion `V ≤ U` of
  order-connected opens (`thickeningSectionsIso_inv_map`, `thickeningSectionsIso_hom_map`).

The sections isomorphism needs no sign condition on `ε`: for `ε < 0` the band, the tube and
`bandOpen ε U` are empty. Derived category structures are instance arguments only where `T`
appears.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf.BandConvolution

/-! ### Thickened opens -/

/-- **The closed `ε`-thickening of an open** `U` of the real line,
`{x | ∃ y ∈ U, dist x y ≤ ε}`, as an open set: a translate of a ball around `y` stays in `U`. -/
def bandOpen (ε : ℝ) (U : Opens realLine) : Opens realLine :=
  ⟨{x | ∃ y ∈ (U : Set ℝ), dist x y ≤ ε}, by
    refine Metric.isOpen_iff.2 fun x ⟨y, hy, hxy⟩ => ?_
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 U.isOpen y hy
    refine ⟨δ, hδ, fun x' hx' => ⟨y + (x' - x), hball ?_, ?_⟩⟩
    · rw [Metric.mem_ball, Real.dist_eq] at hx' ⊢
      rwa [add_sub_cancel_left]
    · rw [Real.dist_eq] at hxy ⊢
      rwa [show x' - (y + (x' - x)) = x - y by ring]⟩

theorem mem_bandOpen {ε : ℝ} {U : Opens realLine} {x : ℝ} :
    x ∈ bandOpen ε U ↔ ∃ y ∈ (U : Set ℝ), dist x y ≤ ε :=
  Iff.rfl

/-- For `0 ≤ ε`, the thickening of `U` contains `U`. -/
theorem le_bandOpen {ε : ℝ} (hε : 0 ≤ ε) (U : Opens realLine) : U ≤ bandOpen ε U :=
  fun x hx => ⟨x, hx, by simpa using hε⟩

/-- At radius `0` the thickening of `U` is `U`. -/
theorem bandOpen_zero (U : Opens realLine) : bandOpen 0 U = U :=
  Opens.ext (Set.ext fun x => ⟨fun ⟨y, hy, h⟩ => by rw [dist_le_zero.1 h]; exact hy,
    fun hx => ⟨x, hx, by simp⟩⟩)

/-- The thickening is monotone in the radius. -/
theorem bandOpen_mono {ε ε' : ℝ} (h : ε ≤ ε') (U : Opens realLine) :
    bandOpen ε U ≤ bandOpen ε' U :=
  fun _ ⟨y, hy, hxy⟩ => ⟨y, hy, hxy.trans h⟩

/-- The thickening is monotone in the open. -/
theorem bandOpen_mono_right (ε : ℝ) {V U : Opens realLine} (h : V ≤ U) :
    bandOpen ε V ≤ bandOpen ε U :=
  fun _ ⟨y, hy, hxy⟩ => ⟨y, h hy, hxy⟩

/-- The thickening of an order-connected open is order-connected. -/
theorem ordConnected_bandOpen (ε : ℝ) {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected) :
    (bandOpen ε U : Set ℝ).OrdConnected := by
  refine ⟨fun x₁ hx₁ x₂ hx₂ z hz => ?_⟩
  obtain ⟨y₁, hy₁, h₁⟩ := hx₁
  obtain ⟨y₂, hy₂, h₂⟩ := hx₂
  rw [Real.dist_eq, abs_le] at h₁ h₂
  have hseg : ∀ y, min y₁ y₂ ≤ y → y ≤ max y₁ y₂ → y ∈ (U : Set ℝ) := fun y hl hr =>
    Set.OrdConnected.uIcc_subset hU hy₁ hy₂ ⟨hl, hr⟩
  rcases le_or_gt z (min y₁ y₂) with hz₁ | hz₁
  · refine ⟨min y₁ y₂, hseg _ le_rfl (min_le_max), ?_⟩
    rw [Real.dist_eq, abs_le]
    constructor <;> cases min_choice y₁ y₂ <;> simp_all <;> linarith [hz.1, hz.2]
  rcases le_or_gt (max y₁ y₂) z with hz₂ | hz₂
  · refine ⟨max y₁ y₂, hseg _ min_le_max le_rfl, ?_⟩
    rw [Real.dist_eq, abs_le]
    constructor <;> cases max_choice y₁ y₂ <;> simp_all <;> linarith [hz.1, hz.2]
  · refine ⟨z, hseg _ hz₁.le hz₂.le, ?_⟩
    rw [dist_self]
    linarith

/-- For `0 ≤ ε` and `a < b`, the thickening of `(a, b)` is `(a - ε, b + ε)`. -/
theorem coe_bandOpen_Ioo {ε : ℝ} (hε : 0 ≤ ε) {a b : ℝ} (hab : a < b) :
    (bandOpen ε ⟨Set.Ioo a b, isOpen_Ioo⟩ : Set ℝ) = Set.Ioo (a - ε) (b + ε) := by
  ext x
  change (∃ y ∈ Set.Ioo a b, dist x y ≤ ε) ↔ _
  simp only [Set.mem_Ioo, Real.dist_eq, abs_le]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, h3, h4⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rcases le_or_gt x a with hxa | hxa
    · refine ⟨min (x + ε) ((a + b) / 2), ⟨lt_min (by linarith) (by linarith),
        (min_le_right _ _).trans_lt (by linarith)⟩, ?_, ?_⟩
      · linarith [min_le_left (x + ε) ((a + b) / 2)]
      · have : a < min (x + ε) ((a + b) / 2) := lt_min (by linarith) (by linarith)
        linarith
    rcases le_or_gt b x with hxb | hxb
    · refine ⟨max (x - ε) ((a + b) / 2), ⟨(by linarith : a < (a + b) / 2).trans_le
        (le_max_right _ _), max_lt (by linarith) (by linarith)⟩, ?_, ?_⟩
      · have : max (x - ε) ((a + b) / 2) < b := max_lt (by linarith) (by linarith)
        linarith
      · linarith [le_max_left (x - ε) ((a + b) / 2)]
    · exact ⟨x, ⟨hxa, hxb⟩, by linarith, by linarith⟩

/-! ### The band geometry -/

/-- The tube `(q ε)⁻¹ U` lies over `bandOpen ε U`. -/
theorem tube_le_bandOpen (ε : ℝ) (U : Opens realLine) :
    (Opens.map (q ε)).obj U ≤ (Opens.map (p ε)).obj (bandOpen ε U) :=
  fun z hz => ⟨z.1.2, hz, z.2⟩

/-- Every point of `bandOpen ε U` is the first coordinate of a point of the tube `(q ε)⁻¹ U`. -/
theorem exists_mem_tube (ε : ℝ) (U : Opens realLine) :
    ∀ x ∈ bandOpen ε U, ∃ z ∈ (Opens.map (q ε)).obj U, p ε z = x := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨⟨(x, y), hxy⟩, hy, rfl⟩

/-- **The first projection of a band is an open map**: under `shear` it is `Prod.snd`. -/
theorem isOpenMap_p (ε : ℝ) : IsOpenMap (p ε) := by
  have h : (p ε : D ε → ℝ) = Prod.snd ∘ shear ε := rfl
  rw [h]
  exact isOpenMap_snd.comp (shear ε).isOpenMap

/-- The fibres of `p ε` on the tube over an order-connected `U` are preconnected: the fibre over
`x` is `{x} × (U ∩ [x - ε, x + ε])`. -/
theorem isPreconnected_tube_fibre (ε : ℝ) {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (x : ℝ) :
    _root_.IsPreconnected (((Opens.map (q ε)).obj U : Set (D ε)) ∩ (p ε) ⁻¹' {x}) := by
  let S : Set ℝ := (U : Set ℝ) ∩ Metric.closedBall x ε
  have hS : _root_.IsPreconnected S :=
    (hU.inter (by rw [Real.closedBall_eq_Icc]; exact Set.ordConnected_Icc)).isPreconnected
  let g : S → D ε := fun y => ⟨(x, y.1), by
    show dist x y.1 ≤ ε
    rw [dist_comm]
    exact y.2.2⟩
  have hg : Continuous g := (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have himg : (((Opens.map (q ε)).obj U : Set (D ε)) ∩ (p ε) ⁻¹' {x}) = Set.range g := by
    ext z
    constructor
    · rintro ⟨hzU, hzx⟩
      have hx : z.1.1 = x := hzx
      refine ⟨⟨z.1.2, hzU, ?_⟩, Subtype.ext (Prod.ext hx.symm rfl)⟩
      rw [Metric.mem_closedBall, dist_comm, ← hx]
      exact z.2
    · rintro ⟨y, rfl⟩
      exact ⟨y.2.1, rfl⟩
  rw [himg]
  have := Subtype.preconnectedSpace hS
  exact isPreconnected_range hg

/-! ### The thickening functor and its sections -/

variable (k : Type) [Ring k]

/-- **The thickening functor** `F ↦ (q ε)_* (p ε)⁻¹ F`, the underived degree-zero part of the band
functor `T k ε`. -/
abbrev thickening (ε : ℝ) : realLine.Sheaf (ModuleCat.{0} k) ⥤ realLine.Sheaf (ModuleCat.{0} k) :=
  TopCat.Sheaf.pullback (ModuleCat.{0} k) (p ε) ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q ε)

/-- The unit map over the tube, `F(bandOpen ε U) ⟶ (thickening k ε F)(U)`, is invertible for an
order-connected open `U`. -/
private theorem isIso_unitRes_tube (ε : ℝ) (F : realLine.Sheaf (ModuleCat.{0} k))
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected) :
    IsIso (pullbackUnitRes k (p ε) F (tube_le_bandOpen ε U)) :=
  isIso_pullbackUnitRes k (p ε) F (tube_le_bandOpen ε U) (exists_mem_tube ε U)
    (fun O _ => isOpenMap_p ε _ O.isOpen) (fun x _ => isPreconnected_tube_fibre ε hU x)

/-- **The thickening formula.** For an order-connected open `U` of the real line, the sections of
`(q ε)_* (p ε)⁻¹ F` over `U` are the sections of `F` over `bandOpen ε U`. The inverse is the
unit of `(p ε)⁻¹ ⊣ (p ε)_*` over `bandOpen ε U` followed by restriction to the tube
`(q ε)⁻¹ U` (`thickeningSectionsIso_inv`). -/
def thickeningSectionsIso (ε : ℝ) (F : realLine.Sheaf (ModuleCat.{0} k)) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) :
    ((thickening k ε).obj F).presheaf.obj (op U) ≅ F.presheaf.obj (op (bandOpen ε U)) :=
  have := isIso_unitRes_tube k ε F hU
  (asIso (pullbackUnitRes k (p ε) F (tube_le_bandOpen ε U))).symm

/-- The inverse of `thickeningSectionsIso` is the unit followed by restriction to the tube. -/
theorem thickeningSectionsIso_inv (ε : ℝ) (F : realLine.Sheaf (ModuleCat.{0} k))
    (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    (thickeningSectionsIso k ε F U hU).inv = pullbackUnitRes k (p ε) F (tube_le_bandOpen ε U) :=
  rfl

/-- `thickeningSectionsIso` is natural in the sheaf (inverse form). -/
@[reassoc]
theorem thickeningSectionsIso_inv_naturality (ε : ℝ) {F G : realLine.Sheaf (ModuleCat.{0} k)}
    (φ : F ⟶ G) (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    φ.hom.app (op (bandOpen ε U)) ≫ (thickeningSectionsIso k ε G U hU).inv =
      (thickeningSectionsIso k ε F U hU).inv ≫ ((thickening k ε).map φ).hom.app (op U) :=
  pullbackUnitRes_naturality k (p ε) φ (tube_le_bandOpen ε U)

/-- **Naturality of the thickening formula in the sheaf.** -/
@[reassoc]
theorem thickeningSectionsIso_hom_naturality (ε : ℝ) {F G : realLine.Sheaf (ModuleCat.{0} k)}
    (φ : F ⟶ G) (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    ((thickening k ε).map φ).hom.app (op U) ≫ (thickeningSectionsIso k ε G U hU).hom =
      (thickeningSectionsIso k ε F U hU).hom ≫ φ.hom.app (op (bandOpen ε U)) := by
  rw [← cancel_epi (thickeningSectionsIso k ε F U hU).inv, Iso.inv_hom_id_assoc,
    ← Category.assoc, ← thickeningSectionsIso_inv_naturality, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The thickening formula as a natural isomorphism of functors to `ModuleCat k`. -/
def thickeningSectionsNatIso (ε : ℝ) (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    thickening k ε ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U) ≅
      sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (bandOpen ε U)) :=
  NatIso.ofComponents (fun F => thickeningSectionsIso k ε F U hU)
    (fun φ => thickeningSectionsIso_hom_naturality k ε φ U hU)

/-- The components of `thickeningSectionsNatIso` are `thickeningSectionsIso`. -/
@[simp]
theorem thickeningSectionsNatIso_app (ε : ℝ) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) (F : realLine.Sheaf (ModuleCat.{0} k)) :
    (thickeningSectionsNatIso k ε U hU).app F = thickeningSectionsIso k ε F U hU :=
  rfl

/-- `thickeningSectionsIso` is compatible with restriction along `V ≤ U` (inverse form). -/
@[reassoc]
theorem thickeningSectionsIso_inv_map (ε : ℝ) (F : realLine.Sheaf (ModuleCat.{0} k))
    {V U : Opens realLine} (hVU : V ≤ U) (hV : (V : Set ℝ).OrdConnected)
    (hU : (U : Set ℝ).OrdConnected) :
    (thickeningSectionsIso k ε F U hU).inv ≫
        ((thickening k ε).obj F).presheaf.map (homOfLE hVU).op =
      F.presheaf.map (homOfLE (bandOpen_mono_right ε hVU)).op ≫
        (thickeningSectionsIso k ε F V hV).inv :=
  pullbackUnitRes_map k (p ε) F (tube_le_bandOpen ε U) (tube_le_bandOpen ε V)
    ((Opens.map (q ε)).monotone hVU) (bandOpen_mono_right ε hVU)

/-- **Compatibility of the thickening formula with restriction.** For order-connected opens
`V ≤ U`, restriction `(thickening k ε F)(U) ⟶ (thickening k ε F)(V)` is the restriction
`F(bandOpen ε U) ⟶ F(bandOpen ε V)`. -/
@[reassoc]
theorem thickeningSectionsIso_hom_map (ε : ℝ) (F : realLine.Sheaf (ModuleCat.{0} k))
    {V U : Opens realLine} (hVU : V ≤ U) (hV : (V : Set ℝ).OrdConnected)
    (hU : (U : Set ℝ).OrdConnected) :
    ((thickening k ε).obj F).presheaf.map (homOfLE hVU).op ≫
        (thickeningSectionsIso k ε F V hV).hom =
      (thickeningSectionsIso k ε F U hU).hom ≫
        F.presheaf.map (homOfLE (bandOpen_mono_right ε hVU)).op := by
  rw [← cancel_epi (thickeningSectionsIso k ε F U hU).inv, Iso.inv_hom_id_assoc,
    ← Category.assoc, thickeningSectionsIso_inv_map k ε F hVU hV hU, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-! ### Degree zero of the band functor -/

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]

/-- **Degree zero of the band functor.** On a sheaf placed in degree `0`, `H⁰ (T k ε F)` is
`thickening k ε F = (q ε)_* (p ε)⁻¹ F`, naturally in `F`. -/
def H0TIso (ε : ℝ) :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ T k ε ⋙ DerivedCategory.Plus.homologyFunctor _ 0 ≅
      thickening k ε :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
      (Functor.associator (pullbackPlus k (p ε)) (pushforwardPlus k (q ε))
        (DerivedCategory.Plus.homologyFunctor _ 0)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (singleRightDerivedFunctorPlusIso (TopCat.Sheaf.pullback (ModuleCat.{0} k) (p ε)) 0).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (homologyZeroRightDerivedSingleIso (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q ε)))

/-- The inverse of `H0TIso` at `F`: the comparison `(q ε)_* G ⟶ H⁰(R(q ε)_* (G[0]))` at
`G = (p ε)⁻¹ F`, followed by `H⁰ R(q ε)_*` of the comparison `((p ε)⁻¹ F)[0] ⟶ R(p ε)⁻¹ (F[0])`. -/
theorem H0TIso_inv_app (ε : ℝ) (F : realLine.Sheaf (ModuleCat.{0} k)) :
    (H0TIso k ε).inv.app F =
      (toHomologyZeroRightDerivedSingle (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q ε))).app
          ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (p ε)).obj F) ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map ((pushforwardPlus k (q ε)).map
          ((singleRightDerivedFunctorPlusComparison
            (TopCat.Sheaf.pullback (ModuleCat.{0} k) (p ε)) 0).app F)) := by
  simp [H0TIso, singleRightDerivedFunctorPlusIso]

/-- **Degree zero of the band functor on sections.** For an order-connected open `U`, the
sections of `H⁰ (T k ε (F[0]))` over `U` are the sections of `F` over `bandOpen ε U`:
`H0TIso` followed by `thickeningSectionsIso`. -/
def H0TSectionsIso (ε : ℝ) (F : realLine.Sheaf (ModuleCat.{0} k)) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) :
    ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((T k ε).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).presheaf.obj (op U) ≅
      F.presheaf.obj (op (bandOpen ε U)) :=
  (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).mapIso ((H0TIso k ε).app F) ≪≫
    thickeningSectionsIso k ε F U hU

end TDA.Sheaf.BandConvolution
