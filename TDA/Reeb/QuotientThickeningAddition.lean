import TDA.Reeb.GeometricThickeningAddition
import TDA.Reeb.RGraphSmoothing

/-!
# The Reeb quotient of the thickening addition map

The addition map `μ_(ε,δ) : T_ε T_δ X → T_(ε+δ) X`, `((x, s), t) ↦ (x, s + t)`, is not a
homeomorphism, and on the one-point space no slice isomorphism `T_1 T_1 P ≅ T_2 P` exists. After the
Reeb quotient it becomes one, with no hypothesis on `X` or on the height function:

```
ℛ μ_(ε,δ) : ReebQuotient (height (height f δ) ε) ≃ₜ ReebQuotient (height f (ε + δ)).
```

## The section and the fibre paths

`addSection X ε δ : T_(ε+δ) X → T_ε T_δ X` sends `(x, u)` to `((x, c), u - c)` with `c` the
projection of `u` onto `[-δ, δ]`. It is continuous, height-preserving (`height_addSection`) and
natural (`addSection_natural`), and it is a section of the addition map
(`addMap_comp_addSection`). For every `z = ((x, s), t)`, the straight segment from `(s, t)` to
`(c, s + t - c)` keeps `x` and `s + t` and stays in `Band δ × Band ε`, by convexity of the bands
(`addFiberPath`). It lies in one height fibre (`height_addFiberPath`), so `z` and `σ (μ z)` are
Reeb-equivalent (`reebRel_addSection_addMap`).

## The homeomorphism

`quotientAddHomeomorph f ε δ` has forward map `ℛ μ` and inverse `ℛ σ`. The identity `μ ∘ σ = id`
gives one composite, the fibre paths give the other, and continuity of both directions is the
functoriality of `ℛ` on the continuous maps `μ` and `σ`. No compactness, Hausdorff or
constructibility argument is used, and the carrier universe is arbitrary. In particular two points
of `T_ε T_δ X` have the same class after `ℛ μ` exactly when they are Reeb-equivalent
(`mk_addMap_eq_mk_addMap_iff`).

## The real slice and coherence

`reebAddIso ε δ : (T_δ ⋙ T_ε) ⋙ ℛ ≅ T_(ε+δ) ⋙ ℛ` has hom `whiskerRight (addNatTrans ε δ) ℛ`
(`reebAddIso_hom`) and inverse `ℛ σ` (`reebAddIso_inv_app_left_hom`). Parameter equalities are
bridged by `bandEqIso`, a pair of band inclusions. The merged lax laws of `addNatTrans` pass
through `ℛ`: associativity (`reebAddIso_assoc`, and in iso form `reebAddIso_assoc_iso`), both unit
laws against `zeroIso` (`reebAddIso_zero_left`, `reebAddIso_zero_right`), both zero-section laws and
band enlargement. As a consequence `ℛ (T_ε μ_(δ,γ))` is an isomorphism
(`isIso_whiskerRight_whiskerRight_addNatTrans`).

## Graph objects

The Reeb quotient of `T_ε T_δ A` is a graph object for every graph object `A`
(`RGraph.isRGraph_quotient_thickening_thickening`), through the isomorphism with the Reeb quotient
of `T_(ε+δ) A`; the double thickening itself is not claimed to be constructible. The functor
`RGraph.doubleThickeningQuotient ε δ : A ↦ ℛ T_ε T_δ A` on graph objects is naturally isomorphic to
the merged `geometricSmoothing (ε + δ)` (`RGraph.geometricSmoothingAddIso`).

The slice and graph packaging is in universe `0`.

See `docs/math/reeb-quotient-thickening-addition.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

universe u v

namespace TDA.Reeb

namespace GeometricThickening

noncomputable section

/-! ### The section of the addition map -/

section AddSection

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- For `u ∈ [-(ε + δ), ε + δ]` and `c` its projection onto `[-δ, δ]`, `u - c ∈ [-ε, ε]`. -/
theorem sub_projIcc_mem_band {ε δ : ℝ≥0} (u : Band (ε + δ)) :
    (u : ℝ) - projIcc (-(δ : ℝ)) δ (neg_le_band δ) u ∈ Band ε := by
  have hs : (projIcc (-(δ : ℝ)) δ (neg_le_band δ) u : ℝ) =
      max (-(δ : ℝ)) (min (δ : ℝ) u) := coe_projIcc _ _ _ _
  have h₁ : -((ε : ℝ) + δ) ≤ u := by have := u.2.1; rwa [NNReal.coe_add] at this
  have h₂ : (u : ℝ) ≤ ε + δ := by have := u.2.2; rwa [NNReal.coe_add] at this
  have hε := ε.coe_nonneg
  have hδ := δ.coe_nonneg
  rw [hs]
  have hm1 : min (δ : ℝ) u ≤ δ := min_le_left _ _
  have hm2 : min (δ : ℝ) u ≤ u := min_le_right _ _
  have hv1 : -(δ : ℝ) ≤ max (-(δ : ℝ)) (min (δ : ℝ) u) := le_max_left _ _
  have hv2 : min (δ : ℝ) u ≤ max (-(δ : ℝ)) (min (δ : ℝ) u) := le_max_right _ _
  rcases min_choice (δ : ℝ) u with hm | hm <;>
    rcases max_choice (-(δ : ℝ)) (min (δ : ℝ) u) with hv | hv <;>
    exact ⟨by linarith, by linarith⟩

/-- The section `σ_(ε,δ) : T_(ε+δ) X → T_ε T_δ X`, `(x, u) ↦ ((x, c), u - c)` with `c` the
projection of `u` onto `[-δ, δ]`. -/
def addSection (X : Type u) [TopologicalSpace X] (ε δ : ℝ≥0) :
    C(X × Band (ε + δ), (X × Band δ) × Band ε) where
  toFun w := ((w.1, projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2),
    ⟨w.2 - projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2, sub_projIcc_mem_band w.2⟩)
  continuous_toFun := by
    have hc : Continuous fun w : X × Band (ε + δ) =>
        projIcc (-(δ : ℝ)) δ (neg_le_band δ) (w.2 : ℝ) :=
      continuous_projIcc.comp (continuous_subtype_val.comp continuous_snd)
    exact (continuous_fst.prodMk hc).prodMk
      (((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp hc)).subtype_mk _)

@[simp] theorem addSection_apply (ε δ : ℝ≥0) (x : X) (u : Band (ε + δ)) :
    addSection X ε δ (x, u) = ((x, projIcc (-(δ : ℝ)) δ (neg_le_band δ) u),
      ⟨u - projIcc (-(δ : ℝ)) δ (neg_le_band δ) u, sub_projIcc_mem_band u⟩) := rfl

/-- The section preserves height: `f x + c + (u - c) = f x + u`. -/
theorem height_addSection (f : C(X, ℝ)) (ε δ : ℝ≥0) (w : X × Band (ε + δ)) :
    height (height f δ) ε (addSection X ε δ w) = height f (ε + δ) w := by
  show f w.1 + (projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2 : ℝ) +
      ((w.2 : ℝ) - projIcc (-(δ : ℝ)) δ (neg_le_band δ) w.2) = f w.1 + w.2
  ring

/-- `σ` is a section of the addition map: `μ ∘ σ = id`. -/
theorem addMap_comp_addSection (ε δ : ℝ≥0) :
    (addMap X ε δ).comp (addSection X ε δ) = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ => Prod.ext rfl (Subtype.ext (add_sub_cancel _ _))

/-- Naturality of the section in every continuous map. -/
theorem addSection_natural (g : C(X, Y)) (ε δ : ℝ≥0) :
    (addSection Y ε δ).comp (map g (ε + δ)) = (map (map g δ) ε).comp (addSection X ε δ) :=
  rfl

end AddSection

/-! ### The fibre paths -/

section FiberPath

variable {X : Type u} [TopologicalSpace X] {ε δ : ℝ≥0}

/-- The straight segment from `z = ((x, s), t)` to `σ (μ z) = ((x, c), s + t - c)`, in the band
coordinates of `T_ε T_δ X`. It keeps `x` and stays in `Band δ × Band ε` by convexity. -/
def addFiberPath (z : (X × Band δ) × Band ε) : Path z (addSection X ε δ (addMap X ε δ z)) where
  toFun r := ((z.1.1, ⟨(1 - (r : ℝ)) * z.1.2 + r * (addSection X ε δ (addMap X ε δ z)).1.2,
      interp_mem_band _ _ r⟩),
    ⟨(1 - (r : ℝ)) * z.2 + r * (addSection X ε δ (addMap X ε δ z)).2, interp_mem_band _ _ r⟩)
  continuous_toFun := by
    have h₁ : Continuous fun r : unitInterval =>
        (1 - (r : ℝ)) * z.1.2 + r * (addSection X ε δ (addMap X ε δ z)).1.2 := by fun_prop
    have h₂ : Continuous fun r : unitInterval =>
        (1 - (r : ℝ)) * z.2 + r * (addSection X ε δ (addMap X ε δ z)).2 := by fun_prop
    exact (continuous_const.prodMk (h₁.subtype_mk _)).prodMk (h₂.subtype_mk _)
  source' := Prod.ext (Prod.ext rfl (Subtype.ext (by simp))) (Subtype.ext (by simp))
  target' := Prod.ext (Prod.ext rfl (Subtype.ext (by simp))) (Subtype.ext (by simp))

/-- The fibre path keeps the thickened height `f x + s + t`. -/
theorem height_addFiberPath (f : C(X, ℝ)) (z : (X × Band δ) × Band ε) (r : unitInterval) :
    height (height f δ) ε (addFiberPath z r) = height (height f δ) ε z := by
  show f z.1.1 + ((1 - (r : ℝ)) * z.1.2 + r * (addSection X ε δ (addMap X ε δ z)).1.2) +
      ((1 - (r : ℝ)) * z.2 + r * (addSection X ε δ (addMap X ε δ z)).2) = f z.1.1 + z.1.2 + z.2
  have h : ((addSection X ε δ (addMap X ε δ z)).2 : ℝ) =
      z.1.2 + z.2 - (addSection X ε δ (addMap X ε δ z)).1.2 := rfl
  rw [h]
  ring

/-- `z` and `σ (μ z)` are Reeb-equivalent for the thickened height of `T_ε T_δ`. -/
theorem reebRel_addSection_addMap (f : C(X, ℝ)) (z : (X × Band δ) × Band ε) :
    ReebRel (height (height f δ) ε) z (addSection X ε δ (addMap X ε δ z)) :=
  ⟨addFiberPath z, height_addFiberPath f z⟩

end FiberPath

/-! ### The Reeb-quotient homeomorphism -/

section Homeomorph

variable {X : Type u} [TopologicalSpace X]

/-- **The Reeb quotient of the addition map is a homeomorphism**, for every `f : C(X, ℝ)` and
every `ε, δ`: the forward map is `ℛ μ` and the inverse is `ℛ σ`. -/
def quotientAddHomeomorph (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    ReebQuotient (height (height f δ) ε) ≃ₜ ReebQuotient (height f (ε + δ)) where
  toFun := ReebQuotient.map (addMap X ε δ) (height_addMap f ε δ)
  invFun := ReebQuotient.map (addSection X ε δ) (height_addSection f ε δ)
  left_inv q := by
    induction q using ReebQuotient.ind with
    | h z => exact ((ReebQuotient.mk_eq_mk_iff _).2 (reebRel_addSection_addMap f z)).symm
  right_inv q := by
    induction q using ReebQuotient.ind with
    | h w => exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_comp_addSection ε δ) w)
  continuous_toFun := (ReebQuotient.map _ _).continuous
  continuous_invFun := (ReebQuotient.map _ _).continuous

theorem coe_quotientAddHomeomorph (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    ⇑(quotientAddHomeomorph f ε δ) = ReebQuotient.map (addMap X ε δ) (height_addMap f ε δ) :=
  rfl

theorem coe_quotientAddHomeomorph_symm (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    ⇑(quotientAddHomeomorph f ε δ).symm =
      ReebQuotient.map (addSection X ε δ) (height_addSection f ε δ) :=
  rfl

@[simp] theorem quotientAddHomeomorph_mk (f : C(X, ℝ)) (ε δ : ℝ≥0) (z : (X × Band δ) × Band ε) :
    quotientAddHomeomorph f ε δ (ReebQuotient.mk _ z) = ReebQuotient.mk _ (addMap X ε δ z) :=
  rfl

@[simp] theorem quotientAddHomeomorph_symm_mk (f : C(X, ℝ)) (ε δ : ℝ≥0) (w : X × Band (ε + δ)) :
    (quotientAddHomeomorph f ε δ).symm (ReebQuotient.mk _ w) =
      ReebQuotient.mk _ (addSection X ε δ w) :=
  rfl

/-- The homeomorphism preserves height. -/
theorem height_quotientAddHomeomorph (f : C(X, ℝ)) (ε δ : ℝ≥0)
    (q : ReebQuotient (height (height f δ) ε)) :
    ReebQuotient.height _ (quotientAddHomeomorph f ε δ q) = ReebQuotient.height _ q :=
  ReebQuotient.height_map_apply (addMap X ε δ) (height_addMap f ε δ) q

/-- `ℛ μ` is bijective. -/
theorem bijective_quotientMap_addMap (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    Function.Bijective (ReebQuotient.map (addMap X ε δ) (height_addMap f ε δ)) :=
  (quotientAddHomeomorph f ε δ).bijective

/-- **Fibre comparison.** Two points of `T_ε T_δ X` have the same class after `ℛ μ` exactly when
they are Reeb-equivalent in `T_ε T_δ X`. -/
theorem mk_addMap_eq_mk_addMap_iff (f : C(X, ℝ)) {ε δ : ℝ≥0} (z z' : (X × Band δ) × Band ε) :
    ReebQuotient.mk (height f (ε + δ)) (addMap X ε δ z) =
        ReebQuotient.mk (height f (ε + δ)) (addMap X ε δ z') ↔
      ReebRel (height (height f δ) ε) z z' :=
  ⟨fun h => (ReebQuotient.mk_eq_mk_iff _).1 ((quotientAddHomeomorph f ε δ).injective
      (a₁ := ReebQuotient.mk _ z) (a₂ := ReebQuotient.mk _ z') h),
    fun h => (ReebQuotient.mk_eq_mk_iff _).2 (h.map (addMap X ε δ) (height_addMap f ε δ))⟩

end Homeomorph

/-! ### The real slice (universe `0`) -/

section Over

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

/-- `ℛ μ_(ε,δ)` is an isomorphism at every object of the real slice. -/
instance isIso_quotientFunctor_map_addNatTrans_app (ε δ : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    IsIso ((ℛ).map ((addNatTrans ε δ).app A)) := by
  let e : (ℛ).obj ((functor ε).obj ((functor δ).obj A)) ≅ (ℛ).obj ((functor (ε + δ)).obj A) :=
    Over.isoMk (TopCat.isoOfHomeo
        (X := ((ℛ).obj ((functor ε).obj ((functor δ).obj A))).left)
        (Y := ((ℛ).obj ((functor (ε + δ)).obj A)).left)
        (quotientAddHomeomorph (overBaseMap A) ε δ)) (by
      ext q
      exact height_quotientAddHomeomorph (overBaseMap A) ε δ q)
  have h : (ℛ).map ((addNatTrans ε δ).app A) = e.hom := by
    ext q
    rfl
  rw [h]
  infer_instance

instance isIso_whiskerRight_addNatTrans (ε δ : ℝ≥0) :
    IsIso (Functor.whiskerRight (addNatTrans ε δ) ℛ) := by
  have : ∀ A, IsIso ((Functor.whiskerRight (addNatTrans ε δ) ℛ).app A) := fun A =>
    isIso_quotientFunctor_map_addNatTrans_app ε δ A
  exact NatIso.isIso_of_isIso_app _

/-- **`ℛ T_ε T_δ ≅ ℛ T_(ε+δ)`** on the real slice, with hom `ℛ μ`. -/
def reebAddIso (ε δ : ℝ≥0) : (functor δ ⋙ functor ε) ⋙ ℛ ≅ functor (ε + δ) ⋙ ℛ :=
  asIso (Functor.whiskerRight (addNatTrans ε δ) ℛ)

theorem reebAddIso_hom (ε δ : ℝ≥0) :
    (reebAddIso ε δ).hom = Functor.whiskerRight (addNatTrans ε δ) ℛ :=
  rfl

/-- The inverse of `reebAddIso` is `ℛ σ`. -/
theorem reebAddIso_inv_app_left_hom (ε δ : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    ((reebAddIso ε δ).inv.app A).left.hom =
      ReebQuotient.map (addSection A.left ε δ) (height_addSection (overBaseMap A) ε δ) := by
  ext q
  have h : quotientAddHomeomorph (overBaseMap A) ε δ (((reebAddIso ε δ).inv.app A).left.hom q) =
      q :=
    congrArg (fun φ => φ.left.hom q) ((reebAddIso ε δ).inv_hom_id_app A)
  exact ((quotientAddHomeomorph (overBaseMap A) ε δ).symm_apply_apply _).symm.trans
    (congrArg (quotientAddHomeomorph (overBaseMap A) ε δ).symm h)

/-- A parameter equality `ε = δ` as an isomorphism `T_ε ≅ T_δ`, by band inclusions in both
directions; not `eqToIso`. -/
def bandEqIso {ε δ : ℝ≥0} (h : ε = δ) : functor ε ≅ functor δ where
  hom := bandInclusionNatTrans h.le
  inv := bandInclusionNatTrans h.ge
  hom_inv_id := by
    ext A z
    rfl
  inv_hom_id := by
    ext A z
    rfl

theorem bandEqIso_hom {ε δ : ℝ≥0} (h : ε = δ) :
    (bandEqIso h).hom = bandInclusionNatTrans h.le :=
  rfl

theorem bandEqIso_inv {ε δ : ℝ≥0} (h : ε = δ) :
    (bandEqIso h).inv = bandInclusionNatTrans h.ge :=
  rfl

/-- **Associativity**, the `ℛ`-image of `addNatTrans_assoc`, with `(ε + δ) + γ = ε + (δ + γ)`
bridged by `bandEqIso`. -/
theorem reebAddIso_assoc (ε δ γ : ℝ≥0) :
    Functor.whiskerLeft (functor γ) (reebAddIso ε δ).hom ≫ (reebAddIso (ε + δ) γ).hom ≫
        Functor.whiskerRight (bandEqIso (add_assoc ε δ γ)).hom ℛ =
      Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ ≫
        (reebAddIso ε (δ + γ)).hom := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_assoc (X := A.left) ε δ γ) z)

/-- `ℛ (T_ε μ_(δ,γ))` is an isomorphism, from associativity. -/
instance isIso_whiskerRight_whiskerRight_addNatTrans (ε δ γ : ℝ≥0) :
    IsIso (Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ) := by
  have : IsIso (Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ ≫
      (reebAddIso ε (δ + γ)).hom) := by
    rw [← reebAddIso_assoc]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (reebAddIso ε (δ + γ)).hom

/-- `ℛ (T_ε μ_(δ,γ)) : ℛ T_ε T_δ T_γ ≅ ℛ T_ε T_(δ+γ)`. -/
def reebAddInnerIso (ε δ γ : ℝ≥0) :
    ((functor γ ⋙ functor δ) ⋙ functor ε) ⋙ ℛ ≅ (functor (δ + γ) ⋙ functor ε) ⋙ ℛ :=
  asIso (Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ)

theorem reebAddInnerIso_hom (ε δ γ : ℝ≥0) :
    (reebAddInnerIso ε δ γ).hom =
      Functor.whiskerRight (Functor.whiskerRight (addNatTrans δ γ) (functor ε)) ℛ :=
  rfl

/-- **Associativity in iso form.** -/
theorem reebAddIso_assoc_iso (ε δ γ : ℝ≥0) :
    Functor.isoWhiskerLeft (functor γ) (reebAddIso ε δ) ≪≫ reebAddIso (ε + δ) γ ≪≫
        Functor.isoWhiskerRight (bandEqIso (add_assoc ε δ γ)) ℛ =
      reebAddInnerIso ε δ γ ≪≫ reebAddIso ε (δ + γ) :=
  Iso.ext (reebAddIso_assoc ε δ γ)

/-- **Left unit law** against `zeroIso`, the `ℛ`-image of `addNatTrans_zero_left`. -/
theorem reebAddIso_zero_left (δ : ℝ≥0) :
    reebAddIso 0 δ ≪≫ Functor.isoWhiskerRight (bandEqIso (zero_add δ)) ℛ =
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (functor δ) zeroIso) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_zero_left (X := A.left) δ) z)

/-- **Right unit law** against `zeroIso`, the `ℛ`-image of `addNatTrans_zero_right`. -/
theorem reebAddIso_zero_right (δ : ℝ≥0) :
    reebAddIso δ 0 ≪≫ Functor.isoWhiskerRight (bandEqIso (add_zero δ)) ℛ =
      Functor.isoWhiskerRight (Functor.isoWhiskerRight zeroIso (functor δ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _) (DFunLike.congr_fun (addMap_zero_right (X := A.left) δ) z)

/-- The outer zero section followed by `ℛ μ` is `ℛ` of the enlargement `δ ≤ ε + δ`. -/
theorem whiskerLeft_zeroSectionNatTrans_comp_reebAddIso (ε δ : ℝ≥0) :
    Functor.whiskerRight (Functor.whiskerLeft (functor δ) (zeroSectionNatTrans ε)) ℛ ≫
        (reebAddIso ε δ).hom =
      Functor.whiskerRight (bandInclusionNatTrans (le_add_self : δ ≤ ε + δ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _)
      (DFunLike.congr_fun (addMap_comp_zeroSection (X := A.left) ε δ) z)

/-- `T_ε` of the inner zero section followed by `ℛ μ` is `ℛ` of the enlargement `ε ≤ ε + δ`. -/
theorem whiskerRight_zeroSectionNatTrans_comp_reebAddIso (ε δ : ℝ≥0) :
    Functor.whiskerRight (Functor.whiskerRight (zeroSectionNatTrans δ) (functor ε)) ℛ ≫
        (reebAddIso ε δ).hom =
      Functor.whiskerRight (bandInclusionNatTrans (le_self_add : ε ≤ ε + δ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z =>
    exact congrArg (ReebQuotient.mk _)
      (DFunLike.congr_fun (addMap_comp_map_zeroSection (X := A.left) ε δ) z)

/-- **Band enlargement**, the `ℛ`-image of `addNatTrans_comp_bandInclusionNatTrans`. -/
theorem reebAddIso_comp_bandInclusionNatTrans {ε ε' δ δ' : ℝ≥0} (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    Functor.whiskerRight (Functor.whiskerRight (bandInclusionNatTrans hδ) (functor ε)) ℛ ≫
        Functor.whiskerRight (Functor.whiskerLeft (functor δ') (bandInclusionNatTrans hε)) ℛ ≫
          (reebAddIso ε' δ').hom =
      (reebAddIso ε δ).hom ≫ Functor.whiskerRight (bandInclusionNatTrans (add_le_add hε hδ)) ℛ := by
  ext A q
  induction q using ReebQuotient.ind with
  | h z => rfl

end Over

end

end GeometricThickening

/-! ### Graph objects -/

noncomputable section

namespace RGraph

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

/-- The Reeb quotient of `T_ε T_δ A` is a graph object for every graph object `A`, through its
isomorphism with the Reeb quotient of `T_(ε+δ) A`. -/
theorem isRGraph_quotient_thickening_thickening {A : Over (TopCat.of ℝ)} (hA : IsRGraph A)
    (ε δ : ℝ≥0) :
    IsRGraph ((ℛ).obj ((GeometricThickening.functor ε).obj
      ((GeometricThickening.functor δ).obj A))) := by
  obtain ⟨m, T, D, ⟨i⟩⟩ :=
    isRGraph_quotient_of_isConstructibleSpace (isConstructibleSpace_thickening hA (ε + δ))
  exact ⟨m, T, D, ⟨(GeometricThickening.reebAddIso ε δ).app A ≪≫ i⟩⟩

/-- `A ↦ ℛ T_ε T_δ A` on graph objects. -/
def doubleThickeningQuotient (ε δ : ℝ≥0) : RGraphCat ⥤ RGraphCat :=
  IsRGraph.lift (IsRGraph.ι ⋙ GeometricThickening.functor δ ⋙ GeometricThickening.functor ε ⋙ ℛ)
    fun A => isRGraph_quotient_thickening_thickening A.property ε δ

theorem doubleThickeningQuotient_comp_ι (ε δ : ℝ≥0) :
    doubleThickeningQuotient ε δ ⋙ IsRGraph.ι =
      IsRGraph.ι ⋙ GeometricThickening.functor δ ⋙ GeometricThickening.functor ε ⋙ ℛ :=
  rfl

/-- **`ℛ T_ε T_δ ≅ U_(ε+δ)`** on graph objects, with target the merged
`geometricSmoothing (ε + δ)`. Its components are those of `GeometricThickening.reebAddIso`. -/
def geometricSmoothingAddIso (ε δ : ℝ≥0) :
    doubleThickeningQuotient ε δ ≅ geometricSmoothing (ε + δ) :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ ((GeometricThickening.reebAddIso ε δ).app A.obj))
    (fun φ => by
      ext1
      exact (GeometricThickening.reebAddIso ε δ).hom.naturality φ.hom)

theorem geometricSmoothingAddIso_hom_app_hom (ε δ : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingAddIso ε δ).hom.app A).hom =
      (ℛ).map ((GeometricThickening.addNatTrans ε δ).app A.obj) :=
  rfl

theorem geometricSmoothingAddIso_inv_app_hom (ε δ : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingAddIso ε δ).inv.app A).hom =
      (GeometricThickening.reebAddIso ε δ).inv.app A.obj :=
  rfl

end RGraph

end

end TDA.Reeb
