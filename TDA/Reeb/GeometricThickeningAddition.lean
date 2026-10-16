import TDA.Reeb.GeometricThickening

/-!
# The thickening addition map and its lax coherence

For ordinary product thickening, `T_ε T_δ ≅ T_(ε+δ)` is false: on a point at height `0` with
`ε = δ = 1`, the height-`0` fibre of `T_1 T_1` is a segment, while that of `T_2` is a point. The
correct statement is a natural height-preserving addition map

```
addMap X ε δ : (X × Band δ) × Band ε → X × Band (ε + δ),   ((x, s), t) ↦ (x, s + t),
```

with the outer parameter first, matching `smoothingCompIso ε δ`.

## The addition map

* It preserves height, `f x + (s + t) = (f x + s) + t` (`height_addMap`), and is natural in every
  continuous map (`addMap_natural`) and compatible with band enlargement
  (`addMap_comp_bandInclusion`).
* It is associative and unital against `zeroHomeomorph` (`addMap_assoc`, `addMap_zero_left`,
  `addMap_zero_right`), and both zero sections are band enlargements (`addMap_comp_zeroSection`,
  `addMap_comp_map_zeroSection`). Parameter equalities such as `ε + (δ + γ) = ε + δ + γ` are
  bridged by `bandInclusion`, never by casts.
* It is surjective (`addMap_surjective`), and not injective for nonempty `X` and `ε, δ > 0`
  (`addMap_not_injective`).

## The real slice

`bandInclusionNatTrans h : functor ε ⟶ functor δ` and
`addNatTrans ε δ : functor δ ⋙ functor ε ⟶ functor (ε + δ)` package band enlargement and the
addition map. Associativity, both unit laws against `zeroIso` and both zero-section laws hold as
equations of natural transformations, so `(functor, zeroSectionNatTrans, addNatTrans)` is a lax
composition law over the additive monoid `ℝ≥0`.

## Path components

`π₀` of the addition map followed by the comparison at `ε + δ` is the comparison at `ε`, then the
smoothing of the comparison at `δ`, then the merged `smoothingCompIso ε δ`
(`addMap_comp_componentComparison`), objectwise and on the slice
(`whiskerRight_addNatTrans_comp_componentComparisonNatIso`). Hence `π₀` of the addition map is an
isomorphism (`isIso_intervalComponentNatTrans_addMap`), although the addition map itself is not
a homeomorphism.

## The one-point counterexample

On `onePoint`, the point over height `0`, the height-`0` fibre of `T_1 T_1` contains the segment
`s ↦ ((*, s), -s)` (`fiber_zero_injective`), while every height-`0` fibre of `T_ε` is a
subsingleton (`fiber_zero_subsingleton`). A slice isomorphism preserves height and is injective,
so no isomorphism `T_1 T_1 P ≅ T_(1+1) P` exists (`not_iso_one_one`); in particular
`(addNatTrans 1 1).app P` is not an isomorphism.

See `docs/math/reeb-geometric-thickening-addition.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

universe u v

namespace TDA.Reeb

namespace GeometricThickening

noncomputable section

open OpenInterval

/-! ### The addition map -/

section AddMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The band is symmetric. -/
theorem neg_mem_band {ε : ℝ≥0} {t : ℝ} (ht : t ∈ Band ε) : -t ∈ Band ε :=
  ⟨neg_le_neg ht.2, by linarith [ht.1]⟩

/-- `[-δ, δ] + [-ε, ε] ⊆ [-(ε + δ), ε + δ]`. -/
theorem add_mem_band {ε δ : ℝ≥0} (s : Band δ) (t : Band ε) : (s : ℝ) + t ∈ Band (ε + δ) := by
  have h₁ := s.2.1
  have h₂ := s.2.2
  have h₃ := t.2.1
  have h₄ := t.2.2
  rw [Band, NNReal.coe_add]
  exact ⟨by linarith, by linarith⟩

/-- The addition map `μ_(ε,δ) : T_ε (T_δ X) → T_(ε+δ) X`, `((x, s), t) ↦ (x, s + t)`, with the
outer parameter first. -/
def addMap (X : Type u) [TopologicalSpace X] (ε δ : ℝ≥0) :
    C((X × Band δ) × Band ε, X × Band (ε + δ)) where
  toFun z := (z.1.1, ⟨z.1.2 + z.2, add_mem_band z.1.2 z.2⟩)
  continuous_toFun := (continuous_fst.comp continuous_fst).prodMk
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).add
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _)

@[simp] theorem addMap_apply (ε δ : ℝ≥0) (x : X) (s : Band δ) (t : Band ε) :
    addMap X ε δ ((x, s), t) = (x, ⟨s + t, add_mem_band s t⟩) := rfl

/-- The addition map preserves height: `f x + (s + t) = (f x + s) + t`. -/
theorem height_addMap (f : C(X, ℝ)) (ε δ : ℝ≥0) (z : (X × Band δ) × Band ε) :
    height f (ε + δ) (addMap X ε δ z) = height (height f δ) ε z :=
  (add_assoc _ _ _).symm

/-- Naturality in every continuous map, with no height hypothesis. -/
theorem addMap_natural (g : C(X, Y)) (ε δ : ℝ≥0) :
    (map g (ε + δ)).comp (addMap X ε δ) = (addMap Y ε δ).comp (map (map g δ) ε) :=
  rfl

/-- Compatibility with band enlargement in both parameters. -/
theorem addMap_comp_bandInclusion {ε ε' δ δ' : ℝ≥0} (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    (addMap X ε' δ').comp ((bandInclusion (X × Band δ') hε).comp (map (bandInclusion X hδ) ε)) =
      (bandInclusion X (add_le_add hε hδ)).comp (addMap X ε δ) :=
  rfl

/-- Associativity on `((X × Band γ) × Band δ) × Band ε`, with `(ε + δ) + γ ≤ ε + (δ + γ)`
bridged by band enlargement. -/
theorem addMap_assoc (ε δ γ : ℝ≥0) :
    (bandInclusion X (add_assoc ε δ γ).le).comp
        ((addMap X (ε + δ) γ).comp (addMap (X × Band γ) ε δ)) =
      (addMap X ε (δ + γ)).comp (map (addMap X δ γ) ε) :=
  ContinuousMap.ext fun z => Prod.ext rfl (Subtype.ext
    (show (z.1.1.2 : ℝ) + (z.1.2 + z.2) = z.1.1.2 + z.1.2 + z.2 from (add_assoc _ _ _).symm))

/-- Left unit law: `μ_(0,δ)` followed by `0 + δ ≤ δ` is `zeroHomeomorph`. -/
theorem addMap_zero_left (δ : ℝ≥0) :
    (bandInclusion X (zero_add δ).le).comp (addMap X 0 δ) =
      (zeroHomeomorph (X × Band δ) : C((X × Band δ) × Band 0, X × Band δ)) :=
  ContinuousMap.ext fun z => Prod.ext rfl (Subtype.ext
    (show (z.1.2 : ℝ) + z.2 = z.1.2 by rw [eq_zero_of_mem_band_zero z.2.2, add_zero]))

/-- Right unit law: `μ_(δ,0)` followed by `δ + 0 ≤ δ` is `T_δ` of `zeroHomeomorph`. -/
theorem addMap_zero_right (δ : ℝ≥0) :
    (bandInclusion X (add_zero δ).le).comp (addMap X δ 0) =
      map (zeroHomeomorph X : C(X × Band 0, X)) δ :=
  ContinuousMap.ext fun z => Prod.ext rfl (Subtype.ext
    (show (z.1.2 : ℝ) + z.2 = z.2 by rw [eq_zero_of_mem_band_zero z.1.2.2, zero_add]))

/-- The outer zero section followed by `μ_(ε,δ)` is the band enlargement `δ ≤ ε + δ`. -/
theorem addMap_comp_zeroSection (ε δ : ℝ≥0) :
    (addMap X ε δ).comp (zeroSection (X × Band δ) ε) = bandInclusion X (le_add_self : δ ≤ ε + δ) :=
  ContinuousMap.ext fun z => Prod.ext rfl (Subtype.ext (add_zero (z.2 : ℝ)))

/-- `T_ε` of the inner zero section followed by `μ_(ε,δ)` is the band enlargement
`ε ≤ ε + δ`. -/
theorem addMap_comp_map_zeroSection (ε δ : ℝ≥0) :
    (addMap X ε δ).comp (map (zeroSection X δ) ε) = bandInclusion X (le_self_add : ε ≤ ε + δ) :=
  ContinuousMap.ext fun z => Prod.ext rfl (Subtype.ext (zero_add (z.2 : ℝ)))

/-- The addition map is surjective: `(x, u)` is the image of `((x, s), u - s)` with `s` the
projection of `u` onto `[-δ, δ]`. -/
theorem addMap_surjective (X : Type u) [TopologicalSpace X] (ε δ : ℝ≥0) :
    Function.Surjective (addMap X ε δ) := by
  rintro ⟨x, u⟩
  set s : Band δ := projIcc (-(δ : ℝ)) δ (neg_le_band δ) u with hs_def
  have hs : (s : ℝ) = max (-(δ : ℝ)) (min (δ : ℝ) u) := coe_projIcc _ _ _ _
  have h₁ : -((ε : ℝ) + δ) ≤ u := by have := u.2.1; rwa [NNReal.coe_add] at this
  have h₂ : (u : ℝ) ≤ ε + δ := by have := u.2.2; rwa [NNReal.coe_add] at this
  have hε := ε.coe_nonneg
  have hδ := δ.coe_nonneg
  have hmem : (u : ℝ) - s ∈ Band ε := by
    rw [hs]
    have hm1 : min (δ : ℝ) u ≤ δ := min_le_left _ _
    have hm2 : min (δ : ℝ) u ≤ u := min_le_right _ _
    have hv1 : -(δ : ℝ) ≤ max (-(δ : ℝ)) (min (δ : ℝ) u) := le_max_left _ _
    have hv2 : min (δ : ℝ) u ≤ max (-(δ : ℝ)) (min (δ : ℝ) u) := le_max_right _ _
    rcases min_choice (δ : ℝ) u with hm | hm <;>
      rcases max_choice (-(δ : ℝ)) (min (δ : ℝ) u) with hv | hv <;>
      exact ⟨by linarith, by linarith⟩
  exact ⟨((x, s), ⟨u - s, hmem⟩), Prod.ext rfl (Subtype.ext (add_sub_cancel _ _))⟩

/-- For nonempty `X` and `ε, δ > 0` the addition map is not injective: with `m = min ε δ`,
`((x, 0), 0)` and `((x, m), -m)` are distinct with the same image. -/
theorem addMap_not_injective [Nonempty X] {ε δ : ℝ≥0} (hε : 0 < ε) (hδ : 0 < δ) :
    ¬ Function.Injective (addMap X ε δ) := by
  intro hinj
  obtain ⟨x⟩ := ‹Nonempty X›
  have hε' : (0 : ℝ) < ε := hε
  have hδ' : (0 : ℝ) < δ := hδ
  have hm : 0 < min (ε : ℝ) δ := lt_min hε' hδ'
  have hmε : min (ε : ℝ) δ ≤ ε := min_le_left _ _
  have hmδ : min (ε : ℝ) δ ≤ δ := min_le_right _ _
  have h := hinj (a₁ := ((x, ⟨0, zero_mem_band δ⟩), ⟨0, zero_mem_band ε⟩))
    (a₂ := ((x, ⟨min (ε : ℝ) δ, ⟨by linarith, hmδ⟩⟩), ⟨-min (ε : ℝ) δ, ⟨by linarith, by linarith⟩⟩))
    (Prod.ext rfl (Subtype.ext (show (0 : ℝ) + 0 = min (ε : ℝ) δ + -min (ε : ℝ) δ by ring)))
  have h' := congrArg (fun z : (X × Band δ) × Band ε => (z.1.2 : ℝ)) h
  exact hm.ne h'

end AddMap

/-! ### Path components -/

section Components

variable {X : Type u} [TopologicalSpace X]

/-- **Path-component compatibility.** `π₀` of `μ_(ε,δ)` followed by `ρ_(ε+δ)` is `ρ_ε`, then
`S_ε ρ_δ`, then the merged `smoothingCompIso ε δ`. -/
theorem addMap_comp_componentComparison (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    intervalComponentNatTrans (addMap X ε δ) (height_addMap f ε δ) ≫
        componentComparison f (ε + δ) =
      componentComparison (height f δ) ε ≫ (smoothing ε).map (componentComparison f δ) ≫
        (smoothingCompIso ε δ).hom.app (intervalComponents f) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk z => rfl

/-- `π₀` of the addition map is an isomorphism, although the addition map is not a
homeomorphism for nonempty `X` and `ε, δ > 0`. -/
instance isIso_intervalComponentNatTrans_addMap (f : C(X, ℝ)) (ε δ : ℝ≥0) :
    IsIso (intervalComponentNatTrans (addMap X ε δ) (height_addMap f ε δ)) := by
  have : IsIso ((smoothing ε).map (componentComparison f δ)) := Functor.map_isIso _ _
  have : IsIso ((smoothingCompIso ε δ).hom.app (intervalComponents f)) :=
    Iso.isIso_hom ((smoothingCompIso ε δ).app _)
  have : IsIso (intervalComponentNatTrans (addMap X ε δ) (height_addMap f ε δ) ≫
      componentComparison f (ε + δ)) := by
    rw [addMap_comp_componentComparison]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (componentComparison f (ε + δ))

/-- At every interval, `π₀` of the addition map is a bijection. -/
theorem intervalComponentNatTrans_addMap_app_bijective (f : C(X, ℝ)) (ε δ : ℝ≥0)
    (I : OpenInterval) :
    Function.Bijective ((intervalComponentNatTrans (addMap X ε δ) (height_addMap f ε δ)).app I) :=
  (isIso_iff_bijective _).1 inferInstance

end Components

/-! ### Packaging on the real slice (universe `0`) -/

section Over

/-- Band enlargement `T_ε ⟶ T_δ` for `ε ≤ δ` on the real slice. -/
def bandInclusionNatTrans {ε δ : ℝ≥0} (h : ε ≤ δ) : functor ε ⟶ functor δ where
  app A := Over.homMk (TopCat.ofHom (bandInclusion A.left h))
    (by ext z; exact height_bandInclusion (overBaseMap A) h z)
  naturality A B φ := by ext z; rfl

theorem bandInclusionNatTrans_app_left_hom {ε δ : ℝ≥0} (h : ε ≤ δ) (A : Over (TopCat.of ℝ)) :
    ((bandInclusionNatTrans h).app A).left.hom = bandInclusion A.left h := rfl

/-- The addition map `μ_(ε,δ) : T_ε T_δ ⟶ T_(ε+δ)` on the real slice. -/
def addNatTrans (ε δ : ℝ≥0) : functor δ ⋙ functor ε ⟶ functor (ε + δ) where
  app A := Over.homMk (TopCat.ofHom (addMap A.left ε δ))
    (by ext z; exact height_addMap (overBaseMap A) ε δ z)
  naturality A B φ := by ext z; rfl

theorem addNatTrans_app_left_hom (ε δ : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    ((addNatTrans ε δ).app A).left.hom = addMap A.left ε δ := rfl

/-- Band enlargement in both parameters, as an equation of natural transformations. -/
theorem addNatTrans_comp_bandInclusionNatTrans {ε ε' δ δ' : ℝ≥0} (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    Functor.whiskerRight (bandInclusionNatTrans hδ) (functor ε) ≫
        Functor.whiskerLeft (functor δ') (bandInclusionNatTrans hε) ≫ addNatTrans ε' δ' =
      addNatTrans ε δ ≫ bandInclusionNatTrans (add_le_add hε hδ) := by
  ext A z
  rfl

/-- Associativity of `addNatTrans`, with `(ε + δ) + γ ≤ ε + (δ + γ)` bridged by band
enlargement. -/
theorem addNatTrans_assoc (ε δ γ : ℝ≥0) :
    Functor.whiskerLeft (functor γ) (addNatTrans ε δ) ≫ addNatTrans (ε + δ) γ ≫
        bandInclusionNatTrans (add_assoc ε δ γ).le =
      Functor.whiskerRight (addNatTrans δ γ) (functor ε) ≫ addNatTrans ε (δ + γ) := by
  ext A z
  exact DFunLike.congr_fun (addMap_assoc (X := A.left) ε δ γ) z

/-- Left unit law against `zeroIso`. -/
theorem addNatTrans_zero_left (δ : ℝ≥0) :
    addNatTrans 0 δ ≫ bandInclusionNatTrans (zero_add δ).le =
      Functor.whiskerLeft (functor δ) zeroIso.hom := by
  ext A z
  exact DFunLike.congr_fun (addMap_zero_left (X := A.left) δ) z

/-- Right unit law against `zeroIso`. -/
theorem addNatTrans_zero_right (δ : ℝ≥0) :
    addNatTrans δ 0 ≫ bandInclusionNatTrans (add_zero δ).le =
      Functor.whiskerRight zeroIso.hom (functor δ) := by
  ext A z
  exact DFunLike.congr_fun (addMap_zero_right (X := A.left) δ) z

/-- The outer zero section followed by `addNatTrans` is the enlargement `δ ≤ ε + δ`. -/
theorem whiskerLeft_zeroSectionNatTrans_comp_addNatTrans (ε δ : ℝ≥0) :
    Functor.whiskerLeft (functor δ) (zeroSectionNatTrans ε) ≫ addNatTrans ε δ =
      bandInclusionNatTrans (le_add_self : δ ≤ ε + δ) := by
  ext A z
  exact DFunLike.congr_fun (addMap_comp_zeroSection (X := A.left) ε δ) z

/-- `T_ε` of the inner zero section followed by `addNatTrans` is the enlargement
`ε ≤ ε + δ`. -/
theorem whiskerRight_zeroSectionNatTrans_comp_addNatTrans (ε δ : ℝ≥0) :
    Functor.whiskerRight (zeroSectionNatTrans δ) (functor ε) ≫ addNatTrans ε δ =
      bandInclusionNatTrans (le_self_add : ε ≤ ε + δ) := by
  ext A z
  exact DFunLike.congr_fun (addMap_comp_map_zeroSection (X := A.left) ε δ) z

/-- Path-component compatibility on the slice, objectwise. -/
theorem map_addNatTrans_comp_componentComparisonNatIso (ε δ : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    intervalComponentsOver.map ((addNatTrans ε δ).app A) ≫
        (componentComparisonNatIso (ε + δ)).hom.app A =
      (componentComparisonNatIso ε).hom.app ((functor δ).obj A) ≫
        (smoothing ε).map ((componentComparisonNatIso δ).hom.app A) ≫
          (smoothingCompIso ε δ).hom.app (intervalComponentsOver.obj A) :=
  addMap_comp_componentComparison (overBaseMap A) ε δ

/-- Path-component compatibility on the slice, as an equation of natural transformations
`(T_ε T_δ) ⋙ 𝒞 ⟶ 𝒞 ⋙ S_(ε+δ)`. -/
theorem whiskerRight_addNatTrans_comp_componentComparisonNatIso (ε δ : ℝ≥0) :
    Functor.whiskerRight (addNatTrans ε δ) intervalComponentsOver ≫
        (componentComparisonNatIso (ε + δ)).hom =
      Functor.whiskerLeft (functor δ) (componentComparisonNatIso ε).hom ≫
        Functor.whiskerRight (componentComparisonNatIso δ).hom (smoothing ε) ≫
          Functor.whiskerLeft intervalComponentsOver (smoothingCompIso ε δ).hom := by
  ext A I c
  induction c using ZerothHomotopy.rec with
  | mk z => rfl

/-- `π₀` of `addNatTrans` is an isomorphism at every object. -/
instance isIso_map_addNatTrans_app (ε δ : ℝ≥0) (A : Over (TopCat.of ℝ)) :
    IsIso (intervalComponentsOver.map ((addNatTrans ε δ).app A)) :=
  isIso_intervalComponentNatTrans_addMap (overBaseMap A) ε δ

end Over

/-! ### The one-point counterexample -/

section OnePoint

/-- The one-point space over height `0`. -/
def onePoint : Over (TopCat.of ℝ) :=
  Over.mk (TopCat.ofHom (ContinuousMap.const PUnit.{1} (0 : ℝ)))

/-- The segment `s ↦ ((*, s), -s)` in `T_1 T_1` of the point. -/
def fiberSegment (s : Band 1) : ((functor 1).obj ((functor 1).obj onePoint)).left :=
  ((PUnit.unit, s), ⟨-s, neg_mem_band s.2⟩)

/-- The height-`0` fibre of `T_1 T_1` of the point contains a segment: `s ↦ ((*, s), -s)` is
injective and lands at height `0`. -/
theorem fiber_zero_injective :
    Function.Injective fiberSegment ∧
      ∀ s, overBaseMap ((functor 1).obj ((functor 1).obj onePoint)) (fiberSegment s) = 0 :=
  ⟨fun s s' h => congrArg (fun z : ((functor 1).obj ((functor 1).obj onePoint)).left => z.1.2) h,
    fun s => show (0 : ℝ) + s + -s = 0 by ring⟩

/-- Every height-`0` fibre of `T_ε` of the point is a subsingleton: its points are `(*, t)` with
`t = 0`. -/
theorem fiber_zero_subsingleton (ε : ℝ≥0) :
    Subsingleton {z : ((functor ε).obj onePoint).left //
      overBaseMap ((functor ε).obj onePoint) z = 0} := by
  constructor
  rintro ⟨⟨a, s⟩, hs⟩ ⟨⟨b, t⟩, ht⟩
  have hs' : (0 : ℝ) + s = 0 := hs
  have ht' : (0 : ℝ) + t = 0 := ht
  exact Subtype.ext (Prod.ext (Subsingleton.elim (α := PUnit.{1}) _ _) (Subtype.ext (by linarith)))

/-- **No isomorphism `T_1 T_1 P ≅ T_(1+1) P`.** A slice isomorphism is injective and preserves
height, so it would embed the segment of `fiber_zero_injective` into the subsingleton of
`fiber_zero_subsingleton`. -/
theorem not_iso_one_one :
    IsEmpty ((functor 1).obj ((functor 1).obj onePoint) ≅ (functor (1 + 1)).obj onePoint) := by
  constructor
  intro e
  have hinj : Function.Injective e.hom.left.hom :=
    (TopCat.homeoOfIso ((Over.forget _).mapIso e)).injective
  have hz : ∀ s, overBaseMap ((functor (1 + 1)).obj onePoint) (e.hom.left.hom (fiberSegment s)) =
      0 := fun s => (overBaseMap_comm e.hom _).trans (fiber_zero_injective.2 s)
  have h01 := hinj (congrArg Subtype.val ((fiber_zero_subsingleton (1 + 1)).elim
    ⟨_, hz ⟨0, zero_mem_band 1⟩⟩ ⟨_, hz ⟨((1 : ℝ≥0) : ℝ), right_mem_Icc.2 (neg_le_band 1)⟩⟩))
  have h := congrArg Subtype.val (fiber_zero_injective.1 h01)
  norm_num at h

/-- The addition map of the point at `ε = δ = 1` is not an isomorphism. -/
theorem not_isIso_addNatTrans_app_one_one : ¬ IsIso ((addNatTrans 1 1).app onePoint) :=
  fun _ => not_iso_one_one.false (asIso ((addNatTrans 1 1).app onePoint))

end OnePoint

end

end GeometricThickening

end TDA.Reeb
