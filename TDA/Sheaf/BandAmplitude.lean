import TDA.Sheaf.BandStalks

/-!
# Amplitude of the band functors and their restriction to `Dᵇ`

Degrees are those of the canonical t-structure: `K : DerivedCategory.Plus C` lies in degrees
`[m, n]` when `K.IsGE m` and `K.IsLE n`, that is, when its homology `Hⁱ K` vanishes outside
`[m, n]`.

Right derived functors on `D⁺`, for abelian `C`, `D` with `C` having enough injectives:

* `isGE_rightDerivedFunctorPlus_obj`: `RF` keeps `IsGE m`, for every additive `F`.
* `nonempty_homology_rightDerivedFunctorPlus_of_exact`: for an exact `F`,
  `Hⁱ(RF K) ≅ F (Hⁱ K)`; hence `isLE_rightDerivedFunctorPlus_obj_of_exact`: `RF` keeps `IsLE n`.

Compact intervals, `RΓ([u, v]; -) = pushforwardPlus k (toPt _)`:

* `isLE_pushforwardPlus_toPt_Icc`: if `G` is `IsLE n`, then `RΓ([u, v]; G)` is `IsLE (n + 1)`.
  On a bounded below injective model `I` of `G`, which is exact above `n`, global sections are
  exact in each degree `i ≥ n + 2` (`sections_exact_Icc`, with the injective `I^{i-2}` as
  germ-surjective source). `isGE_isLE_pushforwardPlus_toPt_Icc` records the amplitude `[0, 1]`.

The band functors `T k a = R(q a)_* (p a)⁻¹`:

* `isGE_T_obj`: `K` in degrees `≥ m` gives `T k a K` in degrees `≥ m`.
* `isLE_T_obj`: `K` in degrees `≤ n` gives `T k a K` in degrees `≤ n + 1`. The stalk at `y` of
  `Hⁱ(T k a K)` is read through `(ptAt y)⁻¹` (`stalkPullbackSheafIso`), and by the stalk formula
  (`nonempty_stalkFormula_homology`) it is `Hⁱ([y - a, y + a]; (fibreEmb a y)⁻¹ (p a)⁻¹ K)`.
* `isGE_isLE_T_obj`: amplitude `[0, 1]`, `[m, n] ↦ [m, n + 1]`.

The bounded derived category. `boundedToPlus C : Dᵇ(C) ⥤ D⁺(C)` is the inclusion. A functor
`Φ : D⁺(C) ⥤ D⁺(D)` with `PreservesBounded Φ` restricts to `restrictBounded Φ hΦ : Dᵇ(C) ⥤ Dᵇ(D)`,
with `restrictBounded Φ hΦ ⋙ boundedToPlus D = boundedToPlus C ⋙ Φ`
(`restrictBounded_comp_boundedToPlus`). Natural transformations restrict by `restrictBoundedMap`
(`restrictBoundedMap_id`, `restrictBoundedMap_comp`, `whiskerRight_restrictBoundedMap`) and
isomorphisms by `restrictBoundedIso`; `restrictBoundedId` and `restrictBoundedComp` compare the
restrictions of `𝟭` and of a composite. A transformation `τ : Φ₁ ⋙ Φ₂ ⟶ Ψ` between composites
restricts to `restrictBoundedCompMap τ`, an isomorphism to `restrictBoundedCompMapIso`
(`whiskerRight_restrictBoundedCompMap`).

For the band functors: `preservesBounded_T`, `TB k a`, `TB_comp_boundedToPlus`; the radius maps
`restrB` (`restrB_refl`, `restrB_trans`), the unit `T0IsoB`, the augmentation `augB` (`augB_eq`,
`augB_zero`, `restrB_comp_augB`), each with its `whiskerRight` equation through `boundedToPlus`,
and `compIsoB μ : TB k a ⋙ TB k b ≅ TB k c` for an isomorphism `μ : T k a ⋙ T k b ≅ T k c`.

The statements on `T` that bound degrees from above take derived category structures on the point
and on every compact interval as instance arguments, used for the stalk formula.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

namespace TDA.Sheaf

section general

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- `Hⁱ` of the localization of a bounded below complex is its `i`-th homology. -/
private def homologyQIso (X : CochainComplex.Plus C) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C i).obj (DerivedCategory.Plus.Q.obj X) ≅
      X.obj.homology i :=
  (DerivedCategory.homologyFunctor C i).mapIso ((DerivedCategory.Plus.QCompιIso C).app X) ≪≫
    (DerivedCategory.homologyFunctorFactors C i).app X.obj

/-- `IsLE n` on `D⁺` is the vanishing of the homology above `n`. -/
private theorem plus_isLE_iff (X : DerivedCategory.Plus C) (n : ℤ) :
    X.IsLE n ↔ ∀ i, n < i → IsZero ((DerivedCategory.Plus.homologyFunctor C i).obj X) := by
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  rfl

variable [EnoughInjectives C]

/-- **Right derived functors do not lower degrees.** For an additive `F`, if `K ∈ D⁺(C)` lies in
degrees `≥ n`, so does `RF(K)`: on an injective model of `K` in degrees `≥ n`, `RF` is `F` applied
termwise. -/
theorem isGE_rightDerivedFunctorPlus_obj (F : C ⥤ D) [F.Additive] (K : DerivedCategory.Plus C)
    (n : ℤ) [K.IsGE n] : (F.rightDerivedFunctorPlus.obj K).IsGE n := by
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let I := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  have (m : ℤ) : Injective (I.obj.X m) := (L.obj.X m).property
  have := isIso_rightDerivedFunctorPlusUnit_app_of_injective F I
  have : CochainComplex.IsStrictlyGE (F.mapCochainComplexPlus.obj I).obj n :=
    inferInstanceAs (CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj
      (((InjectiveObject.ι C).mapHomologicalComplex _).obj L.obj)) n)
  have : DerivedCategory.Plus.TStructure.t.IsGE
      ((F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj I) n := by
    change (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I)).IsGE n
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj (F.mapCochainComplexPlus.obj I).obj).IsGE n
    infer_instance
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (asIso (F.rightDerivedFunctorPlusUnit.app I) ≪≫ F.rightDerivedFunctorPlus.mapIso e) n

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **Homology of the derived functor of an exact functor.** For an exact `F` and `K ∈ D⁺(C)`,
`Hⁱ(RF(K)) ≅ F(Hⁱ K)` in every degree `i`. -/
theorem nonempty_homology_rightDerivedFunctorPlus_of_exact (K : DerivedCategory.Plus C) (i : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor D i).obj (F.rightDerivedFunctorPlus.obj K) ≅
      F.obj ((DerivedCategory.Plus.homologyFunctor C i).obj K)) := by
  have := Localization.essSurj (DerivedCategory.Plus.Q (C := C)) (CochainComplex.Plus.quasiIso C)
  let K₀ := DerivedCategory.Plus.Q.objPreimage K
  let e : DerivedCategory.Plus.Q.obj K₀ ≅ K := DerivedCategory.Plus.Q.objObjPreimageIso K
  exact ⟨(DerivedCategory.Plus.homologyFunctor D i).mapIso
      (F.rightDerivedFunctorPlus.mapIso e.symm ≪≫
        (asIso (F.rightDerivedFunctorPlusUnit.app K₀)).symm) ≪≫
    homologyQIso _ i ≪≫ (K₀.obj.sc i).mapHomologyIso F ≪≫
    F.mapIso ((homologyQIso K₀ i).symm ≪≫ (DerivedCategory.Plus.homologyFunctor C i).mapIso e)⟩

/-- **Derived functors of exact functors do not raise degrees.** For an exact `F`, if
`K ∈ D⁺(C)` lies in degrees `≤ n`, so does `RF(K)`. -/
theorem isLE_rightDerivedFunctorPlus_obj_of_exact (K : DerivedCategory.Plus C) (n : ℤ)
    [K.IsLE n] : (F.rightDerivedFunctorPlus.obj K).IsLE n := by
  rw [plus_isLE_iff]
  intro i hi
  obtain ⟨e⟩ := nonempty_homology_rightDerivedFunctorPlus_of_exact F K i
  exact (F.map_isZero (DerivedCategory.Plus.isZero_homology_of_isLE K n i hi)).of_iso e

end general

section interval

variable {k : Type} [Ring k] [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  {u v : ℝ} [HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

/-- **Cohomological dimension one of a compact interval, for complexes.** If
`G ∈ D⁺(Sh [u, v])` lies in degrees `≤ n`, then `RΓ([u, v]; G)` lies in degrees `≤ n + 1`. -/
theorem isLE_pushforwardPlus_toPt_Icc
    (G : DerivedCategory.Plus ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))) (n : ℤ)
    [G.IsLE n] : ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).obj G).IsLE (n + 1) := by
  obtain ⟨m, hm⟩ := G.property
  have : G.IsGE m := (G.isGE_ι_obj_iff m).1 hm
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso G m
  let I := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
  have (j : ℤ) : Injective (I.obj.X j) := (L.obj.X j).property
  -- The injective model is exact above `n`.
  have hex (j : ℤ) (hj : n < j) : I.obj.ExactAt j := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (DerivedCategory.Plus.isZero_homology_of_isLE G n j hj).of_iso
      ((homologyQIso I j).symm ≪≫ (DerivedCategory.Plus.homologyFunctor _ j).mapIso e)
  rw [plus_isLE_iff]
  intro i hi
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
    ((pushforwardPlus k _).mapIso e.symm) ≪≫ homologyRightDerivedIsoOfInjective _ I i)
  refine HomologicalComplex.ExactAt.isZero_homology ?_
  have h₀ := (HomologicalComplex.exactAt_iff' I.obj (i - 2) (i - 1) i
    ((ComplexShape.up ℤ).prev_eq' (show i - 2 + 1 = i - 1 by omega))
    ((ComplexShape.up ℤ).next_eq' (show i - 1 + 1 = i by omega))).1
    (hex (i - 1) (by omega))
  have h₁ := (HomologicalComplex.exactAt_iff' I.obj (i - 1) i (i + 1)
    ((ComplexShape.up ℤ).prev_eq' (show i - 1 + 1 = i by omega))
    ((ComplexShape.up ℤ).next_eq' rfl)).1
    (hex i (by omega))
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1)
    ((ComplexShape.up ℤ).prev_eq' (show i - 1 + 1 = i by omega))
    ((ComplexShape.up ℤ).next_eq' rfl)]
  apply exact_of_sections_top
  intro s hs
  exact sections_exact_Icc k (I.obj.d (i - 2) (i - 1)) (I.obj.d (i - 1) i) (I.obj.d i (i + 1))
    (I.obj.d_comp_d _ _ _) (I.obj.d_comp_d _ _ _) h₀ h₁ (germSurjective_of_injective k _) s hs

/-- **Amplitude `[0, 1]` of `RΓ` on a compact interval.** If `G ∈ D⁺(Sh [u, v])` lies in degrees
`[m, n]`, then `RΓ([u, v]; G)` lies in degrees `[m, n + 1]`. -/
theorem isGE_isLE_pushforwardPlus_toPt_Icc
    (G : DerivedCategory.Plus ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))) (m n : ℤ)
    [G.IsGE m] [G.IsLE n] :
    ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).obj G).IsGE m ∧
      ((pushforwardPlus k (toPt (TopCat.of (Set.Icc u v)))).obj G).IsLE (n + 1) :=
  ⟨isGE_rightDerivedFunctorPlus_obj _ G m, isLE_pushforwardPlus_toPt_Icc G n⟩

end interval

namespace BandConvolution

section amplitude

variable (k : Type) [Ring k] [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]

/-- **The band functors do not lower degrees.** If `K ∈ D⁺(Sh ℝ)` lies in degrees `≥ m`, so does
`T k a K`. -/
theorem isGE_T_obj (a : ℝ) (K : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) (m : ℤ)
    [K.IsGE m] : ((T k a).obj K).IsGE m := by
  have := isGE_rightDerivedFunctorPlus_obj (TopCat.Sheaf.pullback (ModuleCat.{0} k) (p a)) K m
  exact isGE_rightDerivedFunctorPlus_obj (TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)) _ m

variable [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

/-- **The band functors raise degrees by at most one.** If `K ∈ D⁺(Sh ℝ)` lies in degrees `≤ n`,
then `T k a K` lies in degrees `≤ n + 1`, for every sheaf-valued `K` and every `a`: the fibres of
`q a` are the compact intervals `[y - a, y + a]`. -/
theorem isLE_T_obj (a : ℝ) (K : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) (n : ℤ)
    [K.IsLE n] : ((T k a).obj K).IsLE (n + 1) := by
  rw [plus_isLE_iff]
  intro i hi
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  intro y
  let M := (DerivedCategory.Plus.homologyFunctor _ i).obj ((T k a).obj K)
  have h : IsZero ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).obj M) := by
    obtain ⟨e₁⟩ := nonempty_homology_rightDerivedFunctorPlus_of_exact
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)) ((T k a).obj K) i
    obtain ⟨e₂⟩ := nonempty_stalkFormula_homology k a y ((pullbackPlus k (p a)).obj K) i
    have := isLE_rightDerivedFunctorPlus_obj_of_exact
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) (p a)) K n
    have := isLE_rightDerivedFunctorPlus_obj_of_exact
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)) ((pullbackPlus k (p a)).obj K) n
    have := isLE_pushforwardPlus_toPt_Icc
      ((pullbackPlus k (fibreEmb a y)).obj ((pullbackPlus k (p a)).obj K)) n
    exact (DerivedCategory.Plus.isZero_homology_of_isLE _ (n + 1) i hi).of_iso (e₁.symm ≪≫ e₂)
  exact (Functor.map_isZero (TopCat.Sheaf.forget (ModuleCat.{0} k) pt ⋙
    TopCat.Presheaf.stalkFunctor _ PUnit.unit) h).of_iso
    (stalkPullbackSheafIso k (ptAt y) M PUnit.unit)

/-- **Amplitude `[0, 1]` of the band functors.** If `K ∈ D⁺(Sh ℝ)` lies in degrees `[m, n]`, then
`T k a K` lies in degrees `[m, n + 1]`. -/
theorem isGE_isLE_T_obj (a : ℝ) (K : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k)))
    (m n : ℤ) [K.IsGE m] [K.IsLE n] :
    ((T k a).obj K).IsGE m ∧ ((T k a).obj K).IsLE (n + 1) :=
  ⟨isGE_T_obj k a K m, isLE_T_obj k a K n⟩

end amplitude

end BandConvolution

section bounded

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

variable (C) in
/-- The inclusion `Dᵇ(C) ⥤ D⁺(C)` of the bounded into the bounded below derived category. -/
abbrev boundedToPlus : DerivedCategory.Bounded C ⥤ DerivedCategory.Plus C :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

/-- A functor `Φ : D⁺(C) ⥤ D⁺(D)` preserves bounded objects: it sends objects lying in degrees
`≤ n` for some `n` to objects lying in degrees `≤ n'` for some `n'`. -/
def PreservesBounded (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D) : Prop :=
  ∀ (K : DerivedCategory.Plus C) (n : ℤ), K.IsLE n → ∃ n' : ℤ, (Φ.obj K).IsLE n'

/-- The identity preserves bounded objects. -/
theorem PreservesBounded.id : PreservesBounded (𝟭 (DerivedCategory.Plus C)) :=
  fun _ n h => ⟨n, h⟩

/-- Functors preserving bounded objects compose. -/
theorem PreservesBounded.comp {Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D}
    {Ψ : DerivedCategory.Plus D ⥤ DerivedCategory.Plus E} (hΦ : PreservesBounded Φ)
    (hΨ : PreservesBounded Ψ) : PreservesBounded (Φ ⋙ Ψ) := fun K n h => by
  obtain ⟨n', h'⟩ := hΦ K n h
  exact hΨ _ n' h'

/-- **Restriction to the bounded derived category.** A functor `Φ : D⁺(C) ⥤ D⁺(D)` preserving
bounded objects restricts to `Dᵇ(C) ⥤ Dᵇ(D)`. -/
def restrictBounded (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (hΦ : PreservesBounded Φ) : DerivedCategory.Bounded C ⥤ DerivedCategory.Bounded D :=
  ObjectProperty.lift _ (boundedToPlus C ⋙ Φ ⋙ DerivedCategory.Plus.ι) (fun K => by
    obtain ⟨n, hn⟩ := K.property.2
    obtain ⟨n', hn'⟩ := hΦ ((boundedToPlus C).obj K) n
      ((DerivedCategory.Plus.isLE_ι_obj_iff _ n).1 hn)
    exact ⟨(Φ.obj _).property, n', (DerivedCategory.Plus.isLE_ι_obj_iff _ n').2 hn'⟩)

/-- The restriction followed by the inclusion into `D⁺` is the inclusion followed by `Φ`. -/
theorem restrictBounded_comp_boundedToPlus (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (hΦ : PreservesBounded Φ) :
    restrictBounded Φ hΦ ⋙ boundedToPlus D = boundedToPlus C ⋙ Φ :=
  rfl

variable {Φ Ψ Χ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D} {hΦ : PreservesBounded Φ}
  {hΨ : PreservesBounded Ψ} {hΧ : PreservesBounded Χ}

/-- The restriction of a natural transformation `τ : Φ ⟶ Ψ` to the bounded derived category. -/
@[simps]
def restrictBoundedMap (τ : Φ ⟶ Ψ) : restrictBounded Φ hΦ ⟶ restrictBounded Ψ hΨ where
  app K := ObjectProperty.homMk (τ.app ((boundedToPlus C).obj K)).hom
  naturality _ _ f := by
    ext1
    exact congrArg (fun g => g.hom) (τ.naturality ((boundedToPlus C).map f))

/-- `restrictBoundedMap τ` whiskered by the inclusion into `D⁺` is `τ` whiskered by the inclusion. -/
theorem whiskerRight_restrictBoundedMap (τ : Φ ⟶ Ψ) :
    Functor.whiskerRight (restrictBoundedMap (hΦ := hΦ) (hΨ := hΨ) τ) (boundedToPlus D) =
      Functor.whiskerLeft (boundedToPlus C) τ :=
  rfl

/-- The restriction of the identity transformation is the identity. -/
@[simp]
theorem restrictBoundedMap_id : restrictBoundedMap (hΦ := hΦ) (hΨ := hΦ) (𝟙 Φ) = 𝟙 _ :=
  rfl

/-- Restriction of natural transformations is compatible with composition. -/
@[simp]
theorem restrictBoundedMap_comp (τ : Φ ⟶ Ψ) (σ : Ψ ⟶ Χ) :
    restrictBoundedMap (hΦ := hΦ) (hΨ := hΧ) (τ ≫ σ) =
      restrictBoundedMap (hΨ := hΨ) τ ≫ restrictBoundedMap σ :=
  rfl

/-- The restriction of a natural isomorphism `e : Φ ≅ Ψ` to the bounded derived category. -/
@[simps]
def restrictBoundedIso (e : Φ ≅ Ψ) : restrictBounded Φ hΦ ≅ restrictBounded Ψ hΨ where
  hom := restrictBoundedMap e.hom
  inv := restrictBoundedMap e.inv
  hom_inv_id := by rw [← restrictBoundedMap_comp, e.hom_inv_id, restrictBoundedMap_id]
  inv_hom_id := by rw [← restrictBoundedMap_comp, e.inv_hom_id, restrictBoundedMap_id]

variable (C) in
/-- The restriction of the identity of `D⁺(C)` is the identity of `Dᵇ(C)`. -/
def restrictBoundedId (h : PreservesBounded (𝟭 (DerivedCategory.Plus C))) :
    restrictBounded (𝟭 _) h ≅ 𝟭 (DerivedCategory.Bounded C) :=
  Iso.refl _

/-- The restriction of a composite is the composite of the restrictions. -/
def restrictBoundedComp (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D)
    (Ψ : DerivedCategory.Plus D ⥤ DerivedCategory.Plus E) (hΦ : PreservesBounded Φ)
    (hΨ : PreservesBounded Ψ) (hΦΨ : PreservesBounded (Φ ⋙ Ψ)) :
    restrictBounded (Φ ⋙ Ψ) hΦΨ ≅ restrictBounded Φ hΦ ⋙ restrictBounded Ψ hΨ :=
  Iso.refl _

/-- **Restriction of a transformation between composites.** For `τ : Φ₁ ⋙ Φ₂ ⟶ Ψ` with all
functors preserving bounded objects, the transformation
`restrictBounded Φ₁ ⋙ restrictBounded Φ₂ ⟶ restrictBounded Ψ` of functors on `Dᵇ`. -/
def restrictBoundedCompMap {Φ₁ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D}
    {Φ₂ : DerivedCategory.Plus D ⥤ DerivedCategory.Plus E}
    {Ψ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus E} (h₁ : PreservesBounded Φ₁)
    (h₂ : PreservesBounded Φ₂) (hΨ : PreservesBounded Ψ) (τ : Φ₁ ⋙ Φ₂ ⟶ Ψ) :
    restrictBounded Φ₁ h₁ ⋙ restrictBounded Φ₂ h₂ ⟶ restrictBounded Ψ hΨ :=
  (restrictBoundedComp Φ₁ Φ₂ h₁ h₂ (h₁.comp h₂)).inv ≫ restrictBoundedMap τ

/-- `restrictBoundedCompMap τ` whiskered by the inclusion into `D⁺` is `τ` whiskered by the
inclusion. -/
theorem whiskerRight_restrictBoundedCompMap
    {Φ₁ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D}
    {Φ₂ : DerivedCategory.Plus D ⥤ DerivedCategory.Plus E}
    {Ψ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus E} (h₁ : PreservesBounded Φ₁)
    (h₂ : PreservesBounded Φ₂) (hΨ : PreservesBounded Ψ) (τ : Φ₁ ⋙ Φ₂ ⟶ Ψ) :
    Functor.whiskerRight (restrictBoundedCompMap h₁ h₂ hΨ τ) (boundedToPlus E) =
      Functor.whiskerLeft (boundedToPlus C) τ := by
  ext K
  exact Category.id_comp _

/-- **Restriction of an isomorphism between composites.** For `e : Φ₁ ⋙ Φ₂ ≅ Ψ` with all functors
preserving bounded objects, the isomorphism
`restrictBounded Φ₁ ⋙ restrictBounded Φ₂ ≅ restrictBounded Ψ` of functors on `Dᵇ`; its
components are those of `restrictBoundedCompMap`. -/
def restrictBoundedCompMapIso {Φ₁ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D}
    {Φ₂ : DerivedCategory.Plus D ⥤ DerivedCategory.Plus E}
    {Ψ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus E} (h₁ : PreservesBounded Φ₁)
    (h₂ : PreservesBounded Φ₂) (hΨ : PreservesBounded Ψ) (e : Φ₁ ⋙ Φ₂ ≅ Ψ) :
    restrictBounded Φ₁ h₁ ⋙ restrictBounded Φ₂ h₂ ≅ restrictBounded Ψ hΨ :=
  (restrictBoundedComp Φ₁ Φ₂ h₁ h₂ (h₁.comp h₂)).symm ≪≫ restrictBoundedIso e

end bounded

namespace BandConvolution

section bounded

variable (k : Type) [Ring k] [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

/-- **The band functors preserve the bounded derived category.** -/
theorem preservesBounded_T (a : ℝ) : PreservesBounded (T k a) := fun K n h => by
  have := h
  exact ⟨n + 1, isLE_T_obj k a K n⟩

/-- The band functor `T k a` on the bounded derived category `Dᵇ(Sh(ℝ; k))`. -/
abbrev TB (a : ℝ) : DerivedCategory.Bounded (realLine.Sheaf (ModuleCat.{0} k)) ⥤
    DerivedCategory.Bounded (realLine.Sheaf (ModuleCat.{0} k)) :=
  restrictBounded (T k a) (preservesBounded_T k a)

/-- `TB k a` followed by the inclusion into `D⁺` is the inclusion followed by `T k a`. -/
theorem TB_comp_boundedToPlus (a : ℝ) :
    TB k a ⋙ boundedToPlus _ = boundedToPlus _ ⋙ T k a :=
  rfl

/-- The radius map `TB k b ⟶ TB k a` for `a ≤ b`, the restriction of `restr k h`. -/
abbrev restrB {a b : ℝ} (h : a ≤ b) : TB k b ⟶ TB k a :=
  restrictBoundedMap (restr k h)

/-- `restrB k h` whiskered by the inclusion into `D⁺` is `restr k h` whiskered by the
inclusion. -/
theorem whiskerRight_restrB {a b : ℝ} (h : a ≤ b) :
    Functor.whiskerRight (restrB k h) (boundedToPlus _) =
      Functor.whiskerLeft (boundedToPlus _) (restr k h) :=
  rfl

/-- The bounded radius map of `a ≤ a` is the identity. -/
theorem restrB_refl (a : ℝ) : restrB k (le_refl a) = 𝟙 _ := by
  rw [restrB, restr_refl, restrictBoundedMap_id]

/-- Bounded radius maps compose. -/
theorem restrB_trans {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    restrB k hbc ≫ restrB k hab = restrB k (hab.trans hbc) := by
  rw [restrB, restrB, ← restrictBoundedMap_comp, restr_trans]

/-- `TB k 0 ≅ 𝟭`, the restriction of `T0Iso k`. -/
def T0IsoB : TB k 0 ≅ 𝟭 _ :=
  restrictBoundedIso (hΨ := PreservesBounded.id) (T0Iso k) ≪≫
    restrictBoundedId _ PreservesBounded.id

/-- `T0IsoB k` whiskered by the inclusion into `D⁺` is `T0Iso k` whiskered by the inclusion. -/
theorem whiskerRight_T0IsoB_hom :
    Functor.whiskerRight (T0IsoB k).hom (boundedToPlus _) =
      Functor.whiskerLeft (boundedToPlus _) (T0Iso k).hom := by
  ext K
  exact Category.comp_id _

/-- The augmentation `TB k a ⟶ 𝟭` for `0 ≤ a`, the restriction of `aug k h`. -/
def augB {a : ℝ} (h : 0 ≤ a) : TB k a ⟶ 𝟭 _ :=
  restrictBoundedMap (hΨ := PreservesBounded.id) (aug k h) ≫
    (restrictBoundedId _ PreservesBounded.id).hom

/-- `augB k h` whiskered by the inclusion into `D⁺` is `aug k h` whiskered by the inclusion. -/
theorem whiskerRight_augB {a : ℝ} (h : 0 ≤ a) :
    Functor.whiskerRight (augB k h) (boundedToPlus _) =
      Functor.whiskerLeft (boundedToPlus _) (aug k h) := by
  ext K
  exact Category.comp_id _

/-- The bounded augmentation is the bounded radius map to `TB k 0` followed by `T0IsoB`. -/
theorem augB_eq {a : ℝ} (h : 0 ≤ a) : augB k h = restrB k h ≫ (T0IsoB k).hom := by
  rw [augB, aug, restrictBoundedMap_comp (hΨ := preservesBounded_T k 0), Category.assoc]
  rfl

/-- At `a = 0` the bounded augmentation is `T0IsoB`. -/
theorem augB_zero : augB k (le_refl (0 : ℝ)) = (T0IsoB k).hom := by
  rw [augB_eq, restrB_refl, Category.id_comp]

/-- The bounded augmentation is compatible with the bounded radius maps. -/
theorem restrB_comp_augB {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) :
    restrB k hab ≫ augB k ha = augB k (ha.trans hab) := by
  rw [augB_eq, augB_eq, ← Category.assoc, restrB_trans]

/-- **Restriction of a composition isomorphism.** An isomorphism `μ : T k a ⋙ T k b ≅ T k c`
restricts to `TB k a ⋙ TB k b ≅ TB k c` (`restrictBoundedCompMapIso`). -/
abbrev compIsoB {a b c : ℝ} (μ : T k a ⋙ T k b ≅ T k c) : TB k a ⋙ TB k b ≅ TB k c :=
  restrictBoundedCompMapIso (preservesBounded_T k a) (preservesBounded_T k b)
    (preservesBounded_T k c) μ

/-- `compIsoB k μ` whiskered by the inclusion into `D⁺` is `μ` whiskered by the inclusion. -/
theorem whiskerRight_compIsoB_hom {a b c : ℝ} (μ : T k a ⋙ T k b ≅ T k c) :
    Functor.whiskerRight (compIsoB k μ).hom (boundedToPlus _) =
      Functor.whiskerLeft (boundedToPlus _) μ.hom :=
  whiskerRight_restrictBoundedCompMap _ _ _ μ.hom

end bounded

end BandConvolution

end TDA.Sheaf
