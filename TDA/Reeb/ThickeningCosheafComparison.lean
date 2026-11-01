import TDA.Reeb.ThickeningConstructible
import TDA.Reeb.RGraphSmoothing

/-!
# The thickening–cosheaf comparison on constructible ℝ-spaces

For every constructible ℝ-space `X` and every `ε ≥ 0`, the path-component cosheaf of the
thickening `T_ε X` is the smoothing of the path-component cosheaf of `X`, naturally in all
height-preserving maps (de Silva–Munch–Patel, *Categorified Reeb Graphs*, Theorem 4.24, restricted
to constructible ℝ-spaces). Composed with the inverse of the constructible comparison
(Theorem 3.17) at `T_ε X`, it gives the companion comparison for the Reeb quotient of the
thickening. On graph objects the two comparisons are the existing ones of
`TDA.Reeb.RGraphSmoothing`, the second being DMP Proposition 4.32.

## The comparison

Write `C' = constructibleCosheafFunctor`, `T_ε = thickeningFunctor ε` and
`S_ε = constructibleSmoothing ε`, the smoothing of constructible cosheaves (not the endofunctor
`RGraph.constructibleSmoothing ε` of constructible ℝ-spaces). The first-projection comparison
`ρ = GeometricThickening.componentComparisonNatIso ε` lifts through the full subcategories to

```lean
constructibleThickeningComparisonIso ε :
    thickeningFunctor ε ⋙ constructibleCosheafFunctor ≅
      constructibleCosheafFunctor ⋙ constructibleSmoothing ε
```

with underlying components `ρ_X` (`constructibleThickeningComparisonIso_hom_app_hom`, by `rfl`).
On an interval `I` it sends the class of `(x, t)` in `{z | f x + t ∈ I}` to the class of `x` in
`{x | f x ∈ I^ε}` (`constructibleThickeningComparisonIso_hom_app_hom_app_mk`). Naturality is that
of `ρ`, so it holds for every continuous height-preserving map, whatever presentations its source
and target have. Whiskered by the inclusion of constructible cosheaves it is `ρ` whiskered by the
inclusion of constructible ℝ-spaces
(`isoWhiskerRight_constructibleThickeningComparisonIso`).

## The companion

Write `η = constructibleCosheafComparisonIso : C' ≅ ℛ ⋙ C''`. The companion is the composite

```lean
constructibleThickeningQuotientComparisonIso ε :
    thickeningFunctor ε ⋙ quotientRGraphFunctor ⋙ RGraph.cosheafFunctor ≅
      constructibleCosheafFunctor ⋙ constructibleSmoothing ε :=
  Functor.isoWhiskerLeft (thickeningFunctor ε) constructibleCosheafComparisonIso.symm ≪≫
    constructibleThickeningComparisonIso ε
```

with component `β_X = η_(T_ε X).inv ≫ ρ_X`
(`constructibleThickeningQuotientComparisonIso_hom_app`, by `rfl`).
The canonical hom-component equation `η_(T_ε X).hom ≫ β_X = ρ_X` holds in the full subcategory and
unbundled. On representatives `β_X(I)` sends the class of the Reeb class `q (x, t)` to the class of
`x` (`constructibleThickeningQuotientComparisonIso_hom_app_hom_app_mk`); this identifies
components, and no map from points of the Reeb quotient to `X` is asserted.

## Zero section, unit and `ε = 0`

`thickeningFunctorZeroSection ε : 𝟭 ⟶ T_ε` is the zero section `x ↦ (x, 0)`, lifted to
constructible ℝ-spaces. The comparison sends `C'` of the zero section to the lifted smoothing unit
(`constructibleCosheafFunctor_map_thickeningFunctorZeroSection_comp`). The companion sends `C'` of
the zero section followed by the Reeb projection, `RGraph.constructibleSmoothingUnit ε`, to the
same unit (`constructibleCosheafFunctor_map_constructibleSmoothingUnit_comp`): `C'` of the
projection is `η`, which cancels.

`thickeningFunctorZeroIso : T_0 ≅ 𝟭` is `GeometricThickening.zeroIso`, lifted; its inverse is the
zero section (`thickeningFunctorZeroIso_inv`). Through `ρ` at `ε = 0`, `C'` of it is the lifted
`constructibleSmoothingZeroIso`
(`constructibleCosheafFunctor_map_thickeningFunctorZeroIso_hom_app`).
For the companion, `C''ℛ` of it followed by `η⁻¹` is `β` followed by the same isomorphism
(`cosheafFunctor_map_thickeningFunctorZeroIso_comp_constructibleThickeningQuotientComparisonIso`);
on a constructible ℝ-space the Reeb quotient of `T_0 X` is the Reeb quotient of `X`, not `X`.

## Graph objects

Along `RGraph.rgraphToConstructible`, the comparison is `RGraph.thickeningCosheafComparisonIso ε`
(`isoWhiskerLeft_rgraphToConstructible_constructibleThickeningComparisonIso`) and the companion is
`RGraph.geometricSmoothingComparisonIso ε`
(`isoWhiskerLeft_rgraphToConstructible_constructibleThickeningQuotientComparisonIso`), both by
`rfl` on components.

## Values

`constructibleThickeningValueEquiv ε X I : C'(T_ε X)(I) ≃ C'(X)(I^ε)` and
`constructibleThickeningQuotientValueEquiv ε X I : C''(ℛ T_ε X)(I) ≃ C'(X)(I^ε)` are the two
comparisons at one interval.

The packaging is in universe `0`, as `ConstructibleSpaceCat` and `ConstructibleCosheafCat.{0}`
are. See `docs/math/reeb-thickening-cosheaf-comparison.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

open OpenInterval

/-! ### The comparison (DMP Theorem 4.24 on constructible ℝ-spaces) -/

/-- **DMP Theorem 4.24 on constructible ℝ-spaces**: `C' T_ε ≅ S_ε C'`, as a natural isomorphism
of functors `ConstructibleSpaceCat ⥤ ConstructibleCosheafCat.{0}`, natural in all
height-preserving maps. Its components are those of the first-projection comparison
`GeometricThickening.componentComparisonNatIso ε`. -/
def constructibleThickeningComparisonIso (ε : ℝ≥0) :
    thickeningFunctor ε ⋙ constructibleCosheafFunctor ≅
      constructibleCosheafFunctor ⋙ constructibleSmoothing ε :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ ((GeometricThickening.componentComparisonNatIso ε).app A.obj))
    (fun φ => by
      ext1
      exact (GeometricThickening.componentComparisonNatIso ε).hom.naturality φ.hom)

/-- The underlying component is the first-projection comparison `ρ_X`. -/
theorem constructibleThickeningComparisonIso_hom_app_hom (ε : ℝ≥0) (A : ConstructibleSpaceCat) :
    ((constructibleThickeningComparisonIso ε).hom.app A).hom =
      (GeometricThickening.componentComparisonNatIso ε).hom.app A.obj :=
  rfl

/-- The underlying component of the inverse is the inverse of `ρ_X`. -/
theorem constructibleThickeningComparisonIso_inv_app_hom (ε : ℝ≥0) (A : ConstructibleSpaceCat) :
    ((constructibleThickeningComparisonIso ε).inv.app A).hom =
      (GeometricThickening.componentComparisonNatIso ε).inv.app A.obj :=
  rfl

/-- The underlying component, unbundled: `GeometricThickening.componentComparison` of the structure
map. -/
theorem constructibleThickeningComparisonIso_hom_app_hom_eq (ε : ℝ≥0) (A : ConstructibleSpaceCat) :
    ((constructibleThickeningComparisonIso ε).hom.app A).hom =
      GeometricThickening.componentComparison (overBaseMap A.obj) ε :=
  rfl

/-- **Representative formula** `ρ_X(I) [(x, t)] = [x]`: the class of `(x, t)` with `f x + t ∈ I`
goes to the class of `x` in `{x // f x ∈ I^ε}`. -/
theorem constructibleThickeningComparisonIso_hom_app_hom_app_mk (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) (I : OpenInterval)
    (z : {z : A.obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap A.obj) ε z ∈ I}) :
    ((constructibleThickeningComparisonIso ε).hom.app A).hom.app I (ZerothHomotopy.mk z) =
      ZerothHomotopy.mk (⟨z.1.1, GeometricThickening.fst_mem_thicken z.2⟩ :
        {x : A.obj.left // overBaseMap A.obj x ∈ thicken ε I}) :=
  rfl

/-- On the underlying interval precosheaves, the comparison is `ρ`, whiskered by the inclusion of
constructible ℝ-spaces. -/
theorem isoWhiskerRight_constructibleThickeningComparisonIso (ε : ℝ≥0) :
    Functor.isoWhiskerRight (constructibleThickeningComparisonIso ε)
        (ObjectProperty.ι IsConstructibleCosheaf.{0}) =
      Functor.isoWhiskerLeft IsConstructibleSpace.ι
        (GeometricThickening.componentComparisonNatIso ε) :=
  Iso.ext rfl

/-- **Graph objects.** Along the inclusion of graph objects, the comparison is the graph comparison
`RGraph.thickeningCosheafComparisonIso`. -/
theorem isoWhiskerLeft_rgraphToConstructible_constructibleThickeningComparisonIso (ε : ℝ≥0) :
    Functor.isoWhiskerLeft RGraph.rgraphToConstructible (constructibleThickeningComparisonIso ε) =
      RGraph.thickeningCosheafComparisonIso ε :=
  Iso.ext rfl

/-- **Graph objects**, componentwise. -/
theorem constructibleThickeningComparisonIso_hom_app_rgraphToConstructible (ε : ℝ≥0)
    (A : RGraph.RGraphCat) :
    (constructibleThickeningComparisonIso ε).hom.app (RGraph.rgraphToConstructible.obj A) =
      (RGraph.thickeningCosheafComparisonIso ε).hom.app A :=
  rfl

/-! ### The zero section -/

/-- **The zero section** `x ↦ (x, 0)`, `𝟭 ⟶ T_ε` (de Silva–Munch–Patel, Observation 4.23),
lifted to constructible ℝ-spaces. -/
def thickeningFunctorZeroSection (ε : ℝ≥0) : 𝟭 ConstructibleSpaceCat ⟶ thickeningFunctor ε where
  app A := ObjectProperty.homMk ((GeometricThickening.zeroSectionNatTrans ε).app A.obj)
  naturality _ _ φ := by
    ext1
    exact (GeometricThickening.zeroSectionNatTrans ε).naturality φ.hom

theorem thickeningFunctorZeroSection_app_hom (ε : ℝ≥0) (A : ConstructibleSpaceCat) :
    ((thickeningFunctorZeroSection ε).app A).hom =
      (GeometricThickening.zeroSectionNatTrans ε).app A.obj :=
  rfl

/-- **Zero-section compatibility**: `C'` of the zero section followed by the comparison is the
lifted smoothing unit. -/
theorem constructibleCosheafFunctor_map_thickeningFunctorZeroSection_comp (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) :
    constructibleCosheafFunctor.map ((thickeningFunctorZeroSection ε).app A) ≫
        (constructibleThickeningComparisonIso ε).hom.app A =
      (constructibleSmoothingUnit ε).app (constructibleCosheafFunctor.obj A) := by
  ext1
  exact GeometricThickening.map_zeroSectionNatTrans_comp_componentComparisonNatIso ε A.obj

/-- **Zero-section compatibility**, as an equation of natural transformations
`C' ⟶ C' ⋙ S_ε`. -/
theorem whiskerRight_thickeningFunctorZeroSection_comp_constructibleThickeningComparisonIso
    (ε : ℝ≥0) :
    Functor.whiskerRight (thickeningFunctorZeroSection ε) constructibleCosheafFunctor ≫
        (constructibleThickeningComparisonIso ε).hom =
      Functor.whiskerLeft constructibleCosheafFunctor (constructibleSmoothingUnit ε) := by
  ext A : 2
  exact constructibleCosheafFunctor_map_thickeningFunctorZeroSection_comp ε A

/-! ### `ε = 0` -/

/-- **`T_0 ≅ 𝟭` on constructible ℝ-spaces**: the merged `GeometricThickening.zeroIso`, the first
projection `X × [0, 0] → X`, lifted through the full subcategory. -/
def thickeningFunctorZeroIso : thickeningFunctor 0 ≅ 𝟭 ConstructibleSpaceCat :=
  NatIso.ofComponents (fun A => ObjectProperty.isoMk _ (GeometricThickening.zeroIso.app A.obj))
    (fun φ => by
      ext1
      exact GeometricThickening.zeroIso.hom.naturality φ.hom)

theorem thickeningFunctorZeroIso_hom_app_hom (A : ConstructibleSpaceCat) :
    (thickeningFunctorZeroIso.hom.app A).hom = GeometricThickening.zeroIso.hom.app A.obj :=
  rfl

theorem thickeningFunctorZeroIso_inv_app_hom (A : ConstructibleSpaceCat) :
    (thickeningFunctorZeroIso.inv.app A).hom = GeometricThickening.zeroIso.inv.app A.obj :=
  rfl

/-- The inverse of `T_0 ≅ 𝟭` is the zero section. -/
theorem thickeningFunctorZeroIso_inv :
    thickeningFunctorZeroIso.inv = thickeningFunctorZeroSection 0 := by
  ext A : 2
  apply ObjectProperty.hom_ext
  exact NatTrans.congr_app GeometricThickening.zeroIso_inv A.obj

/-- **Zero comparison**: at `ε = 0`, `C'` of `T_0 ≅ 𝟭` is the comparison followed by the lifted
`S_0 ≅ 𝟭` (from `GeometricThickening.map_zeroIso_hom_app`). -/
theorem constructibleCosheafFunctor_map_thickeningFunctorZeroIso_hom_app
    (A : ConstructibleSpaceCat) :
    constructibleCosheafFunctor.map (thickeningFunctorZeroIso.hom.app A) =
      (constructibleThickeningComparisonIso 0).hom.app A ≫
        constructibleSmoothingZeroIso.hom.app (constructibleCosheafFunctor.obj A) := by
  ext1
  exact GeometricThickening.map_zeroIso_hom_app A.obj

/-! ### The companion: the Reeb quotient of the thickening -/

/-- The companion's source functor is `RGraph.thickeningQuotient ε` followed by `C''`. -/
theorem thickeningFunctor_comp_quotientRGraphFunctor_comp_cosheafFunctor (ε : ℝ≥0) :
    thickeningFunctor ε ⋙ quotientRGraphFunctor ⋙ RGraph.cosheafFunctor =
      RGraph.thickeningQuotient ε ⋙ RGraph.cosheafFunctor :=
  rfl

/-- **The companion comparison** `C'' ℛ T_ε ≅ S_ε C'` on constructible ℝ-spaces: the inverse of
the constructible comparison `η = constructibleCosheafComparisonIso` (DMP Theorem 3.17) at the
thickening, followed by `constructibleThickeningComparisonIso ε`. Natural in all
height-preserving maps. On graph objects it is DMP Proposition 4.32,
`RGraph.geometricSmoothingComparisonIso`. -/
def constructibleThickeningQuotientComparisonIso (ε : ℝ≥0) :
    thickeningFunctor ε ⋙ quotientRGraphFunctor ⋙ RGraph.cosheafFunctor ≅
      constructibleCosheafFunctor ⋙ constructibleSmoothing ε :=
  Functor.isoWhiskerLeft (thickeningFunctor ε) constructibleCosheafComparisonIso.symm ≪≫
    constructibleThickeningComparisonIso ε

/-- `β_X = η_(T_ε X).inv ≫ ρ_X`, in the full subcategory. -/
theorem constructibleThickeningQuotientComparisonIso_hom_app (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) :
    (constructibleThickeningQuotientComparisonIso ε).hom.app A =
      constructibleCosheafComparisonIso.inv.app ((thickeningFunctor ε).obj A) ≫
        (constructibleThickeningComparisonIso ε).hom.app A :=
  rfl

/-- `β_X = η_(T_ε X).inv ≫ ρ_X`, on the underlying interval precosheaves. -/
theorem constructibleThickeningQuotientComparisonIso_hom_app_hom (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) :
    ((constructibleThickeningQuotientComparisonIso ε).hom.app A).hom =
      constructibleComponentComparisonIso.inv.app ((thickeningFunctor ε).obj A) ≫
        (GeometricThickening.componentComparisonNatIso ε).hom.app A.obj :=
  rfl

/-- The inverse: `β_X⁻¹ = ρ_X⁻¹ ≫ η_(T_ε X).hom`. -/
theorem constructibleThickeningQuotientComparisonIso_inv_app (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) :
    (constructibleThickeningQuotientComparisonIso ε).inv.app A =
      (constructibleThickeningComparisonIso ε).inv.app A ≫
        constructibleCosheafComparisonIso.hom.app ((thickeningFunctor ε).obj A) :=
  rfl

/-- **Canonical hom-component equation**, full-subcategory form: `η_(T_ε X).hom ≫ β_X = ρ_X`. -/
theorem constructibleCosheafComparisonIso_hom_app_comp_constructibleThickeningQuotientComparisonIso_hom_app
    (ε : ℝ≥0) (A : ConstructibleSpaceCat) :
    constructibleCosheafComparisonIso.hom.app ((thickeningFunctor ε).obj A) ≫
        (constructibleThickeningQuotientComparisonIso ε).hom.app A =
      (constructibleThickeningComparisonIso ε).hom.app A := by
  rw [constructibleThickeningQuotientComparisonIso_hom_app, Iso.hom_inv_id_app_assoc]

/-- **Canonical hom-component equation**, unbundled: the comparison `intervalComponentComparison`
of the thickened height, followed by `β_X`, is the first-projection comparison
`componentComparison`. -/
theorem intervalComponentComparison_comp_constructibleThickeningQuotientComparisonIso_hom_app_hom
    (ε : ℝ≥0) (A : ConstructibleSpaceCat) :
    ReebQuotient.intervalComponentComparison
          (GeometricThickening.height (overBaseMap A.obj) ε) ≫
        ((constructibleThickeningQuotientComparisonIso ε).hom.app A).hom =
      GeometricThickening.componentComparison (overBaseMap A.obj) ε :=
  Iso.hom_inv_id_app_assoc constructibleComponentComparisonIso _ _

/-- **Representative formula** `β_X(I) [q (x, t)] = [x]`: the class of the Reeb class of `(x, t)`
in `{q // q̄ q ∈ I}` goes to the class of `x` in `{x // f x ∈ I^ε}`. -/
theorem constructibleThickeningQuotientComparisonIso_hom_app_hom_app_mk (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) (I : OpenInterval)
    (z : {z : A.obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap A.obj) ε z ∈ I}) :
    ((constructibleThickeningQuotientComparisonIso ε).hom.app A).hom.app I
        (ZerothHomotopy.mk (⟨ReebQuotient.mk _ z.1, z.2⟩ :
          {q : ReebQuotient (GeometricThickening.height (overBaseMap A.obj) ε) //
            ReebQuotient.height _ q ∈ I})) =
      ZerothHomotopy.mk (⟨z.1.1, GeometricThickening.fst_mem_thicken z.2⟩ :
        {x : A.obj.left // overBaseMap A.obj x ∈ thicken ε I}) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (intervalComponentComparison_comp_constructibleThickeningQuotientComparisonIso_hom_app_hom
      ε A) I) (ZerothHomotopy.mk z)

/-- **Unit compatibility**: the companion sends `C'` of the zero section followed by the Reeb
projection, `RGraph.constructibleSmoothingUnit ε`, to the lifted smoothing unit. `C'` of the
projection is `η_(T_ε X).hom`, which cancels, and zero-section compatibility remains. -/
theorem constructibleCosheafFunctor_map_constructibleSmoothingUnit_comp (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) :
    constructibleCosheafFunctor.map ((RGraph.constructibleSmoothingUnit ε).app A) ≫
        (constructibleThickeningQuotientComparisonIso ε).hom.app A =
      (constructibleSmoothingUnit ε).app (constructibleCosheafFunctor.obj A) := by
  ext1
  refine Eq.trans (congrArg (· ≫ ((constructibleThickeningQuotientComparisonIso ε).hom.app A).hom)
    (intervalComponentsOver.map_comp ((GeometricThickening.zeroSectionNatTrans ε).app A.obj)
      ((ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor ε).obj A.obj)))) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg
    (intervalComponentsOver.map ((GeometricThickening.zeroSectionNatTrans ε).app A.obj) ≫ ·)
    (Iso.hom_inv_id_app_assoc constructibleComponentComparisonIso
      ((thickeningFunctor ε).obj A)
      ((GeometricThickening.componentComparisonNatIso ε).hom.app A.obj))).trans
    (GeometricThickening.map_zeroSectionNatTrans_comp_componentComparisonNatIso ε A.obj)

/-- Unit compatibility on representatives: `[x] ↦ [q (x, 0)] ↦ [x]`, the smoothing unit. -/
theorem constructibleThickeningQuotientComparisonIso_hom_app_hom_app_unit_mk (ε : ℝ≥0)
    (A : ConstructibleSpaceCat) (I : OpenInterval)
    (x : {x : A.obj.left // overBaseMap A.obj x ∈ I}) :
    ((constructibleThickeningQuotientComparisonIso ε).hom.app A).hom.app I
        ((constructibleCosheafFunctor.map ((RGraph.constructibleSmoothingUnit ε).app A)).hom.app I
          (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (⟨x.1, OpenInterval.le_iff_subset.1 (le_thicken ε I) x.2⟩ :
        {y : A.obj.left // overBaseMap A.obj y ∈ thicken ε I}) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    ((ObjectProperty.ι IsConstructibleCosheaf.{0}).congr_map
      (constructibleCosheafFunctor_map_constructibleSmoothingUnit_comp ε A)) I)
    (ZerothHomotopy.mk x)

/-- **Zero comparison for the companion**: at `ε = 0`, `C''ℛ` of `T_0 ≅ 𝟭` followed by `η_X⁻¹` is
the companion followed by the lifted `S_0 ≅ 𝟭`. -/
theorem cosheafFunctor_map_thickeningFunctorZeroIso_comp_constructibleThickeningQuotientComparisonIso
    (A : ConstructibleSpaceCat) :
    RGraph.cosheafFunctor.map (quotientRGraphFunctor.map (thickeningFunctorZeroIso.hom.app A)) ≫
        constructibleCosheafComparisonIso.inv.app A =
      (constructibleThickeningQuotientComparisonIso 0).hom.app A ≫
        constructibleSmoothingZeroIso.hom.app (constructibleCosheafFunctor.obj A) := by
  rw [constructibleThickeningQuotientComparisonIso_hom_app, Category.assoc,
    ← constructibleCosheafFunctor_map_thickeningFunctorZeroIso_hom_app]
  exact constructibleCosheafComparisonIso.inv.naturality (thickeningFunctorZeroIso.hom.app A)

/-- **Graph objects.** Along the inclusion of graph objects, the companion is DMP Proposition 4.32,
`RGraph.geometricSmoothingComparisonIso`. -/
theorem isoWhiskerLeft_rgraphToConstructible_constructibleThickeningQuotientComparisonIso
    (ε : ℝ≥0) :
    Functor.isoWhiskerLeft RGraph.rgraphToConstructible
        (constructibleThickeningQuotientComparisonIso ε) =
      RGraph.geometricSmoothingComparisonIso ε :=
  Iso.ext rfl

/-- **Graph objects**, componentwise. -/
theorem constructibleThickeningQuotientComparisonIso_hom_app_rgraphToConstructible (ε : ℝ≥0)
    (A : RGraph.RGraphCat) :
    (constructibleThickeningQuotientComparisonIso ε).hom.app
        (RGraph.rgraphToConstructible.obj A) =
      (RGraph.geometricSmoothingComparisonIso ε).hom.app A :=
  rfl

/-! ### Values -/

/-- The comparison at one interval, as an equivalence of values: `C'(T_ε X)(I) ≃ C'(X)(I^ε)`. -/
def constructibleThickeningValueEquiv (ε : ℝ≥0) (A : ConstructibleSpaceCat) (I : OpenInterval) :
    (constructibleCosheafFunctor.obj ((thickeningFunctor ε).obj A)).obj.obj I ≃
      (intervalComponents (overBaseMap A.obj)).obj (thicken ε I) :=
  (((ObjectProperty.ι IsConstructibleCosheaf.{0}).mapIso
    ((constructibleThickeningComparisonIso ε).app A)).app I).toEquiv

theorem constructibleThickeningValueEquiv_apply (ε : ℝ≥0) (A : ConstructibleSpaceCat)
    (I : OpenInterval)
    (c : (constructibleCosheafFunctor.obj ((thickeningFunctor ε).obj A)).obj.obj I) :
    constructibleThickeningValueEquiv ε A I c =
      ((constructibleThickeningComparisonIso ε).hom.app A).hom.app I c :=
  rfl

/-- The companion at one interval, as an equivalence of values: `C''(ℛ T_ε X)(I) ≃ C'(X)(I^ε)`. -/
def constructibleThickeningQuotientValueEquiv (ε : ℝ≥0) (A : ConstructibleSpaceCat)
    (I : OpenInterval) :
    (RGraph.cosheafFunctor.obj ((RGraph.thickeningQuotient ε).obj A)).obj.obj I ≃
      (intervalComponents (overBaseMap A.obj)).obj (thicken ε I) :=
  (((ObjectProperty.ι IsConstructibleCosheaf.{0}).mapIso
    ((constructibleThickeningQuotientComparisonIso ε).app A)).app I).toEquiv

theorem constructibleThickeningQuotientValueEquiv_apply (ε : ℝ≥0) (A : ConstructibleSpaceCat)
    (I : OpenInterval)
    (c : (RGraph.cosheafFunctor.obj ((RGraph.thickeningQuotient ε).obj A)).obj.obj I) :
    constructibleThickeningQuotientValueEquiv ε A I c =
      ((constructibleThickeningQuotientComparisonIso ε).hom.app A).hom.app I c :=
  rfl

end

end TDA.Reeb
