import TDA.Reeb.RGraphThickening
import TDA.Reeb.ConstructibleSmoothing
import TDA.Reeb.InterleavingDistance

/-!
# Geometric smoothing of finite ℝ-graphs

The geometric smoothing `U_ε = ℛ T_ε` of finite ℝ-graphs (de Silva–Munch–Patel, *Categorified
Reeb Graphs*, Definition 4.30) and its canonical comparison with the smoothing of constructible
cosheaves (Proposition 4.32).

## The functor

`geometricSmoothing ε : RGraphCat ⥤ RGraphCat` is `thickeningToConstructible ε ⋙
quotientRGraphFunctor`: the actual product thickening `T_ε`, which is a constructible ℝ-space on
graph input (Proposition 4.26), followed by the Reeb functor on constructible ℝ-spaces. Under the
graph inclusion it is literally `IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙
ReebQuotient.quotientFunctor ℝ`, on objects and on all maps (`geometricSmoothing_comp_ι`, by
`rfl`).

## The comparison

Write `η = constructibleCosheafComparisonIso` for the natural isomorphism `C' ≅ C'' ℛ` on
constructible ℝ-spaces, and `ρ = GeometricThickening.componentComparisonNatIso ε` for the
first-projection comparison `C T_ε ≅ S_ε C` on the real slice. On graph objects, `ρ` lifts
componentwise to `thickeningCosheafComparisonIso ε : thickeningToConstructible ε ⋙
constructibleCosheafFunctor ≅ cosheafFunctor ⋙ constructibleSmoothing ε`. The principal isomorphism

```lean
geometricSmoothingComparisonIso ε :
    geometricSmoothing ε ⋙ cosheafFunctor ≅ cosheafFunctor ⋙ constructibleSmoothing ε
```

has component `β_A = η_(T_ε A).inv ≫ ρ_A.hom` at a graph object `A`
(`geometricSmoothingComparisonIso_hom_app`, by `rfl`). Its naturality is that of the composite of
the two natural isomorphisms, so it holds for every graph map, whatever critical lists present its
source and target.

The canonical hom-component equation `η_(T_ε A).hom ≫ β_A = ρ_A.hom` holds in three forms: in the
full subcategory, for the functor-level `constructibleComponentComparisonIso`
(`constructibleComponentComparisonIso_hom_app_comp_geometricSmoothingComparisonIso_hom_app`), and
for the unbundled `ReebQuotient.intervalComponentComparison` and
`GeometricThickening.componentComparison`. On representatives, `β_A(I)` sends the class of the
Reeb class `q (x, t)` in `{q // q̄ q ∈ I}` to the class of `x` in `{x // f x ∈ I^ε}`
(`geometricSmoothingComparisonIso_hom_app_hom_app_mk`). No map from points of the Reeb quotient
to `X` is asserted.

## The unit

`geometricSmoothingUnit ε : 𝟭 ⟶ geometricSmoothing ε` is the actual zero section `x ↦ (x, 0)`
followed by the actual Reeb projection of the thickening (Observation 4.34). The comparison sends
`C''(ζ)` to the lifted smoothing unit
(`cosheafFunctor_map_geometricSmoothingUnit_comp_geometricSmoothingComparisonIso`, Proposition
4.35): `C''` of the projection is `η`, which cancels, and the unit equation of the first-projection
comparison remains.

## `ε = 0`

`geometricSmoothingZeroIso : geometricSmoothing 0 ≅ 𝟭 RGraphCat` is `ℛ` of
`GeometricThickening.zeroIso` followed by the inverse of `projNatIso`, composed in the real slice
and lifted to graph objects. Through `β` it is compatible with `constructibleSmoothingZeroIso`
(`cosheafFunctor_map_geometricSmoothingZeroIso_hom_app`), and the geometric unit at `ε = 0` is its
inverse (`geometricSmoothingUnit_zero`).

## Underlying precosheaves and distance

`geometricSmoothingPrecosheafIso ε` is the comparison on the underlying interval precosheaves,
and `geometricSmoothingValueEquiv ε A I : C(U_ε A)(I) ≃ C(A)(I^ε)` is its value at one interval.
`U_ε` does not increase the interleaving distance of the underlying precosheaves
(`interleavingDistance_geometricSmoothing_le`); no new distance is defined.

The packaging is in universe `0`, as `RGraphCat` and the real slice are.

See `docs/math/reeb-rgraph-smoothing.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace RGraph

open OpenInterval

/-! ### The functor -/

/-- **Geometric smoothing of graph objects** `U_ε = ℛ T_ε` (DMP Definition 4.30): the actual
product thickening, lifted to constructible ℝ-spaces by `thickeningToConstructible`, followed by
the Reeb functor `quotientRGraphFunctor` on constructible ℝ-spaces. -/
def geometricSmoothing (ε : ℝ≥0) : RGraphCat ⥤ RGraphCat :=
  thickeningToConstructible ε ⋙ quotientRGraphFunctor

/-- Under the graph inclusion, `U_ε` is literally the Reeb quotient functor of the actual product
thickening, on objects and on all maps. -/
theorem geometricSmoothing_comp_ι (ε : ℝ≥0) :
    geometricSmoothing ε ⋙ IsRGraph.ι =
      IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ :=
  rfl

theorem geometricSmoothing_obj_obj (ε : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothing ε).obj A).obj =
      (ReebQuotient.quotientFunctor ℝ).obj ((GeometricThickening.functor ε).obj A.obj) :=
  rfl

theorem geometricSmoothing_map_hom (ε : ℝ≥0) {A B : RGraphCat} (φ : A ⟶ B) :
    ((geometricSmoothing ε).map φ).hom =
      (ReebQuotient.quotientFunctor ℝ).map ((GeometricThickening.functor ε).map φ.hom) :=
  rfl

/-- The underlying precosheaves of `C'' U_ε`: interval components of the Reeb quotient of the
actual thickening. -/
theorem geometricSmoothing_comp_cosheafFunctor_comp_ι (ε : ℝ≥0) :
    geometricSmoothing ε ⋙ cosheafFunctor ⋙ ObjectProperty.ι IsConstructibleCosheaf.{0} =
      IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ ⋙
        intervalComponentsOver :=
  rfl

/-! ### The comparison (DMP Proposition 4.32) -/

/-- The first-projection comparison on graph objects, lifted to constructible cosheaves:
`C' T_ε ≅ S_ε C''`, the second isomorphism in the proof of DMP Proposition 4.32. Its components
are those of `GeometricThickening.componentComparisonNatIso ε`. -/
def thickeningCosheafComparisonIso (ε : ℝ≥0) :
    thickeningToConstructible ε ⋙ constructibleCosheafFunctor ≅
      cosheafFunctor ⋙ constructibleSmoothing ε :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ ((GeometricThickening.componentComparisonNatIso ε).app A.obj))
    (fun φ => by
      ext1
      exact (GeometricThickening.componentComparisonNatIso ε).hom.naturality φ.hom)

theorem thickeningCosheafComparisonIso_hom_app_hom (ε : ℝ≥0) (A : RGraphCat) :
    ((thickeningCosheafComparisonIso ε).hom.app A).hom =
      (GeometricThickening.componentComparisonNatIso ε).hom.app A.obj :=
  rfl

/-- **DMP Proposition 4.32** on graph objects: `C'' U_ε ≅ S_ε C''`, as a natural isomorphism of
functors `RGraphCat ⥤ ConstructibleCosheafCat.{0}`. The component at `A` is the inverse of the
comparison `η = constructibleCosheafComparisonIso` at the actual thickening `T_ε A`, followed by
the first-projection comparison `ρ_A`; naturality is that of the composite of the two actual
natural isomorphisms. -/
def geometricSmoothingComparisonIso (ε : ℝ≥0) :
    geometricSmoothing ε ⋙ cosheafFunctor ≅ cosheafFunctor ⋙ constructibleSmoothing ε :=
  NatIso.ofComponents
    (fun A => (constructibleCosheafComparisonIso.app ((thickeningToConstructible ε).obj A)).symm ≪≫
      (thickeningCosheafComparisonIso ε).app A)
    (fun φ => (Functor.isoWhiskerLeft (thickeningToConstructible ε)
      constructibleCosheafComparisonIso.symm ≪≫ thickeningCosheafComparisonIso ε).hom.naturality φ)

/-- `β_A = η_(T_ε A).inv ≫ ρ_A.hom`, in the full subcategory. -/
theorem geometricSmoothingComparisonIso_hom_app (ε : ℝ≥0) (A : RGraphCat) :
    (geometricSmoothingComparisonIso ε).hom.app A =
      constructibleCosheafComparisonIso.inv.app ((thickeningToConstructible ε).obj A) ≫
        (thickeningCosheafComparisonIso ε).hom.app A :=
  rfl

/-- `β_A = η_(T_ε A).inv ≫ ρ_A.hom`, on the underlying interval precosheaves. -/
theorem geometricSmoothingComparisonIso_hom_app_hom (ε : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingComparisonIso ε).hom.app A).hom =
      constructibleComponentComparisonIso.inv.app ((thickeningToConstructible ε).obj A) ≫
        (GeometricThickening.componentComparisonNatIso ε).hom.app A.obj :=
  rfl

/-- **Canonical hom-component equation**, full-subcategory form: `η_(T_ε A).hom ≫ β_A = ρ_A`. -/
theorem constructibleCosheafComparisonIso_hom_app_comp_geometricSmoothingComparisonIso_hom_app
    (ε : ℝ≥0) (A : RGraphCat) :
    constructibleCosheafComparisonIso.hom.app ((thickeningToConstructible ε).obj A) ≫
        (geometricSmoothingComparisonIso ε).hom.app A =
      (thickeningCosheafComparisonIso ε).hom.app A := by
  rw [geometricSmoothingComparisonIso_hom_app, Iso.hom_inv_id_app_assoc]

/-- **Canonical hom-component equation** `η_(T_ε A).hom ≫ β_A = ρ_A.hom`, with `η` the
functor-level comparison `constructibleComponentComparisonIso` at the actual thickening and `ρ`
the first-projection comparison `GeometricThickening.componentComparisonNatIso`. -/
theorem constructibleComponentComparisonIso_hom_app_comp_geometricSmoothingComparisonIso_hom_app
    (ε : ℝ≥0) (A : RGraphCat) :
    constructibleComponentComparisonIso.hom.app ((thickeningToConstructible ε).obj A) ≫
        ((geometricSmoothingComparisonIso ε).hom.app A).hom =
      (GeometricThickening.componentComparisonNatIso ε).hom.app A.obj :=
  Iso.hom_inv_id_app_assoc constructibleComponentComparisonIso _ _

/-- **Canonical hom-component equation**, unbundled: the actual comparison
`intervalComponentComparison` of the thickened height, followed by `β_A`, is the actual
first-projection comparison `componentComparison`. -/
theorem intervalComponentComparison_comp_geometricSmoothingComparisonIso_hom_app_hom
    (ε : ℝ≥0) (A : RGraphCat) :
    ReebQuotient.intervalComponentComparison
          (GeometricThickening.height (overBaseMap A.obj) ε) ≫
        ((geometricSmoothingComparisonIso ε).hom.app A).hom =
      GeometricThickening.componentComparison (overBaseMap A.obj) ε :=
  constructibleComponentComparisonIso_hom_app_comp_geometricSmoothingComparisonIso_hom_app ε A

/-- **Representative formula** `β_A(I) [q (x, t)] = [x]`: the class of the Reeb class of `(x, t)`
in `{q // q̄ q ∈ I}` goes to the class of `x` in `{x // f x ∈ I^ε}`. -/
theorem geometricSmoothingComparisonIso_hom_app_hom_app_mk (ε : ℝ≥0) (A : RGraphCat)
    (I : OpenInterval)
    (z : {z : A.obj.left × GeometricThickening.Band ε //
      GeometricThickening.height (overBaseMap A.obj) ε z ∈ I}) :
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app I
        (ZerothHomotopy.mk (⟨ReebQuotient.mk _ z.1, z.2⟩ :
          {q : ReebQuotient (GeometricThickening.height (overBaseMap A.obj) ε) //
            ReebQuotient.height _ q ∈ I})) =
      ZerothHomotopy.mk (⟨z.1.1, GeometricThickening.fst_mem_thicken z.2⟩ :
        {x : A.obj.left // overBaseMap A.obj x ∈ thicken ε I}) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (intervalComponentComparison_comp_geometricSmoothingComparisonIso_hom_app_hom ε A) I)
    (ZerothHomotopy.mk z)

/-! ### The geometric unit (DMP Observation 4.34 and Proposition 4.35) -/

/-- **The geometric unit** `ζ^ε : 𝟭 ⟶ U_ε`: the actual zero section `x ↦ (x, 0)` followed by the
actual Reeb projection of the thickening. -/
def geometricSmoothingUnit (ε : ℝ≥0) : 𝟭 RGraphCat ⟶ geometricSmoothing ε where
  app A := ObjectProperty.homMk ((GeometricThickening.zeroSectionNatTrans ε).app A.obj ≫
    (ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor ε).obj A.obj))
  naturality _ _ φ := by
    ext1
    exact (GeometricThickening.zeroSectionNatTrans ε ≫
      Functor.whiskerLeft (GeometricThickening.functor ε) (ReebQuotient.projNatTrans ℝ)).naturality
        φ.hom

theorem geometricSmoothingUnit_app_hom (ε : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingUnit ε).app A).hom =
      (GeometricThickening.zeroSectionNatTrans ε).app A.obj ≫
        (ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor ε).obj A.obj) :=
  rfl

/-- On points: `ζ (x) = q (x, 0)`. -/
theorem geometricSmoothingUnit_app_hom_left_apply (ε : ℝ≥0) (A : RGraphCat) (x : A.obj.left) :
    ((geometricSmoothingUnit ε).app A).hom.left.hom x =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) ε)
        (GeometricThickening.zeroSection A.obj.left ε x) :=
  rfl

/-- **Unit compatibility** (DMP Proposition 4.35): the comparison sends `C''(ζ)` to the lifted
smoothing unit. `C''(ζ) = C(τ) ≫ η_(T_ε A)`, so `η` cancels and the unit equation
`GeometricThickening.map_zeroSectionNatTrans_comp_componentComparisonNatIso` remains. -/
theorem cosheafFunctor_map_geometricSmoothingUnit_comp_geometricSmoothingComparisonIso
    (ε : ℝ≥0) (A : RGraphCat) :
    cosheafFunctor.map ((geometricSmoothingUnit ε).app A) ≫
        (geometricSmoothingComparisonIso ε).hom.app A =
      (constructibleSmoothingUnit ε).app (cosheafFunctor.obj A) := by
  ext1
  refine Eq.trans (congrArg (· ≫ ((geometricSmoothingComparisonIso ε).hom.app A).hom)
    (intervalComponentsOver.map_comp ((GeometricThickening.zeroSectionNatTrans ε).app A.obj)
      ((ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor ε).obj A.obj)))) ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (congrArg
    (intervalComponentsOver.map ((GeometricThickening.zeroSectionNatTrans ε).app A.obj) ≫ ·)
    (Iso.hom_inv_id_app_assoc constructibleComponentComparisonIso
      ((thickeningToConstructible ε).obj A)
      ((GeometricThickening.componentComparisonNatIso ε).hom.app A.obj))).trans
    (GeometricThickening.map_zeroSectionNatTrans_comp_componentComparisonNatIso ε A.obj)

/-- Unit compatibility on the underlying precosheaves. -/
theorem intervalComponentsOver_map_geometricSmoothingUnit_comp (ε : ℝ≥0) (A : RGraphCat) :
    intervalComponentsOver.map ((geometricSmoothingUnit ε).app A).hom ≫
        ((geometricSmoothingComparisonIso ε).hom.app A).hom =
      (smoothingUnit ε).app (intervalComponentsOver.obj A.obj) :=
  (ObjectProperty.ι IsConstructibleCosheaf.{0}).congr_map
    (cosheafFunctor_map_geometricSmoothingUnit_comp_geometricSmoothingComparisonIso ε A)

/-- Unit compatibility on representatives: `[x] ↦ [q (x, 0)] ↦ [x]`, the smoothing unit. -/
theorem geometricSmoothingComparisonIso_hom_app_hom_app_unit_mk (ε : ℝ≥0) (A : RGraphCat)
    (I : OpenInterval) (x : {x : A.obj.left // overBaseMap A.obj x ∈ I}) :
    ((geometricSmoothingComparisonIso ε).hom.app A).hom.app I
        ((cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom.app I (ZerothHomotopy.mk x)) =
      ZerothHomotopy.mk (⟨x.1, OpenInterval.le_iff_subset.1 (le_thicken ε I) x.2⟩ :
        {y : A.obj.left // overBaseMap A.obj y ∈ thicken ε I}) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (intervalComponentsOver_map_geometricSmoothingUnit_comp ε A) I) (ZerothHomotopy.mk x)

/-! ### `ε = 0` -/

/-- **`U_0 ≅ 𝟭` on graph objects**: `ℛ` of the merged `GeometricThickening.zeroIso`, followed by the
inverse of the merged projection isomorphism `projNatIso`, composed in the real slice and lifted
through the full subcategory. (On an arbitrary space the quotient at `0` is `ℛ`, not `𝟭`.) -/
def geometricSmoothingZeroIso : geometricSmoothing 0 ≅ 𝟭 RGraphCat :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _
      ((ReebQuotient.quotientFunctor ℝ).mapIso (GeometricThickening.zeroIso.app A.obj) ≪≫
        (projNatIso.app A).symm))
    (fun φ => by
      ext1
      exact (Functor.isoWhiskerLeft IsRGraph.ι
        (Functor.isoWhiskerRight GeometricThickening.zeroIso (ReebQuotient.quotientFunctor ℝ)) ≪≫
          projNatIso.symm).hom.naturality φ)

theorem geometricSmoothingZeroIso_hom_app_hom (A : RGraphCat) :
    (geometricSmoothingZeroIso.hom.app A).hom =
      (ReebQuotient.quotientFunctor ℝ).map (GeometricThickening.zeroIso.hom.app A.obj) ≫
        projNatIso.inv.app A :=
  rfl

/-- The projection of `T_0 A` followed by `U_0 ≅ 𝟭` is the merged `zeroIso`. -/
theorem projNatTrans_app_comp_geometricSmoothingZeroIso_hom_app_hom (A : RGraphCat) :
    (ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor 0).obj A.obj) ≫
        (geometricSmoothingZeroIso.hom.app A).hom =
      GeometricThickening.zeroIso.hom.app A.obj := by
  have hp : (ReebQuotient.projNatTrans ℝ).app ((𝟭 (Over (TopCat.of ℝ))).obj A.obj) ≫
      projNatIso.inv.app A = 𝟙 _ :=
    projNatIso.hom_inv_id_app A
  rw [geometricSmoothingZeroIso_hom_app_hom, ← Category.assoc,
    ← (ReebQuotient.projNatTrans ℝ).naturality, Category.assoc, hp, Category.comp_id]
  rfl

/-- **Zero comparison**: at `ε = 0`, `C''` of `U_0 ≅ 𝟭` is the comparison followed by the lifted
`S_0 ≅ 𝟭`. After cancelling `η_(T_0 A)` this is `GeometricThickening.map_zeroIso_hom_app`. -/
theorem cosheafFunctor_map_geometricSmoothingZeroIso_hom_app (A : RGraphCat) :
    cosheafFunctor.map (geometricSmoothingZeroIso.hom.app A) =
      (geometricSmoothingComparisonIso 0).hom.app A ≫
        constructibleSmoothingZeroIso.hom.app (cosheafFunctor.obj A) := by
  ext1
  apply (cancel_epi
    (constructibleComponentComparisonIso.hom.app ((thickeningToConstructible 0).obj A))).1
  refine ((intervalComponentsOver.map_comp
    ((ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor 0).obj A.obj))
    (geometricSmoothingZeroIso.hom.app A).hom).symm.trans
      ((congrArg intervalComponentsOver.map
        (projNatTrans_app_comp_geometricSmoothingZeroIso_hom_app_hom A)).trans
        (GeometricThickening.map_zeroIso_hom_app A.obj))).trans ?_
  refine (Iso.hom_inv_id_app_assoc constructibleComponentComparisonIso
    ((thickeningToConstructible 0).obj A) _).symm.trans ?_
  exact congrArg
    (constructibleComponentComparisonIso.hom.app ((thickeningToConstructible 0).obj A) ≫ ·)
    (Category.assoc _ _ _).symm

/-- At `ε = 0` the geometric unit is the inverse of `U_0 ≅ 𝟭` (an additive coherence check, the
geometric counterpart of the merged `constructibleSmoothingUnit_zero`). -/
theorem geometricSmoothingUnit_zero : geometricSmoothingUnit 0 = geometricSmoothingZeroIso.inv := by
  have h : geometricSmoothingUnit 0 ≫ geometricSmoothingZeroIso.hom = 𝟙 _ := by
    ext A : 2
    apply ObjectProperty.hom_ext
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((GeometricThickening.zeroSectionNatTrans 0).app A.obj ≫ ·)
      (projNatTrans_app_comp_geometricSmoothingZeroIso_hom_app_hom A)).trans ?_
    rw [← GeometricThickening.zeroIso_inv]
    exact GeometricThickening.zeroIso.inv_hom_id_app A.obj
  rw [← Category.id_comp geometricSmoothingZeroIso.inv, ← h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-! ### Underlying precosheaves, values and the contraction corollary -/

/-- The underlying natural isomorphism of interval precosheaves on graph objects. -/
def geometricSmoothingPrecosheafIso (ε : ℝ≥0) :
    IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ ⋙
        intervalComponentsOver ≅
      IsRGraph.ι ⋙ intervalComponentsOver ⋙ smoothing ε :=
  Functor.isoWhiskerRight (geometricSmoothingComparisonIso ε)
    (ObjectProperty.ι IsConstructibleCosheaf.{0})

theorem geometricSmoothingPrecosheafIso_hom_app (ε : ℝ≥0) (A : RGraphCat) :
    (geometricSmoothingPrecosheafIso ε).hom.app A =
      ((geometricSmoothingComparisonIso ε).hom.app A).hom :=
  rfl

/-- The comparison at one interval, as an equivalence of values: `C(U_ε A)(I) ≃ C(A)(I^ε)`. -/
def geometricSmoothingValueEquiv (ε : ℝ≥0) (A : RGraphCat) (I : OpenInterval) :
    (cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj.obj I ≃
      (intervalComponents (overBaseMap A.obj)).obj (thicken ε I) :=
  (((geometricSmoothingPrecosheafIso ε).app A).app I).toEquiv

theorem geometricSmoothingValueEquiv_apply (ε : ℝ≥0) (A : RGraphCat) (I : OpenInterval)
    (c : (cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj.obj I) :
    geometricSmoothingValueEquiv ε A I c =
      ((geometricSmoothingComparisonIso ε).hom.app A).hom.app I c :=
  rfl

/-- **Contraction corollary** for the merged cosheaf interleaving distance:
`d(C(U_ε A), C(U_ε B)) ≤ d(C A, C B)`, from the comparison, `interleavingDistance_congr` and
`interleavingDistance_smoothing_le`. No new distance is defined. -/
theorem interleavingDistance_geometricSmoothing_le (ε : ℝ≥0) (A B : RGraphCat) :
    interleavingDistance (cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj
        (cosheafFunctor.obj ((geometricSmoothing ε).obj B)).obj ≤
      interleavingDistance (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj :=
  (interleavingDistance_congr ((geometricSmoothingPrecosheafIso ε).app A)
    ((geometricSmoothingPrecosheafIso ε).app B)).le.trans (interleavingDistance_smoothing_le ε _ _)

end RGraph

end

end TDA.Reeb
