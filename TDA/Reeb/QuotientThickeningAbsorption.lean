import TDA.Reeb.QuotientThickeningAddition
import TDA.Reeb.ConstructibleComparison

/-!
# Absorption of the Reeb quotient and the geometric smoothing semigroup

Write `q_X : X ⟶ ℛ X` for the Reeb projection on the real slice and `U_ε = ℛ T_ε` for the merged
geometric smoothing of graph objects. The **absorption morphism**

```
ℛ (T_ε q_X) : ℛ T_ε X ⟶ ℛ T_ε ℛ X,     [(x, t)] ↦ [([x], t)],
```

is an isomorphism whenever `X` is a constructible ℝ-space and `ℛ T_ε X` is a graph object
(`isIso_quotientFunctor_map_functor_map_projNatTrans_app`). The case used below is `X = T_δ A` for
a graph object `A`, which is constructible but need not be a graph object: there `q_X` itself need
not be an isomorphism (it is not on `T_(1/4)` of a single edge), so the merged `projNatIso` does not
apply.

## The route

No point-set inverse is constructed. Interval components `Φ = intervalComponentsOver` send the
absorption morphism to an isomorphism:

* `Φ q_X` is the comparison `κ_X` (`intervalComponentsOver_map_projNatTrans_app`), an isomorphism
  on constructible `X`, so `Φ (T_ε q_X)` is one through the first-projection comparison
  `componentComparisonNatIso` (`isIso_map_functor_map_projNatTrans_app`);
* `κ` at `T_ε X` is surjective (merged) and injective, because `κ_(T_ε X) ≫ Φ (ℛ T_ε q_X)` equals
  the isomorphism `Φ (T_ε q_X) ≫ κ_(T_ε ℛ X)`
  (`isIso_intervalComponentComparison_thickening`), so `Φ (ℛ T_ε q_X)` is an isomorphism
  (`isIso_map_quotientFunctor_map_functor_map_projNatTrans_app`).

Both ends of the absorption morphism are graph objects, and the merged component functor
`cosheafFunctor` on graph objects is fully faithful, so it reflects the isomorphism. Only full
faithfulness is used, not essential surjectivity. The inverse sends `[([x], t)]` to `[(x, t)]`
(`absorption_inv_mk`).

## The semigroup

On graph objects absorption gives `geometricSmoothingAbsorptionIso ε δ : ℛ T_ε T_δ ≅ U_ε U_δ`.
Composed with the merged `geometricSmoothingAddIso ε δ : ℛ T_ε T_δ ≅ U_(ε+δ)` it gives the
semigroup isomorphism `geometricSmoothingCompIso ε δ : U_ε U_δ ≅ U_(ε+δ)`, sending
`[([(x, s)], t)]` to `[(x, s + t)]`. It is associative and unital against the merged
`geometricSmoothingZeroIso`, with parameter equalities bridged by `geometricSmoothingEqIso`
(band inclusions, never casts), and it is compatible with the precosheaf semigroup
`smoothingCompIso` through the merged comparison `geometricSmoothingComparisonIso`
(`cosheafFunctor_map_geometricSmoothingCompIso_hom_app`).

Everything is in universe `0`, the universe of the real slice and of `RGraphCat`.

See `docs/math/reeb-quotient-thickening-absorption.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

namespace RGraph

open OpenInterval

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

/-! ### Interval components of the thickened projection -/

/-- **`π₀` of the Reeb projection is the comparison**: `Φ q_X = κ_X`. -/
theorem intervalComponentsOver_map_projNatTrans_app (X : Over (TopCat.of ℝ)) :
    intervalComponentsOver.map ((ReebQuotient.projNatTrans ℝ).app X) =
      ReebQuotient.intervalComponentComparison (overBaseMap X) :=
  rfl

/-- On a constructible `X`, interval components of the thickened projection `T_ε q_X` form an
isomorphism, through the first-projection comparison. -/
theorem isIso_map_functor_map_projNatTrans_app {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    IsIso (intervalComponentsOver.map
      ((GeometricThickening.functor ε).map ((ReebQuotient.projNatTrans ℝ).app X))) := by
  have : IsIso (intervalComponentsOver.map ((ReebQuotient.projNatTrans ℝ).app X)) := by
    rw [intervalComponentsOver_map_projNatTrans_app]
    exact isIso_intervalComponentComparison_of_constructible hX
  have : IsIso ((smoothing ε).map
      (intervalComponentsOver.map ((ReebQuotient.projNatTrans ℝ).app X))) :=
    Functor.map_isIso (smoothing ε) _
  have h : IsIso ((GeometricThickening.componentComparisonNatIso ε).hom.app X ≫
      (smoothing ε).map (intervalComponentsOver.map ((ReebQuotient.projNatTrans ℝ).app X)) ≫
        (GeometricThickening.componentComparisonNatIso ε).inv.app ((ℛ).obj X)) :=
    inferInstance
  change IsIso ((GeometricThickening.functor ε ⋙ intervalComponentsOver).map
    ((ReebQuotient.projNatTrans ℝ).app X))
  rw [← NatIso.naturality_2 (GeometricThickening.componentComparisonNatIso ε)]
  exact h

/-- **The comparison at `T_ε X`.** For constructible `X`, `κ` is an isomorphism at the thickening
`T_ε X`, without using constructibility of `T_ε X`: it is surjective at every interval, and
injective because `κ_(T_ε X) ≫ Φ (ℛ T_ε q_X)` is an isomorphism. -/
theorem isIso_intervalComponentComparison_thickening {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    IsIso (ReebQuotient.intervalComponentComparison
      (overBaseMap ((GeometricThickening.functor ε).obj X))) := by
  let g := (GeometricThickening.functor ε).map ((ReebQuotient.projNatTrans ℝ).app X)
  have := isIso_map_functor_map_projNatTrans_app hX ε
  have : IsIso (ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj ((ℛ).obj X))) :=
    isIso_intervalComponentComparison_of_constructible
      (isConstructibleSpace_thickening (isRGraph_quotient_of_isConstructibleSpace hX) ε)
  have hsq : intervalComponentsOver.map g ≫ ReebQuotient.intervalComponentComparisonOver.app
        ((GeometricThickening.functor ε).obj ((ℛ).obj X)) =
      ReebQuotient.intervalComponentComparisonOver.app ((GeometricThickening.functor ε).obj X) ≫
        (ReebQuotient.quotientFunctor ℝ ⋙ intervalComponentsOver).map g :=
    ReebQuotient.intervalComponentComparisonOver.naturality g
  have hc : IsIso (ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj X) ≫ intervalComponentsOver.map ((ℛ).map g)) := by
    change IsIso (ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj X) ≫
        (ReebQuotient.quotientFunctor ℝ ⋙ intervalComponentsOver).map g)
    rw [← hsq]
    infer_instance
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun I => ?_
  refine (isIso_iff_bijective _).2 ⟨?_, ReebQuotient.intervalComponentComparison_app_surjective _ I⟩
  have hI : IsIso ((ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj X) ≫ intervalComponentsOver.map ((ℛ).map g)).app I) :=
    inferInstance
  exact Function.Injective.of_comp ((isIso_iff_bijective _).1 hI).1

/-- `Φ (ℛ T_ε q_X)` is an isomorphism on constructible `X`. -/
theorem isIso_map_quotientFunctor_map_functor_map_projNatTrans_app {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0) :
    IsIso (intervalComponentsOver.map ((ℛ).map
      ((GeometricThickening.functor ε).map ((ReebQuotient.projNatTrans ℝ).app X)))) := by
  let g := (GeometricThickening.functor ε).map ((ReebQuotient.projNatTrans ℝ).app X)
  have := isIso_map_functor_map_projNatTrans_app hX ε
  have : IsIso (ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj ((ℛ).obj X))) :=
    isIso_intervalComponentComparison_of_constructible
      (isConstructibleSpace_thickening (isRGraph_quotient_of_isConstructibleSpace hX) ε)
  have : IsIso (ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj X)) :=
    isIso_intervalComponentComparison_thickening hX ε
  have hc : IsIso (ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj X) ≫ intervalComponentsOver.map ((ℛ).map g)) := by
    change IsIso (ReebQuotient.intervalComponentComparisonOver.app
      ((GeometricThickening.functor ε).obj X) ≫
        (ReebQuotient.quotientFunctor ℝ ⋙ intervalComponentsOver).map g)
    have hsq : intervalComponentsOver.map g ≫ ReebQuotient.intervalComponentComparisonOver.app
          ((GeometricThickening.functor ε).obj ((ℛ).obj X)) =
        ReebQuotient.intervalComponentComparisonOver.app ((GeometricThickening.functor ε).obj X) ≫
          (ReebQuotient.quotientFunctor ℝ ⋙ intervalComponentsOver).map g :=
      ReebQuotient.intervalComponentComparisonOver.naturality g
    rw [← hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left (ReebQuotient.intervalComponentComparisonOver.app
    ((GeometricThickening.functor ε).obj X)) (intervalComponentsOver.map ((ℛ).map g))

/-! ### Absorption -/

/-- **Absorption.** For a constructible `X` such that `ℛ T_ε X` is a graph object, the absorption
morphism `ℛ (T_ε q_X) : ℛ T_ε X ⟶ ℛ T_ε ℛ X` is an isomorphism. Both ends are graph objects, and
the isomorphism `Φ (ℛ T_ε q_X)` is reflected by the fully faithful `cosheafFunctor`. -/
theorem isIso_quotientFunctor_map_functor_map_projNatTrans_app {X : Over (TopCat.of ℝ)}
    (hX : IsConstructibleSpace X) (ε : ℝ≥0)
    (hT : IsRGraph ((ℛ).obj ((GeometricThickening.functor ε).obj X))) :
    IsIso ((ℛ).map
      ((GeometricThickening.functor ε).map ((ReebQuotient.projNatTrans ℝ).app X))) := by
  let s : RGraphCat := ⟨(ℛ).obj ((GeometricThickening.functor ε).obj X), hT⟩
  let t : RGraphCat := ⟨(ℛ).obj ((GeometricThickening.functor ε).obj ((ℛ).obj X)),
    isRGraph_quotient_of_isConstructibleSpace
      (isConstructibleSpace_thickening (isRGraph_quotient_of_isConstructibleSpace hX) ε)⟩
  let G : s ⟶ t := ObjectProperty.homMk
    ((ℛ).map ((GeometricThickening.functor ε).map ((ReebQuotient.projNatTrans ℝ).app X)))
  have : IsIso ((ObjectProperty.ι IsConstructibleCosheaf.{0}).map (cosheafFunctor.map G)) :=
    isIso_map_quotientFunctor_map_functor_map_projNatTrans_app hX ε
  have : IsIso (cosheafFunctor.map G) :=
    (ObjectProperty.fullyFaithfulι IsConstructibleCosheaf.{0}).isIso_of_isIso_map _
  have : IsIso G := cosheafFullyFaithful.isIso_of_isIso_map G
  exact (inferInstance : IsIso (IsRGraph.ι.map G))

/-- **The inverse of absorption** sends `[([x], t)]` to `[(x, t)]`. -/
theorem absorption_inv_mk {X : Over (TopCat.of ℝ)} (hX : IsConstructibleSpace X) (ε : ℝ≥0)
    (hT : IsRGraph ((ℛ).obj ((GeometricThickening.functor ε).obj X))) (x : X.left)
    (t : GeometricThickening.Band ε) :
    haveI := isIso_quotientFunctor_map_functor_map_projNatTrans_app hX ε hT
    (inv ((ℛ).map ((GeometricThickening.functor ε).map
        ((ReebQuotient.projNatTrans ℝ).app X)))).left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap ((ℛ).obj X)) ε)
          (ReebQuotient.mk (overBaseMap X) x, t)) =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap X) ε) (x, t) := by
  have := isIso_quotientFunctor_map_functor_map_projNatTrans_app hX ε hT
  exact congrArg (fun φ => φ.left.hom
    (ReebQuotient.mk (GeometricThickening.height (overBaseMap X) ε) (x, t)))
    (IsIso.hom_inv_id ((ℛ).map ((GeometricThickening.functor ε).map
      ((ReebQuotient.projNatTrans ℝ).app X))))

/-- **Graph-object control.** On a graph object `A` the hypotheses of absorption hold, and the
absorption morphism is an isomorphism. -/
instance isIso_quotientFunctor_map_functor_map_projNatTrans_app_rgraph (A : RGraphCat)
    (ε : ℝ≥0) :
    IsIso ((ℛ).map ((GeometricThickening.functor ε).map
      ((ReebQuotient.projNatTrans ℝ).app A.obj))) :=
  isIso_quotientFunctor_map_functor_map_projNatTrans_app
    (isConstructibleSpace_of_isRGraph A.property) ε
    (isRGraph_quotient_of_isConstructibleSpace (isConstructibleSpace_thickening A.property ε))

/-- On a graph object the inverse of absorption is `ℛ T_ε` of the inverse of `projNatIso`. -/
theorem inv_quotientFunctor_map_functor_map_projNatTrans_app_of_isRGraph (A : RGraphCat)
    (ε : ℝ≥0) :
    inv ((ℛ).map ((GeometricThickening.functor ε).map
        ((ReebQuotient.projNatTrans ℝ).app A.obj))) =
      (ℛ).map ((GeometricThickening.functor ε).map (projNatIso.inv.app A)) := by
  refine IsIso.inv_eq_of_hom_inv_id ?_
  have hp : (ReebQuotient.projNatTrans ℝ).app A.obj ≫ projNatIso.inv.app A = 𝟙 _ :=
    projNatIso.hom_inv_id_app A
  rw [← Functor.map_comp, ← Functor.map_comp, hp, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- Absorption at the thickening `T_δ A` of a graph object `A`: (H1) is
`isConstructibleSpace_thickening` and (H2) is `isRGraph_quotient_thickening_thickening`. -/
instance isIso_quotientFunctor_map_functor_map_projNatTrans_app_thickening (A : RGraphCat)
    (ε δ : ℝ≥0) :
    IsIso ((ℛ).map ((GeometricThickening.functor ε).map
      ((ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor δ).obj A.obj)))) :=
  isIso_quotientFunctor_map_functor_map_projNatTrans_app
    (isConstructibleSpace_thickening A.property δ) ε
    (isRGraph_quotient_thickening_thickening A.property ε δ)

/-! ### Absorption on graph objects -/

/-- **Absorption on graph objects**, `ℛ T_ε T_δ ≅ U_ε U_δ`, with components `ℛ (T_ε q_(T_δ A))`. -/
def geometricSmoothingAbsorptionIso (ε δ : ℝ≥0) :
    doubleThickeningQuotient ε δ ≅ geometricSmoothing δ ⋙ geometricSmoothing ε :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _
      (@asIso _ _ _ _ ((ℛ).map ((GeometricThickening.functor ε).map
        ((ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor δ).obj A.obj))))
        (isIso_quotientFunctor_map_functor_map_projNatTrans_app_thickening A ε δ)))
    (fun φ => by
      ext1
      exact (Functor.whiskerRight (Functor.whiskerRight (ReebQuotient.projNatTrans ℝ)
        (GeometricThickening.functor ε)) ℛ).naturality ((GeometricThickening.functor δ).map φ.hom))

theorem geometricSmoothingAbsorptionIso_hom_app_hom (ε δ : ℝ≥0) (A : RGraphCat) :
    ((geometricSmoothingAbsorptionIso ε δ).hom.app A).hom =
      (ℛ).map ((GeometricThickening.functor ε).map
        ((ReebQuotient.projNatTrans ℝ).app ((GeometricThickening.functor δ).obj A.obj))) :=
  rfl

/-- The inverse of absorption on graph objects sends `[([z], t)]` to `[(z, t)]`. -/
theorem geometricSmoothingAbsorptionIso_inv_app_hom_left_mk (ε δ : ℝ≥0) (A : RGraphCat)
    (z : A.obj.left × GeometricThickening.Band δ) (t : GeometricThickening.Band ε) :
    ((geometricSmoothingAbsorptionIso ε δ).inv.app A).hom.left.hom
        (ReebQuotient.mk _ (ReebQuotient.mk
          (GeometricThickening.height (overBaseMap A.obj) δ) z, t)) =
      ReebQuotient.mk _ (z, t) :=
  absorption_inv_mk (isConstructibleSpace_thickening A.property δ) ε
    (isRGraph_quotient_thickening_thickening A.property ε δ) z t

/-! ### The semigroup -/

/-- **The geometric smoothing semigroup** `U_ε U_δ ≅ U_(ε+δ)` on graph objects (DMP
Observation 4.33, first bullet; proved here independently): the inverse of absorption followed by
the merged `geometricSmoothingAddIso`. -/
def geometricSmoothingCompIso (ε δ : ℝ≥0) :
    geometricSmoothing δ ⋙ geometricSmoothing ε ≅ geometricSmoothing (ε + δ) :=
  (geometricSmoothingAbsorptionIso ε δ).symm ≪≫ geometricSmoothingAddIso ε δ

/-- `[([(x, s)], t)] ↦ [(x, s + t)]`. -/
theorem geometricSmoothingCompIso_hom_app_hom_left_mk (ε δ : ℝ≥0) (A : RGraphCat)
    (z : A.obj.left × GeometricThickening.Band δ) (t : GeometricThickening.Band ε) :
    ((geometricSmoothingCompIso ε δ).hom.app A).hom.left.hom
        (ReebQuotient.mk _ (ReebQuotient.mk
          (GeometricThickening.height (overBaseMap A.obj) δ) z, t)) =
      ReebQuotient.mk _ (GeometricThickening.addMap A.obj.left ε δ (z, t)) := by
  change ((geometricSmoothingAddIso ε δ).hom.app A).hom.left.hom
      (((geometricSmoothingAbsorptionIso ε δ).inv.app A).hom.left.hom
        (ReebQuotient.mk _ (ReebQuotient.mk
          (GeometricThickening.height (overBaseMap A.obj) δ) z, t))) = _
  rw [geometricSmoothingAbsorptionIso_inv_app_hom_left_mk]
  rfl

/-- The inverse sends `[w]` to `[([σ w].1, (σ w).2)]` with `σ = addSection`. -/
theorem geometricSmoothingCompIso_inv_app_hom_left_mk (ε δ : ℝ≥0) (A : RGraphCat)
    (w : A.obj.left × GeometricThickening.Band (ε + δ)) :
    ((geometricSmoothingCompIso ε δ).inv.app A).hom.left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) (ε + δ)) w) =
      ReebQuotient.mk _ (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) δ)
          (GeometricThickening.addSection A.obj.left ε δ w).1,
        (GeometricThickening.addSection A.obj.left ε δ w).2) := by
  change ((geometricSmoothingAbsorptionIso ε δ).hom.app A).hom.left.hom
      (((GeometricThickening.reebAddIso ε δ).inv.app A.obj).left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) (ε + δ)) w)) = _
  rw [GeometricThickening.reebAddIso_inv_app_left_hom]
  rfl

/-! ### Parameter equality -/

/-- A parameter equality `ε = δ` as `U_ε ≅ U_δ`, by `ℛ` of band inclusions; not `eqToIso`. -/
def geometricSmoothingEqIso {ε δ : ℝ≥0} (h : ε = δ) :
    geometricSmoothing ε ≅ geometricSmoothing δ :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _
      ((Functor.isoWhiskerRight (GeometricThickening.bandEqIso h) ℛ).app A.obj))
    (fun φ => by
      ext1
      exact (Functor.isoWhiskerRight (GeometricThickening.bandEqIso h) ℛ).hom.naturality φ.hom)

/-- `[(x, s)] ↦ [(x, s)]`, through the band inclusion `ε ≤ δ`. -/
theorem geometricSmoothingEqIso_hom_app_hom_left_mk {ε δ : ℝ≥0} (h : ε = δ) (A : RGraphCat)
    (x : A.obj.left) (s : GeometricThickening.Band ε) :
    ((geometricSmoothingEqIso h).hom.app A).hom.left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) ε) (x, s)) =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) δ)
        (GeometricThickening.bandInclusion A.obj.left h.le (x, s)) :=
  rfl

/-! ### Coherence -/

/-- On points, `U_ε` of a graph map acts on the outer representative. -/
theorem geometricSmoothing_map_hom_left_mk (ε : ℝ≥0) {A B : RGraphCat} (φ : A ⟶ B)
    (x : A.obj.left) (t : GeometricThickening.Band ε) :
    ((geometricSmoothing ε).map φ).hom.left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) ε) (x, t)) =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap B.obj) ε) (φ.hom.left.hom x, t) :=
  rfl

/-- `U_0 ≅ 𝟭` sends `[(b, s)]` to `b`. -/
theorem geometricSmoothingZeroIso_hom_app_hom_left_mk (A : RGraphCat) (b : A.obj.left)
    (s : GeometricThickening.Band 0) :
    (geometricSmoothingZeroIso.hom.app A).hom.left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) 0) (b, s)) = b :=
  congrArg (fun φ => φ.left.hom (b, s))
    (projNatTrans_app_comp_geometricSmoothingZeroIso_hom_app_hom A)

/-- **Associativity**, with `(ε + δ) + γ = ε + (δ + γ)` bridged by `geometricSmoothingEqIso`. -/
theorem geometricSmoothingCompIso_assoc (ε δ γ : ℝ≥0) :
    Functor.isoWhiskerLeft (geometricSmoothing γ) (geometricSmoothingCompIso ε δ) ≪≫
        geometricSmoothingCompIso (ε + δ) γ ≪≫ geometricSmoothingEqIso (add_assoc ε δ γ) =
      Functor.isoWhiskerRight (geometricSmoothingCompIso δ γ) (geometricSmoothing ε) ≪≫
        geometricSmoothingCompIso ε (δ + γ) := by
  ext A q
  obtain ⟨⟨p, u⟩, rfl⟩ := ReebQuotient.mk_surjective _ q
  obtain ⟨⟨r, t⟩, rfl⟩ := ReebQuotient.mk_surjective _ p
  obtain ⟨z, rfl⟩ := ReebQuotient.mk_surjective _ r
  have e1 := geometricSmoothingCompIso_hom_app_hom_left_mk ε δ ((geometricSmoothing γ).obj A)
    (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) γ) z, t) u
  have e2 := geometricSmoothingCompIso_hom_app_hom_left_mk (ε + δ) γ A z
    (GeometricThickening.addMap ((geometricSmoothing γ).obj A).obj.left ε δ
      ((ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) γ) z, t), u)).2
  have e3 := geometricSmoothingCompIso_hom_app_hom_left_mk δ γ A z t
  have e4 := geometricSmoothingCompIso_hom_app_hom_left_mk ε (δ + γ) A
    (GeometricThickening.addMap A.obj.left δ γ (z, t)) u
  refine ((congrArg (fun w => ((geometricSmoothingEqIso (add_assoc ε δ γ)).hom.app A).hom.left.hom
    (((geometricSmoothingCompIso (ε + δ) γ).hom.app A).hom.left.hom w)) e1).trans
    ((congrArg (fun w => ((geometricSmoothingEqIso (add_assoc ε δ γ)).hom.app A).hom.left.hom w)
      e2).trans ?_)).trans
    ((congrArg (fun w => ((geometricSmoothingCompIso ε (δ + γ)).hom.app A).hom.left.hom
      (ReebQuotient.mk _ (w, u))) e3).trans e4).symm
  exact congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext (add_assoc _ _ _).symm))

/-- **Left unit law** against `geometricSmoothingZeroIso`. -/
theorem geometricSmoothingCompIso_zero_left (δ : ℝ≥0) :
    geometricSmoothingCompIso 0 δ ≪≫ geometricSmoothingEqIso (zero_add δ) =
      Functor.isoWhiskerLeft (geometricSmoothing δ) geometricSmoothingZeroIso ≪≫
        Functor.rightUnitor _ := by
  ext A q
  obtain ⟨⟨p, t⟩, rfl⟩ := ReebQuotient.mk_surjective _ q
  obtain ⟨z, rfl⟩ := ReebQuotient.mk_surjective _ p
  refine (congrArg (fun w => ((geometricSmoothingEqIso (zero_add δ)).hom.app A).hom.left.hom w)
    (geometricSmoothingCompIso_hom_app_hom_left_mk 0 δ A z t)).trans ?_
  refine Eq.trans ?_ (geometricSmoothingZeroIso_hom_app_hom_left_mk
    ((geometricSmoothing δ).obj A) _ t).symm
  refine congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext ?_))
  show (z.2 : ℝ) + t = z.2
  rw [GeometricThickening.eq_zero_of_mem_band_zero t.2, add_zero]

/-- **Right unit law** against `geometricSmoothingZeroIso`. -/
theorem geometricSmoothingCompIso_zero_right (δ : ℝ≥0) :
    geometricSmoothingCompIso δ 0 ≪≫ geometricSmoothingEqIso (add_zero δ) =
      Functor.isoWhiskerRight geometricSmoothingZeroIso (geometricSmoothing δ) ≪≫
        Functor.leftUnitor _ := by
  ext A q
  obtain ⟨⟨p, t⟩, rfl⟩ := ReebQuotient.mk_surjective _ q
  obtain ⟨⟨x, s⟩, rfl⟩ := ReebQuotient.mk_surjective _ p
  refine (congrArg (fun w => ((geometricSmoothingEqIso (add_zero δ)).hom.app A).hom.left.hom w)
    (geometricSmoothingCompIso_hom_app_hom_left_mk δ 0 A (x, s) t)).trans ?_
  refine Eq.trans ?_ (congrArg (fun b => ReebQuotient.mk
    (GeometricThickening.height (overBaseMap A.obj) δ) (b, t))
    (geometricSmoothingZeroIso_hom_app_hom_left_mk A x s)).symm
  refine congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext ?_))
  show (s : ℝ) + t = t
  rw [GeometricThickening.eq_zero_of_mem_band_zero s.2, zero_add]

/-! ### Compatibility with the precosheaf semigroup -/

/-- **Cosheaf compatibility.** Under the merged comparisons `β`, the component functor sends the
geometric semigroup to the precosheaf semigroup `smoothingCompIso`:
`C(U_ε U_δ A) ⟶ C(U_(ε+δ) A) ⟶ S_(ε+δ) C(A)` equals
`C(U_ε U_δ A) ⟶ S_ε C(U_δ A) ⟶ S_ε S_δ C(A) ⟶ S_(ε+δ) C(A)`. -/
theorem cosheafFunctor_map_geometricSmoothingCompIso_hom_app (ε δ : ℝ≥0) (A : RGraphCat) :
    (cosheafFunctor.map ((geometricSmoothingCompIso ε δ).hom.app A)).hom ≫
        ((geometricSmoothingComparisonIso (ε + δ)).hom.app A).hom =
      ((geometricSmoothingComparisonIso ε).hom.app ((geometricSmoothing δ).obj A)).hom ≫
        (smoothing ε).map ((geometricSmoothingComparisonIso δ).hom.app A).hom ≫
          (smoothingCompIso ε δ).hom.app (intervalComponentsOver.obj A.obj) := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk Q' =>
    obtain ⟨Q, hQ⟩ := Q'
    obtain ⟨⟨b, t⟩, rfl⟩ := ReebQuotient.mk_surjective _ Q
    obtain ⟨z, rfl⟩ := ReebQuotient.mk_surjective _ b
    have e := geometricSmoothingCompIso_hom_app_hom_left_mk ε δ A z t
    have hw : GeometricThickening.height (overBaseMap A.obj) (ε + δ)
        (GeometricThickening.addMap A.obj.left ε δ (z, t)) ∈ I := by
      rw [GeometricThickening.height_addMap]
      exact hQ
    have key : ∀ (y : ReebQuotient (GeometricThickening.height (overBaseMap A.obj) (ε + δ)))
        (hy : ReebQuotient.height (GeometricThickening.height (overBaseMap A.obj) (ε + δ)) y ∈ I),
        y = ReebQuotient.mk _ (GeometricThickening.addMap A.obj.left ε δ (z, t)) →
        ((geometricSmoothingComparisonIso (ε + δ)).hom.app A).hom.app I
            (ZerothHomotopy.mk ⟨y, hy⟩) =
          ((geometricSmoothingComparisonIso (ε + δ)).hom.app A).hom.app I
            (ZerothHomotopy.mk
              ⟨ReebQuotient.mk _ (GeometricThickening.addMap A.obj.left ε δ (z, t)), hw⟩) := by
      rintro y hy rfl
      rfl
    have l2 := geometricSmoothingComparisonIso_hom_app_hom_app_mk (ε + δ) A I
      ⟨GeometricThickening.addMap A.obj.left ε δ (z, t), hw⟩
    have r1 := geometricSmoothingComparisonIso_hom_app_hom_app_mk ε ((geometricSmoothing δ).obj A) I
      ⟨(ReebQuotient.mk _ z, t), hQ⟩
    have r2 := geometricSmoothingComparisonIso_hom_app_hom_app_mk δ A (thicken ε I)
      ⟨z, GeometricThickening.fst_mem_thicken hQ⟩
    refine ((key _ _ e).trans l2).trans ?_
    refine Eq.trans ?_ (congrArg (fun w =>
      ((smoothingCompIso ε δ).hom.app (intervalComponentsOver.obj A.obj)).app I
        (((geometricSmoothingComparisonIso δ).hom.app A).hom.app (thicken ε I) w)) r1).symm
    exact (congrArg (fun w =>
      ((smoothingCompIso ε δ).hom.app (intervalComponentsOver.obj A.obj)).app I w) r2).symm

end RGraph

end

end TDA.Reeb
