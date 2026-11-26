import TDA.Sheaf.BaseChangePasting
import TDA.Sheaf.BandStalks

/-!
# Proper base change on the fibres of a band projection

Let `k` be a ring and `a y : ℝ`. The fibre square of the second projection `q a : D a ⟶ ℝ` at `y`

```
             fibreEmb a y
  [y - a, y + a] ------> D a
        |                 |
   toPt |                 | q a
        v                 v
       pt  ----------->   ℝ
             ptAt y
```

commutes definitionally (`fibreEmb_comp_q`). This file identifies its base-change morphisms.

* `baseChangeCochain_fibreEmb_app_hom_f`: termwise on a complex, the underived base change of the
  fibre square is the stalk comparison `stalkComparison k a y` of `TDA.Sheaf.BandStalks`
  (`baseChangeSheaf_fibreEmb_app`); it is an isomorphism of complexes
  (`isIso_baseChangeCochain_fibreEmb_app`).
* `isIso_baseChange_fibreEmb`: **proper base change on the fibres of `q a`.** The derived
  base-change morphism `R(q a)_* ⋙ (ptAt y)⁻¹ ⟶ (fibreEmb a y)⁻¹ ⋙ RΓ([y - a, y + a]; -)` is an
  isomorphism: `fibreEmb a y` is a fibre parametrisation of the interval fibration `q a`
  (`isFibreParam_fibreEmb`), and `FibreCoordinate.IsFibreParam.isIso_baseChange` applies.
* `stalkFormula k a y`: the canonical stalk formula, the natural isomorphism
  `R(q a)_* ⋙ (ptAt y)⁻¹ ≅ (fibreEmb a y)⁻¹ ⋙ RΓ([y - a, y + a]; -)` whose underlying morphism is
  `baseChange k (fibreEmb_comp_q a y)` (`stalkFormula_hom`); on `Q K` it is described by
  `stalkFormula_hom_app_Q`. Its components witness `nonempty_stalkFormula`.

Derived categories are instance arguments for exactly the spaces each statement mentions.
-/

noncomputable section
open CategoryTheory Limits

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Ring k] (a y : ℝ)

/-- In degree `n`, the termwise underived base change of the fibre square is the stalk
comparison at the `n`-th term. -/
@[simp]
theorem baseChangeCochain_fibreEmb_app_hom_f
    (K : CochainComplex.Plus ((D a).Sheaf (ModuleCat.{0} k))) (n : ℤ) :
    ((baseChangeCochain k (fibreEmb_comp_q a y)).app K).hom.f n =
      stalkComparison k a y (K.obj.X n) := by
  rw [baseChangeCochain_app_hom_f, baseChangeSheaf_fibreEmb_app]

/-- The termwise underived base change of the fibre square is an isomorphism of complexes. -/
instance isIso_baseChangeCochain_fibreEmb_app
    (K : CochainComplex.Plus ((D a).Sheaf (ModuleCat.{0} k))) :
    IsIso ((baseChangeCochain k (fibreEmb_comp_q a y)).app K) :=
  (isFibreParam_fibreEmb a y).isIso_baseChangeCochain_app k K

variable [HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory ((TopCat.of (Set.Icc (y - a) (y + a))).Sheaf (ModuleCat.{0} k))]

/-- **Proper base change on the fibres of a band projection.** The base-change morphism of the
fibre square `fibreEmb a y ≫ q a = toPt _ ≫ ptAt y`,
`R(q a)_* ⋙ (ptAt y)⁻¹ ⟶ (fibreEmb a y)⁻¹ ⋙ RΓ([y - a, y + a]; -)`, is an isomorphism. -/
instance isIso_baseChange_fibreEmb : IsIso (baseChange k (fibreEmb_comp_q a y)) :=
  (isFibreParam_fibreEmb a y).isIso_baseChange k

/-- **The canonical stalk formula for the band projections.** For `F ∈ D⁺(Sh(D a))`, the stalk
at `y` of `R(q a)_* F` (its inverse image `(ptAt y)⁻¹` to the point) is `RΓ` of the fibre
`(q a)⁻¹ {y} ≅ [y - a, y + a]` with coefficients in `(fibreEmb a y)⁻¹ F`, naturally in `F`. The
isomorphism is the base-change morphism of the fibre square (`isIso_baseChange_fibreEmb`). -/
def stalkFormula :
    pushforwardPlus k (q a) ⋙ pullbackPlus k (ptAt y) ≅
      pullbackPlus k (fibreEmb a y) ⋙
        pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a)))) :=
  asIso (baseChange k (fibreEmb_comp_q a y))

/-- The stalk formula is the base-change morphism of the fibre square. -/
@[simp]
theorem stalkFormula_hom : (stalkFormula k a y).hom = baseChange k (fibreEmb_comp_q a y) := rfl

/-- **The stalk formula on `Q K`.** For a bounded below complex `K` of sheaves on `D a`, after
`(ptAt y)⁻¹` of the comparison `(q a)_* K ⟶ R(q a)_* K`, the stalk formula is the inverse
comparison of `(ptAt y)⁻¹`, then `Q` of the termwise stalk comparisons
(`baseChangeCochain_fibreEmb_app_hom_f`), then the comparisons of `Γ([y - a, y + a]; -)` and of
`(fibreEmb a y)⁻¹`. -/
theorem stalkFormula_hom_app_Q (K : CochainComplex.Plus ((D a).Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (ptAt y)).map
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).rightDerivedFunctorPlusUnit.app K) ≫
      (stalkFormula k a y).hom.app (DerivedCategory.Plus.Q.obj K) =
    inv ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (ptAt y)).rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (q a)).mapCochainComplexPlus.obj K)) ≫
      DerivedCategory.Plus.Q.map ((baseChangeCochain k (fibreEmb_comp_q a y)).app K) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k)
          (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).rightDerivedFunctorPlusUnit.app
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).mapCochainComplexPlus.obj K) ≫
      (pushforwardPlus k (toPt (TopCat.of (Set.Icc (y - a) (y + a))))).map
        ((TopCat.Sheaf.pullback (ModuleCat.{0} k) (fibreEmb a y)).rightDerivedFunctorPlusUnit.app
          K) :=
  baseChange_app_Q k (fibreEmb_comp_q a y) K

end TDA.Sheaf.BandConvolution
