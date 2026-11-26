import TDA.Sheaf.BandConvolution
import TDA.Sheaf.IntervalCohomology

/-!
# Transport of interval cohomology and the fibres of a band projection

Let `k` be a ring. `Hⁱ(X; G)` is the `i`-th homology of `pushforwardPlus k (toPt X)` applied to
the sheaf `G` placed in degree `0`, as in `TDA.Sheaf.IntervalCohomology`.

* `comp_toPt`: `h ≫ toPt Y = toPt X` for every `h : X ⟶ Y`.
* `H_iso_of_homeo h G i`: along a homeomorphism `h : X ⟶ Y`,
  `Hⁱ(X; G) ≅ Hⁱ(Y; h_* G)`. It is the composition isomorphism
  `R(h ≫ toPt Y)_* ≅ Rh_* ⋙ R(toPt Y)_*` (`pushforwardPlusCompIso`) followed by
  `Rh_* (G[0]) ≅ (h_* G)[0]` (`rightDerivedFunctorPlusSingleIso`), since `h_*` is an equivalence
  and hence exact.
* `isIso_derivedUnit_toPt_app_of_homeo`: the derived unit of `toPt` is invertible at `M` on `X`
  when it is on `Y` (`derivedUnit_comp_app'`).
* `isIso_toPt_Icc_self u`: the singleton interval `[u, u]` is homeomorphic to the point, so the
  derived unit of `toPt` on it is invertible at every object (`isIso_derivedUnit_toPt_Icc_self`).

For `a y : ℝ`, `BandConvolution.fibre a y` is the fibre `(q a)⁻¹ {y}` of the second projection
of the closed band `D a`, with the subspace topology.

* `fibreHomeo a y`: the fibre is homeomorphic to `[y - a, y + a]` by the first coordinate;
  `fibreIso a y` is the isomorphism in `TopCat`, with `fibreIso_toPt`.
* `isZero_H_fibre`: `Hⁱ((q a)⁻¹ {y}; G) = 0` for `2 ≤ i` and every sheaf `G`, all `a`, `y`.
* `isIso_derivedUnit_toPt_fibre` (`0 ≤ a`): the derived unit `N ⟶ RΓ((q a)⁻¹ {y}; constSh N)`
  is an isomorphism for every sheaf `N` of `k`-modules on the point.

The fibre statements need a derived category structure on the interval `[y - a, y + a]` as an
instance argument, as the interval statements they are transported from do.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

namespace TDA.Sheaf

/-- Every map followed by the map to the point is the map to the point. -/
theorem comp_toPt {X Y : TopCat.{0}} (h : X ⟶ Y) : h ≫ toPt Y = toPt X := rfl

/-- A singleton interval is homeomorphic to the point. -/
instance isIso_toPt_Icc_self (u : ℝ) : IsIso (toPt (TopCat.of (Set.Icc u u))) := by
  refine ⟨⟨TopCat.ofHom ⟨fun _ => ⟨u, Set.left_mem_Icc.2 le_rfl⟩, continuous_const⟩, ?_, ?_⟩⟩
  · exact TopCat.ext fun z => Subtype.ext (le_antisymm z.2.1 z.2.2)
  · exact TopCat.ext fun _ => rfl

variable {k : Type} [Ring k]

section transport

variable {X Y : TopCat.{0}} [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))] [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]

/-- **Transport of cohomology along a homeomorphism.** For a homeomorphism `h : X ⟶ Y` and a
sheaf `G` of `k`-modules on `X`, `Hⁱ(X; G) ≅ Hⁱ(Y; h_* G)`. -/
def H_iso_of_homeo (h : X ⟶ Y) [IsIso h] (G : X.Sheaf (ModuleCat.{0} k)) (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ i).obj
        ((pushforwardPlus k (toPt X)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≅
      (DerivedCategory.Plus.homologyFunctor _ i).obj
        ((pushforwardPlus k (toPt Y)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) h).obj G))) :=
  (DerivedCategory.Plus.homologyFunctor _ i).mapIso
    ((pushforwardPlusCompIso k h (toPt Y)).app _ ≪≫
      (pushforwardPlus k (toPt Y)).mapIso (rightDerivedFunctorPlusSingleIso _ 0 G))

/-- Along a homeomorphism `h : X ⟶ Y`, the derived unit `M ⟶ R(toPt X)_* (toPt X)⁻¹ M` is an
isomorphism when the derived unit of `toPt Y` is one at `M`. -/
theorem isIso_derivedUnit_toPt_app_of_homeo (h : X ⟶ Y) [IsIso h]
    (M : DerivedCategory.Plus (pt.Sheaf (ModuleCat.{0} k)))
    (hM : IsIso ((derivedUnit k (toPt Y)).app M)) : IsIso ((derivedUnit k (toPt X)).app M) := by
  rw [← comp_toPt h, derivedUnit_comp_app']
  infer_instance

end transport

/-- On a singleton interval the derived unit `𝟭 ⟶ (toPt _)⁻¹ ⋙ R(toPt _)_*` is invertible. -/
theorem isIso_derivedUnit_toPt_Icc_self (u : ℝ)
    [HasDerivedCategory ((TopCat.of (Set.Icc u u)).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))] :
    IsIso (derivedUnit k (toPt (TopCat.of (Set.Icc u u)))) :=
  inferInstance

namespace BandConvolution

/-- The fibre `(q a)⁻¹ {y}` of the second band projection, as a `TopCat.{0}`. -/
abbrev fibre (a y : ℝ) : TopCat.{0} := TopCat.of ((q a) ⁻¹' {y} : Set (D a))

/-- **The fibres of `q a`.** The fibre of `q a` over `y` is the interval `[y - a, y + a]`, by the
first coordinate. For `a < 0` both are empty. -/
def fibreHomeo (a y : ℝ) : ((q a) ⁻¹' {y} : Set (D a)) ≃ₜ Set.Icc (y - a) (y + a) where
  toFun z := ⟨z.1.1.1, by
    have h1 : dist z.1.1.1 z.1.1.2 ≤ a := z.1.2
    have h2 : z.1.1.2 = y := z.2
    rw [Real.dist_eq, abs_le, h2] at h1
    exact ⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩⟩
  invFun x := ⟨⟨(x.1, y), by
      change dist x.1 y ≤ a
      rw [Real.dist_eq, abs_le]
      exact ⟨by linarith [x.2.1, x.2.2], by linarith [x.2.1, x.2.2]⟩⟩, rfl⟩
  left_inv z := by
    have h2 : z.1.1.2 = y := z.2
    exact Subtype.ext (Subtype.ext (Prod.ext rfl h2.symm))
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun :=
    (((continuous_subtype_val.prodMk continuous_const).subtype_mk _).subtype_mk _)

/-- `fibreHomeo` is the first coordinate. -/
@[simp]
theorem coe_fibreHomeo_apply (a y : ℝ) (z : (q a) ⁻¹' {y}) :
    (fibreHomeo a y z : ℝ) = z.1.1.1 := rfl

/-- The fibre of `q a` over `y` and `[y - a, y + a]` are isomorphic in `TopCat`. -/
def fibreIso (a y : ℝ) : fibre a y ≅ TopCat.of (Set.Icc (y - a) (y + a)) :=
  TopCat.isoOfHomeo (fibreHomeo a y)

/-- The isomorphism `fibreIso` is compatible with the maps to the point. -/
theorem fibreIso_toPt (a y : ℝ) : (fibreIso a y).hom ≫ toPt _ = toPt (fibre a y) :=
  comp_toPt _

/-- **Fibres of `q a` have cohomological dimension at most one.** For every sheaf `G` of
`k`-modules on the fibre `(q a)⁻¹ {y}`, `Hⁱ((q a)⁻¹ {y}; G) = 0` for `2 ≤ i`. -/
theorem isZero_H_fibre {a y : ℝ} [HasDerivedCategory ((fibre a y).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory ((TopCat.of (Set.Icc (y - a) (y + a))).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
    (G : (fibre a y).Sheaf (ModuleCat.{0} k)) {i : ℤ} (hi : 2 ≤ i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((pushforwardPlus k (toPt (fibre a y))).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
  (isZero_H_Icc _ hi).of_iso (H_iso_of_homeo (fibreIso a y).hom G i)

/-- **Constant coefficients on the fibres of `q a`.** For `0 ≤ a`, the derived unit
`N ⟶ R(toPt _)_* (toPt _)⁻¹ N` on the fibre `(q a)⁻¹ {y}` is an isomorphism for every sheaf `N`
of `k`-modules on the point. -/
theorem isIso_derivedUnit_toPt_fibre {a : ℝ} (ha : 0 ≤ a) (y : ℝ)
    [HasDerivedCategory ((fibre a y).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory ((TopCat.of (Set.Icc (y - a) (y + a))).Sheaf (ModuleCat.{0} k))]
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))] (N : pt.Sheaf (ModuleCat.{0} k)) :
    IsIso ((derivedUnit k (toPt (fibre a y))).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) :=
  isIso_derivedUnit_toPt_app_of_homeo (fibreIso a y).hom _
    (isIso_derivedUnit_toPt_Icc (by linarith) N)

end BandConvolution

end TDA.Sheaf
