import TDA.Reeb.CriticalValuesShift
import TDA.Reeb.RGraphCosheafEquivalence

/-!
# Constructibility under smoothing

The smoothing `smoothing ε` of a precosheaf that is constructible at `S` is constructible at the
shifted witness `S.shifted ε`, and smoothing restricts to an endofunctor of constructible interval
cosheaves (de Silva–Munch–Patel, Proposition 4.19 and the constructible half of Theorem 4.18).

## Constructibility

`CriticalValues.IsConstructibleAt.smoothing`: for `F : OpenInterval ⥤ Type u` constructible at
`S`, the actual `(smoothing ε).obj F` is constructible at `S.shifted ε`, for every `ε : ℝ≥0` and
every value universe `u`. No cosheaf hypothesis is used. The predicate is the corrected one of
`TDA.Reeb.ConstructibleCosheaf`, whose interval rule requires a nonempty source.

* Finiteness. The value at `I` is `F (thicken ε I)`.
* Interval rule. The map of `(smoothing ε).obj F` at `I ≤ J` is `F` at
  `thicken ε I ≤ thicken ε J`. If `I` is nonempty and `I`, `J` meet the same shifted levels, then
  `thicken ε I ⊇ I` is nonempty and the thickenings meet the same levels of `S`
  (`value_mem_thicken_iff_of_shifted`), so the rule for `F` applies.
* Tails. The lower tail `(-∞, a 0 - ε)` of the shifted witness thickens to the lower tail
  `(-∞, a 0)` of `S` (`thicken_iio`), and the upper tail likewise (`thicken_ioi`).

At `ε = 0`, constructibility at `S.shifted 0` and at `S` are equivalent
(`isConstructibleAt_shifted_zero_iff`), by refinement invariance in both directions.

`IsConstructibleCosheaf.smoothing` combines this with `isIntervalCosheaf_smoothing`: the smoothing
of a constructible interval cosheaf is a constructible interval cosheaf. Thickening does not
preserve intersections, and no step uses such a property.

## The restricted functor

`constructibleSmoothing ε : ConstructibleCosheafCat.{u} ⥤ ConstructibleCosheafCat.{u}` is
`ObjectProperty.lift` of `ι ⋙ smoothing ε`. Its composite with the inclusion is
`ι ⋙ smoothing ε` (`constructibleSmoothing_comp_ι`), and the underlying object, map and
components are those of `smoothing ε` (`constructibleSmoothing_obj_obj`,
`constructibleSmoothing_map_hom`, `constructibleSmoothing_map_hom_app`), all by `rfl`.

The lifted unit `constructibleSmoothingUnit ε : 𝟭 ⟶ constructibleSmoothing ε` and the lifted zero
comparison `constructibleSmoothingZeroIso : constructibleSmoothing 0 ≅ 𝟭` have as underlying maps
the actual `smoothingUnit ε` and `smoothingZeroIso` (`constructibleSmoothingUnit_app_hom`,
`constructibleSmoothingZeroIso_hom_app_hom`, `constructibleSmoothingZeroIso_inv_app_hom`, by
`rfl`). The lifted zero unit is the inverse of the lifted zero comparison
(`constructibleSmoothingUnit_zero`).

See `docs/math/reeb-constructible-smoothing.md`.
-/

open Set CategoryTheory
open scoped NNReal

universe u

namespace TDA.Reeb

noncomputable section

open OpenInterval

namespace CriticalValues

variable {n : ℕ} {S : CriticalValues n}

/-- DMP Proposition 4.19 (corrected): smoothing a precosheaf constructible at `S` gives a
precosheaf constructible at the shifted witness. The cosheaf condition is not used. -/
theorem IsConstructibleAt.smoothing {F : OpenInterval ⥤ Type u} (hF : S.IsConstructibleAt F)
    (ε : ℝ≥0) : (S.shifted ε).IsConstructibleAt ((TDA.Reeb.smoothing ε).obj F) where
  finite I := hF.finite (thicken ε I)
  bijective I J h hI hhit :=
    hF.bijective (thicken_mono h) (hI.mono (OpenInterval.le_iff_subset.1 (le_thicken ε I)))
      (S.value_mem_thicken_iff_of_shifted ε h hI hhit)
  isEmpty_lowerTail := by
    change IsEmpty (F.obj (thicken ε (iio ((S.shifted ε).value 0))))
    rw [S.shifted_value_zero ε, thicken_iio, sub_add_cancel]
    exact hF.isEmpty_lowerTail
  isEmpty_upperTail := by
    change IsEmpty (F.obj (thicken ε (ioi ((S.shifted ε).value (Fin.last _)))))
    rw [S.shifted_value_last ε, thicken_ioi, add_sub_cancel_right]
    exact hF.isEmpty_upperTail

/-- At `ε = 0` the shifted witness has the levels of `S`, so constructibility at either is the
same. -/
theorem isConstructibleAt_shifted_zero_iff {F : OpenInterval ⥤ Type u} :
    (S.shifted 0).IsConstructibleAt F ↔ S.IsConstructibleAt F :=
  ⟨fun h => h.of_refines (S.range_shifted_zero).le,
    fun h => h.of_refines (S.range_shifted_zero).ge⟩

end CriticalValues

namespace IsConstructibleCosheaf

/-- DMP Theorem 4.18, constructible half: smoothing preserves constructible interval cosheaves.
The cosheaf half is the merged `isIntervalCosheaf_smoothing`. -/
theorem smoothing {F : OpenInterval ⥤ Type u} (hF : IsConstructibleCosheaf F) (ε : ℝ≥0) :
    IsConstructibleCosheaf ((TDA.Reeb.smoothing ε).obj F) := by
  obtain ⟨hc, n, S, hS⟩ := hF
  exact of_isConstructibleAt (hS.smoothing ε) (isIntervalCosheaf_smoothing hc ε)

end IsConstructibleCosheaf

/-- Smoothing of constructible interval cosheaves: the actual `smoothing ε`, lifted through the
full subcategory `ConstructibleCosheafCat`. -/
def constructibleSmoothing (ε : ℝ≥0) :
    ConstructibleCosheafCat.{u} ⥤ ConstructibleCosheafCat.{u} :=
  ObjectProperty.lift IsConstructibleCosheaf.{u}
    (ObjectProperty.ι IsConstructibleCosheaf.{u} ⋙ smoothing ε) fun G => G.property.smoothing ε

theorem constructibleSmoothing_comp_ι (ε : ℝ≥0) :
    constructibleSmoothing.{u} ε ⋙ ObjectProperty.ι IsConstructibleCosheaf.{u} =
      ObjectProperty.ι IsConstructibleCosheaf.{u} ⋙ smoothing ε :=
  rfl

@[simp] theorem constructibleSmoothing_obj_obj (ε : ℝ≥0) (G : ConstructibleCosheafCat.{u}) :
    ((constructibleSmoothing ε).obj G).obj = (smoothing ε).obj G.obj :=
  rfl

@[simp] theorem constructibleSmoothing_map_hom (ε : ℝ≥0) {G G' : ConstructibleCosheafCat.{u}}
    (f : G ⟶ G') : ((constructibleSmoothing ε).map f).hom = (smoothing ε).map f.hom :=
  rfl

theorem constructibleSmoothing_map_hom_app (ε : ℝ≥0) {G G' : ConstructibleCosheafCat.{u}}
    (f : G ⟶ G') (I : OpenInterval) :
    ((constructibleSmoothing ε).map f).hom.app I = f.hom.app (thicken ε I) :=
  rfl

/-- The lifted unit `G ⟶ S_ε G`; its underlying transformation is the actual `smoothingUnit`. -/
def constructibleSmoothingUnit (ε : ℝ≥0) :
    𝟭 ConstructibleCosheafCat.{u} ⟶ constructibleSmoothing ε where
  app G := ObjectProperty.homMk ((smoothingUnit ε).app G.obj)
  naturality _ _ f := by
    ext : 1
    exact (smoothingUnit ε).naturality f.hom

@[simp] theorem constructibleSmoothingUnit_app_hom (ε : ℝ≥0) (G : ConstructibleCosheafCat.{u}) :
    ((constructibleSmoothingUnit ε).app G).hom = (smoothingUnit ε).app G.obj :=
  rfl

/-- The lifted zero comparison `S_0 ≅ 𝟭`; its underlying isomorphism is the actual
`smoothingZeroIso`. -/
def constructibleSmoothingZeroIso : constructibleSmoothing.{u} 0 ≅ 𝟭 ConstructibleCosheafCat.{u} :=
  NatIso.ofComponents (fun G => ObjectProperty.isoMk _ (smoothingZeroIso.app G.obj)) fun f => by
    ext : 1
    exact smoothingZeroIso.hom.naturality f.hom

@[simp] theorem constructibleSmoothingZeroIso_hom_app_hom (G : ConstructibleCosheafCat.{u}) :
    (constructibleSmoothingZeroIso.hom.app G).hom = smoothingZeroIso.hom.app G.obj :=
  rfl

@[simp] theorem constructibleSmoothingZeroIso_inv_app_hom (G : ConstructibleCosheafCat.{u}) :
    (constructibleSmoothingZeroIso.inv.app G).hom = smoothingZeroIso.inv.app G.obj :=
  rfl

/-- The lifted zero unit is the inverse of the lifted zero comparison (from the merged
`smoothingUnit_zero`). -/
theorem constructibleSmoothingUnit_zero :
    constructibleSmoothingUnit.{u} 0 = constructibleSmoothingZeroIso.inv := by
  ext G : 2
  apply ObjectProperty.hom_ext
  exact NatTrans.congr_app smoothingUnit_zero G.obj

end

end TDA.Reeb
