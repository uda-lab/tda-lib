import TDA.Reeb.GeometricInterleaving

/-!
# Geometric and cosheaf interleavings of graph objects coincide

Write `U_ε = geometricSmoothing ε`, `μ_(ε,δ) : U_ε U_δ ≅ U_(ε+δ)` for `geometricSmoothingCompIso`,
`C = cosheafFunctor`, `β^ε : U_ε ⋙ C ≅ C ⋙ constructibleSmoothing ε` for the comparison and
`S_ε = smoothing ε` on interval precosheaves.

Morphisms of constructible cosheaves are exactly natural transformations of the underlying
precosheaves, `C` is fully faithful and `β^ε_B` is an isomorphism. So the shifted map
`cosheafShiftMap φ = C φ ≫ β^ε_B` is a bijection `(A ⟶ U_ε B) ≃ ((C A).obj ⟶ S_ε (C B).obj)`
(`cosheafShiftEquiv`). Its injectivity turns every precosheaf triangle into a geometric one,
because both sides of a geometric triangle have shifted maps given by `cosheafShiftMap_comp` and
`cosheafShiftMap_unit`. Hence `GeometricInterleaving.toCosheaf` is an equivalence
(`GeometricInterleaving.cosheafEquiv`) at every parameter, and the geometric interleaving distance
equals the interleaving distance of the component precosheaves
(`geometricInterleavingDistance_eq_interleavingDistance`).

Composition of geometric interleavings (`GeometricInterleaving.trans`, at `ε + δ`), the triangle
inequality, invariance under isomorphism and the zero-distance characterization are transported
from the precosheaf results through this equivalence. `trans` is defined by transport; its first
component is the geometric shifted composite (`GeometricInterleaving.trans_φ`), by the
three-object form `cosheafShiftMap_comp'` of the composite law.

Only full faithfulness of `C` and invertibility of `β^ε` are used; essential surjectivity of `C`
is not. These are library statements proved from merged facts, not attributed to a numbered
source result. Everything is in universe `0`.

See `docs/math/reeb-geometric-interleaving-equivalence.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace RGraph

open OpenInterval

/-! ### The shifted-map bijection -/

/-- **The shifted-map bijection**: `cosheafShiftMap` identifies maps `A ⟶ U_ε B` with all natural
transformations `(C A).obj ⟶ S_ε (C B).obj`. The inverse sends `f` to the preimage under the fully
faithful `C` of `f ≫ (β^ε_B)⁻¹`, a morphism of constructible cosheaves with no further proof
obligation. -/
def cosheafShiftEquiv (ε : ℝ≥0) (A B : RGraphCat) :
    (A ⟶ (geometricSmoothing ε).obj B) ≃
      ((cosheafFunctor.obj A).obj ⟶ (smoothing ε).obj (cosheafFunctor.obj B).obj) where
  toFun := cosheafShiftMap
  invFun f := cosheafFullyFaithful.preimage
    (ObjectProperty.homMk (f ≫ ((geometricSmoothingComparisonIso ε).inv.app B).hom))
  left_inv φ := by
    have h1 : ((geometricSmoothingComparisonIso ε).hom.app B).hom ≫
        ((geometricSmoothingComparisonIso ε).inv.app B).hom = 𝟙 _ :=
      congrArg (fun f => f.hom) ((geometricSmoothingComparisonIso ε).hom_inv_id_app B)
    have h : ObjectProperty.homMk (P := IsConstructibleCosheaf)
        (cosheafShiftMap φ ≫ ((geometricSmoothingComparisonIso ε).inv.app B).hom) =
          cosheafFunctor.map φ := by
      ext1
      exact (Category.assoc _ _ _).trans
        ((congrArg ((cosheafFunctor.map φ).hom ≫ ·) h1).trans (Category.comp_id _))
    exact (congrArg cosheafFullyFaithful.preimage h).trans (cosheafFullyFaithful.preimage_map φ)
  right_inv f := by
    have h1 : ((geometricSmoothingComparisonIso ε).inv.app B).hom ≫
        ((geometricSmoothingComparisonIso ε).hom.app B).hom = 𝟙 _ :=
      congrArg (fun f => f.hom) ((geometricSmoothingComparisonIso ε).inv_hom_id_app B)
    change (cosheafFunctor.map (cosheafFullyFaithful.preimage _)).hom ≫ _ = f
    rw [Functor.FullyFaithful.map_preimage]
    exact (Category.assoc _ _ _).trans ((congrArg (f ≫ ·) h1).trans (Category.comp_id _))

variable {ε δ : ℝ≥0} {A B D : RGraphCat}

@[simp] theorem cosheafShiftEquiv_apply (φ : A ⟶ (geometricSmoothing ε).obj B) :
    cosheafShiftEquiv ε A B φ = cosheafShiftMap φ :=
  rfl

/-- `cosheafShiftMap` is injective. -/
theorem cosheafShiftMap_injective (ε : ℝ≥0) (A B : RGraphCat) :
    Function.Injective (cosheafShiftMap : (A ⟶ (geometricSmoothing ε).obj B) → _) :=
  (cosheafShiftEquiv ε A B).injective

/-- Every natural transformation `(C A).obj ⟶ S_ε (C B).obj` is a shifted map. -/
theorem cosheafShiftMap_cosheafShiftEquiv_symm
    (f : (cosheafFunctor.obj A).obj ⟶ (smoothing ε).obj (cosheafFunctor.obj B).obj) :
    cosheafShiftMap ((cosheafShiftEquiv ε A B).symm f) = f :=
  (cosheafShiftEquiv ε A B).apply_symm_apply f

/-- **Composite law, three-object form**: for `φ : A ⟶ U_ε B` and `ψ : B ⟶ U_δ D`, the shifted
map of `A ⟶ U_ε B ⟶ U_ε U_δ D ≅ U_(ε+δ) D` is the precosheaf shifted composite. -/
theorem cosheafShiftMap_comp' (φ : A ⟶ (geometricSmoothing ε).obj B)
    (ψ : B ⟶ (geometricSmoothing δ).obj D) :
    cosheafShiftMap (φ ≫ (geometricSmoothing ε).map ψ ≫
        (geometricSmoothingCompIso ε δ).hom.app D) =
      cosheafShiftMap φ ≫ (smoothing ε).map (cosheafShiftMap ψ) ≫
        (smoothingCompIso ε δ).hom.app (cosheafFunctor.obj D).obj := by
  have hnat : (cosheafFunctor.map ((geometricSmoothing ε).map ψ)).hom ≫
      ((geometricSmoothingComparisonIso ε).hom.app ((geometricSmoothing δ).obj D)).hom =
        ((geometricSmoothingComparisonIso ε).hom.app B).hom ≫
          (smoothing ε).map (cosheafFunctor.map ψ).hom :=
    congrArg (fun f => f.hom) ((geometricSmoothingComparisonIso ε).hom.naturality ψ)
  have hsq := cosheafFunctor_map_geometricSmoothingCompIso_hom_app ε δ D
  have e1 : (cosheafFunctor.map (φ ≫ (geometricSmoothing ε).map ψ ≫
      (geometricSmoothingCompIso ε δ).hom.app D)).hom =
        (cosheafFunctor.map φ).hom ≫ (cosheafFunctor.map ((geometricSmoothing ε).map ψ)).hom ≫
          (cosheafFunctor.map ((geometricSmoothingCompIso ε δ).hom.app D)).hom := by
    rw [Functor.map_comp, Functor.map_comp]
    rfl
  -- The chase of `cosheafShiftMap_comp`; it never uses that the endpoint is the source.
  refine ((congrArg (· ≫ ((geometricSmoothingComparisonIso (ε + δ)).hom.app D).hom) e1).trans
    ((Category.assoc _ _ _).trans (congrArg ((cosheafFunctor.map φ).hom ≫ ·)
      ((Category.assoc _ _ _).trans (congrArg
        ((cosheafFunctor.map ((geometricSmoothing ε).map ψ)).hom ≫ ·) hsq))))).trans ?_
  refine (congrArg ((cosheafFunctor.map φ).hom ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hnat))).trans ?_
  refine (congrArg ((cosheafFunctor.map φ).hom ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (((cosheafFunctor.map φ).hom ≫
    ((geometricSmoothingComparisonIso ε).hom.app B).hom) ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ (smoothingCompIso ε δ).hom.app (cosheafFunctor.obj D).obj)
    ((smoothing ε).map_comp _ _).symm

/-! ### Interleavings from the cosheaf side, and the equivalence -/

namespace GeometricInterleaving

/-- A precosheaf `ε`-interleaving of the component cosheaves gives a geometric `ε`-interleaving:
the maps are the preimages of the shifted-map bijection, and the triangles follow by injectivity of
`cosheafShiftMap` from the precosheaf triangles. -/
def ofCosheaf (j : Interleaving ε (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj) :
    GeometricInterleaving ε A B where
  φ := (cosheafShiftEquiv ε A B).symm j.φ
  ψ := (cosheafShiftEquiv ε B A).symm j.ψ
  φ_ψ := cosheafShiftMap_injective (ε + ε) A A (by
    rw [cosheafShiftMap_comp, cosheafShiftMap_cosheafShiftEquiv_symm,
      cosheafShiftMap_cosheafShiftEquiv_symm, j.φ_ψ, cosheafShiftMap_unit])
  ψ_φ := cosheafShiftMap_injective (ε + ε) B B (by
    rw [cosheafShiftMap_comp, cosheafShiftMap_cosheafShiftEquiv_symm,
      cosheafShiftMap_cosheafShiftEquiv_symm, j.ψ_φ, cosheafShiftMap_unit])

theorem ofCosheaf_toCosheaf (i : GeometricInterleaving ε A B) : ofCosheaf i.toCosheaf = i :=
  GeometricInterleaving.ext ((cosheafShiftEquiv ε A B).symm_apply_apply i.φ)
    ((cosheafShiftEquiv ε B A).symm_apply_apply i.ψ)

theorem toCosheaf_ofCosheaf
    (j : Interleaving ε (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj) :
    (ofCosheaf j).toCosheaf = j :=
  Interleaving.ext (cosheafShiftMap_cosheafShiftEquiv_symm j.φ)
    (cosheafShiftMap_cosheafShiftEquiv_symm j.ψ)

/-- **Geometric and cosheaf interleavings coincide**: `toCosheaf` is an equivalence at every
parameter. -/
def cosheafEquiv (ε : ℝ≥0) (A B : RGraphCat) :
    GeometricInterleaving ε A B ≃
      Interleaving ε (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj where
  toFun := toCosheaf
  invFun := ofCosheaf
  left_inv := ofCosheaf_toCosheaf
  right_inv := toCosheaf_ofCosheaf

theorem cosheafEquiv_apply (i : GeometricInterleaving ε A B) :
    cosheafEquiv ε A B i = i.toCosheaf :=
  rfl

theorem cosheafEquiv_symm_apply
    (j : Interleaving ε (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj) :
    (cosheafEquiv ε A B).symm j = ofCosheaf j :=
  rfl

theorem nonempty_iff_cosheaf :
    Nonempty (GeometricInterleaving ε A B) ↔
      Nonempty (Interleaving ε (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj) :=
  (cosheafEquiv ε A B).nonempty_congr

end GeometricInterleaving

/-! ### `d_geo = d_cosheaf` and the transported distance laws -/

/-- **`d_geo = d_cosheaf`**: the geometric interleaving distance of graph objects is the
interleaving distance of their component precosheaves. -/
theorem geometricInterleavingDistance_eq_interleavingDistance (A B : RGraphCat) :
    geometricInterleavingDistance A B =
      interleavingDistance (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj :=
  le_antisymm
    (le_iInf₂ fun _ ⟨j⟩ => (GeometricInterleaving.ofCosheaf j).geometricInterleavingDistance_le)
    (interleavingDistance_cosheafFunctor_le_geometricInterleavingDistance A B)

/-- Approximation from above, without assuming the infimum is attained. -/
theorem geometricInterleavingDistance_lt_iff {r : ℝ≥0∞} :
    geometricInterleavingDistance A B < r ↔
      ∃ ε : ℝ≥0, (ε : ℝ≥0∞) < r ∧ Nonempty (GeometricInterleaving ε A B) := by
  simp only [geometricInterleavingDistance, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- Zero distance means geometric witnesses at every positive parameter; it does not give a
`0`-witness, hence no isomorphism. -/
theorem geometricInterleavingDistance_eq_zero_iff :
    geometricInterleavingDistance A B = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε → Nonempty (GeometricInterleaving ε A B) := by
  rw [geometricInterleavingDistance_eq_interleavingDistance, interleavingDistance_eq_zero_iff]
  exact forall₂_congr fun _ _ => GeometricInterleaving.nonempty_iff_cosheaf.symm

/-! ### Composition, triangle inequality and isomorphism invariance -/

namespace GeometricInterleaving

/-- **Composition**: geometric interleavings `A ↔ B` at `ε` and `B ↔ D` at `δ` give `A ↔ D` at
`ε + δ`, transported from `Interleaving.trans`. -/
def trans (i : GeometricInterleaving ε A B) (j : GeometricInterleaving δ B D) :
    GeometricInterleaving (ε + δ) A D :=
  ofCosheaf (i.toCosheaf.trans j.toCosheaf)

theorem trans_toCosheaf (i : GeometricInterleaving ε A B) (j : GeometricInterleaving δ B D) :
    (i.trans j).toCosheaf = i.toCosheaf.trans j.toCosheaf :=
  toCosheaf_ofCosheaf _

/-- The first component of the composite is the geometric shifted composite
`A ⟶ U_ε B ⟶ U_ε U_δ D ≅ U_(ε+δ) D`. -/
theorem trans_φ (i : GeometricInterleaving ε A B) (j : GeometricInterleaving δ B D) :
    (i.trans j).φ =
      i.φ ≫ (geometricSmoothing ε).map j.φ ≫ (geometricSmoothingCompIso ε δ).hom.app D :=
  cosheafShiftMap_injective (ε + δ) A D
    ((cosheafShiftMap_cosheafShiftEquiv_symm _).trans (cosheafShiftMap_comp' i.φ j.φ).symm)

end GeometricInterleaving

/-- **Triangle inequality** for the geometric interleaving distance. -/
theorem geometricInterleavingDistance_triangle (A B D : RGraphCat) :
    geometricInterleavingDistance A D ≤
      geometricInterleavingDistance A B + geometricInterleavingDistance B D := by
  rw [geometricInterleavingDistance_eq_interleavingDistance,
    geometricInterleavingDistance_eq_interleavingDistance,
    geometricInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_triangle _ _ _

/-- Invariance under isomorphism, on both arguments. -/
theorem geometricInterleavingDistance_congr {A A' B B' : RGraphCat} (e : A ≅ A') (e' : B ≅ B') :
    geometricInterleavingDistance A B = geometricInterleavingDistance A' B' := by
  rw [geometricInterleavingDistance_eq_interleavingDistance,
    geometricInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_congr ((ObjectProperty.ι _).mapIso (cosheafFunctor.mapIso e))
    ((ObjectProperty.ι _).mapIso (cosheafFunctor.mapIso e'))

theorem geometricInterleavingDistance_congr_left {A A' : RGraphCat} (e : A ≅ A')
    (B : RGraphCat) :
    geometricInterleavingDistance A B = geometricInterleavingDistance A' B :=
  geometricInterleavingDistance_congr e (Iso.refl B)

theorem geometricInterleavingDistance_congr_right (A : RGraphCat) {B B' : RGraphCat}
    (e : B ≅ B') :
    geometricInterleavingDistance A B = geometricInterleavingDistance A B' :=
  geometricInterleavingDistance_congr (Iso.refl A) e

end RGraph

end

end TDA.Reeb
