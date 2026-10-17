import TDA.Reeb.GeometricInterleavingEquivalence

/-!
# Enlargement and self-smoothing for geometric interleavings

This module proves the enlargement, monotonicity, composition, and self-smoothing statements for
geometric interleavings, together with their distance consequences. These are library statements
proved from the merged facts already present in the library, not assertions attributed to a
numbered source result. The mathematical conventions and the equivalence used here are documented
in `docs/math/reeb-geometric-interleaving-equivalence.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

universe u v

namespace TDA.Reeb

noncomputable section

namespace Interleaving

open OpenInterval

variable {C : Type u} [Category.{v} C]

/-- Transport an `ε`-interleaving along an isomorphism of its second precosheaf argument. -/
def isoRight {ε : ℝ≥0} {F G G' : OpenInterval ⥤ C} (j : Interleaving ε F G) (e : G ≅ G') :
    Interleaving ε F G' where
  φ := j.φ ≫ (smoothing ε).map e.hom
  ψ := e.inv ≫ j.ψ
  φ_ψ := by
    ext I
    dsimp
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_app_assoc]
    have hφψ :
        j.φ.app I ≫ j.ψ.app (thicken ε I) ≫
            F.map ((thickenCompIso ε ε).hom.app I) =
          ((smoothingUnit (ε + ε)).app F).app I :=
      congrArg (fun t => t.app I) j.φ_ψ
    exact hφψ
  ψ_φ := by
    ext I
    dsimp
    simp only [Category.assoc]
    erw [← e.hom.naturality]
    have hψφ :
        j.ψ.app I ≫ j.φ.app (thicken ε I) ≫
            G.map ((thickenCompIso ε ε).hom.app I) =
          ((smoothingUnit (ε + ε)).app G).app I :=
      congrArg (fun t => t.app I) j.ψ_φ
    erw [reassoc_of% hψφ]
    erw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
    rfl

/-- The first component of `Interleaving.isoRight` is the shifted original component. -/
theorem isoRight_φ {ε : ℝ≥0} {F G G' : OpenInterval ⥤ C} (j : Interleaving ε F G)
    (e : G ≅ G') :
    (j.isoRight e).φ = j.φ ≫ (smoothing ε).map e.hom :=
  rfl

/-- The second component of `Interleaving.isoRight` is the inverse transport followed by the
original second component. -/
theorem isoRight_ψ {ε : ℝ≥0} {F G G' : OpenInterval ⥤ C} (j : Interleaving ε F G)
    (e : G ≅ G') :
    (j.isoRight e).ψ = e.inv ≫ j.ψ :=
  rfl

end Interleaving

namespace RGraph

open OpenInterval

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

variable {ε δ η : ℝ≥0} {A B D : RGraphCat}

/-- The geometric enlargement `U_ε ⟶ U_δ` induced by the band inclusion for `ε ≤ δ`. -/
def geometricEnlargement {ε δ : ℝ≥0} (h : ε ≤ δ) :
    geometricSmoothing ε ⟶ geometricSmoothing δ where
  app A := ObjectProperty.homMk
    ((Functor.whiskerRight (GeometricThickening.bandInclusionNatTrans h) ℛ).app A.obj)
  naturality _ _ φ := by
    ext1
    exact (Functor.whiskerRight (GeometricThickening.bandInclusionNatTrans h) ℛ).naturality φ.hom

/-- On a Reeb representative, geometric enlargement preserves the point and changes only its
band membership. -/
theorem geometricEnlargement_app_hom_left_mk (h : ε ≤ δ) (A : RGraphCat)
    (x : A.obj.left) (s : GeometricThickening.Band ε) :
    ((geometricEnlargement h).app A).hom.left.hom
        (ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) ε) (x, s)) =
      ReebQuotient.mk (GeometricThickening.height (overBaseMap A.obj) δ)
        (GeometricThickening.bandInclusion A.obj.left h (x, s)) :=
  rfl

/-- Geometric enlargement is the identity at a reflexive inequality. -/
theorem geometricEnlargement_refl (ε : ℝ≥0) :
    geometricEnlargement (le_refl ε) = 𝟙 (geometricSmoothing ε) := by
  ext A q
  obtain ⟨z, rfl⟩ := ReebQuotient.mk_surjective _ q
  rfl

/-- Geometric enlargements compose along a chain of inequalities. -/
theorem geometricEnlargement_comp (h : ε ≤ δ) (h' : δ ≤ η) :
    geometricEnlargement h ≫ geometricEnlargement h' = geometricEnlargement (h.trans h') := by
  ext A q
  obtain ⟨z, rfl⟩ := ReebQuotient.mk_surjective _ q
  rfl

/-- The geometric unit is compatible with geometric enlargement. -/
theorem geometricSmoothingUnit_comp_geometricEnlargement (h : ε ≤ δ) :
    geometricSmoothingUnit ε ≫ geometricEnlargement h = geometricSmoothingUnit δ := by
  ext A x
  rfl

/-- The equality isomorphism of geometric smoothings is the corresponding enlargement. -/
theorem geometricSmoothingEqIso_hom_eq (h : ε = δ) :
    (geometricSmoothingEqIso h).hom = geometricEnlargement h.le := by
  ext A q
  obtain ⟨z, rfl⟩ := ReebQuotient.mk_surjective _ q
  rfl

/-- Under the geometric-to-cosheaf comparison, geometric enlargement is precosheaf smoothing
enlargement. -/
theorem cosheafFunctor_map_geometricEnlargement_app (h : ε ≤ δ) (B : RGraphCat) :
    (cosheafFunctor.map ((geometricEnlargement h).app B)).hom ≫
        ((geometricSmoothingComparisonIso δ).hom.app B).hom =
      ((geometricSmoothingComparisonIso ε).hom.app B).hom ≫
        (smoothingMap h).app (cosheafFunctor.obj B).obj := by
  ext I c
  induction c using ZerothHomotopy.rec with
  | mk Q' =>
    obtain ⟨Q, hQ⟩ := Q'
    obtain ⟨z, rfl⟩ :=
      ReebQuotient.mk_surjective (GeometricThickening.height (overBaseMap B.obj) ε) Q
    have hQ' : GeometricThickening.height (overBaseMap B.obj) δ
        (GeometricThickening.bandInclusion B.obj.left h z) ∈ I := by
      rw [GeometricThickening.height_bandInclusion]
      exact hQ
    change
      ((geometricSmoothingComparisonIso δ).hom.app B).hom.app I
          (ZerothHomotopy.mk
            ⟨ReebQuotient.mk _ (GeometricThickening.bandInclusion B.obj.left h z), hQ'⟩) =
        ((smoothingMap h).app (cosheafFunctor.obj B).obj).app I
          (((geometricSmoothingComparisonIso ε).hom.app B).hom.app I
            (ZerothHomotopy.mk ⟨ReebQuotient.mk _ z, hQ⟩))
    have l := geometricSmoothingComparisonIso_hom_app_hom_app_mk δ B I
      ⟨GeometricThickening.bandInclusion B.obj.left h z, hQ'⟩
    have r := geometricSmoothingComparisonIso_hom_app_hom_app_mk ε B I ⟨z, hQ⟩
    refine l.trans (Eq.trans ?_ (congrArg (fun w =>
      ((smoothingMap h).app (cosheafFunctor.obj B).obj).app I w) r).symm)
    rfl

/-- The shifted map respects geometric enlargement. -/
theorem cosheafShiftMap_comp_geometricEnlargement (h : ε ≤ δ)
    (f : A ⟶ (geometricSmoothing ε).obj B) :
    cosheafShiftMap (f ≫ (geometricEnlargement h).app B) =
      cosheafShiftMap f ≫ (smoothingMap h).app (cosheafFunctor.obj B).obj := by
  have e1 : (cosheafFunctor.map (f ≫ (geometricEnlargement h).app B)).hom =
      (cosheafFunctor.map f).hom ≫ (cosheafFunctor.map ((geometricEnlargement h).app B)).hom := by
    rw [Functor.map_comp]
    rfl
  refine (congrArg (· ≫ ((geometricSmoothingComparisonIso δ).hom.app B).hom) e1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((cosheafFunctor.map f).hom ≫ ·)
    (cosheafFunctor_map_geometricEnlargement_app h B)).trans ?_
  exact (Category.assoc _ _ _).symm

namespace GeometricInterleaving

/-- Enlarge a geometric interleaving by transporting the enlarged precosheaf interleaving back
through the geometric-to-cosheaf equivalence. -/
def mono (i : GeometricInterleaving ε A B) {δ : ℝ≥0} (h : ε ≤ δ) :
    GeometricInterleaving δ A B :=
  ofCosheaf (i.toCosheaf.mono h)

/-- The cosheaf image of geometric interleaving monotonicity is precosheaf monotonicity. -/
theorem mono_toCosheaf (i : GeometricInterleaving ε A B) (h : ε ≤ δ) :
    (i.mono h).toCosheaf = i.toCosheaf.mono h :=
  toCosheaf_ofCosheaf _

/-- The first component of a monotone geometric interleaving is the original component followed
by geometric enlargement. -/
theorem mono_φ (i : GeometricInterleaving ε A B) (h : ε ≤ δ) :
    (i.mono h).φ = i.φ ≫ (geometricEnlargement h).app B := by
  apply cosheafShiftMap_injective δ A B
  rw [← toCosheaf_φ (i.mono h)]
  calc
    (i.mono h).toCosheaf.φ = (i.toCosheaf.mono h).φ := by rw [mono_toCosheaf]
    _ = i.toCosheaf.φ ≫ (smoothingMap h).app (cosheafFunctor.obj B).obj := rfl
    _ = cosheafShiftMap i.φ ≫ (smoothingMap h).app (cosheafFunctor.obj B).obj := by
      rw [toCosheaf_φ]
    _ = cosheafShiftMap (i.φ ≫ (geometricEnlargement h).app B) :=
      (cosheafShiftMap_comp_geometricEnlargement h i.φ).symm

/-- The second component of a monotone geometric interleaving is the original component followed
by geometric enlargement. -/
theorem mono_ψ (i : GeometricInterleaving ε A B) (h : ε ≤ δ) :
    (i.mono h).ψ = i.ψ ≫ (geometricEnlargement h).app A := by
  apply cosheafShiftMap_injective δ B A
  rw [← toCosheaf_ψ (i.mono h)]
  calc
    (i.mono h).toCosheaf.ψ = (i.toCosheaf.mono h).ψ := by rw [mono_toCosheaf]
    _ = i.toCosheaf.ψ ≫ (smoothingMap h).app (cosheafFunctor.obj A).obj := rfl
    _ = cosheafShiftMap i.ψ ≫ (smoothingMap h).app (cosheafFunctor.obj A).obj := by
      rw [toCosheaf_ψ]
    _ = cosheafShiftMap (i.ψ ≫ (geometricEnlargement h).app A) :=
      (cosheafShiftMap_comp_geometricEnlargement h i.ψ).symm

end GeometricInterleaving

/-- Nonemptiness of geometric interleavings is monotone in the parameter. -/
theorem nonempty_mono (h : ε ≤ δ) :
    Nonempty (GeometricInterleaving ε A B) → Nonempty (GeometricInterleaving δ A B)
  | ⟨i⟩ => ⟨GeometricInterleaving.mono i h⟩

/-- Every parameter strictly above the geometric interleaving distance carries a witness. -/
theorem nonempty_of_geometricInterleavingDistance_lt {ε : ℝ≥0}
    (h : geometricInterleavingDistance A B < ε) :
    Nonempty (GeometricInterleaving ε A B) := by
  obtain ⟨ε₀, hε₀, hi⟩ := geometricInterleavingDistance_lt_iff.1 h
  exact nonempty_mono (ENNReal.coe_lt_coe.1 hε₀).le hi

/-- The geometric interleaving distance is the upper envelope of parameters carrying witnesses. -/
theorem geometricInterleavingDistance_le_iff {r : ℝ≥0∞} :
    geometricInterleavingDistance A B ≤ r ↔
      ∀ ε : ℝ≥0, r < ε → Nonempty (GeometricInterleaving ε A B) := by
  constructor
  · intro h ε hε
    exact nonempty_of_geometricInterleavingDistance_lt (h.trans_lt hε)
  · intro h
    apply le_of_forall_gt_imp_ge_of_dense
    intro a ha
    by_cases ha_top : a = ⊤
    · rw [ha_top]
      exact le_top
    · obtain ⟨ε, hrε, hεa⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
      exact (geometricInterleavingDistance_le_of_nonempty (h ε hrε)).trans hεa.le

namespace GeometricInterleaving

/-- The second component of geometric interleaving composition, written through the parameter
equality isomorphism. -/
theorem trans_ψ (i : GeometricInterleaving ε A B)
    (j : GeometricInterleaving δ B D) :
    (i.trans j).ψ =
      j.ψ ≫ (geometricSmoothing δ).map i.ψ ≫ (geometricSmoothingCompIso δ ε).hom.app A ≫
        (geometricSmoothingEqIso (add_comm δ ε)).hom.app A := by
  apply cosheafShiftMap_injective (ε + δ) D A
  rw [← toCosheaf_ψ (i.trans j), trans_toCosheaf]
  rw [geometricSmoothingEqIso_hom_eq]
  rw [← Category.assoc, ← Category.assoc]
  rw [cosheafShiftMap_comp_geometricEnlargement]
  rw [Category.assoc]
  rw [cosheafShiftMap_comp']
  rw [← toCosheaf_ψ j, ← toCosheaf_ψ i]
  rfl

/-- The second component of geometric interleaving composition, written as a band enlargement. -/
theorem trans_ψ' (i : GeometricInterleaving ε A B)
    (j : GeometricInterleaving δ B D) :
    (i.trans j).ψ =
      j.ψ ≫ (geometricSmoothing δ).map i.ψ ≫ (geometricSmoothingCompIso δ ε).hom.app A ≫
        (geometricEnlargement (add_comm δ ε).le).app A := by
  rw [← geometricSmoothingEqIso_hom_eq (add_comm δ ε)]
  exact trans_ψ i j

end GeometricInterleaving

/-- The geometric self-smoothing interleaving, transported from the component precosheaf
self-smoothing through the comparison isomorphism. -/
def GeometricInterleaving.selfSmoothing (ε : ℝ≥0) (A : RGraphCat) :
    GeometricInterleaving ε A ((geometricSmoothing ε).obj A) :=
  GeometricInterleaving.ofCosheaf
    ((Interleaving.selfSmoothing ε (cosheafFunctor.obj A).obj).isoRight
      ((geometricSmoothingPrecosheafIso ε).app A).symm)

/-- The first component of geometric self-smoothing is the two successive geometric units. -/
theorem GeometricInterleaving.selfSmoothing_φ (ε : ℝ≥0) (A : RGraphCat) :
    (GeometricInterleaving.selfSmoothing ε A).φ =
      (geometricSmoothingUnit ε).app A ≫
        (geometricSmoothingUnit ε).app ((geometricSmoothing ε).obj A) := by
  apply cosheafShiftMap_injective ε A ((geometricSmoothing ε).obj A)
  rw [← GeometricInterleaving.toCosheaf_φ (GeometricInterleaving.selfSmoothing ε A)]
  let e : (smoothing ε).obj (cosheafFunctor.obj A).obj ≅
      (cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj :=
    ((geometricSmoothingPrecosheafIso ε).app A).symm
  have hto :
      (GeometricInterleaving.selfSmoothing ε A).toCosheaf =
        (Interleaving.selfSmoothing ε (cosheafFunctor.obj A).obj).isoRight e := by
    change
      (GeometricInterleaving.ofCosheaf
        ((Interleaving.selfSmoothing ε (cosheafFunctor.obj A).obj).isoRight e)).toCosheaf =
          (Interleaving.selfSmoothing ε (cosheafFunctor.obj A).obj).isoRight e
    exact GeometricInterleaving.toCosheaf_ofCosheaf _
  rw [hto]
  rw [Interleaving.isoRight_φ]
  change
    ((smoothingUnit ε).app (cosheafFunctor.obj A).obj ≫
      (smoothingUnit ε).app ((smoothing ε).obj (cosheafFunctor.obj A).obj)) ≫
        (smoothing ε).map e.hom =
      cosheafShiftMap ((geometricSmoothingUnit ε).app A ≫
        (geometricSmoothingUnit ε).app ((geometricSmoothing ε).obj A))
  simp only [Category.assoc]
  rw [← (smoothingUnit ε).naturality e.hom]
  have hunit :
      (cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom =
        (smoothingUnit ε).app (cosheafFunctor.obj A).obj ≫
          ((geometricSmoothingPrecosheafIso ε).app A).symm.hom := by
    have h := congrArg
      (fun k => k ≫ ((geometricSmoothingPrecosheafIso ε).app A).symm.hom)
      (cosheafShiftMap_unit ε A)
    dsimp [cosheafShiftMap] at h
    rw [← geometricSmoothingPrecosheafIso_hom_app ε A] at h
    erw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at h
    exact h
  have hcomp :
      cosheafShiftMap ((geometricSmoothingUnit ε).app A ≫
        (geometricSmoothingUnit ε).app ((geometricSmoothing ε).obj A)) =
        (cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom ≫
          cosheafShiftMap ((geometricSmoothingUnit ε).app ((geometricSmoothing ε).obj A)) := by
    unfold cosheafShiftMap
    rw [Functor.map_comp]
    rfl
  calc
    (smoothingUnit ε).app (cosheafFunctor.obj A).obj ≫
        ((geometricSmoothingPrecosheafIso ε).app A).symm.hom ≫
          (smoothingUnit ε).app ((cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj) =
      (cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom ≫
        (smoothingUnit ε).app ((cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj) := by
          rw [hunit]
          exact (Category.assoc _ _ _).symm
    _ = (cosheafFunctor.map ((geometricSmoothingUnit ε).app A)).hom ≫
        cosheafShiftMap ((geometricSmoothingUnit ε).app ((geometricSmoothing ε).obj A)) := by
          rw [cosheafShiftMap_unit]
    _ = cosheafShiftMap ((geometricSmoothingUnit ε).app A ≫
        (geometricSmoothingUnit ε).app ((geometricSmoothing ε).obj A)) := hcomp.symm

/-- The second component of geometric self-smoothing is the identity. -/
theorem GeometricInterleaving.selfSmoothing_ψ (ε : ℝ≥0) (A : RGraphCat) :
    (GeometricInterleaving.selfSmoothing ε A).ψ = 𝟙 _ := by
  apply cosheafShiftMap_injective ε ((geometricSmoothing ε).obj A) A
  rw [← GeometricInterleaving.toCosheaf_ψ (GeometricInterleaving.selfSmoothing ε A)]
  let e : (smoothing ε).obj (cosheafFunctor.obj A).obj ≅
      (cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj :=
    ((geometricSmoothingPrecosheafIso ε).app A).symm
  have hto :
      (GeometricInterleaving.selfSmoothing ε A).toCosheaf =
        (Interleaving.selfSmoothing ε (cosheafFunctor.obj A).obj).isoRight e := by
    change
      (GeometricInterleaving.ofCosheaf
        ((Interleaving.selfSmoothing ε (cosheafFunctor.obj A).obj).isoRight e)).toCosheaf =
          (Interleaving.selfSmoothing ε (cosheafFunctor.obj A).obj).isoRight e
    exact GeometricInterleaving.toCosheaf_ofCosheaf _
  rw [hto]
  rw [Interleaving.isoRight_ψ]
  change
    e.inv ≫ 𝟙 _ = cosheafShiftMap (𝟙 _)
  rw [Category.comp_id]
  have e1 : (cosheafFunctor.map (𝟙 ((geometricSmoothing ε).obj A))).hom = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact (geometricSmoothingPrecosheafIso_hom_app ε A).trans
    ((Category.id_comp _).symm.trans
      (congrArg (· ≫ ((geometricSmoothingComparisonIso ε).hom.app A).hom) e1.symm))

/-- The geometric distance from a graph object to its smoothing is at most the smoothing
parameter. -/
theorem geometricInterleavingDistance_geometricSmoothing_self_le (ε : ℝ≥0) (A : RGraphCat) :
    geometricInterleavingDistance A ((geometricSmoothing ε).obj A) ≤ ε :=
  (GeometricInterleaving.selfSmoothing ε A).geometricInterleavingDistance_le

/-- Geometric smoothing is nonexpansive for the geometric interleaving distance. -/
theorem geometricInterleavingDistance_geometricSmoothing_le (ε : ℝ≥0) (A B : RGraphCat) :
    geometricInterleavingDistance ((geometricSmoothing ε).obj A)
        ((geometricSmoothing ε).obj B) ≤ geometricInterleavingDistance A B := by
  rw [geometricInterleavingDistance_eq_interleavingDistance,
    geometricInterleavingDistance_eq_interleavingDistance]
  exact interleavingDistance_geometricSmoothing_le ε A B

end RGraph

end

end TDA.Reeb
