import TDA.Sheaf.BandDirectImageStability
import TDA.Sheaf.BandSkyscraperDistance
import TDA.Topology.SubdivisionRealization

/-!
# Constant coefficients and sharpness of real direct-image stability

Vertex heights on a finite simplicial complex extend affinely on its realization. For the
constant sheaf in degree zero, the distance between the derived direct images is bounded by
the extended supremum of the height displacement. The point calculation identifies both
direct images with skyscrapers, so their distance equals the displacement.
-/

noncomputable section

open CategoryTheory DerivedCategory
open TDA.Simplicial TDA.Topology
open scoped ENNReal

namespace TDA.Sheaf.BandConvolution

attribute [local instance] Classical.propDecidable

variable (k : Type) [Ring k]

private abbrev pointCoefficients : pt.Sheaf (ModuleCat k) :=
  _root_.skyscraperSheaf PUnit.unit (ModuleCat.of k k)

/-- The constant sheaf with value `k` in degree zero on the source space. -/
abbrev constantCoefficients (X : TopCat.{0}) [HasDerivedCategory (X.Sheaf (ModuleCat k))] :
    Plus (X.Sheaf (ModuleCat k)) :=
  (Plus.singleFunctor _ 0).obj (constSh k X (pointCoefficients k))

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

/-- The real PL height given by affine interpolation of vertex values on a finite realization. -/
abbrev realizationHeight {V : Type} [Fintype V] (K : PreAbstractSimplicialComplex V)
    (h : V → ℝ) : TopCat.of (Realization K) ⟶ realLine :=
  TopCat.ofHom (SubdivisionRealization.realize h K 0)

/-- Extended sup stability for real PL heights and constant coefficients on a finite simplicial
realization. The displacements are evaluated at all points of the realization. -/
theorem distance_directImage_realizationHeight_le {V : Type} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    [HasDerivedCategory ((TopCat.of (Realization K)).Sheaf (ModuleCat k))] (h j : V → ℝ) :
    distance ((pushforwardPlus k (realizationHeight K h)).obj (constantCoefficients k _))
      ((pushforwardPlus k (realizationHeight K j)).obj (constantCoefficients k _)) ≤
        ⨆ x : Realization K, edist (realizationHeight K h x) (realizationHeight K j x) :=
  distance_directImage_le k (realizationHeight K h) (realizationHeight K j)
    (constantCoefficients k _)

/-- Extended sup stability for any bounded representatives of the two constant-coefficient
direct images of real PL heights. -/
theorem distanceB_directImage_realizationHeight_le {V : Type} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    [HasDerivedCategory ((TopCat.of (Realization K)).Sheaf (ModuleCat k))] (h j : V → ℝ)
    {A B : Bounded (realLine.Sheaf (ModuleCat k))}
    (eh : (boundedToPlus _).obj A ≅
      (pushforwardPlus k (realizationHeight K h)).obj (constantCoefficients k _))
    (ej : (boundedToPlus _).obj B ≅
      (pushforwardPlus k (realizationHeight K j)).obj (constantCoefficients k _)) :
    distanceB A B ≤
      ⨆ x : Realization K, edist (realizationHeight K h x) (realizationHeight K j x) :=
  distanceB_directImage_le k _ _ _ eh ej

section Point

variable {k} in
private def constSh_pt_iso (N : pt.Sheaf (ModuleCat k)) : constSh k pt N ≅ N := by
  have hi : toPt pt = 𝟙 pt := TopCat.ext fun x => Subsingleton.elim _ _
  let adj : TopCat.Sheaf.pullback (ModuleCat k) (toPt pt) ⊣ 𝟭 _ := by
    have ha := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat k) (toPt pt)
    rw [show TopCat.Sheaf.pushforward (ModuleCat k) (toPt pt) = 𝟭 _ by rw [hi]; rfl] at ha
    exact ha
  exact (adj.leftAdjointUniq Adjunction.id).app N

private def pushforward_ptOf_pointCoefficients_iso (a : ℝ) :
    (TopCat.Sheaf.pushforward (ModuleCat k) (ptOf (X := realLine) a)).obj (pointCoefficients k) ≅
      _root_.skyscraperSheaf a (ModuleCat.of k k) := by
  apply eqToIso
  apply ObjectProperty.FullSubcategory.ext
  exact (skyscraperPresheaf_eq_pushforward (X := realLine) a (ModuleCat.of k k)).symm

end Point

section Sharpness

variable (K : Type) [Field K]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat K))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat K))]

/-- The derived direct image of the degree-zero constant sheaf from the point is the
degree-zero skyscraper at its image. -/
def directImageConstantPointIso (a : ℝ) :
    (pushforwardPlus K (ptOf (X := realLine) a)).obj (constantCoefficients K pt) ≅
      skyscraper K a := by
  let N := pointCoefficients K
  let f := ptOf (X := realLine) a
  let G := TopCat.Sheaf.pushforward (ModuleCat K) f
  let I := singlePlus 0 N
  haveI : ∀ n, TopCat.Sheaf.IsFlasque (I.obj.X n) := by
    intro n
    by_cases h : n = 0
    · subst n
      haveI : N.IsFlasque :=
        isFlasque_skyscraperSheaf_of_hasZeroObject (X := pt) PUnit.unit (ModuleCat.of K K)
      exact isFlasque_of_iso (HomologicalComplex.singleObjXSelf _ 0 N).symm
    · exact isFlasque_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  haveI : IsIso (G.rightDerivedFunctorPlusUnit.app I) :=
    isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque f I
  haveI : IsIso ((singleRightDerivedFunctorPlusComparison G 0).app N) := by
    rw [singleRightDerivedFunctorPlusComparison_app]
    infer_instance
  exact (pushforwardPlus K f).mapIso ((Plus.singleFunctor _ 0).mapIso (constSh_pt_iso N)) ≪≫
    (asIso ((singleRightDerivedFunctorPlusComparison G 0).app N)).symm ≪≫
    (Plus.singleFunctor _ 0).mapIso (pushforward_ptOf_pointCoefficients_iso K a)

variable [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat K))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat K))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat K))]

/-- Two point maps attain the extended sup bound. Their direct images have distance
`edist a b = ENNReal.ofReal |a - b|`. -/
theorem distance_directImage_constantPoint (a b : ℝ) :
    distance ((pushforwardPlus K (ptOf (X := realLine) a)).obj (constantCoefficients K pt))
      ((pushforwardPlus K (ptOf (X := realLine) b)).obj (constantCoefficients K pt)) =
        ⨆ x : pt, edist (ptOf (X := realLine) a x) (ptOf (X := realLine) b x) := by
  rw [distance_congr (directImageConstantPointIso K a) (directImageConstantPointIso K b),
    distance_skyscraper]
  change ENNReal.ofReal |a - b| = ⨆ _ : pt, edist a b
  simp [edist_dist, Real.dist_eq]

end Sharpness

end TDA.Sheaf.BandConvolution
