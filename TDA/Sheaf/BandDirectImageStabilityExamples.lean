import TDA.Sheaf.BandDirectImageApplications

/-!
# Fixtures for real direct-image stability

The maps from the point at heights zero and one give a radius-one witness and attain the
supremum bound. The affine heights on a finite realization use the constant-coefficient bound.
-/

noncomputable section

open CategoryTheory DerivedCategory TDA.Sheaf TDA.Sheaf.BandConvolution TDA.Simplicial TDA.Topology
open scoped ENNReal

attribute [local instance] HasDerivedCategory.standard

example : Witness ℚ (zero_le_one : (0 : ℝ) ≤ 1)
    ((pushforwardPlus ℚ (ptOf (X := realLine) 0)).obj (constantCoefficients ℚ pt))
    ((pushforwardPlus ℚ (ptOf (X := realLine) 1)).obj (constantCoefficients ℚ pt)) :=
  directImageWitness ℚ zero_le_one (ptOf 0) (ptOf 1)
    (fun _ => by
      change dist (0 : ℝ) 1 ≤ 1
      norm_num [Real.dist_eq]) (constantCoefficients ℚ pt)

example :
    distance ((pushforwardPlus ℚ (ptOf (X := realLine) 0)).obj (constantCoefficients ℚ pt))
      ((pushforwardPlus ℚ (ptOf (X := realLine) 1)).obj (constantCoefficients ℚ pt)) = 1 := by
  rw [distance_directImage_constantPoint]
  change (⨆ _ : pt, edist (0 : ℝ) 1) = 1
  simp [edist_dist, Real.dist_eq]

example (K : PreAbstractSimplicialComplex (Fin 2)) (h j : Fin 2 → ℝ) :
    distance ((pushforwardPlus ℚ (realizationHeight K h)).obj (constantCoefficients ℚ _))
      ((pushforwardPlus ℚ (realizationHeight K j)).obj (constantCoefficients ℚ _)) ≤
        ⨆ x : Realization K, edist (realizationHeight K h x) (realizationHeight K j x) :=
  distance_directImage_realizationHeight_le ℚ K h j

example (a : ℝ) : Witness ℚ (le_refl (0 : ℝ))
    ((pushforwardPlus ℚ (ptOf (X := realLine) a)).obj (constantCoefficients ℚ pt))
    ((pushforwardPlus ℚ (ptOf (X := realLine) a)).obj (constantCoefficients ℚ pt)) :=
  directImageWitness ℚ le_rfl (ptOf a) (ptOf a) (fun _ => by simp) (constantCoefficients ℚ pt)

private def boundedPoint (a : ℝ) : Bounded (realLine.Sheaf (ModuleCat ℚ)) :=
  ⟨(singleFunctor _ 0).obj (skyscraperSheaf ℚ a),
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩

example : distanceB (boundedPoint 0) (boundedPoint 1) ≤ 1 := by
  have h := distanceB_directImage_le ℚ (ptOf (X := realLine) 0)
    (ptOf (X := realLine) 1) (constantCoefficients ℚ pt)
    (A := boundedPoint 0) (B := boundedPoint 1)
    (directImageConstantPointIso ℚ 0).symm (directImageConstantPointIso ℚ 1).symm
  change distanceB (boundedPoint 0) (boundedPoint 1) ≤ ⨆ _ : pt, edist (0 : ℝ) 1 at h
  simpa [edist_dist, Real.dist_eq] using h
