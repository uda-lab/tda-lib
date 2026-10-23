import TDA.Persistence.RankReconstruction
import TDA.Persistence.RankInvariantExamples
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic

universe u
namespace TDA.Persistence
open CategoryTheory
open scoped BigOperators
variable {k : Type u} [Field k]
open RankExampleFixtures

private theorem ioc01 : Finset.Ioc (0 : ℕ) 1 = {1} := by decide
private theorem ioc02 : Finset.Ioc (0 : ℕ) 2 = {1, 2} := by decide
private theorem ioc12 : Finset.Ioc (1 : ℕ) 2 = {2} := by decide
private theorem range2 : Finset.range 2 = {0, 1} := by decide

private theorem emptyRectangle (M : PModule.{u,0,u} k (Fin 0))
    [∀ i : Fin 0, FiniteDimensional k (M.obj i)] :
    (∑ x ∈ Finset.Icc 0 0, ∑ y ∈ Finset.Ioc 0 0,
      moduleMultiplicityInteger M x y) = 0 := by
  simp

private theorem oneStageReconstruction (M : PModule.{u,0,u} k (Fin 1))
    [∀ i : Fin 1, FiniteDimensional k (M.obj i)] :
    (structureMapRank M 0 0 (le_refl _) : ℤ) = moduleMultiplicityInteger M 0 1 := by
  simpa [ioc01] using
    structureMapRank_eq_sum_moduleMultiplicityInteger M 0 0 (le_refl _)

private theorem oneStageFieldReconstruction :
    (structureMapRank (oneStageDiagram (k := k)) 0 0 (le_refl _) : ℤ) = 1 := by
  rw [oneStageReconstruction, oneStageField]

private theorem oneStageZeroReconstruction :
    (structureMapRank (oneStageZeroDiagram (k := k)) 0 0 (le_refl _) : ℤ) = 0 := by
  rw [oneStageReconstruction, oneStageZero]

private theorem emptyDeathRectangle (M : PModule.{u,0,u} k (Fin 2))
    [∀ i : Fin 2, FiniteDimensional k (M.obj i)] :
    (∑ x ∈ Finset.Icc 0 0, ∑ y ∈ Finset.Ioc 1 1,
      moduleMultiplicityInteger M x y) = 0 := by
  simp

private theorem singleBirthRectangle (M : PModule.{u,0,u} k (Fin 2))
    [∀ i : Fin 2, FiniteDimensional k (M.obj i)] :
    (∑ x ∈ Finset.Icc 0 0, ∑ y ∈ Finset.Ioc 0 2,
      moduleMultiplicityInteger M x y) =
      (structureMapRank M 0 0 (le_refl _) : ℤ) := by
  have h := moduleMultiplicityInteger_sum_rectangle M 0 0 0 2
    (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.cast_zero, Nat.cast_ofNat, zero_sub] at h
  have hneg := moduleRankInteger_neg_one M (2 : ℤ)
  have hneg0 := moduleRankInteger_neg_one M (0 : ℤ)
  have hterm := moduleRankInteger_at_size M (0 : ℤ)
  change moduleRankInteger M 0 2 = 0 at hterm
  have hself := moduleRankInteger_fin M (0 : Fin 2) 0 (le_refl _)
  change moduleRankInteger M 0 0 = _ at hself
  rw [hneg, hneg0, hterm, hself] at h
  simpa using h

private theorem identityReconstruction :
    (structureMapRank (identityTransitionDiagram k) 0 0 (le_refl _) : ℤ) = 1 ∧
    (structureMapRank (identityTransitionDiagram k) 0 1 (by decide) : ℤ) = 1 ∧
    (structureMapRank (identityTransitionDiagram k) 1 1 (le_refl _) : ℤ) = 1 := by
  have hm := identityTwoStage (k := k)
  constructor
  · rw [structureMapRank_eq_sum_moduleMultiplicityInteger]
    simp [Finset.range_one, ioc02, hm.1, hm.2.1]
  constructor
  · rw [structureMapRank_eq_sum_moduleMultiplicityInteger]
    simp [Finset.range_one, hm.2.1]
  · rw [structureMapRank_eq_sum_moduleMultiplicityInteger]
    simp [range2, hm.2.1, hm.2.2]

private theorem zeroReconstruction :
    (structureMapRank (zeroTransitionDiagram k) 0 0 (le_refl _) : ℤ) = 1 ∧
    (structureMapRank (zeroTransitionDiagram k) 0 1 (by decide) : ℤ) = 0 ∧
    (structureMapRank (zeroTransitionDiagram k) 1 1 (le_refl _) : ℤ) = 1 := by
  have hm := zeroTwoStage (k := k)
  constructor
  · rw [structureMapRank_eq_sum_moduleMultiplicityInteger]
    simp [Finset.range_one, ioc02, hm.1, hm.2.1]
  constructor
  · rw [structureMapRank_eq_sum_moduleMultiplicityInteger]
    simp [Finset.range_one, hm.2.1]
  · rw [structureMapRank_eq_sum_moduleMultiplicityInteger]
    simp [range2, hm.2.1, hm.2.2]

private theorem truncatedContrast :
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (identityTransitionDiagram k) b d) = 0 ∧
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (zeroTransitionDiagram k) b d) = 1 := by
  constructor
  · simpa only [Finset.range_one, ioc01, Finset.sum_singleton] using
      (identityTwoStage (k := k)).1
  · simpa only [Finset.range_one, ioc01, Finset.sum_singleton] using
      (zeroTwoStage (k := k)).1

private def doubleIdentityDiagram : PModule.{u,0,u} k (Fin 2) where
  obj _ := ModuleCat.of k (k × k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

private instance doubleIdentityFD (i : Fin 2) :
    FiniteDimensional k ((doubleIdentityDiagram (k := k)).obj i) := by
  change FiniteDimensional k (k × k)
  infer_instance

private theorem doubleTransitionRank :
    structureMapRank (doubleIdentityDiagram (k := k)) 0 1 (by decide) = 2 := by
  change Module.finrank k (LinearMap.range (LinearMap.id : (k × k) →ₗ[k] (k × k))) = 2
  rw [LinearMap.range_id, finrank_top, Module.finrank_prod, Module.finrank_self]

private theorem doubleMultiplicity :
    moduleMultiplicityInteger (doubleIdentityDiagram (k := k)) 0 1 = 0 ∧
    moduleMultiplicityInteger (doubleIdentityDiagram (k := k)) 0 2 = 2 ∧
    moduleMultiplicityInteger (doubleIdentityDiagram (k := k)) 1 2 = 0 := by
  have h := twoStageValues (doubleIdentityDiagram (k := k))
  rw [doubleTransitionRank] at h
  have hdim : Module.finrank k (k × k) = 2 := by
    simp [Module.finrank_prod]
  have hdim0 : Module.finrank k ((doubleIdentityDiagram (k := k)).obj (0 : Fin 2)) = 2 := hdim
  have hdim1 : Module.finrank k ((doubleIdentityDiagram (k := k)).obj (1 : Fin 2)) = 2 := hdim
  simpa only [hdim0, hdim1, Nat.cast_ofNat, sub_self] using h

private theorem doubleReconstruction :
    (structureMapRank (doubleIdentityDiagram (k := k)) 0 1 (by decide) : ℤ) =
      ∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 1 2,
        moduleMultiplicityInteger (doubleIdentityDiagram (k := k)) b d := by
  exact structureMapRank_eq_sum_moduleMultiplicityInteger
    (doubleIdentityDiagram (k := k)) 0 1 (by decide)

private theorem doubleReconstructionEvaluated :
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 1 2,
      moduleMultiplicityInteger (doubleIdentityDiagram (k := k)) b d) = 2 := by
  rw [← doubleReconstruction]
  exact_mod_cast doubleTransitionRank (k := k)

private theorem rationalFixtures :
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (identityTransitionDiagram ℚ) b d) = 0 ∧
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (zeroTransitionDiagram ℚ) b d) = 1 ∧
    moduleMultiplicityInteger (doubleIdentityDiagram (k := ℚ)) 0 2 = 2 ∧
    (structureMapRank (doubleIdentityDiagram (k := ℚ)) 0 1 (by decide) : ℤ) = 2 ∧
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 1 2,
      moduleMultiplicityInteger (doubleIdentityDiagram (k := ℚ)) b d) = 2 := by
  exact ⟨(truncatedContrast (k := ℚ)).1, (truncatedContrast (k := ℚ)).2,
    (doubleMultiplicity (k := ℚ)).2.1,
    by exact_mod_cast (doubleTransitionRank (k := ℚ)),
    doubleReconstructionEvaluated (k := ℚ)⟩

private theorem binaryFixtures :
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (identityTransitionDiagram (ZMod 2)) b d) = 0 ∧
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 0 1,
      moduleMultiplicityInteger (zeroTransitionDiagram (ZMod 2)) b d) = 1 ∧
    moduleMultiplicityInteger (doubleIdentityDiagram (k := ZMod 2)) 0 2 = 2 ∧
    (structureMapRank (doubleIdentityDiagram (k := ZMod 2)) 0 1 (by decide) : ℤ) = 2 ∧
    (∑ b ∈ Finset.range 1, ∑ d ∈ Finset.Ioc 1 2,
      moduleMultiplicityInteger (doubleIdentityDiagram (k := ZMod 2)) b d) = 2 := by
  exact ⟨(truncatedContrast (k := ZMod 2)).1, (truncatedContrast (k := ZMod 2)).2,
    (doubleMultiplicity (k := ZMod 2)).2.1,
    by exact_mod_cast (doubleTransitionRank (k := ZMod 2)),
    doubleReconstructionEvaluated (k := ZMod 2)⟩

end TDA.Persistence
