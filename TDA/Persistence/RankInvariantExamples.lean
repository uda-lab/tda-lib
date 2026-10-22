import TDA.Persistence.RankInvariant
import Mathlib.Data.Rat.Defs

universe u
namespace TDA.Persistence
open CategoryTheory
variable {k : Type u} [Field k]

private theorem rankEmpty (M : PModule.{u,0,u} k (Fin 0))
    [∀ i : Fin 0, FiniteDimensional k (M.obj i)] (i j : ℤ) :
    moduleRankInteger M i j = 0 := by
  unfold moduleRankInteger
  split_ifs with h
  · omega
  · rfl

private theorem noEmptyEndpoints (b d : ℕ) : ¬(b < d ∧ d ≤ 0) := by omega
-- Fixtures shared by the rank-invariant example modules; not part of the library API.
namespace RankExampleFixtures

def oneStageDiagram : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k k
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

instance oneStageFD (i : Fin 1) :
    FiniteDimensional k ((oneStageDiagram (k := k)).obj i) := by
  change FiniteDimensional k k
  infer_instance

theorem oneStageMultiplicity (M : PModule.{u,0,u} k (Fin 1))
    [∀ i : Fin 1, FiniteDimensional k (M.obj i)] :
    moduleMultiplicityInteger M 0 1 = Module.finrank k (M.obj 0) := by
  have hself := moduleRankInteger_fin M (0 : Fin 1) (0 : Fin 1) (le_refl _)
  have hr : structureMapRank M (0 : Fin 1) 0 (le_refl _) =
      Module.finrank k (M.obj 0) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  simp only [moduleMultiplicityInteger, Nat.cast_zero, Nat.cast_one]
  norm_num only
  simp only [moduleRankInteger_neg_one]
  rw [show moduleRankInteger M 0 1 = 0 from moduleRankInteger_at_size M 0]
  change moduleRankInteger M 0 0 = _ at hself
  rw [hself, hr]
  ring

theorem oneStageField : moduleMultiplicityInteger (oneStageDiagram (k := k)) 0 1 = 1 := by
  rw [oneStageMultiplicity]
  change ((Module.finrank k k : ℕ) : ℤ) = 1
  rw [Module.finrank_self]
  rfl

theorem oneStageZeroFiber (M : PModule.{u,0,u} k (Fin 1))
    [∀ i : Fin 1, FiniteDimensional k (M.obj i)]
    [Subsingleton (M.obj (0 : Fin 1))] : moduleMultiplicityInteger M 0 1 = 0 := by
  rw [oneStageMultiplicity]
  exact_mod_cast Module.finrank_zero_of_subsingleton (R := k) (M := M.obj (0 : Fin 1))


def oneStageZeroDiagram : PModule.{u,0,u} k (Fin 1) where
  obj _ := ModuleCat.of k (Fin 0 → k)
  map _ := 𝟙 _
  map_id _ := by simp
  map_comp _ _ := by simp

instance oneStageZeroFD (i : Fin 1) :
    FiniteDimensional k ((oneStageZeroDiagram (k := k)).obj i) := by
  change FiniteDimensional k (Fin 0 → k)
  infer_instance

theorem oneStageZero : moduleMultiplicityInteger (oneStageZeroDiagram (k := k)) 0 1 = 0 := by
  have hzero : Subsingleton ((oneStageZeroDiagram (k := k)).obj (0 : Fin 1)) := by
    change Subsingleton (Fin 0 → k)
    infer_instance
  exact @oneStageZeroFiber k _ (oneStageZeroDiagram (k := k))
    (fun i => oneStageZeroFD i) hzero

theorem twoStageValues (M : PModule.{u,0,u} k (Fin 2))
    [∀ i : Fin 2, FiniteDimensional k (M.obj i)] :
    moduleMultiplicityInteger M 0 1 =
      (Module.finrank k (M.obj (0 : Fin 2)) : ℤ) -
        structureMapRank M 0 1 (by decide) ∧
    moduleMultiplicityInteger M 0 2 =
      (structureMapRank M 0 1 (by decide) : ℤ) ∧
    moduleMultiplicityInteger M 1 2 =
      (Module.finrank k (M.obj (1 : Fin 2)) : ℤ) -
        structureMapRank M 0 1 (by decide) := by
  have h00 := moduleRankInteger_fin M (0 : Fin 2) 0 (le_refl _)
  have h01 := moduleRankInteger_fin M (0 : Fin 2) 1 (by decide)
  have h11 := moduleRankInteger_fin M (1 : Fin 2) 1 (le_refl _)
  have h0 : structureMapRank M 0 0 (le_refl (0 : Fin 2)) =
      Module.finrank k (M.obj 0) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  have h1 : structureMapRank M 1 1 (le_refl (1 : Fin 2)) =
      Module.finrank k (M.obj 1) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  simp only [moduleMultiplicityInteger, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  norm_num only
  simp only [moduleRankInteger_neg_one]
  rw [show moduleRankInteger M 0 2 = 0 from moduleRankInteger_at_size M 0,
    show moduleRankInteger M 1 2 = 0 from moduleRankInteger_at_size M 1]
  change moduleRankInteger M 0 0 = _ at h00
  change moduleRankInteger M 0 1 = _ at h01
  change moduleRankInteger M 1 1 = _ at h11
  rw [h00, h01, h11, h0, h1]
  constructor
  · ring
  · constructor <;> ring

instance identityTwoStageFD (i : Fin 2) :
    FiniteDimensional k ((identityTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

instance zeroTwoStageFD (i : Fin 2) :
    FiniteDimensional k ((zeroTransitionDiagram k).obj i) := by
  change FiniteDimensional k k
  infer_instance

theorem identityTwoStageRanks :
    structureMapRank (identityTransitionDiagram k) 0 1 (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = 1
  rw [LinearMap.range_id, finrank_top]
  exact Module.finrank_self k

theorem zeroTwoStageRanks :
    structureMapRank (zeroTransitionDiagram k) 0 1 (by decide) = 0 := by
  change Module.finrank k (LinearMap.range (0 : k →ₗ[k] k)) = 0
  simp

theorem identityTwoStage :
    moduleMultiplicityInteger (identityTransitionDiagram k) 0 1 = 0 ∧
    moduleMultiplicityInteger (identityTransitionDiagram k) 0 2 = 1 ∧
    moduleMultiplicityInteger (identityTransitionDiagram k) 1 2 = 0 := by
  have h := twoStageValues (identityTransitionDiagram k)
  rw [identityTwoStageRanks] at h
  simpa only [show Module.finrank k ((identityTransitionDiagram k).obj (0 : Fin 2)) = 1
      from Module.finrank_self k,
    show Module.finrank k ((identityTransitionDiagram k).obj (1 : Fin 2)) = 1
      from Module.finrank_self k, Nat.cast_one, sub_self] using h

theorem zeroTwoStage :
    moduleMultiplicityInteger (zeroTransitionDiagram k) 0 1 = 1 ∧
    moduleMultiplicityInteger (zeroTransitionDiagram k) 0 2 = 0 ∧
    moduleMultiplicityInteger (zeroTransitionDiagram k) 1 2 = 1 := by
  have h := twoStageValues (zeroTransitionDiagram k)
  rw [zeroTwoStageRanks] at h
  simpa only [show Module.finrank k ((zeroTransitionDiagram k).obj (0 : Fin 2)) = 1
      from Module.finrank_self k,
    show Module.finrank k ((zeroTransitionDiagram k).obj (1 : Fin 2)) = 1
      from Module.finrank_self k, Nat.cast_one, Nat.cast_zero, sub_zero] using h

end RankExampleFixtures

open RankExampleFixtures

private def threeStageDiagram (f : k →ₗ[k] k × k) (g : (k × k) →ₗ[k] k) :
    PModule.{u,0,u} k (Fin 3) where
  obj i := if i.val = 1 then ModuleCat.of k (k × k) else ModuleCat.of k k
  map {p q} h := by
    rcases p with ⟨p, hp⟩
    rcases q with ⟨q, hq⟩
    interval_cases p <;> interval_cases q
    · exact 𝟙 _
    · exact ModuleCat.ofHom f
    · exact ModuleCat.ofHom (g.comp f)
    · have hh : (1 : Fin 3) ≤ 0 := leOfHom h
      exact False.elim ((by decide : ¬(1 : Fin 3) ≤ 0) hh)
    · exact 𝟙 _
    · exact ModuleCat.ofHom g
    · have hh : (2 : Fin 3) ≤ 0 := leOfHom h
      exact False.elim ((by decide : ¬(2 : Fin 3) ≤ 0) hh)
    · have hh : (2 : Fin 3) ≤ 1 := leOfHom h
      exact False.elim ((by decide : ¬(2 : Fin 3) ≤ 1) hh)
    · exact 𝟙 _
  map_id i := by
    fin_cases i <;> apply ModuleCat.hom_ext <;> rfl
  map_comp {i j l} h1 h2 := by
    apply ModuleCat.hom_ext
    fin_cases i <;> fin_cases j <;> fin_cases l
    all_goals
      have hi := leOfHom h1
      have hj := leOfHom h2
      simp_all [Fin.le_iff_val_le_val]

private def includeFirst : k →ₗ[k] k × k :=
  { toFun := fun x => (x, 0)
    map_add' := by intros; ext <;> simp
    map_smul' := by intros; ext <;> simp }

private def projectFirst : (k × k) →ₗ[k] k := LinearMap.fst k k k
private def projectSecond : (k × k) →ₗ[k] k := LinearMap.snd k k k

private instance threeStageFD (f : k →ₗ[k] k × k) (g : (k × k) →ₗ[k] k)
    (i : Fin 3) : FiniteDimensional k ((threeStageDiagram f g).obj i) := by
  fin_cases i
  · change FiniteDimensional k k; infer_instance
  · change FiniteDimensional k (k × k); infer_instance
  · change FiniteDimensional k k; infer_instance

private theorem threeStageValues (M : PModule.{u,0,u} k (Fin 3))
    [∀ i : Fin 3, FiniteDimensional k (M.obj i)] :
    moduleMultiplicityInteger M 1 2 =
      (structureMapRank M 1 1 (by decide) : ℤ) -
      structureMapRank M 0 1 (by decide) -
      structureMapRank M 1 2 (by decide) +
      structureMapRank M 0 2 (by decide) ∧
    moduleMultiplicityInteger M 0 2 =
      (structureMapRank M 0 1 (by decide) : ℤ) -
      structureMapRank M 0 2 (by decide) := by
  have h01 := moduleRankInteger_fin M (0 : Fin 3) 1 (by decide)
  have h02 := moduleRankInteger_fin M (0 : Fin 3) 2 (by decide)
  have h11 := moduleRankInteger_fin M (1 : Fin 3) 1 (by decide)
  have h12 := moduleRankInteger_fin M (1 : Fin 3) 2 (by decide)
  simp only [moduleMultiplicityInteger, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  norm_num only
  simp only [moduleRankInteger_neg_one]
  change moduleRankInteger M 0 1 = _ at h01
  change moduleRankInteger M 0 2 = _ at h02
  change moduleRankInteger M 1 1 = _ at h11
  change moduleRankInteger M 1 2 = _ at h12
  rw [h01, h02, h11, h12]
  constructor <;> ring

private theorem includeFirst_injective : Function.Injective (includeFirst (k := k)) := by
  intro x y h
  exact congrArg Prod.fst h

private theorem threeRank01 (g : (k × k) →ₗ[k] k) :
    structureMapRank (threeStageDiagram (includeFirst (k := k)) g) 0 1
      (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (includeFirst (k := k))) = 1
  rw [LinearMap.finrank_range_of_inj includeFirst_injective]
  exact Module.finrank_self k

private theorem threeRank11 (g : (k × k) →ₗ[k] k) :
    structureMapRank (threeStageDiagram (includeFirst (k := k)) g) 1 1
      (by decide) = 2 := by
  rw [show structureMapRank (threeStageDiagram (includeFirst (k := k)) g) 1 1
      (by decide) = Module.finrank k (k × k) by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
    rfl]
  simp

private theorem threeRank12First :
    structureMapRank (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k)))
      1 2 (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (projectFirst (k := k))) = 1
  rw [LinearMap.range_eq_top_of_surjective]
  · rw [finrank_top]
    exact Module.finrank_self k
  · intro y
    exact ⟨(y, 0), rfl⟩

private theorem threeRank12Second :
    structureMapRank (threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k)))
      1 2 (by decide) = 1 := by
  change Module.finrank k (LinearMap.range (projectSecond (k := k))) = 1
  rw [LinearMap.range_eq_top_of_surjective]
  · rw [finrank_top]
    exact Module.finrank_self k
  · intro y
    exact ⟨(0, y), rfl⟩

private theorem threeRank02First :
    structureMapRank (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k)))
      0 2 (by decide) = 1 := by
  have he : (projectFirst (k := k)).comp (includeFirst (k := k)) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    rfl
  change Module.finrank k (LinearMap.range
    ((projectFirst (k := k)).comp (includeFirst (k := k)))) = 1
  rw [he, LinearMap.range_id, finrank_top]
  exact Module.finrank_self k

private theorem threeRank02Second :
    structureMapRank (threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k)))
      0 2 (by decide) = 0 := by
  have he : (projectSecond (k := k)).comp (includeFirst (k := k)) = 0 := by
    apply LinearMap.ext
    intro x
    rfl
  change Module.finrank k (LinearMap.range
    ((projectSecond (k := k)).comp (includeFirst (k := k)))) = 0
  rw [he]
  simp

private theorem threeStageFirst :
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k))) 1 2 = 1 ∧
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k))) 0 2 = 0 := by
  have h := threeStageValues
    (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k)))
  rw [threeRank11, threeRank01, threeRank12First, threeRank02First] at h
  norm_num at h
  exact h

private theorem threeStageSecond :
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k))) 1 2 = 0 ∧
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k))) 0 2 = 1 := by
  have h := threeStageValues
    (threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k)))
  rw [threeRank11, threeRank01, threeRank12Second, threeRank02Second] at h
  norm_num at h
  exact h

private theorem firstRestrictedKernel :
    Module.finrank k (LinearMap.ker
      ((structureMapLinear
        (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k)))
        (show (1 : Fin 3) ≤ 2 by decide)).comp
        (LinearMap.range (structureMapLinear
          (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k)))
          (show (0 : Fin 3) ≤ 1 by decide))).subtype)) = 0 := by
  let M := threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k))
  have h := structureMapRank_drop M (0 : Fin 3) 1 2 (by decide) (by decide)
  rw [threeRank01, threeRank02First] at h
  change 1 = 1 + Module.finrank k (LinearMap.ker
    ((structureMapLinear M (show (1 : Fin 3) ≤ 2 by decide)).comp
      (LinearMap.range (structureMapLinear M (show (0 : Fin 3) ≤ 1 by decide))).subtype)) at h
  change Module.finrank k (LinearMap.ker
    ((structureMapLinear M (show (1 : Fin 3) ≤ 2 by decide)).comp
      (LinearMap.range (structureMapLinear M (show (0 : Fin 3) ≤ 1 by decide))).subtype)) = 0
  omega

private theorem firstFullKernel :
    Module.finrank k (LinearMap.ker
      ((structureMapLinear
        (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k)))
        (show (1 : Fin 3) ≤ 2 by decide)).comp
        (LinearMap.range (structureMapLinear
          (threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k)))
          (show (1 : Fin 3) ≤ 1 by decide))).subtype)) = 1 := by
  let M := threeStageDiagram (includeFirst (k := k)) (projectFirst (k := k))
  have h := structureMapRank_drop M (1 : Fin 3) 1 2 (by decide) (by decide)
  rw [threeRank11, threeRank12First] at h
  change 2 = 1 + Module.finrank k (LinearMap.ker
    ((structureMapLinear M (show (1 : Fin 3) ≤ 2 by decide)).comp
      (LinearMap.range (structureMapLinear M (show (1 : Fin 3) ≤ 1 by decide))).subtype)) at h
  change Module.finrank k (LinearMap.ker
    ((structureMapLinear M (show (1 : Fin 3) ≤ 2 by decide)).comp
      (LinearMap.range (structureMapLinear M (show (1 : Fin 3) ≤ 1 by decide))).subtype)) = 1
  omega

private theorem secondRestrictedKernel :
    Module.finrank k (LinearMap.ker
      ((structureMapLinear
        (threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k)))
        (show (1 : Fin 3) ≤ 2 by decide)).comp
        (LinearMap.range (structureMapLinear
          (threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k)))
          (show (0 : Fin 3) ≤ 1 by decide))).subtype)) = 1 := by
  let M := threeStageDiagram (includeFirst (k := k)) (projectSecond (k := k))
  have h := structureMapRank_drop M (0 : Fin 3) 1 2 (by decide) (by decide)
  rw [threeRank01, threeRank02Second] at h
  change 1 = 0 + Module.finrank k (LinearMap.ker
    ((structureMapLinear M (show (1 : Fin 3) ≤ 2 by decide)).comp
      (LinearMap.range (structureMapLinear M (show (0 : Fin 3) ≤ 1 by decide))).subtype)) at h
  change Module.finrank k (LinearMap.ker
    ((structureMapLinear M (show (1 : Fin 3) ≤ 2 by decide)).comp
      (LinearMap.range (structureMapLinear M (show (0 : Fin 3) ≤ 1 by decide))).subtype)) = 1
  omega

private theorem firstRat :
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := ℚ)) (projectFirst (k := ℚ))) 1 2 = 1 :=
  (threeStageFirst (k := ℚ)).1
private theorem secondRat :
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := ℚ)) (projectSecond (k := ℚ))) 0 2 = 1 :=
  (threeStageSecond (k := ℚ)).2
private theorem firstZModTwo :
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := ZMod 2)) (projectFirst (k := ZMod 2))) 1 2 = 1 :=
  (threeStageFirst (k := ZMod 2)).1
private theorem secondZModTwo :
    moduleMultiplicityInteger
      (threeStageDiagram (includeFirst (k := ZMod 2)) (projectSecond (k := ZMod 2))) 0 2 = 1 :=
  (threeStageSecond (k := ZMod 2)).2
private theorem twoRat : moduleMultiplicityInteger (identityTransitionDiagram ℚ) 0 2 = 1 :=
  (identityTwoStage (k := ℚ)).2.1
private theorem twoZModTwo :
    moduleMultiplicityInteger (zeroTransitionDiagram (ZMod 2)) 0 1 = 1 :=
  (zeroTwoStage (k := ZMod 2)).1
