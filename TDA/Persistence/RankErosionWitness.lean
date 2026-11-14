import TDA.Persistence.RankErosionInterleaving
import TDA.Persistence.FinitePresentationClosure
import TDA.Persistence.HookInfinity

/-!
# Rank witnesses against coordinate interleavings

A failed weak-pair rank inequality excludes an interleaving at that radius.
Finite-presentation attainment turns this into a strict distance lower bound.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal ENNReal ZeroObject

variable {k : Type u} [Field k] {n : ℕ}
variable {M N : PModule.{u,0,u} k (Fin n → ℝ)}

/-- A concrete strict rank comparison rules out an interleaving at that radius. -/
theorem no_coordinateInterleaving_of_rank_violation {ε : ℝ≥0}
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    {a b : Fin n → ℝ} (hab : a ≤ b)
    (h : rankOfStructureMap N hab < rankOfStructureMap M (erosionWide_le ε hab)) :
    ¬ Nonempty (CoordinateInterleaving ε M N) := by
  rintro ⟨I⟩
  exact (not_le.mpr h) (I.rank_erosion_le a b hab)

/-- Without attainment, a rank violation gives a non-strict distance bound. -/
theorem radius_le_coordinateInterleavingDistance_of_rank_violation {ε : ℝ≥0}
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    {a b : Fin n → ℝ} (hab : a ≤ b)
    (h : rankOfStructureMap N hab < rankOfStructureMap M (erosionWide_le ε hab)) :
    (ε : ℝ≥0∞) ≤ coordinateInterleavingDistance M N := by
  apply le_coordinateInterleavingDistance_iff.mpr
  intro δ ⟨I⟩
  by_contra hn
  exact no_coordinateInterleaving_of_rank_violation hab h
    ⟨I.mono (ENNReal.coe_lt_coe.mp (lt_of_not_ge hn)).le⟩

/-- Finite-presentation attainment makes the same obstruction strict, even if
the interleaving distance is infinite. -/
theorem radius_lt_coordinateInterleavingDistance_of_rank_violation {ε : ℝ≥0}
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (hM : GradedFree.FinitelyPresented (R := k) M)
    (hN : GradedFree.FinitelyPresented (R := k) N)
    {a b : Fin n → ℝ} (hab : a ≤ b)
    (h : rankOfStructureMap N hab < rankOfStructureMap M (erosionWide_le ε hab)) :
    (ε : ℝ≥0∞) < coordinateInterleavingDistance M N := by
  apply lt_of_not_ge
  intro hdist
  exact no_coordinateInterleaving_of_rank_violation hab h
    ((GradedFree.finitelyPresented_distance_le_iff_interleaving hM hN ε).mp hdist)

namespace RankErosionWitness

variable {n : ℕ}

private def origin : Fin n → ℝ := fun _ => 0

/-- The zero module satisfies erosion at every radius, even over `Fin 0`. -/
theorem zeroModule_self (ε : ℝ≥0) :
    RankErosion ε (0 : PModule.{0,0,0} ℚ (Fin n → ℝ)) 0 := by
  constructor <;> intro a b hab <;> simp

/-- The principal upset born at the origin has rank one on its diagonal map. -/
theorem originHook_diagonal_rank :
    rankOfStructureMap (HookInfinity.module (R := ℚ) (origin (n := n)))
      (le_refl (origin (n := n))) = 1 := by
  unfold rankOfStructureMap
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact ((HookInfinity.fiberEquivOfLe (R := ℚ)
    (i := origin (n := n)) (a := origin (n := n)) le_rfl).finrank_eq).trans
    (by simp)

/-- Every actual structure map entirely within the principal upset has rank one. -/
theorem originHook_supported_rank {a b : Fin n → ℝ}
    (ha : origin (n := n) ≤ a) (hab : a ≤ b) :
    rankOfStructureMap (HookInfinity.module (R := ℚ) (origin (n := n))) hab = 1 := by
  unfold rankOfStructureMap
  have hinj : Function.Injective
      (structureMapLinear (HookInfinity.module (R := ℚ) (origin (n := n))) hab) := by
    intro x y hxy
    apply (HookInfinity.fiberEquivOfLe (R := ℚ) ha).injective
    calc
      HookInfinity.fiberEquivOfLe ha x =
          HookInfinity.fiberEquivOfLe (ha.trans hab)
            (structureMapLinear (HookInfinity.module (R := ℚ) (origin (n := n))) hab x) :=
        (HookInfinity.fiberEquivOfLe_structureMap ha hab x).symm
      _ = HookInfinity.fiberEquivOfLe (ha.trans hab)
            (structureMapLinear (HookInfinity.module (R := ℚ) (origin (n := n))) hab y) :=
        congrArg _ hxy
      _ = HookInfinity.fiberEquivOfLe ha y :=
        HookInfinity.fiberEquivOfLe_structureMap ha hab y
  rw [LinearMap.finrank_range_of_inj hinj]
  exact ((HookInfinity.fiberEquivOfLe (R := ℚ) ha).finrank_eq).trans (by simp)

/-- A diagonal weak-pair witness excludes zero interleaving with zero, including
when the coordinate set is empty. -/
theorem originHook_no_zero_interleaving :
    ¬ Nonempty (CoordinateInterleaving 0
      (HookInfinity.module (R := ℚ) (origin (n := n))) 0) := by
  letI : ∀ p, FiniteDimensional ℚ
      ((HookInfinity.module (R := ℚ) (origin (n := n))).obj p) :=
    fun p => HookInfinity.finiteDimensional (origin (n := n)) p
  letI : ∀ p, Subsingleton ((0 : PModule.{0,0,0} ℚ (Fin n → ℝ)).obj p) :=
    fun p => ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
  letI : ∀ p, FiniteDimensional ℚ
      ((0 : PModule.{0,0,0} ℚ (Fin n → ℝ)).obj p) := fun _ => inferInstance
  apply no_coordinateInterleaving_of_rank_violation
    (M := HookInfinity.module (R := ℚ) (origin (n := n)))
    (N := 0) (hab := le_refl (origin (n := n)))
  simp only [rankOfStructureMap_zero]
  have hrank := originHook_diagonal_rank (n := n)
  have hzero : erosionLower 0 (origin (n := n)) = origin (n := n) := by
    funext i; simp [erosionLower]
  have hone : erosionUpper 0 (origin (n := n)) = origin (n := n) := by
    funext i; simp [erosionUpper]
  simpa only [hzero, hone, hrank] using (show 0 < (1 : ℕ) by decide)

example : ¬ Nonempty (CoordinateInterleaving 0
    (HookInfinity.module (R := ℚ) (origin (n := 0))) 0) :=
  originHook_no_zero_interleaving (n := 0)

/-- Positive-radius obstruction on a genuinely off-diagonal pair. -/
theorem originHook_positive_radius_no_interleaving :
    ¬ Nonempty (CoordinateInterleaving 1
      (HookInfinity.module (R := ℚ) (origin (n := 1))) 0) := by
  let a : Fin 1 → ℝ := fun _ => 1
  let b : Fin 1 → ℝ := fun _ => 2
  have hab : a ≤ b := by intro i; norm_num [a, b]
  have ha : origin (n := 1) ≤ erosionLower 1 a := by
    intro i
    norm_num [origin, erosionLower, a]
  letI : ∀ p, FiniteDimensional ℚ
      ((HookInfinity.module (R := ℚ) (origin (n := 1))).obj p) :=
    fun p => HookInfinity.finiteDimensional (origin (n := 1)) p
  letI : ∀ p, Subsingleton ((0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)).obj p) :=
    fun p => ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
  letI : ∀ p, FiniteDimensional ℚ
      ((0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)).obj p) := fun _ => inferInstance
  apply no_coordinateInterleaving_of_rank_violation
    (M := HookInfinity.module (R := ℚ) (origin (n := 1)))
    (N := 0) (hab := hab)
  rw [rankOfStructureMap_zero, originHook_supported_rank ha (erosionWide_le 1 hab)]
  decide

end RankErosionWitness

end TDA.Persistence
