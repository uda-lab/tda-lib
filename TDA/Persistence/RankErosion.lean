import TDA.Persistence.FiniteRankProjectiveResolution
import TDA.Persistence.CoordinateInterleavingDistance
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
# Weak-pair rank erosion

For pointwise finite-dimensional modules, erosion compares the ranks of structure
maps on all weak pairs of coordinate grades. In particular, diagonal ranks remain
part of the comparison. The distance is an extended pseudometric.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CoordinateShift
open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k] {n : ℕ}
variable {M N P : PModule.{u,0,u} k (Fin n → ℝ)}

/-- Lower every coordinate by a nonnegative radius. -/
def erosionLower (ε : ℝ≥0) (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a i - (ε : ℝ)

/-- Raise every coordinate by a nonnegative radius. -/
def erosionUpper (ε : ℝ≥0) (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a i + (ε : ℝ)

@[simp] theorem erosionLower_zero (a : Fin n → ℝ) : erosionLower 0 a = a := by
  funext i
  simp [erosionLower]

@[simp] theorem erosionUpper_zero (a : Fin n → ℝ) : erosionUpper 0 a = a := by
  funext i
  simp [erosionUpper]

theorem erosionLower_le (ε : ℝ≥0) (a : Fin n → ℝ) : erosionLower ε a ≤ a := by
  intro i
  change a i - (ε : ℝ) ≤ a i
  exact sub_le_self _ ε.coe_nonneg

theorem le_erosionUpper (ε : ℝ≥0) (a : Fin n → ℝ) : a ≤ erosionUpper ε a := by
  intro i
  change a i ≤ a i + (ε : ℝ)
  exact le_add_of_nonneg_right ε.coe_nonneg

theorem erosionWide_le (ε : ℝ≥0) {a b : Fin n → ℝ} (hab : a ≤ b) :
    erosionLower ε a ≤ erosionUpper ε b :=
  (erosionLower_le ε a).trans (hab.trans (le_erosionUpper ε b))

theorem erosionLower_add (ε δ : ℝ≥0) (a : Fin n → ℝ) :
    erosionLower ε (erosionLower δ a) = erosionLower (ε + δ) a := by
  funext i
  simp [erosionLower, NNReal.coe_add, sub_add_eq_sub_sub]
  ring

theorem erosionUpper_add (ε δ : ℝ≥0) (a : Fin n → ℝ) :
    erosionUpper ε (erosionUpper δ a) = erosionUpper (ε + δ) a := by
  funext i
  simp [erosionUpper, NNReal.coe_add, add_comm, add_left_comm]

/-- The rank of an actual composite is bounded by the rank of either factor.
Finite dimensionality prevents `finrank` from collapsing an infinite image to zero. -/
theorem finrank_range_comp_le {U V W : Type u}
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k U]
    [FiniteDimensional k V] (f : U →ₗ[k] V) (g : V →ₗ[k] W) :
    Module.finrank k (LinearMap.range (g.comp f)) ≤
      Module.finrank k (LinearMap.range f) ∧
    Module.finrank k (LinearMap.range (g.comp f)) ≤
      Module.finrank k (LinearMap.range g) := by
  constructor
  · exact Module.finrank_le_finrank_of_rank_le_rank (by
      simpa using LinearMap.rank_comp_le_right f g) (Module.rank_lt_aleph0 _ _)
  · exact Module.finrank_le_finrank_of_rank_le_rank (by
      simpa using LinearMap.rank_comp_le_left f g) (Module.rank_lt_aleph0 _ _)

/-- Ranks decrease when a structure-map interval is widened at both ends. -/
theorem rankOfStructureMap_four_point (M : PModule.{u,0,u} k (Fin n → ℝ))
    [∀ p, FiniteDimensional k (M.obj p)]
    {a₀ a₁ b₁ b₀ : Fin n → ℝ}
    (ha : a₀ ≤ a₁) (hab : a₁ ≤ b₁) (hb : b₁ ≤ b₀) :
    rankOfStructureMap M (ha.trans (hab.trans hb)) ≤
      rankOfStructureMap M hab := by
  letI := (inferInstance : FiniteDimensional k (M.obj a₀))
  letI := (inferInstance : FiniteDimensional k (M.obj a₁))
  letI := (inferInstance : FiniteDimensional k (M.obj b₁))
  unfold rankOfStructureMap
  rw [structureMapLinear_comp M ha (hab.trans hb),
    structureMapLinear_comp M hab hb]
  exact ((finrank_range_comp_le (structureMapLinear M ha)
      ((structureMapLinear M hb).comp (structureMapLinear M hab))).2).trans
    (finrank_range_comp_le (structureMapLinear M hab) (structureMapLinear M hb)).1

/-- The two rank inequalities that define erosion at radius `ε`. -/
def RankErosion (ε : ℝ≥0) (M N : PModule.{u,0,u} k (Fin n → ℝ)) : Prop :=
  (∀ (a b : Fin n → ℝ) (hab : a ≤ b),
    rankOfStructureMap M (erosionWide_le ε hab) ≤ rankOfStructureMap N hab) ∧
  (∀ (a b : Fin n → ℝ) (hab : a ≤ b),
    rankOfStructureMap N (erosionWide_le ε hab) ≤ rankOfStructureMap M hab)

/-- Radius zero compares every weak-pair rank, including fiber dimensions on
the diagonal. -/
theorem rankErosion_zero_iff : RankErosion 0 M N ↔
    ∀ (a b : Fin n → ℝ) (hab : a ≤ b),
      rankOfStructureMap M hab = rankOfStructureMap N hab := by
  constructor
  · intro h a b hab
    exact Nat.le_antisymm (by simpa only [erosionLower_zero, erosionUpper_zero] using
      (h.1 a b hab)) (by simpa only [erosionLower_zero, erosionUpper_zero] using
      (h.2 a b hab))
  · intro h
    constructor
    · intro a b hab
      simpa only [erosionLower_zero, erosionUpper_zero] using (h a b hab).le
    · intro a b hab
      simpa only [erosionLower_zero, erosionUpper_zero] using (h a b hab).ge

theorem RankErosion.symm {ε : ℝ≥0} (h : RankErosion ε M N) : RankErosion ε N M :=
  ⟨h.2, h.1⟩

theorem RankErosion.refl (ε : ℝ≥0) (M : PModule.{u,0,u} k (Fin n → ℝ))
    [∀ p, FiniteDimensional k (M.obj p)] : RankErosion ε M M := by
  constructor <;> intro a b hab <;>
    exact rankOfStructureMap_four_point M (erosionLower_le ε a) hab
      (le_erosionUpper ε b)

theorem RankErosion.mono {ε δ : ℝ≥0} (hεδ : ε ≤ δ)
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (h : RankErosion ε M N) : RankErosion δ M N := by
  constructor
  · intro a b hab
    have hleft : erosionLower δ a ≤ erosionLower ε a := by
      intro i
      change a i - (δ : ℝ) ≤ a i - (ε : ℝ)
      exact sub_le_sub_left (NNReal.coe_le_coe.mpr hεδ) _
    have hright : erosionUpper ε b ≤ erosionUpper δ b := by
      intro i
      simpa [erosionUpper, add_comm] using
        add_le_add_left (NNReal.coe_le_coe.mpr hεδ) (b i)
    exact (rankOfStructureMap_four_point M hleft (erosionWide_le ε hab) hright).trans
      (h.1 a b hab)
  · intro a b hab
    have hleft : erosionLower δ a ≤ erosionLower ε a := by
      intro i
      exact sub_le_sub_left (NNReal.coe_le_coe.mpr hεδ) _
    have hright : erosionUpper ε b ≤ erosionUpper δ b := by
      intro i
      simpa [erosionUpper, add_comm] using
        add_le_add_left (NNReal.coe_le_coe.mpr hεδ) (b i)
    exact (rankOfStructureMap_four_point N hleft (erosionWide_le ε hab) hright).trans
      (h.2 a b hab)

theorem RankErosion.trans {ε δ : ℝ≥0}
    (h : RankErosion ε M N) (j : RankErosion δ N P) :
    RankErosion (ε + δ) M P := by
  constructor
  · intro a b hab
    have hwide : erosionLower δ a ≤ erosionUpper δ b := erosionWide_le δ hab
    have h₁ := h.1 (erosionLower δ a) (erosionUpper δ b) hwide
    have h₂ := j.1 a b hab
    simpa only [erosionLower_add, erosionUpper_add] using h₁.trans h₂
  · intro a b hab
    have hwide : erosionLower ε a ≤ erosionUpper ε b := erosionWide_le ε hab
    have h₁ := j.2 (erosionLower ε a) (erosionUpper ε b) hwide
    have h₂ := h.2 a b hab
    simpa only [erosionLower_add, erosionUpper_add, add_comm] using h₁.trans h₂

/-- Extended infimum of admissible finite erosion radii. -/
noncomputable def rankErosionDistance
    (M N : PModule.{u,0,u} k (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : RankErosion ε M N), (ε : ℝ≥0∞)

theorem rankErosionDistance_le_of_erosion {ε : ℝ≥0}
    (h : RankErosion ε M N) : rankErosionDistance M N ≤ ε :=
  iInf₂_le ε h

theorem rankErosionDistance_self (M : PModule.{u,0,u} k (Fin n → ℝ))
    [∀ p, FiniteDimensional k (M.obj p)] : rankErosionDistance M M = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using
    (rankErosionDistance_le_of_erosion (RankErosion.refl 0 M)))

theorem rankErosionDistance_comm (M N : PModule.{u,0,u} k (Fin n → ℝ)) :
    rankErosionDistance M N = rankErosionDistance N M :=
  le_antisymm (le_iInf₂ fun _ h => rankErosionDistance_le_of_erosion h.symm)
    (le_iInf₂ fun _ h => rankErosionDistance_le_of_erosion h.symm)

theorem rankErosionDistance_triangle (M N P : PModule.{u,0,u} k (Fin n → ℝ)) :
    rankErosionDistance M P ≤ rankErosionDistance M N + rankErosionDistance N P := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ε h δ j
  simpa only [ENNReal.coe_add] using
    (rankErosionDistance_le_of_erosion (h.trans j))

end TDA.Persistence
