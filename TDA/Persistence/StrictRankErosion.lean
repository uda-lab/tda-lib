import TDA.Persistence.RankErosion

/-!
# Strict-pair rank erosion

`RankErosion` compares the ranks of structure maps at all weak pairs `a ≤ b` of coordinate
grades, including the diagonal `a = b`. `StrictRankErosion` asks for the same two inequalities
only at the strict pairs of the product order: `a ≤ b` and `a ≠ b`. A pair that is strict in
the product order need not be strict in every coordinate.

The weak predicate implies the strict one at the same radius. With at least one coordinate and
finite-dimensional fibers, the strict predicate at a radius implies the weak predicate at every
larger radius, so the two extended distances agree. The predicates themselves need not agree
at a fixed radius, and with no coordinates there is no strict pair: the strict predicate then
holds for all modules.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k] {n : ℕ}
variable {M N P : PModule.{u,0,u} k (Fin n → ℝ)}

/-- The two rank inequalities of erosion at radius `ε`, required only at the strict pairs of
the product order: `a ≤ b` and `a ≠ b`. -/
def StrictRankErosion (ε : ℝ≥0) (M N : PModule.{u,0,u} k (Fin n → ℝ)) : Prop :=
  (∀ (a b : Fin n → ℝ) (hab : a ≤ b), a ≠ b →
    rankOfStructureMap M (erosionWide_le ε hab) ≤ rankOfStructureMap N hab) ∧
  (∀ (a b : Fin n → ℝ) (hab : a ≤ b), a ≠ b →
    rankOfStructureMap N (erosionWide_le ε hab) ≤ rankOfStructureMap M hab)

/-- The strict pairs are those of the strict product order `a < b`. -/
theorem strictRankErosion_iff_lt {ε : ℝ≥0} : StrictRankErosion ε M N ↔
    (∀ (a b : Fin n → ℝ) (hab : a < b),
      rankOfStructureMap M (erosionWide_le ε hab.le) ≤ rankOfStructureMap N hab.le) ∧
    (∀ (a b : Fin n → ℝ) (hab : a < b),
      rankOfStructureMap N (erosionWide_le ε hab.le) ≤ rankOfStructureMap M hab.le) :=
  ⟨fun h => ⟨fun a b hab => h.1 a b hab.le hab.ne, fun a b hab => h.2 a b hab.le hab.ne⟩,
    fun h => ⟨fun a b hab hne => h.1 a b (lt_of_le_of_ne hab hne),
      fun a b hab hne => h.2 a b (lt_of_le_of_ne hab hne)⟩⟩

/-- Weak-pair erosion implies strict-pair erosion at the same radius. -/
theorem RankErosion.strict {ε : ℝ≥0} (h : RankErosion ε M N) : StrictRankErosion ε M N :=
  ⟨fun a b hab _ => h.1 a b hab, fun a b hab _ => h.2 a b hab⟩

/-- Radius zero compares the ranks at every strict pair. -/
theorem strictRankErosion_zero_iff : StrictRankErosion 0 M N ↔
    ∀ (a b : Fin n → ℝ) (hab : a ≤ b), a ≠ b →
      rankOfStructureMap M hab = rankOfStructureMap N hab := by
  constructor
  · intro h a b hab hne
    exact Nat.le_antisymm (by simpa only [erosionLower_zero, erosionUpper_zero] using
      (h.1 a b hab hne)) (by simpa only [erosionLower_zero, erosionUpper_zero] using
      (h.2 a b hab hne))
  · intro h
    constructor
    · intro a b hab hne
      simpa only [erosionLower_zero, erosionUpper_zero] using (h a b hab hne).le
    · intro a b hab hne
      simpa only [erosionLower_zero, erosionUpper_zero] using (h a b hab hne).ge

theorem StrictRankErosion.symm {ε : ℝ≥0} (h : StrictRankErosion ε M N) :
    StrictRankErosion ε N M :=
  ⟨h.2, h.1⟩

private theorem erosionLower_anti {ε δ : ℝ≥0} (hεδ : ε ≤ δ) (a : Fin n → ℝ) :
    erosionLower δ a ≤ erosionLower ε a := fun i =>
  sub_le_sub_left (NNReal.coe_le_coe.mpr hεδ) (a i)

private theorem erosionUpper_mono {ε δ : ℝ≥0} (hεδ : ε ≤ δ) (b : Fin n → ℝ) :
    erosionUpper ε b ≤ erosionUpper δ b := fun i =>
  add_le_add_right (NNReal.coe_le_coe.mpr hεδ) (b i)

theorem StrictRankErosion.mono {ε δ : ℝ≥0} (hεδ : ε ≤ δ)
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (h : StrictRankErosion ε M N) : StrictRankErosion δ M N :=
  ⟨fun a b hab hne =>
      (rankOfStructureMap_four_point M (erosionLower_anti hεδ a) (erosionWide_le ε hab)
        (erosionUpper_mono hεδ b)).trans (h.1 a b hab hne),
    fun a b hab hne =>
      (rankOfStructureMap_four_point N (erosionLower_anti hεδ a) (erosionWide_le ε hab)
        (erosionUpper_mono hεδ b)).trans (h.2 a b hab hne)⟩

/-- Widening a strict pair gives a strict pair. -/
private theorem erosionLower_ne_erosionUpper (δ : ℝ≥0) {a b : Fin n → ℝ} (hab : a ≤ b)
    (hne : a ≠ b) : erosionLower δ a ≠ erosionUpper δ b := by
  intro h
  apply hne
  funext i
  have hi : a i - (δ : ℝ) = b i + (δ : ℝ) := congrFun h i
  have hδ : (0 : ℝ) ≤ δ := δ.coe_nonneg
  have hle : a i ≤ b i := hab i
  linarith

theorem StrictRankErosion.trans {ε δ : ℝ≥0}
    (h : StrictRankErosion ε M N) (j : StrictRankErosion δ N P) :
    StrictRankErosion (ε + δ) M P := by
  constructor
  · intro a b hab hne
    have h₁ := h.1 (erosionLower δ a) (erosionUpper δ b) (erosionWide_le δ hab)
      (erosionLower_ne_erosionUpper δ hab hne)
    have h₂ := j.1 a b hab hne
    simpa only [erosionLower_add, erosionUpper_add] using h₁.trans h₂
  · intro a b hab hne
    have h₁ := j.2 (erosionLower ε a) (erosionUpper ε b) (erosionWide_le ε hab)
      (erosionLower_ne_erosionUpper ε hab hne)
    have h₂ := h.2 a b hab hne
    simpa only [erosionLower_add, erosionUpper_add, add_comm] using h₁.trans h₂

/-- With at least one coordinate, widening any weak pair by a positive radius gives a strict
pair. -/
private theorem erosionLower_ne_erosionUpper_of_pos [NeZero n] {δ : ℝ≥0} (hδ : 0 < δ)
    {a b : Fin n → ℝ} (hab : a ≤ b) : erosionLower δ a ≠ erosionUpper δ b := by
  intro h
  have hi : a 0 - (δ : ℝ) = b 0 + (δ : ℝ) := congrFun h 0
  have hpos : (0 : ℝ) < δ := NNReal.coe_pos.mpr hδ
  have hle : a 0 ≤ b 0 := hab 0
  linarith

/-- With at least one coordinate and finite-dimensional fibers, strict-pair erosion at `ε`
implies weak-pair erosion at `ε + δ` for every positive `δ`: the weak pair `a ≤ b` is tested
at the strict pair `(a - δ, b + δ)`. -/
theorem StrictRankErosion.rankErosion_add [NeZero n] {ε δ : ℝ≥0} (hδ : 0 < δ)
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (h : StrictRankErosion ε M N) : RankErosion (ε + δ) M N := by
  constructor
  · intro a b hab
    have h₁ := h.1 (erosionLower δ a) (erosionUpper δ b) (erosionWide_le δ hab)
      (erosionLower_ne_erosionUpper_of_pos hδ hab)
    have h₂ := rankOfStructureMap_four_point N (erosionLower_le δ a) hab (le_erosionUpper δ b)
    simpa only [erosionLower_add, erosionUpper_add] using h₁.trans h₂
  · intro a b hab
    have h₁ := h.2 (erosionLower δ a) (erosionUpper δ b) (erosionWide_le δ hab)
      (erosionLower_ne_erosionUpper_of_pos hδ hab)
    have h₂ := rankOfStructureMap_four_point M (erosionLower_le δ a) hab (le_erosionUpper δ b)
    simpa only [erosionLower_add, erosionUpper_add] using h₁.trans h₂

/-- The same implication for an arbitrary strictly larger radius. -/
theorem StrictRankErosion.rankErosion_of_lt [NeZero n] {ε ε' : ℝ≥0} (hlt : ε < ε')
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (h : StrictRankErosion ε M N) : RankErosion ε' M N := by
  have h' := h.rankErosion_add (tsub_pos_of_lt hlt)
  rwa [add_tsub_cancel_of_le hlt.le] at h'

/-- With no coordinates there is one grade and no strict pair, so strict-pair erosion holds for
all modules at every radius. -/
theorem strictRankErosion_fin_zero (ε : ℝ≥0) (M N : PModule.{u,0,u} k (Fin 0 → ℝ)) :
    StrictRankErosion ε M N :=
  ⟨fun a b _ hne => absurd (Subsingleton.elim a b) hne,
    fun a b _ hne => absurd (Subsingleton.elim a b) hne⟩

/-- Extended infimum of the radii admissible for strict-pair erosion. -/
noncomputable def strictRankErosionDistance
    (M N : PModule.{u,0,u} k (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : StrictRankErosion ε M N), (ε : ℝ≥0∞)

theorem strictRankErosionDistance_le_of_erosion {ε : ℝ≥0}
    (h : StrictRankErosion ε M N) : strictRankErosionDistance M N ≤ ε :=
  iInf₂_le ε h

/-- The strict-pair distance is at most the weak-pair distance. -/
theorem strictRankErosionDistance_le_rankErosionDistance
    (M N : PModule.{u,0,u} k (Fin n → ℝ)) :
    strictRankErosionDistance M N ≤ rankErosionDistance M N :=
  le_iInf₂ fun _ h => strictRankErosionDistance_le_of_erosion h.strict

/-- With at least one coordinate and finite-dimensional fibers, the strict-pair and weak-pair
distances agree, including when they are infinite. -/
theorem strictRankErosionDistance_eq_rankErosionDistance [NeZero n]
    (M N : PModule.{u,0,u} k (Fin n → ℝ))
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)] :
    strictRankErosionDistance M N = rankErosionDistance M N := by
  refine le_antisymm (strictRankErosionDistance_le_rankErosionDistance M N)
    (le_iInf₂ fun ε h => ?_)
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have h' := rankErosionDistance_le_of_erosion (h.rankErosion_add hδ)
  rwa [ENNReal.coe_add] at h'

/-- With no coordinates the strict-pair distance of any two modules is zero. -/
theorem strictRankErosionDistance_fin_zero (M N : PModule.{u,0,u} k (Fin 0 → ℝ)) :
    strictRankErosionDistance M N = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using
    (strictRankErosionDistance_le_of_erosion (strictRankErosion_fin_zero 0 M N)))

theorem strictRankErosionDistance_self (M : PModule.{u,0,u} k (Fin n → ℝ))
    [∀ p, FiniteDimensional k (M.obj p)] : strictRankErosionDistance M M = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using
    (strictRankErosionDistance_le_of_erosion (RankErosion.refl 0 M).strict))

theorem strictRankErosionDistance_comm (M N : PModule.{u,0,u} k (Fin n → ℝ)) :
    strictRankErosionDistance M N = strictRankErosionDistance N M :=
  le_antisymm (le_iInf₂ fun _ h => strictRankErosionDistance_le_of_erosion h.symm)
    (le_iInf₂ fun _ h => strictRankErosionDistance_le_of_erosion h.symm)

theorem strictRankErosionDistance_triangle (M N P : PModule.{u,0,u} k (Fin n → ℝ)) :
    strictRankErosionDistance M P ≤
      strictRankErosionDistance M N + strictRankErosionDistance N P := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ε h δ j
  simpa only [ENNReal.coe_add] using
    (strictRankErosionDistance_le_of_erosion (h.trans j))

/-- A radius at which weak-pair erosion fails is a lower bound for the weak-pair distance. The
bound is not strict: the infimum need not be admissible. -/
theorem le_rankErosionDistance_of_not_rankErosion {ε : ℝ≥0}
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (h : ¬ RankErosion ε M N) : (ε : ℝ≥0∞) ≤ rankErosionDistance M N :=
  le_iInf₂ fun _ hδ => ENNReal.coe_le_coe.mpr
    (le_of_not_ge fun hδε => h (hδ.mono hδε))

/-- A radius at which strict-pair erosion fails is a lower bound for the strict-pair
distance. -/
theorem le_strictRankErosionDistance_of_not_strictRankErosion {ε : ℝ≥0}
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)]
    (h : ¬ StrictRankErosion ε M N) : (ε : ℝ≥0∞) ≤ strictRankErosionDistance M N :=
  le_iInf₂ fun _ hδ => ENNReal.coe_le_coe.mpr
    (le_of_not_ge fun hδε => h (hδ.mono hδε))

end TDA.Persistence
