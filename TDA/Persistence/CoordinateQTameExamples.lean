import TDA.Persistence.CoordinateQTame
import TDA.Persistence.ERankQTameExamples

/-!
# Coordinatewise q-tameness: fixtures

`axisEphemeral` is the real ephemeral module of `ERankQTameExamples` pulled back along the
second coordinate of `Fin 2 → ℝ`: fibre `ℕ →₀ ℚ` at every grade, the identity when the
second coordinates agree and zero when the second coordinate increases. It is coordinatewise
q-tame and not pointwise finite-dimensional. The axis-parallel pair from the origin to the
first unit vector is a strict pair of the product order, so strict erosion tests it, but it is
not coordinatewise strict, and its structure map is the identity of an infinite-dimensional
space, of extended rank `⊤`. So the product-strict finiteness condition fails for this
coordinatewise q-tame module. Against zero, extended-rank erosion fails at radius `0` at that
pair and holds at every positive radius. With one coordinate, `fromReal realEphemeral` is
coordinatewise q-tame through the q-tame bridge; with no coordinate, the infinite ephemeral
module is not.
-/

set_option autoImplicit false

namespace TDA.Persistence.CoordinateQTameExamples

open CategoryTheory TDA.Persistence CoordinateRealBridge CoordinateShift
open TDA.Persistence.ERankQTameExamples (realEphemeral)
open TDA.Persistence.ERankErosionExamples (ephemeralInfinite)
open scoped ZeroObject NNReal ENNReal

/-- The real ephemeral module pulled back along the second coordinate of `Fin 2 → ℝ`. -/
noncomputable abbrev axisEphemeral : PModule.{0,0,0} ℚ (Fin 2 → ℝ) :=
  reindex (Pi.evalOrderHom (π := fun _ : Fin 2 => ℝ) 1) realEphemeral

/-- When the second coordinate increases, the structure map of `axisEphemeral` has extended
rank `0`. -/
theorem eRank_axisEphemeral_of_lt {a b : Fin 2 → ℝ} (hab : a ≤ b) (h1 : a 1 < b 1) :
    eRankOfStructureMap axisEphemeral hab = 0 :=
  ERankQTameExamples.eRank_realEphemeral_of_lt h1

/-- `axisEphemeral` is coordinatewise q-tame. -/
theorem axisEphemeral_coordQTame : axisEphemeral.CoordQTame :=
  (PModule.coordQTame_iff_eRankOfStructureMap_ne_top _).mpr fun _ _ hab => by
    rw [eRank_axisEphemeral_of_lt _ (hab 1)]
    exact ENat.zero_ne_top

/-- No fibre of `axisEphemeral` is finite-dimensional. -/
theorem axisEphemeral_not_finiteDimensional (a : Fin 2 → ℝ) :
    ¬ FiniteDimensional ℚ (axisEphemeral.obj a) :=
  ERankQTameExamples.realEphemeral_not_finiteDimensional (a 1)

/-- The origin of `Fin 2 → ℝ`. -/
def axisLow : Fin 2 → ℝ := ![0, 0]

/-- The first unit vector of `Fin 2 → ℝ`. -/
def axisHigh : Fin 2 → ℝ := ![1, 0]

/-- The axis-parallel pair is a strict pair of the product order, so strict erosion tests
it. -/
theorem axisLow_lt_axisHigh : axisLow < axisHigh := by
  refine Pi.lt_def.mpr ⟨fun i => ?_, 0, ?_⟩
  · fin_cases i <;> simp [axisLow, axisHigh]
  · simp [axisLow, axisHigh]

/-- The axis-parallel pair is not strictly ordered in every coordinate. -/
theorem not_forall_axisLow_lt_axisHigh : ¬ ∀ i, axisLow i < axisHigh i :=
  fun h => lt_irrefl (0 : ℝ) (by simpa [axisLow, axisHigh] using h 1)

/-- The axis-parallel structure map of `axisEphemeral` has extended rank `⊤`. -/
theorem eRank_axisEphemeral_axis :
    eRankOfStructureMap axisEphemeral axisLow_lt_axisHigh.le = ⊤ := by
  change eRankOfStructureMap realEphemeral (le_refl (0 : ℝ)) = ⊤
  rw [eRankOfStructureMap_self]
  change (Module.rank ℚ (ℕ →₀ ℚ)).toENat = ⊤
  simp

/-- The product-strict finiteness condition fails for the coordinatewise q-tame module
`axisEphemeral`. -/
theorem axisEphemeral_not_forall_lt_eRank_ne_top :
    ¬ ∀ (a b : Fin 2 → ℝ) (hab : a < b), eRankOfStructureMap axisEphemeral hab.le ≠ ⊤ :=
  fun h => h axisLow axisHigh axisLow_lt_axisHigh eRank_axisEphemeral_axis

/-- At radius `0` the extended-rank erosion test against zero fails at the axis-parallel
pair. -/
theorem axisEphemeral_axis_not_eRank_le_zero :
    ¬ eRankOfStructureMap axisEphemeral axisLow_lt_axisHigh.le ≤
      eRankOfStructureMap (0 : PModule.{0,0,0} ℚ (Fin 2 → ℝ)) axisLow_lt_axisHigh.le := by
  rw [eRank_axisEphemeral_axis, eRankOfStructureMap_zero]
  exact fun h => ENat.top_ne_zero (le_antisymm h zero_le)

/-- Extended-rank erosion of `axisEphemeral` against zero fails at radius `0`. -/
theorem axisEphemeral_not_eRankErosion_zero :
    ¬ ERankErosion 0 axisEphemeral 0 := fun h =>
  axisEphemeral_axis_not_eRank_le_zero
    ((eRankErosion_zero_iff.mp h) axisLow axisHigh axisLow_lt_axisHigh.le).le

/-- Extended-rank erosion of `axisEphemeral` against zero holds at every positive radius. -/
theorem axisEphemeral_eRankErosion {ε : ℝ≥0} (hε : 0 < ε) :
    ERankErosion ε axisEphemeral 0 := by
  constructor
  · intro a b hab
    have h1 : erosionLower ε a 1 < erosionUpper ε b 1 := by
      have := hab 1
      have hε' : (0 : ℝ) < ε := hε
      change a 1 - (ε : ℝ) < b 1 + (ε : ℝ)
      linarith
    rw [eRank_axisEphemeral_of_lt _ h1]
    exact zero_le
  · intro a b hab
    rw [eRankOfStructureMap_zero]
    exact zero_le

/-- The extended erosion distance of `axisEphemeral` from zero is `0` and is not attained. -/
theorem axisEphemeral_eRankErosionDistance :
    eRankErosionDistance axisEphemeral 0 = 0 ∧ ¬ ERankErosion 0 axisEphemeral 0 := by
  refine ⟨?_, axisEphemeral_not_eRankErosion_zero⟩
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  exact eRankErosionDistance_le_of_erosion (axisEphemeral_eRankErosion hε)

/-- The coordinatewise consumer on a module that is not pointwise finite-dimensional. -/
example {a b : Fin 2 → ℝ} (hab : a ≤ b) (hlt : ∀ i, a i < b i) :
    eRankOfStructureMap axisEphemeral hab ≠ ⊤ :=
  axisEphemeral_coordQTame.eRankOfStructureMap_ne_top hab hlt

/-- Every positive diagonal shift of `axisEphemeral` has finite extended rank. -/
example {δ : ℝ≥0} (hδ : 0 < δ) (a : Fin 2 → ℝ) :
    eRankOfStructureMap axisEphemeral (le_translation δ a) ≠ ⊤ :=
  axisEphemeral_coordQTame.eRankOfStructureMap_translation_ne_top hδ a

/-- With one coordinate, the one-coordinate real ephemeral module is coordinatewise
q-tame. -/
theorem fromReal_realEphemeral_coordQTame : (fromReal realEphemeral).CoordQTame :=
  (PModule.qTame_iff_coordQTame_fromReal _).mp ERankQTameExamples.realEphemeral_qTame

/-- With no coordinate, the infinite ephemeral module is not coordinatewise q-tame. -/
theorem ephemeralInfinite_fin_zero_not_coordQTame :
    ¬ (ephemeralInfinite (n := 0)).CoordQTame := by
  rw [PModule.coordQTame_fin_zero_iff]
  intro h
  have htop := ERankErosionExamples.eRank_ephemeralInfinite_self (0 : Fin 0 → ℝ)
  rw [eRankOfStructureMap_self, ← Module.finrank_eq_rank, Cardinal.toENat_nat] at htop
  exact ENat.natCast_ne_top _ htop

/-- The gap in `CoordinateInterleaving.eRankOfStructureMap_ne_top_of_coordQTame` must be
strict: with a gap of exactly `2ε`, at radius `0`, the coordinatewise q-tame module
`fromReal realEphemeral` interleaved with itself and the diagonal pair, the conclusion would make
the identity of an infinite-dimensional fibre finite. -/
example : ¬ ∀ {M N : PModule.{0,0,0} ℚ (Fin 1 → ℝ)} (_ : CoordinateInterleaving 0 M N),
    N.CoordQTame → ∀ {a b : Fin 1 → ℝ} (hab : a ≤ b),
      (∀ j, a j + 2 * ((0 : ℝ≥0) : ℝ) ≤ b j) → eRankOfStructureMap M hab ≠ ⊤ :=
  fun h => h (CoordinateInterleaving.refl 0 _) fromReal_realEphemeral_coordQTame
    (le_refl (0 : Fin 1 → ℝ)) (fun j => by simp)
    (ERankQTameExamples.eRank_fromReal_realEphemeral_self 0)

end TDA.Persistence.CoordinateQTameExamples
