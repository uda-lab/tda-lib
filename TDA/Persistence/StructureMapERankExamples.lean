import TDA.Persistence.RankErosion
import TDA.Persistence.StructureMapERank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Extended-natural image rank: fixtures

An infinite-dimensional constant module has extended rank `⊤` at every pair, while its
`ℕ`-valued `rankOfStructureMap` is `0`, the same as that of the zero module. A
one-dimensional constant module has both ranks equal to `1`. Constant modules of
dimensions `ℵ₀` and `𝔠` have the same extended rank `⊤` though their cardinal ranks differ. The extended ranks of modules
whose carriers live in different universes are compared without `Cardinal.lift`.
-/

set_option autoImplicit false

namespace TDA.Persistence.StructureMapERankExamples

open CategoryTheory TDA.Persistence
open scoped ZeroObject

/-- The constant one-parameter module with fiber `V`. -/
noncomputable def constModule (V : ModuleCat.{0} ℚ) : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  (Functor.const (Fin 1 → ℝ)).obj V

theorem eRankOfStructureMap_constModule (V : ModuleCat.{0} ℚ) {a b : Fin 1 → ℝ}
    (hab : a ≤ b) :
    eRankOfStructureMap (constModule V) hab = (Module.rank ℚ V).toENat := by
  have hsurj : LinearMap.range (structureMapLinear (constModule V) hab) = ⊤ :=
    LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩
  rw [eRankOfStructureMap_eq_toENat_rank, hsurj, rank_top]
  rfl

/-- The countably-infinite-dimensional constant module. -/
noncomputable abbrev infinite : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  constModule (ModuleCat.of ℚ (ℕ →₀ ℚ))

/-- The one-dimensional constant module. -/
noncomputable abbrev line : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  constModule (ModuleCat.of ℚ ℚ)

/-- Every structure map of the infinite constant module has extended rank `⊤`. -/
theorem eRank_infinite {a b : Fin 1 → ℝ} (hab : a ≤ b) :
    eRankOfStructureMap infinite hab = ⊤ := by
  rw [eRankOfStructureMap_constModule]
  simp

/-- Its `ℕ`-valued rank is `0`: `Module.finrank` collapses the infinite image. -/
theorem rank_infinite {a b : Fin 1 → ℝ} (hab : a ≤ b) :
    rankOfStructureMap infinite hab = 0 := by
  rw [rankOfStructureMap_eq_toNat_eRankOfStructureMap, eRank_infinite]
  rfl

/-- The `ℕ`-valued ranks do not separate the infinite constant module from zero, while the
extended ranks do, already at the diagonal. -/
theorem infinite_vs_zero :
    (∀ (a b : Fin 1 → ℝ) (hab : a ≤ b),
      rankOfStructureMap infinite hab = rankOfStructureMap (0 : PModule.{0,0,0} ℚ _) hab) ∧
    (∀ (a b : Fin 1 → ℝ) (hab : a ≤ b),
      eRankOfStructureMap infinite hab ≠
        eRankOfStructureMap (0 : PModule.{0,0,0} ℚ _) hab) := by
  constructor
  · intro a b hab
    rw [rank_infinite, rankOfStructureMap_zero]
  · intro a b hab
    rw [eRank_infinite, eRankOfStructureMap_zero]
    exact ENat.top_ne_zero

/-- Consequently the `ℕ`-valued erosion predicate holds at radius `0` between the infinite
constant module and zero. -/
theorem rankErosion_zero_infinite :
    RankErosion 0 infinite (0 : PModule.{0,0,0} ℚ (Fin 1 → ℝ)) :=
  rankErosion_zero_iff.mpr fun a b hab => infinite_vs_zero.1 a b hab

/-- On the one-dimensional constant module both ranks are `1`. -/
theorem eRank_line {a b : Fin 1 → ℝ} (hab : a ≤ b) :
    eRankOfStructureMap line hab = 1 ∧ rankOfStructureMap line hab = 1 := by
  have h : eRankOfStructureMap line hab = 1 := by
    rw [eRankOfStructureMap_constModule]
    simp
  refine ⟨h, ?_⟩
  have hfd : FiniteDimensional ℚ (line.obj a) :=
    inferInstanceAs (FiniteDimensional ℚ ℚ)
  have := eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional_source line hab
  rw [h] at this
  exact_mod_cast this.symm

/-- The constant module with fiber `ℝ` over `ℚ`, of dimension `𝔠`. -/
noncomputable abbrev continuumConst : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  constModule (ModuleCat.of ℚ ℝ)

/-- Infinite cardinals are collapsed: the constant modules of dimensions `ℵ₀` and `𝔠` have
the same extended rank at every pair, while the cardinal ranks of their structure maps
differ. -/
theorem continuumConst_collapse {a b : Fin 1 → ℝ} (hab : a ≤ b) :
    eRankOfStructureMap continuumConst hab = eRankOfStructureMap infinite hab ∧
      (structureMapLinear continuumConst hab).rank ≠
        (structureMapLinear infinite hab).rank := by
  have hc : LinearMap.range (structureMapLinear continuumConst hab) = ⊤ :=
    LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩
  have hi : LinearMap.range (structureMapLinear infinite hab) = ⊤ :=
    LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩
  have rc : (structureMapLinear continuumConst hab).rank = Cardinal.continuum := by
    rw [LinearMap.rank, hc, rank_top]
    exact Real.rank_rat_real
  have ri : (structureMapLinear infinite hab).rank = Cardinal.aleph0 := by
    rw [LinearMap.rank, hi, rank_top]
    change Module.rank ℚ (ℕ →₀ ℚ) = Cardinal.aleph0
    simp
  refine ⟨?_, ?_⟩
  · rw [eRank_infinite, eRankOfStructureMap, rc]
    simp
  · rw [rc, ri]
    exact Cardinal.aleph0_lt_continuum.ne'

/-- Four-point monotonicity needs no finite dimensionality. -/
example {a₀ a₁ b₁ b₀ : Fin 1 → ℝ} (ha : a₀ ≤ a₁) (hab : a₁ ≤ b₁) (hb : b₁ ≤ b₀) :
    eRankOfStructureMap infinite (ha.trans (hab.trans hb)) ≤
      eRankOfStructureMap infinite hab :=
  eRankOfStructureMap_four_point infinite ha hab hb

/-- A constant module whose carrier lives in `Type 1`. -/
noncomputable abbrev infiniteLarge : PModule.{0,0,1} ℚ (Fin 1 → ℝ) :=
  (Functor.const (Fin 1 → ℝ)).obj (ModuleCat.of ℚ (ULift.{1} (ℕ →₀ ℚ)))

/-- Extended ranks of modules in different carrier universes are compared directly. -/
theorem eRank_infiniteLarge {a b : Fin 1 → ℝ} (hab : a ≤ b) :
    eRankOfStructureMap infiniteLarge hab = eRankOfStructureMap infinite hab := by
  have hsurj : LinearMap.range (structureMapLinear infiniteLarge hab) = ⊤ :=
    LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩
  rw [eRank_infinite, eRankOfStructureMap_eq_toENat_rank, hsurj, rank_top]
  change (Module.rank ℚ (ULift.{1} (ℕ →₀ ℚ))).toENat = ⊤
  simp

end TDA.Persistence.StructureMapERankExamples
