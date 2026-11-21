import TDA.Persistence.RankErosionInterleaving
import TDA.Persistence.StructureMapERank

/-!
# Weak-pair rank erosion on extended ranks

`ERankErosion ε M N` is the weak-pair erosion predicate of `RankErosion`, with the
`ℕ`-valued `rankOfStructureMap` replaced by the extended rank `eRankOfStructureMap`, and
`eRankErosionDistance` is the infimum of its admissible radii in `ℝ≥0∞`. Because the
extended rank is monotone on composites for every module, the erosion laws (monotonicity in
the radius, reflexivity, symmetry, the triangle law) and the bound by the coordinate
interleaving distance hold without finite dimensionality. On pointwise finite-dimensional
modules the predicate and the distance are `RankErosion` and `rankErosionDistance`.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k] {n : ℕ}
variable {M N P : PModule.{u,0,u} k (Fin n → ℝ)}

/-- The two extended-rank inequalities that define erosion at radius `ε`. -/
def ERankErosion (ε : ℝ≥0) (M N : PModule.{u,0,u} k (Fin n → ℝ)) : Prop :=
  (∀ (a b : Fin n → ℝ) (hab : a ≤ b),
    eRankOfStructureMap M (erosionWide_le ε hab) ≤ eRankOfStructureMap N hab) ∧
  (∀ (a b : Fin n → ℝ) (hab : a ≤ b),
    eRankOfStructureMap N (erosionWide_le ε hab) ≤ eRankOfStructureMap M hab)

/-- Radius zero compares every weak-pair extended rank, including the extended fiber
dimensions on the diagonal. -/
theorem eRankErosion_zero_iff : ERankErosion 0 M N ↔
    ∀ (a b : Fin n → ℝ) (hab : a ≤ b),
      eRankOfStructureMap M hab = eRankOfStructureMap N hab := by
  constructor
  · intro h a b hab
    exact le_antisymm (by simpa only [erosionLower_zero, erosionUpper_zero] using
      (h.1 a b hab)) (by simpa only [erosionLower_zero, erosionUpper_zero] using
      (h.2 a b hab))
  · intro h
    constructor
    · intro a b hab
      simpa only [erosionLower_zero, erosionUpper_zero] using (h a b hab).le
    · intro a b hab
      simpa only [erosionLower_zero, erosionUpper_zero] using (h a b hab).ge

/-- Erosion is symmetric in the two modules. -/
theorem ERankErosion.symm {ε : ℝ≥0} (h : ERankErosion ε M N) : ERankErosion ε N M :=
  ⟨h.2, h.1⟩

/-- Every module erodes to itself at every radius, with no finite dimensionality. -/
theorem ERankErosion.refl (ε : ℝ≥0) (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    ERankErosion ε M M := by
  constructor <;> intro a b hab <;>
    exact eRankOfStructureMap_four_point M (erosionLower_le ε a) hab
      (le_erosionUpper ε b)

/-- Erosion persists at larger radii, with no finite dimensionality. -/
theorem ERankErosion.mono {ε δ : ℝ≥0} (hεδ : ε ≤ δ) (h : ERankErosion ε M N) :
    ERankErosion δ M N := by
  have hleft (a : Fin n → ℝ) : erosionLower δ a ≤ erosionLower ε a := by
    intro i
    change a i - (δ : ℝ) ≤ a i - (ε : ℝ)
    exact sub_le_sub_left (NNReal.coe_le_coe.mpr hεδ) _
  have hright (b : Fin n → ℝ) : erosionUpper ε b ≤ erosionUpper δ b := by
    intro i
    change b i + (ε : ℝ) ≤ b i + (δ : ℝ)
    exact add_le_add_right (NNReal.coe_le_coe.mpr hεδ) _
  constructor
  · intro a b hab
    exact (eRankOfStructureMap_four_point M (hleft a) (erosionWide_le ε hab)
      (hright b)).trans (h.1 a b hab)
  · intro a b hab
    exact (eRankOfStructureMap_four_point N (hleft a) (erosionWide_le ε hab)
      (hright b)).trans (h.2 a b hab)

/-- Erosion composes, adding the radii, with no finite dimensionality. -/
theorem ERankErosion.trans {ε δ : ℝ≥0}
    (h : ERankErosion ε M N) (j : ERankErosion δ N P) :
    ERankErosion (ε + δ) M P := by
  constructor
  · intro a b hab
    have h₁ := h.1 (erosionLower δ a) (erosionUpper δ b) (erosionWide_le δ hab)
    have h₂ := j.1 a b hab
    simpa only [erosionLower_add, erosionUpper_add] using h₁.trans h₂
  · intro a b hab
    have h₁ := j.2 (erosionLower ε a) (erosionUpper ε b) (erosionWide_le ε hab)
    have h₂ := h.2 a b hab
    simpa only [erosionLower_add, erosionUpper_add, add_comm] using h₁.trans h₂

/-- Extended infimum of the radii admissible for extended-rank erosion. -/
noncomputable def eRankErosionDistance
    (M N : PModule.{u,0,u} k (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : ERankErosion ε M N), (ε : ℝ≥0∞)

/-- Any radius at which erosion holds bounds the distance. -/
theorem eRankErosionDistance_le_of_erosion {ε : ℝ≥0}
    (h : ERankErosion ε M N) : eRankErosionDistance M N ≤ ε :=
  iInf₂_le ε h

/-- A radius at which extended-rank erosion fails is a lower bound for the distance. -/
theorem le_eRankErosionDistance_of_not_eRankErosion {ε : ℝ≥0}
    (h : ¬ ERankErosion ε M N) : (ε : ℝ≥0∞) ≤ eRankErosionDistance M N :=
  le_iInf₂ fun _ hδ => ENNReal.coe_le_coe.mpr
    (le_of_not_ge fun hδε => h (hδ.mono hδε))

/-- The distance is `⊤` exactly when erosion fails at every finite radius. -/
theorem eRankErosionDistance_eq_top_iff :
    eRankErosionDistance M N = ⊤ ↔ ∀ ε : ℝ≥0, ¬ ERankErosion ε M N := by
  simp only [eRankErosionDistance, iInf_eq_top, ENNReal.coe_ne_top, imp_false]

/-- Every module is at extended erosion distance `0` from itself. -/
theorem eRankErosionDistance_self (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    eRankErosionDistance M M = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using
    (eRankErosionDistance_le_of_erosion (ERankErosion.refl 0 M)))

/-- The distance is symmetric. -/
theorem eRankErosionDistance_comm (M N : PModule.{u,0,u} k (Fin n → ℝ)) :
    eRankErosionDistance M N = eRankErosionDistance N M :=
  le_antisymm (le_iInf₂ fun _ h => eRankErosionDistance_le_of_erosion h.symm)
    (le_iInf₂ fun _ h => eRankErosionDistance_le_of_erosion h.symm)

/-- The triangle law, also for infinite summands. -/
theorem eRankErosionDistance_triangle (M N P : PModule.{u,0,u} k (Fin n → ℝ)) :
    eRankErosionDistance M P ≤ eRankErosionDistance M N + eRankErosionDistance N P := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ε h δ j
  simpa only [ENNReal.coe_add] using
    (eRankErosionDistance_le_of_erosion (h.trans j))

/-- Extended-rank domination from the actual interleaving factorization, with no finite
dimensionality. -/
theorem CoordinateInterleaving.eRank_erosion_le {ε : ℝ≥0}
    (I : CoordinateInterleaving ε M N) (a b : Fin n → ℝ) (hab : a ≤ b) :
    eRankOfStructureMap M (erosionWide_le ε hab) ≤ eRankOfStructureMap N hab := by
  let x := erosionLower ε a
  have hx : translation ε x = a := translation_erosionLower ε a
  let h : translation ε x ≤ b := hx.symm ▸ hab
  have hxy : x ≤ translation ε b := by
    intro i
    change a i - (ε : ℝ) ≤ b i + (ε : ℝ)
    exact (sub_le_self _ ε.coe_nonneg).trans
      ((hab i).trans (le_add_of_nonneg_right ε.coe_nonneg))
  have hfactorLinear := congrArg ModuleCat.Hom.hom (I.factor_structureMap h hxy)
  have same_start {p q : Fin n → ℝ} (e : p = q) (hp : p ≤ b) (hq : q ≤ b) :
      eRankOfStructureMap N hp = eRankOfStructureMap N hq := by
    cases e
    rfl
  have hbound : (((I.ψ.app b).hom).comp
      ((structureMap N h).hom.comp (I.φ.app x).hom)).rank.toENat ≤
      eRankOfStructureMap N h :=
    (Cardinal.toENat.monotone' (LinearMap.rank_comp_le_right _ _)).trans
      (Cardinal.toENat.monotone' (LinearMap.rank_comp_le_left _ _))
  calc
    eRankOfStructureMap M (erosionWide_le ε hab) =
        (structureMap M hxy).hom.rank.toENat := rfl
    _ = (((I.ψ.app b).hom).comp
        ((structureMap N h).hom.comp (I.φ.app x).hom)).rank.toENat := by
      rw [hfactorLinear]
      rfl
    _ ≤ eRankOfStructureMap N h := hbound
    _ = eRankOfStructureMap N hab := same_start hx h hab

/-- Every actual interleaving supplies both extended-rank erosion inequalities. -/
theorem CoordinateInterleaving.eRankErosion {ε : ℝ≥0}
    (I : CoordinateInterleaving ε M N) : ERankErosion ε M N :=
  ⟨I.eRank_erosion_le, I.symm.eRank_erosion_le⟩

/-- Extended-rank erosion is bounded by coordinate interleaving distance, for every module. -/
theorem eRankErosionDistance_le_coordinateInterleavingDistance
    (M N : PModule.{u,0,u} k (Fin n → ℝ)) :
    eRankErosionDistance M N ≤ coordinateInterleavingDistance M N := by
  apply le_iInf₂
  intro ε ⟨I⟩
  exact eRankErosionDistance_le_of_erosion I.eRankErosion

/-- On pointwise finite-dimensional modules extended-rank erosion is `RankErosion`. -/
theorem eRankErosion_iff_rankErosion {ε : ℝ≥0}
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)] :
    ERankErosion ε M N ↔ RankErosion ε M N := by
  simp only [ERankErosion, RankErosion, eRankOfStructureMap_le_eRankOfStructureMap_iff]

/-- On pointwise finite-dimensional modules the extended-rank erosion distance is
`rankErosionDistance`. -/
theorem eRankErosionDistance_eq_rankErosionDistance
    [∀ p, FiniteDimensional k (M.obj p)]
    [∀ p, FiniteDimensional k (N.obj p)] :
    eRankErosionDistance M N = rankErosionDistance M N := by
  simp only [eRankErosionDistance, rankErosionDistance, eRankErosion_iff_rankErosion]

end TDA.Persistence
