import TDA.Persistence.StrictRankErosion
import TDA.Persistence.FinitePresentationGrid
import TDA.Persistence.FinitePresentationFiniteDimensional
import TDA.Persistence.FinitePresentationHookKernel
import TDA.Persistence.FinitePresentationLifting
import TDA.Persistence.F2GridRep
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Attainment of the rank-erosion distance for finitely presented modules

A finitely presented module is constant under small diagonal moves to the right. Its rank
invariant is therefore unchanged when the target of a structure map, or both of its ends, are
raised by a small radius. A rank inequality of `RankErosion ε` that fails at a pair `a ≤ b`
then also fails at radius `ε + δ` for every small `δ`, at the pair `(a + δ, b + δ)`: the widened
structure map keeps its source and its target is raised by `2δ`, while the compared structure
map is raised by `δ` at both ends.

Hence the admissible radii of two finitely presented modules contain their infimum: the
distance is at most `ε` exactly when `RankErosion ε` holds, a failed predicate gives a strict
lower bound of the distance, and the distance is zero exactly when all weak-pair ranks agree.
The hypothesis is the original finite presentation `GradedFree.FinitelyPresented` of both
modules; no rank or isomorphism condition is asked of the caller. The Kan extension of a valid
`F2GridRep` is finitely presented, so executed tests are consumers.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal ZeroObject

variable {k : Type u} [Field k] {n : ℕ}
variable {M N : PModule.{u,0,u} k (Fin n → ℝ)}

/-- Raising two comparable grades by the same radius keeps them comparable. -/
theorem erosionUpper_le_erosionUpper (δ : ℝ≥0) {a b : Fin n → ℝ} (hab : a ≤ b) :
    erosionUpper δ a ≤ erosionUpper δ b := fun i =>
  add_le_add_left (hab i) (δ : ℝ)

private theorem rank_congr (M : PModule.{u,0,u} k (Fin n → ℝ)) {a a' b b' : Fin n → ℝ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    rankOfStructureMap M h = rankOfStructureMap M h' := by
  subst ha
  subst hb
  rfl

private theorem structureMapLinear_bijective_of_isIso (M : PModule.{u,0,u} k (Fin n → ℝ))
    {a b : Fin n → ℝ} (hab : a ≤ b) (h : IsIso (structureMap M hab)) :
    Function.Bijective (structureMapLinear M hab) :=
  ConcreteCategory.bijective_of_isIso (structureMap M hab)

/-- Following a structure map by an invertible one keeps its rank. -/
private theorem rank_trans_of_isIso_right (M : PModule.{u,0,u} k (Fin n → ℝ))
    {a b c : Fin n → ℝ} (hab : a ≤ b) (hbc : b ≤ c) (h : IsIso (structureMap M hbc)) :
    rankOfStructureMap M (hab.trans hbc) = rankOfStructureMap M hab := by
  unfold rankOfStructureMap
  rw [structureMapLinear_comp M hab hbc, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective _
    (structureMapLinear_bijective_of_isIso M hbc h).injective _).symm.finrank_eq

/-- Preceding a structure map by an invertible one keeps its rank. -/
private theorem rank_trans_of_isIso_left (M : PModule.{u,0,u} k (Fin n → ℝ))
    {a b c : Fin n → ℝ} (hab : a ≤ b) (hbc : b ≤ c) (h : IsIso (structureMap M hab)) :
    rankOfStructureMap M (hab.trans hbc) = rankOfStructureMap M hbc := by
  unfold rankOfStructureMap
  rw [structureMapLinear_comp M hab hbc, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (structureMapLinear_bijective_of_isIso M hab h).surjective)]

namespace GradedFree

/-- The zero module on any preordered index type is finitely presented, with no generators and
no relations. -/
theorem finitelyPresented_zero {P : Type v} [Preorder P] :
    FinitelyPresented.{u,v,0} (R := k) (P := P) (0 : PModule.{u,v,u} k P) := by
  let W : GradedGenerators.{v,0} P := ⟨Empty, Empty.elim⟩
  have : Finite W.Carrier := inferInstanceAs (Finite Empty)
  have hzero : Limits.IsZero (module (R := k) W) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply hom_ext_birth W
    intro g
    exact g.elim
  exact finitelyPresented_of_iso (free_finitelyPresented W) hzero.isoZero

/-- The rank invariant of a finitely presented module is locally constant to the right: at
every weak pair there is a positive radius below which raising the target, or raising both
grades, does not change the rank. The radius comes from the presentation, through
`finitelyPresented_exists_pos_structureMap_isIso` at the two grades. -/
theorem finitelyPresented_exists_pos_rankOfStructureMap_erosionUpper
    (hM : FinitelyPresented.{u,0,0} (R := k) M) {a b : Fin n → ℝ} (hab : a ≤ b) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ δ : ℝ≥0, δ ≤ η →
      rankOfStructureMap M (hab.trans (le_erosionUpper δ b)) = rankOfStructureMap M hab ∧
      rankOfStructureMap M (erosionUpper_le_erosionUpper δ hab) = rankOfStructureMap M hab := by
  obtain ⟨εa, hεa, hisoA⟩ := finitelyPresented_exists_pos_structureMap_isIso M hM a
  obtain ⟨εb, hεb, hisoB⟩ := finitelyPresented_exists_pos_structureMap_isIso M hM b
  refine ⟨⟨min εa εb, (lt_min hεa hεb).le⟩, NNReal.coe_pos.mp (lt_min hεa hεb),
    fun δ hδ => ?_⟩
  have hδ' : (δ : ℝ) ≤ min εa εb := NNReal.coe_le_coe.mpr hδ
  have hA : IsIso (structureMap M (le_erosionUpper δ a)) :=
    hisoA δ δ.coe_nonneg (hδ'.trans (min_le_left _ _))
  have hB : IsIso (structureMap M (le_erosionUpper δ b)) :=
    hisoB δ δ.coe_nonneg (hδ'.trans (min_le_right _ _))
  have hfirst := rank_trans_of_isIso_right M hab (le_erosionUpper δ b) hB
  refine ⟨hfirst, ?_⟩
  rw [← hfirst]
  exact (rank_trans_of_isIso_left M (le_erosionUpper δ a) (erosionUpper_le_erosionUpper δ hab)
    hA).symm

private theorem erosionLower_erosionUpper_add (ε δ : ℝ≥0) (a : Fin n → ℝ) :
    erosionLower (ε + δ) (erosionUpper δ a) = erosionLower ε a := by
  funext i
  simp only [erosionLower, erosionUpper, NNReal.coe_add]
  ring

private theorem erosionUpper_erosionUpper_add (ε δ : ℝ≥0) (b : Fin n → ℝ) :
    erosionUpper (ε + δ) (erosionUpper δ b) = erosionUpper (δ + δ) (erosionUpper ε b) := by
  funext i
  simp only [erosionUpper, NNReal.coe_add]
  ring

/-- A failed first inequality at `ε` and `a ≤ b` fails at `ε + δ` and `(a + δ, b + δ)`. -/
private theorem exists_pos_not_rankErosion_add_of_lt
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    {ε : ℝ≥0} {a b : Fin n → ℝ} (hab : a ≤ b)
    (hlt : rankOfStructureMap N hab < rankOfStructureMap M (erosionWide_le ε hab)) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ δ : ℝ≥0, δ ≤ η → ¬ RankErosion (ε + δ) M N := by
  obtain ⟨ηM, hηM, hrankM⟩ :=
    finitelyPresented_exists_pos_rankOfStructureMap_erosionUpper hM (erosionWide_le ε hab)
  obtain ⟨ηN, hηN, hrankN⟩ :=
    finitelyPresented_exists_pos_rankOfStructureMap_erosionUpper hN hab
  refine ⟨min (ηM / 2) ηN, lt_min (half_pos hηM) hηN, fun δ hδ H => ?_⟩
  have hδM : δ + δ ≤ ηM := by
    have h2 : δ ≤ ηM / 2 := hδ.trans (min_le_left _ _)
    calc δ + δ ≤ ηM / 2 + ηM / 2 := add_le_add h2 h2
      _ = ηM := add_halves ηM
  have hδN : δ ≤ ηN := hδ.trans (min_le_right _ _)
  have hle := H.1 (erosionUpper δ a) (erosionUpper δ b) (erosionUpper_le_erosionUpper δ hab)
  rw [(hrankN δ hδN).2, rank_congr M (erosionLower_erosionUpper_add ε δ a)
    (erosionUpper_erosionUpper_add ε δ b) _
    ((erosionWide_le ε hab).trans (le_erosionUpper (δ + δ) (erosionUpper ε b))),
    (hrankM (δ + δ) hδM).1] at hle
  exact absurd hle (not_le.mpr hlt)

/-- For finitely presented modules, a radius at which erosion fails is followed by an interval
of radii at which it fails. -/
theorem finitelyPresented_exists_pos_not_rankErosion_add
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    {ε : ℝ≥0} (h : ¬ RankErosion ε M N) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ δ : ℝ≥0, δ ≤ η → ¬ RankErosion (ε + δ) M N := by
  by_cases h₁ : ∀ (a b : Fin n → ℝ) (hab : a ≤ b),
      rankOfStructureMap M (erosionWide_le ε hab) ≤ rankOfStructureMap N hab
  · have h₂ : ¬ ∀ (a b : Fin n → ℝ) (hab : a ≤ b),
        rankOfStructureMap N (erosionWide_le ε hab) ≤ rankOfStructureMap M hab :=
      fun h₂ => h ⟨h₁, h₂⟩
    simp only [not_forall, not_le] at h₂
    obtain ⟨a, b, hab, hlt⟩ := h₂
    obtain ⟨η, hη, hfail⟩ := exists_pos_not_rankErosion_add_of_lt hN hM hab hlt
    exact ⟨η, hη, fun δ hδ H => hfail δ hδ H.symm⟩
  · simp only [not_forall, not_le] at h₁
    obtain ⟨a, b, hab, hlt⟩ := h₁
    exact exists_pos_not_rankErosion_add_of_lt hM hN hab hlt

/-- For finitely presented modules, a radius at which erosion fails is a strict lower bound of
the erosion distance, also when the distance is infinite. -/
theorem finitelyPresented_lt_rankErosionDistance_of_not_rankErosion
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    {ε : ℝ≥0} (h : ¬ RankErosion ε M N) : (ε : ℝ≥0∞) < rankErosionDistance M N := by
  have := finitelyPresented_finiteDimensional M hM
  have := finitelyPresented_finiteDimensional N hN
  obtain ⟨η, hη, hfail⟩ := finitelyPresented_exists_pos_not_rankErosion_add hM hN h
  exact (ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right ε hη)).trans_le
    (le_rankErosionDistance_of_not_rankErosion (hfail η le_rfl))

/-- Erosion attainment: for finitely presented modules, every finite bound of the erosion
distance is an admissible radius. -/
theorem finitelyPresented_rankErosionDistance_le_iff_rankErosion
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    (ε : ℝ≥0) : rankErosionDistance M N ≤ (ε : ℝ≥0∞) ↔ RankErosion ε M N :=
  ⟨fun h => by_contra fun hne =>
      absurd h
        (not_le.mpr (finitelyPresented_lt_rankErosionDistance_of_not_rankErosion hM hN hne)),
    rankErosionDistance_le_of_erosion⟩

/-- A finite erosion distance of finitely presented modules is an admissible radius. -/
theorem finitelyPresented_rankErosion_at_distance
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    (hf : rankErosionDistance M N ≠ ⊤) :
    RankErosion (rankErosionDistance M N).toNNReal M N :=
  (finitelyPresented_rankErosionDistance_le_iff_rankErosion hM hN _).mp
    (ENNReal.coe_toNNReal hf).symm.le

/-- For finitely presented modules, erosion distance zero is equality of the rank invariants
at all weak pairs, the diagonal included. -/
theorem finitelyPresented_rankErosionDistance_eq_zero_iff
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N) :
    rankErosionDistance M N = 0 ↔
      ∀ (a b : Fin n → ℝ) (hab : a ≤ b),
        rankOfStructureMap M hab = rankOfStructureMap N hab := by
  rw [← rankErosion_zero_iff, ← finitelyPresented_rankErosionDistance_le_iff_rankErosion hM hN,
    ENNReal.coe_zero, nonpos_iff_eq_zero]

/-- When the erosion distance of finitely presented modules is finite, the admissible radii
are exactly the radii from the distance on. -/
theorem finitelyPresented_rankErosion_parameters_eq_Ici
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    (hf : rankErosionDistance M N ≠ ⊤) :
    {ε : ℝ≥0 | RankErosion ε M N} = Set.Ici (rankErosionDistance M N).toNNReal := by
  ext ε
  rw [Set.mem_ofPred_eq, ← finitelyPresented_rankErosionDistance_le_iff_rankErosion hM hN,
    Set.mem_Ici, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hf]

/-- The admissible erosion radii of finitely presented modules form a closed set, also when
it is empty. -/
theorem finitelyPresented_isClosed_rankErosion_parameters
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N) :
    IsClosed {ε : ℝ≥0 | RankErosion ε M N} := by
  have he : {ε : ℝ≥0 | RankErosion ε M N} =
      (fun ε : ℝ≥0 => (ε : ℝ≥0∞)) ⁻¹' Set.Ici (rankErosionDistance M N) := by
    ext ε
    exact (finitelyPresented_rankErosionDistance_le_iff_rankErosion hM hN ε).symm
  rw [he]
  exact isClosed_Ici.preimage ENNReal.continuous_coe

end GradedFree

namespace F2GridRep

/-- The Kan extension of the grid module of a valid representation is finitely presented. -/
theorem finitelyPresented_lan_toModule {n : ℕ} (R : F2GridRep n) (h : R.Valid) :
    GradedFree.FinitelyPresented.{0,0,0} (R := ZMod 2) (R.grid.lan.obj (R.toModule h)) :=
  GradedFree.finitelyPresented_lan_of_finiteGrid R.grid
    (GradedFree.pfd_finitelyPresented_of_finite_poset (R.toModule h)
      fun p => R.finiteDimensional_toModule_obj h p)

end F2GridRep

end TDA.Persistence
