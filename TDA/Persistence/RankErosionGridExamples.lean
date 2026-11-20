import TDA.Persistence.RankErosionGrid
import TDA.Persistence.HookInfinity
import TDA.Persistence.HookProjective

/-!
# Consumers of the finite rank-erosion criterion

The interval module `[0, 1)`, the Kan extension of a hook module on the grid `{0, 1}`, is
compared with the zero module at radius `1/4`: the erosion inequalities hold at every pair of
original grid values, yet the predicate fails, because the criterion's test point
`1/4 = 0 + 1/4`, a shifted breakpoint that is not a grid value, violates the first inequality.

Two further one-parameter modules are Kan extensions of principal-upset modules on one-point
grids: one is born at `0`, the other at `1`.

* At radius `1/2` the erosion inequalities hold at every pair of original grid values, yet
  the predicate fails: the criterion's test point `1/2 = 0 + 1/2`, a shifted breakpoint that
  is not a grid value, violates the first inequality.
* At radius `1` the predicate holds. It is obtained from the criterion by checking the four
  breakpoint values `-1, 0, 1, 2`.

Two degenerate cases follow: with no coordinates the predicate is equality of a single rank at
every radius, and a grid pair with an empty coordinate set gives the predicate for all modules.
-/

set_option autoImplicit false

namespace TDA.Persistence.CoordinateGrid.RankErosionGridExamples

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence NNReal ZeroObject

/-- The one-coordinate grid with the single value `c`. -/
def single (c : ℝ) : CoordinateGrid 1 := fun _ => {c}

/-- Its only point. -/
def point (c : ℝ) : (single c).Point := fun _ => ⟨c, Finset.mem_singleton_self c⟩

theorem point_le (c : ℝ) (p : (single c).Point) : point c ≤ p := by
  intro i
  have h : (p i).val = c := Finset.mem_singleton.mp (p i).property
  exact le_of_eq (Subtype.ext h.symm)

/-- The principal-upset module on the one-point grid, over `ℚ`. -/
noncomputable def upset (c : ℝ) : PModule.{0,0,0} ℚ (single c).Point :=
  HookInfinity.module (R := ℚ) (point c)

/-- The one-parameter module born at `c`: the actual Kan extension of `upset c`. -/
noncomputable def ray (c : ℝ) : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  (single c).lan.obj (upset c)

private theorem upset_rank (c : ℝ) {p q : (single c).Point} (hpq : p ≤ q) :
    rankOfStructureMap (upset c) hpq = 1 := by
  unfold rankOfStructureMap
  have hp := point_le c p
  have hinj : Function.Injective (structureMapLinear (upset c) hpq) := by
    intro x y hxy
    apply (HookInfinity.fiberEquivOfLe (R := ℚ) hp).injective
    calc
      HookInfinity.fiberEquivOfLe hp x =
          HookInfinity.fiberEquivOfLe (hp.trans hpq) (structureMapLinear (upset c) hpq x) :=
        (HookInfinity.fiberEquivOfLe_structureMap hp hpq x).symm
      _ = HookInfinity.fiberEquivOfLe (hp.trans hpq) (structureMapLinear (upset c) hpq y) :=
        congrArg _ hxy
      _ = HookInfinity.fiberEquivOfLe hp y :=
        HookInfinity.fiberEquivOfLe_structureMap hp hpq y
  rw [LinearMap.finrank_range_of_inj hinj]
  exact ((HookInfinity.fiberEquivOfLe (R := ℚ) hp).finrank_eq).trans (by simp)

theorem hasLowerPoint_single (c : ℝ) (a : Fin 1 → ℝ) :
    (single c).HasLowerPoint a ↔ c ≤ a 0 := by
  rw [hasLowerPoint_iff]
  constructor
  · intro h
    obtain ⟨g, hg, hle⟩ := h 0
    rwa [Finset.mem_singleton.mp hg] at hle
  · intro h i
    exact ⟨c, Finset.mem_singleton_self c, by rwa [Subsingleton.elim i 0]⟩

/-- From its birth onwards every structure map of the ray has rank one. -/
theorem ray_rank_eq_one (c : ℝ) {a b : Fin 1 → ℝ} (hab : a ≤ b) (h : c ≤ a 0) :
    rankOfStructureMap (ray c) hab = 1 := by
  rw [ray, rankOfStructureMap_lan _ _ hab ((hasLowerPoint_single c a).mpr h)]
  exact upset_rank c _

/-- Before its birth every structure map of the ray has rank zero. -/
theorem ray_rank_eq_zero (c : ℝ) {a b : Fin 1 → ℝ} (hab : a ≤ b) (h : a 0 < c) :
    rankOfStructureMap (ray c) hab = 0 :=
  rankOfStructureMap_lan_eq_zero _ _ hab fun hl => absurd ((hasLowerPoint_single c a).mp hl)
    (not_le.mpr h)

theorem ray_rank_le_one (c : ℝ) {a b : Fin 1 → ℝ} (hab : a ≤ b) :
    rankOfStructureMap (ray c) hab ≤ 1 := by
  rcases le_or_gt c (a 0) with h | h
  · exact (ray_rank_eq_one c hab h).le
  · rw [ray_rank_eq_zero c hab h]
    exact Nat.zero_le 1

/-- The radius one half. -/
noncomputable def half : ℝ≥0 := ⟨1 / 2, by norm_num⟩

/-- At radius `1/2`, both erosion inequalities hold at every pair of original grid values. -/
theorem original_values_pass {a b : Fin 1 → ℝ} (hab : a ≤ b) (ha : a 0 = 0 ∨ a 0 = 1) :
    rankOfStructureMap (ray 0) (erosionWide_le half hab) ≤ rankOfStructureMap (ray 1) hab ∧
      rankOfStructureMap (ray 1) (erosionWide_le half hab) ≤ rankOfStructureMap (ray 0) hab := by
  have hlow : erosionLower half a 0 = a 0 - 1 / 2 := rfl
  constructor
  · rcases ha with h | h
    · rw [ray_rank_eq_zero 0 _ (by rw [hlow, h]; norm_num)]
      exact Nat.zero_le _
    · rw [ray_rank_eq_one 1 hab (by rw [h])]
      exact ray_rank_le_one 0 _
  · rw [ray_rank_eq_zero 1 _ (by rw [hlow]; rcases ha with h | h <;> rw [h] <;> norm_num)]
    exact Nat.zero_le _

/-- The value `1/2 = 0 + 1/2` is a breakpoint of the two grids at radius `1/2`. -/
theorem half_mem_breakpoints : (1 / 2 : ℝ) ∈ erosionBreakpoints (single 0) (single 1) half 0 :=
  mem_erosionBreakpoints.mpr
    (Or.inr (Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, by
      change (0 : ℝ) + 1 / 2 = 1 / 2
      norm_num⟩)))

/-- It is not an original grid value. -/
theorem half_not_mem_grids : (1 / 2 : ℝ) ∉ single 0 0 ∪ single 1 0 := by
  simp [single]

/-- The predicate fails at radius `1/2`: the criterion's test point `1/2` violates the first
inequality, although every pair of original grid values passes. -/
theorem not_rankErosion_half : ¬ RankErosion half (ray 0) (ray 1) := by
  intro h
  let p : (erosionBreakpoints (single 0) (single 1) half).Point :=
    fun _ => ⟨1 / 2, by
      have := half_mem_breakpoints
      rwa [Subsingleton.elim (0 : Fin 1) _] at this⟩
  have hp := ((rankErosion_lan_iff (single 0) (single 1) (upset 0) (upset 1) half).mp h
    p p le_rfl).1
  have hwide : rankOfStructureMap (ray 0)
      (erosionWide_le half ((erosionBreakpoints (single 0) (single 1) half).embedding.monotone
        (le_refl p))) = 1 :=
    ray_rank_eq_one 0 _ (by
      change (0 : ℝ) ≤ 1 / 2 - 1 / 2
      norm_num)
  have hnarrow : rankOfStructureMap (ray 1)
      ((erosionBreakpoints (single 0) (single 1) half).embedding.monotone (le_refl p)) = 0 :=
    ray_rank_eq_zero 1 _ (by
      change (1 / 2 : ℝ) < 1
      norm_num)
  have hp' : rankOfStructureMap (ray 0)
      (erosionWide_le half ((erosionBreakpoints (single 0) (single 1) half).embedding.monotone
        (le_refl p))) ≤ rankOfStructureMap (ray 1)
      ((erosionBreakpoints (single 0) (single 1) half).embedding.monotone (le_refl p)) := hp
  rw [hwide, hnarrow] at hp'
  exact absurd hp' (by decide)

/-- The breakpoint values of the two grids at radius one. -/
theorem breakpoint_values {c : ℝ} (hc : c ∈ erosionBreakpoints (single 0) (single 1) 1 0) :
    c = -1 ∨ c = 0 ∨ c = 1 ∨ c = 2 := by
  rcases mem_erosionBreakpoints.mp hc with h | h | ⟨g, hg, h⟩ | ⟨g, hg, h⟩ | ⟨g, hg, h⟩ |
    ⟨g, hg, h⟩
  · exact Or.inr (Or.inl (Finset.mem_singleton.mp h))
  · exact Or.inr (Or.inr (Or.inl (Finset.mem_singleton.mp h)))
  · rw [Finset.mem_singleton.mp hg] at h
    exact Or.inr (Or.inr (Or.inl (by rw [← h]; norm_num)))
  · rw [Finset.mem_singleton.mp hg] at h
    exact Or.inl (by rw [← h]; norm_num)
  · rw [Finset.mem_singleton.mp hg] at h
    exact Or.inr (Or.inr (Or.inr (by rw [← h]; norm_num)))
  · rw [Finset.mem_singleton.mp hg] at h
    exact Or.inr (Or.inl (by rw [← h]; norm_num))

/-- At radius one the predicate holds; the criterion reduces it to the four breakpoint
values of the source grade. -/
theorem rankErosion_one : RankErosion 1 (ray 0) (ray 1) := by
  refine (rankErosion_lan_iff (single 0) (single 1) (upset 0) (upset 1) 1).mpr ?_
  intro p q hpq
  have hlow : erosionLower 1
      ((erosionBreakpoints (single 0) (single 1) 1).embedding p) 0 = (p 0).val - 1 := by
    simp [erosionLower]
  have hval : (erosionBreakpoints (single 0) (single 1) 1).embedding p 0 = (p 0).val := rfl
  change rankOfStructureMap (ray 0) _ ≤ rankOfStructureMap (ray 1) _ ∧
    rankOfStructureMap (ray 1) _ ≤ rankOfStructureMap (ray 0) _
  rcases breakpoint_values (p 0).property with h | h | h | h
  · constructor
    · rw [ray_rank_eq_zero 0 _ (by rw [hlow, h]; norm_num)]
      exact Nat.zero_le _
    · rw [ray_rank_eq_zero 1 _ (by rw [hlow, h]; norm_num)]
      exact Nat.zero_le _
  · constructor
    · rw [ray_rank_eq_zero 0 _ (by rw [hlow, h]; norm_num)]
      exact Nat.zero_le _
    · rw [ray_rank_eq_zero 1 _ (by rw [hlow, h]; norm_num)]
      exact Nat.zero_le _
  · constructor
    · rw [ray_rank_eq_one 1 _ (by rw [hval, h])]
      exact ray_rank_le_one 0 _
    · rw [ray_rank_eq_zero 1 _ (by rw [hlow, h]; norm_num)]
      exact Nat.zero_le _
  · constructor
    · rw [ray_rank_eq_one 1 _ (by rw [hval, h]; norm_num)]
      exact ray_rank_le_one 0 _
    · rw [ray_rank_eq_one 0 _ (by rw [hval, h]; norm_num)]
      exact ray_rank_le_one 1 _

section Interval

/-- The one-coordinate grid with the two values `0` and `1`. -/
noncomputable def pair : CoordinateGrid 1 := fun _ => {0, 1}

/-- Its point at `0`. -/
def lower : pair.Point := fun _ => ⟨0, by simp [pair]⟩

/-- Its point at `1`. -/
def upper : pair.Point := fun _ => ⟨1, by simp [pair]⟩

/-- The hook module on the two-point grid: one copy of `ℚ` at `0`, zero at `1`. -/
noncomputable abbrev hookOnPair : PModule.{0,0,0} ℚ pair.Point := Hook.module lower upper

/-- The interval module `[0, 1)`: the actual Kan extension of `hookOnPair`. -/
noncomputable def interval : PModule.{0,0,0} ℚ (Fin 1 → ℝ) := pair.lan.obj hookOnPair

/-- The zero module, as the Kan extension of the zero module on a one-point grid. -/
noncomputable def zeroExtension : PModule.{0,0,0} ℚ (Fin 1 → ℝ) :=
  (single 0).lan.obj (0 : PModule.{0,0,0} ℚ (single 0).Point)

theorem lower_le (p : pair.Point) : lower ≤ p := by
  intro i
  have h : (p i).val = 0 ∨ (p i).val = 1 := by simpa [pair] using (p i).property
  change (0 : ℝ) ≤ (p i).val
  rcases h with h | h <;> norm_num [h]

private theorem hookOnPair_rank_eq_one {p q : pair.Point} (hpq : p ≤ q)
    (hp : p ∈ Hook.support lower upper) (hq : q ∈ Hook.support lower upper) :
    rankOfStructureMap hookOnPair hpq = 1 := by
  unfold rankOfStructureMap
  have hinj : Function.Injective (structureMapLinear hookOnPair hpq) := by
    intro x y hxy
    apply Subtype.ext
    have hv := congrArg
      (fun z : SupportInterval.fiber (k := ℚ) (Hook.support lower upper) q => (z : ℚ)) hxy
    rw [SupportInterval.structureMap_val (Hook.support lower upper)
        (Hook.support_ordConnected lower upper) hpq x,
      SupportInterval.structureMap_val (Hook.support lower upper)
        (Hook.support_ordConnected lower upper) hpq y] at hv
    simpa [hq] using hv
  rw [LinearMap.finrank_range_of_inj hinj]
  change Module.finrank ℚ (SupportInterval.fiber (k := ℚ) (Hook.support lower upper) p) = 1
  rw [show SupportInterval.fiber (k := ℚ) (Hook.support lower upper) p = ⊤ by
    simp [SupportInterval.fiber, hp]]
  simp

private theorem hookOnPair_rank_eq_zero {p q : pair.Point} (hpq : p ≤ q)
    (hq : q ∉ Hook.support lower upper) : rankOfStructureMap hookOnPair hpq = 0 := by
  unfold rankOfStructureMap
  rw [show structureMapLinear hookOnPair hpq = 0 from
    SupportInterval.structureMap_eq_zero_of_not_mem (Hook.support lower upper)
      (Hook.support_ordConnected lower upper) hpq fun h => hq h.2,
    LinearMap.range_zero, finrank_bot]

theorem hasLowerPoint_pair (a : Fin 1 → ℝ) : pair.HasLowerPoint a ↔ 0 ≤ a 0 := by
  rw [hasLowerPoint_iff]
  constructor
  · intro h
    obtain ⟨g, hg, hle⟩ := h 0
    have hg' : g = 0 ∨ g = 1 := by simpa [pair] using hg
    rcases hg' with rfl | rfl
    · exact hle
    · exact le_trans zero_le_one hle
  · intro h i
    exact ⟨0, by simp [pair], by rwa [Subsingleton.elim i 0]⟩

private theorem floor_mem_support {x : Fin 1 → ℝ} (hx : pair.HasLowerPoint x) (h : x 0 < 1) :
    pair.floor x hx ∈ Hook.support lower upper :=
  ⟨lower_le _, fun hu => by
    have h1 : (1 : ℝ) ≤ (pair.floor x hx 0).val := hu 0
    have h2 : (pair.floor x hx 0).val ≤ x 0 := pair.floor_le x hx 0
    linarith⟩

/-- Between `0` and `1` every structure map of the interval module has rank one. -/
theorem interval_rank_eq_one {a b : Fin 1 → ℝ} (hab : a ≤ b) (ha : 0 ≤ a 0) (hb : b 0 < 1) :
    rankOfStructureMap interval hab = 1 := by
  have hla := (hasLowerPoint_pair a).mpr ha
  rw [interval, rankOfStructureMap_lan _ _ hab hla]
  exact hookOnPair_rank_eq_one _ (floor_mem_support hla (lt_of_le_of_lt (hab 0) hb))
    (floor_mem_support _ hb)

/-- Before `0` every structure map of the interval module has rank zero. -/
theorem interval_rank_eq_zero_of_lt {a b : Fin 1 → ℝ} (hab : a ≤ b) (ha : a 0 < 0) :
    rankOfStructureMap interval hab = 0 :=
  rankOfStructureMap_lan_eq_zero _ _ hab fun hl => absurd ((hasLowerPoint_pair a).mp hl)
    (not_le.mpr ha)

/-- A structure map of the interval module ending at or after `1` has rank zero. -/
theorem interval_rank_eq_zero_of_le {a b : Fin 1 → ℝ} (hab : a ≤ b) (hb : 1 ≤ b 0) :
    rankOfStructureMap interval hab = 0 := by
  by_cases hla : pair.HasLowerPoint a
  · rw [interval, rankOfStructureMap_lan _ _ hab hla]
    have hlb := pair.hasLowerPoint_mono hab hla
    refine hookOnPair_rank_eq_zero _ fun hmem => hmem.2 (pair.le_floor b hlb ?_)
    intro i
    change (1 : ℝ) ≤ b i
    rwa [Subsingleton.elim i 0]
  · exact rankOfStructureMap_lan_eq_zero _ _ hab hla

/-- Every structure map of the zero extension has rank zero. -/
theorem zeroExtension_rank {a b : Fin 1 → ℝ} (hab : a ≤ b) :
    rankOfStructureMap zeroExtension hab = 0 := by
  by_cases hla : (single 0).HasLowerPoint a
  · rw [zeroExtension, rankOfStructureMap_lan _ _ hab hla]
    exact rankOfStructureMap_zero _
  · exact rankOfStructureMap_lan_eq_zero _ _ hab hla

/-- The radius one quarter. -/
noncomputable def quarter : ℝ≥0 := ⟨1 / 4, by norm_num⟩

/-- At radius `1/4`, both erosion inequalities between the interval module and zero hold at
every weak pair whose source is an original grid value. -/
theorem interval_original_values_pass {a b : Fin 1 → ℝ} (hab : a ≤ b)
    (ha : a 0 = 0 ∨ a 0 = 1) :
    rankOfStructureMap interval (erosionWide_le quarter hab) ≤
        rankOfStructureMap zeroExtension hab ∧
      rankOfStructureMap zeroExtension (erosionWide_le quarter hab) ≤
        rankOfStructureMap interval hab := by
  have hlow : erosionLower quarter a 0 = a 0 - 1 / 4 := rfl
  have hup : erosionUpper quarter b 0 = b 0 + 1 / 4 := rfl
  constructor
  · rcases ha with h | h
    · rw [interval_rank_eq_zero_of_lt _ (by rw [hlow, h]; norm_num)]
      exact Nat.zero_le _
    · rw [interval_rank_eq_zero_of_le _ (by
        rw [hup]
        have := hab 0
        linarith)]
      exact Nat.zero_le _
  · rw [zeroExtension_rank]
    exact Nat.zero_le _

/-- The value `1/4 = 0 + 1/4` is a breakpoint of the two grids at radius `1/4`. -/
theorem quarter_mem_breakpoints :
    (1 / 4 : ℝ) ∈ erosionBreakpoints pair (single 0) quarter 0 :=
  mem_erosionBreakpoints.mpr
    (Or.inr (Or.inr (Or.inl ⟨0, by simp [pair], by
      change (0 : ℝ) + 1 / 4 = 1 / 4
      norm_num⟩)))

/-- It is not an original grid value. -/
theorem quarter_not_mem_grids : (1 / 4 : ℝ) ∉ pair 0 ∪ single 0 0 := by
  norm_num [pair, single]

/-- The interval module `[0, 1)` and the zero module do not satisfy erosion at radius `1/4`:
the criterion's test point `1/4` violates the first inequality, although every pair of
original grid values passes. -/
theorem not_rankErosion_quarter : ¬ RankErosion quarter interval zeroExtension := by
  intro h
  let p : (erosionBreakpoints pair (single 0) quarter).Point :=
    fun _ => ⟨1 / 4, by
      have := quarter_mem_breakpoints
      rwa [Subsingleton.elim (0 : Fin 1) _] at this⟩
  have hp : rankOfStructureMap interval
      (erosionWide_le quarter ((erosionBreakpoints pair (single 0) quarter).embedding.monotone
        (le_refl p))) ≤ rankOfStructureMap zeroExtension
      ((erosionBreakpoints pair (single 0) quarter).embedding.monotone (le_refl p)) :=
    ((rankErosion_lan_iff pair (single 0) hookOnPair
      (0 : PModule.{0,0,0} ℚ (single 0).Point) quarter).mp h p p le_rfl).1
  rw [interval_rank_eq_one _
      (by
        change (0 : ℝ) ≤ 1 / 4 - 1 / 4
        norm_num)
      (by
        change (1 / 4 : ℝ) + 1 / 4 < 1
        norm_num),
    zeroExtension_rank] at hp
  exact absurd hp (by decide)

end Interval

section Degenerate

universe u

variable {k : Type u} [Field k]

/-- With no coordinates there is one grade, and erosion at any radius is equality of the
single rank of the two extensions. -/
theorem rankErosion_zero_coordinates (G H : CoordinateGrid 0)
    (M : PModule.{u,0,u} k G.Point) (N : PModule.{u,0,u} k H.Point) (ε : ℝ≥0)
    (a : Fin 0 → ℝ) :
    RankErosion ε (G.lan.obj M) (H.lan.obj N) ↔
      rankOfStructureMap (G.lan.obj M) (le_refl a) =
        rankOfStructureMap (H.lan.obj N) (le_refl a) := by
  have hM : ∀ {x y : Fin 0 → ℝ} (hxy : x ≤ y),
      rankOfStructureMap (G.lan.obj M) hxy = rankOfStructureMap (G.lan.obj M) (le_refl a) :=
    fun hxy => rankOfStructureMap_lan_congr G M hxy (le_refl a) (fun i => i.elim0)
      (fun i => i.elim0)
  have hN : ∀ {x y : Fin 0 → ℝ} (hxy : x ≤ y),
      rankOfStructureMap (H.lan.obj N) hxy = rankOfStructureMap (H.lan.obj N) (le_refl a) :=
    fun hxy => rankOfStructureMap_lan_congr H N hxy (le_refl a) (fun i => i.elim0)
      (fun i => i.elim0)
  constructor
  · intro h
    have h1 := h.1 a a le_rfl
    have h2 := h.2 a a le_rfl
    rw [hM, hN] at h1
    rw [hN, hM] at h2
    exact le_antisymm h1 h2
  · intro h
    refine (rankErosion_lan_iff G H M N ε).mpr fun p q hpq => ?_
    exact ⟨(hM _).trans_le (h.trans_le (hN _).ge), (hN _).trans_le (h.symm.trans_le (hM _).ge)⟩

/-- If some coordinate has no value in either grid, there is no test point and the predicate
holds for all modules. -/
theorem rankErosion_of_empty_coordinate {n : ℕ} (G H : CoordinateGrid n)
    (M : PModule.{u,0,u} k G.Point) (N : PModule.{u,0,u} k H.Point) (ε : ℝ≥0)
    (i : Fin n) (hG : G i = ∅) (hH : H i = ∅) :
    RankErosion ε (G.lan.obj M) (H.lan.obj N) := by
  refine (rankErosion_lan_iff G H M N ε).mpr fun p _ _ => ?_
  have hp := (p i).property
  simp [erosionBreakpoints, hG, hH] at hp

end Degenerate

end TDA.Persistence.CoordinateGrid.RankErosionGridExamples
