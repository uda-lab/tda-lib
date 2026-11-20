import TDA.Persistence.F2GridRep

/-!
# Executable rank-erosion test for F₂ grid representations

For two `F2GridRep`s and a rational radius `e`, `F2GridRep.runErosion` validates the input and
then tests the weak-pair rank inequalities of `RankErosion` on the comparable pairs of grades of
the rational breakpoint grid: the values of both grids and their shifts by `±e`. It returns
`invalid`, `pass`, or `fail` with a failed inequality: its direction, the pair of grades and the
two ranks.

The real image of the rational breakpoint grid is the breakpoint grid of the two real grids, so
the finite criterion `CoordinateGrid.rankErosion_lan_iff_of_subset` applies: the test passes if
and only if `RankErosion` holds for the actual Kan extensions of the two grid modules, and a
reported failure is a violation by those extensions.

A failure proves that the predicate fails at this radius. It gives no strict lower bound for an
erosion or interleaving distance. Which violation is reported depends on the enumeration order.
The test evaluates every comparable pair of breakpoint grades, with four enumeration ranks each;
no polynomial bound is claimed.
-/

set_option autoImplicit false

namespace TDA.Persistence

open scoped TDA.Persistence NNReal

namespace RatGrid

/-- Explicit enumeration of the rational grid grades. A grade is listed once for each way of
choosing its coordinates from the lists. -/
def pointList : {n : ℕ} → RatGrid n → List (Fin n → ℚ)
  | 0, _ => [![]]
  | _ + 1, V => (V 0).flatMap fun a => (pointList fun i => V i.succ).map fun f => Fin.cons a f

theorem mem_pointList : ∀ {n : ℕ} {V : RatGrid n} {a : Fin n → ℚ},
    a ∈ V.pointList ↔ a ∈ V.points
  | 0, V, a => by
    rw [mem_points]
    simp only [pointList, List.mem_singleton]
    exact ⟨fun _ i => i.elim0, fun _ => Subsingleton.elim _ _⟩
  | n + 1, V, a => by
    rw [mem_points]
    simp only [pointList, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, f, hf, rfl⟩ i
      have hf' := (mem_points (V := fun i => V i.succ)).mp (mem_pointList.mp hf)
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using hf' j
    · intro h
      refine ⟨a 0, h 0, Fin.tail a, ?_, Fin.cons_self_tail a⟩
      exact mem_pointList.mpr ((mem_points (V := fun i => V i.succ)).mpr fun j => h j.succ)

variable {n : ℕ}

/-- The rational breakpoints of two grids at a rational radius: per coordinate, the values of
both grids and their shifts by `±e`. -/
def erosionBreakpoints (V W : RatGrid n) (e : ℚ) : RatGrid n := fun i =>
  V i ++ W i ++ (V i).map (· + e) ++ (V i).map (· - e) ++ (W i).map (· + e) ++ (W i).map (· - e)

/-- The real radius of a nonnegative rational radius. -/
def radius (e : ℚ) (he : 0 ≤ e) : ℝ≥0 := ⟨(e : ℝ), Rat.cast_nonneg.mpr he⟩

@[simp] theorem coe_radius (e : ℚ) (he : 0 ≤ e) : ((radius e he : ℝ≥0) : ℝ) = (e : ℝ) := rfl

/-- The real image of the rational breakpoint grid is the breakpoint grid of the real grids. -/
theorem grid_erosionBreakpoints (V W : RatGrid n) (e : ℚ) (he : 0 ≤ e) :
    (erosionBreakpoints V W e).grid =
      CoordinateGrid.erosionBreakpoints V.grid W.grid (radius e he) := by
  funext i
  ext c
  simp only [mem_grid, CoordinateGrid.mem_erosionBreakpoints, erosionBreakpoints,
    List.mem_append, List.mem_map, coe_radius]
  constructor
  · rintro ⟨q, (((((hq | hq) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩), rfl⟩
    · exact Or.inl ⟨q, hq, rfl⟩
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨g, ⟨g, hg, rfl⟩, by push_cast; rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g, ⟨g, hg, rfl⟩, by push_cast; rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g, ⟨g, hg, rfl⟩, by push_cast; rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g, ⟨g, hg, rfl⟩, by push_cast; rfl⟩))))
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨_, ⟨g, hg, rfl⟩, rfl⟩ | ⟨_, ⟨g, hg, rfl⟩, rfl⟩ |
      ⟨_, ⟨g, hg, rfl⟩, rfl⟩ | ⟨_, ⟨g, hg, rfl⟩, rfl⟩)
    · exact ⟨q, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hq)))), rfl⟩
    · exact ⟨q, Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hq)))), rfl⟩
    · exact ⟨g + e, Or.inl (Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩))), by push_cast; rfl⟩
    · exact ⟨g - e, Or.inl (Or.inl (Or.inr ⟨g, hg, rfl⟩)), by push_cast; rfl⟩
    · exact ⟨g + e, Or.inl (Or.inr ⟨g, hg, rfl⟩), by push_cast; rfl⟩
    · exact ⟨g - e, Or.inr ⟨g, hg, rfl⟩, by push_cast; rfl⟩

/-- Lower every coordinate of a rational grade by a rational radius. -/
def lower (e : ℚ) (x : Fin n → ℚ) : Fin n → ℚ := fun i => x i - e

/-- Raise every coordinate of a rational grade by a rational radius. -/
def upper (e : ℚ) (x : Fin n → ℚ) : Fin n → ℚ := fun i => x i + e

theorem realGrade_lower (e : ℚ) (he : 0 ≤ e) (x : Fin n → ℚ) :
    realGrade (lower e x) = erosionLower (radius e he) (realGrade x) := by
  funext i
  simp only [realGrade_apply, lower, erosionLower, Rat.cast_sub, coe_radius]

theorem realGrade_upper (e : ℚ) (he : 0 ≤ e) (x : Fin n → ℚ) :
    realGrade (upper e x) = erosionUpper (radius e he) (realGrade x) := by
  funext i
  simp only [realGrade_apply, upper, erosionUpper, Rat.cast_add, coe_radius]

end RatGrid

namespace F2GridRep

open RatGrid

variable {n : ℕ}

/-- A failed erosion inequality: its direction, the pair of grades and the two ranks. -/
structure ErosionFailure (n : ℕ) where
  /-- `true`: the wide rank of the first module exceeds the narrow rank of the second;
  `false`: the wide rank of the second exceeds the narrow rank of the first. -/
  firstWide : Bool
  /-- The lower grade of the weak pair. -/
  source : Fin n → ℚ
  /-- The upper grade of the weak pair. -/
  target : Fin n → ℚ
  /-- The rank of the widened structure map. -/
  wideRank : ℕ
  /-- The rank of the structure map of the other module between the two grades. -/
  narrowRank : ℕ
  deriving DecidableEq

/-- The failure of the two inequalities at one pair of rational grades, if any. -/
def erosionFailureAt (R S : F2GridRep n) (e : ℚ) (p q : Fin n → ℚ) :
    Option (ErosionFailure n) :=
  if S.rankAt p q < R.rankAt (lower e p) (upper e q) then
    some ⟨true, p, q, R.rankAt (lower e p) (upper e q), S.rankAt p q⟩
  else if R.rankAt p q < S.rankAt (lower e p) (upper e q) then
    some ⟨false, p, q, S.rankAt (lower e p) (upper e q), R.rankAt p q⟩
  else none

/-- The first failure among the comparable pairs of breakpoint grades, if any. -/
def erosionFailure? (R S : F2GridRep n) (e : ℚ) : Option (ErosionFailure n) :=
  let T := (erosionBreakpoints R.values S.values e).pointList
  T.findSome? fun p => T.findSome? fun q => if p ≤ q then erosionFailureAt R S e p q else none

/-- Outcome of the executable erosion test. -/
inductive ErosionResult (n : ℕ) where
  /-- A representation is not valid, or the radius is negative. -/
  | invalid
  /-- Both inequalities hold at every comparable pair of breakpoint grades. -/
  | pass
  /-- An inequality fails. -/
  | fail (w : ErosionFailure n)
  deriving DecidableEq

/-- Validate both representations and the radius, then test erosion. -/
def runErosion (R S : F2GridRep n) (e : ℚ) : ErosionResult n :=
  if R.Valid ∧ S.Valid ∧ 0 ≤ e then
    match erosionFailure? R S e with
    | none => .pass
    | some w => .fail w
  else .invalid

variable (R S : F2GridRep n)

theorem erosionFailureAt_eq_none_iff (e : ℚ) (p q : Fin n → ℚ) :
    erosionFailureAt R S e p q = none ↔
      R.rankAt (lower e p) (upper e q) ≤ S.rankAt p q ∧
        S.rankAt (lower e p) (upper e q) ≤ R.rankAt p q := by
  unfold erosionFailureAt
  split_ifs with h₁ h₂
  · simp only [false_iff, not_and, not_le]
    exact fun h => absurd h (not_le.mpr h₁)
  · simp only [false_iff, not_and, not_le]
    exact fun _ => h₂
  · simp only [true_iff]
    exact ⟨not_lt.mp h₁, not_lt.mp h₂⟩

/-- A failure reported at a pair records that pair, a strict inequality and the two executed
ranks of the failed direction. -/
theorem erosionFailureAt_eq_some {e : ℚ} {p q : Fin n → ℚ} {w : ErosionFailure n}
    (h : erosionFailureAt R S e p q = some w) :
    w.source = p ∧ w.target = q ∧ w.narrowRank < w.wideRank ∧
      (w.firstWide = true →
        w.wideRank = R.rankAt (lower e p) (upper e q) ∧ w.narrowRank = S.rankAt p q) ∧
      (w.firstWide = false →
        w.wideRank = S.rankAt (lower e p) (upper e q) ∧ w.narrowRank = R.rankAt p q) := by
  unfold erosionFailureAt at h
  split_ifs at h with h₁ h₂
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, h₁, fun _ => ⟨rfl, rfl⟩, fun hf => absurd hf (by simp)⟩
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, h₂, fun hf => absurd hf (by simp), fun _ => ⟨rfl, rfl⟩⟩

theorem erosionFailure?_eq_none_iff_forall (e : ℚ) :
    erosionFailure? R S e = none ↔
      ∀ p ∈ (erosionBreakpoints R.values S.values e).points,
        ∀ q ∈ (erosionBreakpoints R.values S.values e).points, p ≤ q →
          R.rankAt (lower e p) (upper e q) ≤ S.rankAt p q ∧
            S.rankAt (lower e p) (upper e q) ≤ R.rankAt p q := by
  simp only [erosionFailure?, List.findSome?_eq_none_iff, mem_pointList]
  refine forall₂_congr fun p _ => forall₂_congr fun q _ => ?_
  by_cases hpq : p ≤ q
  · simp only [hpq, ↓reduceIte, forall_true_left, erosionFailureAt_eq_none_iff]
  · simp only [hpq, ↓reduceIte, false_imp_iff]

/-- A reported failure occurs at a comparable pair of breakpoint grades. -/
theorem erosionFailure?_eq_some {e : ℚ} {w : ErosionFailure n}
    (h : erosionFailure? R S e = some w) :
    ∃ p ∈ (erosionBreakpoints R.values S.values e).points,
      ∃ q ∈ (erosionBreakpoints R.values S.values e).points,
        p ≤ q ∧ erosionFailureAt R S e p q = some w := by
  obtain ⟨p, hp, hw⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨q, hq, hw'⟩ := List.exists_of_findSome?_eq_some hw
  by_cases hpq : p ≤ q
  · simp only [hpq, ↓reduceIte] at hw'
    exact ⟨p, mem_pointList.mp hp, q, mem_pointList.mp hq, hpq, hw'⟩
  · simp only [hpq, ↓reduceIte] at hw'
    exact absurd hw' (by simp)

/-- The executed wide rank is the rank of the actual Kan extension between the lowered and the
raised real grades. -/
theorem rankAt_lower_upper (hR : R.Valid) (e : ℚ) (he : 0 ≤ e) {p q : Fin n → ℚ}
    {a b : Fin n → ℝ} (ha : realGrade p = a) (hb : realGrade q = b) (hab : a ≤ b) :
    R.rankAt (lower e p) (upper e q) =
      rankOfStructureMap (R.grid.lan.obj (R.toModule hR)) (erosionWide_le (radius e he) hab) :=
  R.rankAt_eq_of_eq hR ((realGrade_lower e he p).trans (congrArg _ ha))
    ((realGrade_upper e he q).trans (congrArg _ hb)) _

/-- **Soundness and completeness of the finite test.** For valid representations and a
nonnegative radius, the test finds no failure if and only if `RankErosion` holds for the actual
Kan extensions of the two grid modules. -/
theorem erosionFailure?_eq_none_iff (hR : R.Valid) (hS : S.Valid) (e : ℚ) (he : 0 ≤ e) :
    erosionFailure? R S e = none ↔
      RankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
        (S.grid.lan.obj (S.toModule hS)) := by
  rw [erosionFailure?_eq_none_iff_forall]
  constructor
  · intro h
    refine (CoordinateGrid.rankErosion_lan_iff_of_subset R.grid S.grid (R.toModule hR)
      (S.toModule hS) (radius e he) (T := (erosionBreakpoints R.values S.values e).grid)
      (fun i => by rw [grid_erosionBreakpoints R.values S.values e he])).mpr ?_
    intro P Q hPQ
    have hp := (erosionBreakpoints R.values S.values e).realGrade_ratPoint P
    have hq := (erosionBreakpoints R.values S.values e).realGrade_ratPoint Q
    obtain ⟨h₁, h₂⟩ := h _ ((erosionBreakpoints R.values S.values e).ratPoint_mem_points P) _
      ((erosionBreakpoints R.values S.values e).ratPoint_mem_points Q)
      ((erosionBreakpoints R.values S.values e).ratPoint_le_iff.mpr hPQ)
    have hab := (erosionBreakpoints R.values S.values e).grid.embedding.monotone hPQ
    rw [R.rankAt_lower_upper hR e he hp hq hab, S.rankAt_eq_of_eq hS hp hq hab] at h₁
    rw [S.rankAt_lower_upper hS e he hp hq hab, R.rankAt_eq_of_eq hR hp hq hab] at h₂
    exact ⟨h₁, h₂⟩
  · intro h p _ q _ hpq
    have hab : realGrade p ≤ realGrade q := realGrade_le_iff.mpr hpq
    rw [R.rankAt_lower_upper hR e he rfl rfl hab, S.rankAt_eq_of_eq hS rfl rfl hab,
      S.rankAt_lower_upper hS e he rfl rfl hab, R.rankAt_eq_of_eq hR rfl rfl hab]
    exact ⟨h.1 _ _ hab, h.2 _ _ hab⟩

theorem runErosion_eq_invalid_iff (e : ℚ) :
    runErosion R S e = .invalid ↔ ¬ (R.Valid ∧ S.Valid ∧ 0 ≤ e) := by
  unfold runErosion
  split_ifs with hv
  · refine iff_of_false ?_ (not_not.mpr hv)
    split <;> simp
  · exact iff_of_true rfl hv

/-- The test passes exactly when the input is valid and `RankErosion` holds for the actual Kan
extensions. -/
theorem runErosion_eq_pass_iff (e : ℚ) :
    runErosion R S e = .pass ↔ ∃ (hR : R.Valid) (hS : S.Valid) (he : 0 ≤ e),
      RankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
        (S.grid.lan.obj (S.toModule hS)) := by
  unfold runErosion
  split_ifs with hv
  · obtain ⟨hR, hS, he⟩ := hv
    constructor
    · intro h
      refine ⟨hR, hS, he, (erosionFailure?_eq_none_iff R S hR hS e he).mp ?_⟩
      cases hf : erosionFailure? R S e with
      | none => rfl
      | some w => simp [hf] at h
    · rintro ⟨_, _, _, h⟩
      rw [(erosionFailure?_eq_none_iff R S hR hS e he).mpr h]
  · refine iff_of_false (by simp) ?_
    rintro ⟨hR, hS, he, _⟩
    exact hv ⟨hR, hS, he⟩

/-- A reported failure is a genuine violation by the actual Kan extensions: the input is valid,
the two grades are comparable, the recorded ranks are the ranks of the widened structure map of
one extension and of the structure map of the other, the first exceeds the second, and
`RankErosion` fails. -/
theorem runErosion_eq_fail (e : ℚ) (w : ErosionFailure n) (h : runErosion R S e = .fail w) :
    ∃ (hR : R.Valid) (hS : S.Valid) (he : 0 ≤ e) (hpq : w.source ≤ w.target),
      w.narrowRank < w.wideRank ∧
      (w.firstWide = true →
        w.wideRank = rankOfStructureMap (R.grid.lan.obj (R.toModule hR))
            (erosionWide_le (radius e he) (realGrade_le_iff.mpr hpq)) ∧
          w.narrowRank = rankOfStructureMap (S.grid.lan.obj (S.toModule hS))
            (realGrade_le_iff.mpr hpq)) ∧
      (w.firstWide = false →
        w.wideRank = rankOfStructureMap (S.grid.lan.obj (S.toModule hS))
            (erosionWide_le (radius e he) (realGrade_le_iff.mpr hpq)) ∧
          w.narrowRank = rankOfStructureMap (R.grid.lan.obj (R.toModule hR))
            (realGrade_le_iff.mpr hpq)) ∧
      ¬ RankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
          (S.grid.lan.obj (S.toModule hS)) := by
  unfold runErosion at h
  split_ifs at h with hv
  obtain ⟨hR, hS, he⟩ := hv
  have hsome : erosionFailure? R S e = some w := by
    cases hf : erosionFailure? R S e with
    | none => simp [hf] at h
    | some w' =>
      simp only [hf, ErosionResult.fail.injEq] at h
      rw [h]
  obtain ⟨p, _, q, _, hpq, hat⟩ := erosionFailure?_eq_some R S hsome
  obtain ⟨rfl, rfl, hlt, h₁, h₂⟩ := erosionFailureAt_eq_some R S hat
  have hab : realGrade w.source ≤ realGrade w.target := realGrade_le_iff.mpr hpq
  refine ⟨hR, hS, he, hpq, hlt, fun hf => ?_, fun hf => ?_, fun hE => ?_⟩
  · rw [← R.rankAt_lower_upper hR e he rfl rfl hab, ← S.rankAt_eq_of_eq hS rfl rfl hab]
    exact h₁ hf
  · rw [← S.rankAt_lower_upper hS e he rfl rfl hab, ← R.rankAt_eq_of_eq hR rfl rfl hab]
    exact h₂ hf
  · rw [(erosionFailure?_eq_none_iff R S hR hS e he).mpr hE] at hsome
    exact absurd hsome (by simp)

end F2GridRep

end TDA.Persistence
