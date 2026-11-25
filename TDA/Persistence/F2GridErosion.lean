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

A failure proves that the predicate fails at this radius. This module states no distance bound.
The Kan extensions of valid representations are finitely presented, and `RankErosionCertificate`
derives from a failure that the tested radius is strictly below the erosion distance, which is
at most the interleaving distance. Which violation is reported depends on the enumeration order.
The test evaluates every comparable pair of breakpoint grades, with four enumeration ranks each.
A coordinate has at most three times as many breakpoints as the two grids have values there,
and the grades are the product over the coordinates; no polynomial bound is claimed.

Compiled code runs the scan as `erosionFailureCached?`, which reads each rank through a table
of thunks keyed by the floored pair, so each distinct pair is evaluated at most once and only
when reached. `erosionFailure?_eq_cached`, registered with `@[csimp]`, states that the two
functions are equal; kernel evaluation is unaffected.
-/

set_option autoImplicit false

namespace TDA.Persistence

open scoped TDA.Persistence NNReal

namespace RatGrid

/-- Explicit enumeration of the rational grid grades. A grade is listed once for each way of
choosing its coordinates from the lists. -/
def pointList : {n : ℕ} → RatGrid n → List (Fin n → ℚ)
  | 0, _ => [Fin.elim0]
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
both grids and their shifts by `±e`, without repetitions. -/
def erosionBreakpoints (V W : RatGrid n) (e : ℚ) : RatGrid n := fun i =>
  (V i ++ W i ++ (V i).map (· + e) ++ (V i).map (· - e) ++ (W i).map (· + e) ++
    (W i).map (· - e)).dedup

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
    List.mem_dedup, List.mem_append, List.mem_map, coe_radius]
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

/-- If every entry of an association list satisfies `P` and the fallback does, the looked-up
value with that fallback satisfies `P`. -/
theorem lookup_getD_of_forall {α β : Type*} [BEq α] [LawfulBEq α] (P : α → β → Prop)
    (l : List (α × β)) (k : α) (d : β) (hl : ∀ p ∈ l, P p.1 p.2) (hd : P k d) :
    P k ((l.lookup k).getD d) := by
  induction l with
  | nil => simpa using hd
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : k == a
    · obtain rfl : k = a := eq_of_beq h
      simpa [List.lookup] using hl (k, b) (List.mem_cons_self ..)
    · simpa [List.lookup, h] using ih fun q hq => hl q (List.mem_cons_of_mem _ hq)

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
  deriving DecidableEq, Repr

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

/-- `erosionFailureAt` with the four rank uses replaced by the given rank functions. -/
def erosionFailureAtBy (rR rS : (Fin n → ℚ) → (Fin n → ℚ) → ℕ) (e : ℚ) (p q : Fin n → ℚ) :
    Option (ErosionFailure n) :=
  if rS p q < rR (lower e p) (upper e q) then
    some ⟨true, p, q, rR (lower e p) (upper e q), rS p q⟩
  else if rR p q < rS (lower e p) (upper e q) then
    some ⟨false, p, q, rS (lower e p) (upper e q), rR p q⟩
  else none

theorem erosionFailureAt_eq_erosionFailureAtBy (R S : F2GridRep n) (e : ℚ) (p q : Fin n → ℚ) :
    erosionFailureAt R S e p q = erosionFailureAtBy R.rankAt S.rankAt e p q := rfl

/-- The ranks of the stored matrices, as a two-level association list of thunks: for each listed
source grade `a`, a thunk of the row of target grades `b`, each with a thunk of the rank of
`R.map a b`. Building the outer list costs one entry per listed source; a row is built when it is
first read, and a rank is computed when it is first read, then kept. Equal keys share the first
matching entry, so the lists need no deduplication. -/
def rankTable (R : F2GridRep n) (xs ys : List (Fin n → ℚ)) :
    List ((Fin n → ℚ) × Thunk (List ((Fin n → ℚ) × Thunk ℕ))) :=
  xs.map fun a => (a, Thunk.mk fun _ =>
    ys.map fun b => (b, Thunk.mk fun _ => Reduction.F2Matrix.rank (R.map a b)))

/-- `rankAt` read through a two-level table of rank thunks of floored grades. A source or target
missing from the table is computed as `rankAt` does. -/
def rankAtWith (R : F2GridRep n) (tbl : List ((Fin n → ℚ) × Thunk (List ((Fin n → ℚ) × Thunk ℕ))))
    (x y : Fin n → ℚ) : ℕ :=
  if R.values.hasLower x then
    Thunk.get
      ((((tbl.lookup (R.values.floor x)).getD (Thunk.mk fun _ => [])).get.lookup
          (R.values.floor y)).getD
        (Thunk.mk fun _ => Reduction.F2Matrix.rank (R.map (R.values.floor x) (R.values.floor y))))
  else 0

/-- Reading through a table built by `rankTable`, whatever its listed grades, is `rankAt`. -/
theorem rankAtWith_rankTable (R : F2GridRep n) (xs ys : List (Fin n → ℚ)) :
    R.rankAtWith (R.rankTable xs ys) = R.rankAt := by
  funext x y
  unfold rankAtWith rankAt
  split_ifs
  · have hrow := lookup_getD_of_forall
      (fun (a : Fin n → ℚ) (row : Thunk (List ((Fin n → ℚ) × Thunk ℕ))) =>
        ∀ q ∈ row.get, q.2.get = Reduction.F2Matrix.rank (R.map a q.1))
      (R.rankTable xs ys) (R.values.floor x) (Thunk.mk fun _ => [])
      (by
        intro p hp
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
        intro q hq
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hq
        rfl)
      (by
        intro q hq
        exact nomatch (show q ∈ ([] : List ((Fin n → ℚ) × Thunk ℕ)) from hq))
    exact lookup_getD_of_forall
      (fun (b : Fin n → ℚ) (t : Thunk ℕ) =>
        t.get = Reduction.F2Matrix.rank (R.map (R.values.floor x) b))
      _ (R.values.floor y) _ hrow rfl
  · rfl

/-- The scan of `erosionFailure?` with each rank of a stored matrix computed at most once per
module and read through a two-level table of thunks. Only the outer list, one entry per listed
source grade, is built before the scan; rows and ranks are built when first read, so a scan that
stops early builds little. The enumeration order and the reported fields are those of
`erosionFailure?`, to which it is equal (`erosionFailure?_eq_cached`). -/
def erosionFailureCached? (R S : F2GridRep n) (e : ℚ) : Option (ErosionFailure n) :=
  let T := (erosionBreakpoints R.values S.values e).pointList
  let xs := T ++ T.map (lower e)
  let ys := T ++ T.map (upper e)
  let rR := R.rankAtWith (R.rankTable (xs.map R.values.floor) (ys.map R.values.floor))
  let rS := S.rankAtWith (S.rankTable (xs.map S.values.floor) (ys.map S.values.floor))
  T.findSome? fun p => T.findSome? fun q =>
    if p ≤ q then erosionFailureAtBy rR rS e p q else none

/-- The cached scan is the scan. Registered with `@[csimp]`, so that compiled code, among it
`runErosion`, evaluates each distinct matrix rank once; the definition of `erosionFailure?`
and every statement about it are unchanged. -/
@[csimp] theorem erosionFailure?_eq_cached :
    @erosionFailure? = @erosionFailureCached? := by
  funext n R S e
  simp only [erosionFailureCached?, erosionFailure?, rankAtWith_rankTable]
  rfl

/-- Outcome of the executable erosion test. -/
inductive ErosionResult (n : ℕ) where
  /-- A representation is not valid, or the radius is negative. -/
  | invalid
  /-- Both inequalities hold at every comparable pair of breakpoint grades. -/
  | pass
  /-- An inequality fails. -/
  | fail (w : ErosionFailure n)
  deriving DecidableEq, Repr

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
the two grades are comparable grades of the breakpoint grid, the recorded ranks are the ranks of
the widened structure map of one extension and of the structure map of the other, the first
exceeds the second, and `RankErosion` fails. -/
theorem runErosion_eq_fail (e : ℚ) (w : ErosionFailure n) (h : runErosion R S e = .fail w) :
    ∃ (hR : R.Valid) (hS : S.Valid) (he : 0 ≤ e) (hpq : w.source ≤ w.target),
      w.source ∈ (erosionBreakpoints R.values S.values e).points ∧
      w.target ∈ (erosionBreakpoints R.values S.values e).points ∧
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
  obtain ⟨p, hpm, q, hqm, hpq, hat⟩ := erosionFailure?_eq_some R S hsome
  obtain ⟨rfl, rfl, hlt, h₁, h₂⟩ := erosionFailureAt_eq_some R S hat
  have hab : realGrade w.source ≤ realGrade w.target := realGrade_le_iff.mpr hpq
  refine ⟨hR, hS, he, hpq, hpm, hqm, hlt, fun hf => ?_, fun hf => ?_, fun hE => ?_⟩
  · rw [← R.rankAt_lower_upper hR e he rfl rfl hab, ← S.rankAt_eq_of_eq hS rfl rfl hab]
    exact h₁ hf
  · rw [← S.rankAt_lower_upper hS e he rfl rfl hab, ← R.rankAt_eq_of_eq hR rfl rfl hab]
    exact h₂ hf
  · rw [(erosionFailure?_eq_none_iff R S hR hS e he).mpr hE] at hsome
    exact absurd hsome (by simp)

end F2GridRep

end TDA.Persistence
