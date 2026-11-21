import TDA.Persistence.F2GridHomologyIso
import TDA.Persistence.RankErosionCertificate
import TDA.Persistence.FiniteSimplicialErosion

/-!
# End-to-end erosion test of two rationally graded complexes

`RatGradedInput.runErosion xs ys p e` validates two rationally graded inputs and a rational
radius, generates both F₂ grid representations in degree `p` (`RatGradedInput.toF2GridRep`) and
runs the existing fixed-radius test `F2GridRep.erosionFailure?` on them. Its outcome
`RatGradedInput.ErosionResult` keeps an invalid first input, an invalid second input and a
negative radius apart from `pass` and `fail w`; the witness `w` is the existing
`F2GridRep.ErosionFailure`.

Through the isomorphism `RatGradedInput.toF2GridRep_lanIso` every outcome is a statement about
the actual homology modules `RatGradedInput.homology`: `pass` holds exactly when `RankErosion`
holds at the radius, and a failure records a direction, a comparable pair of breakpoint grades
and the ranks of the actual widened and narrow structure maps, which violate the inequality.
The actual modules are finitely presented (`finiteSimplicialHomology_finitelyPresented`), so a
pass bounds both erosion distances by the radius, and a failure puts the radius strictly below
the erosion distance, which is at most the interleaving distance.

For two inputs with the same face list, the grade-error bound of the actual homology modules
gives erosion, hence a pass, at any rational bound of the grade differences.

One selected degree, coefficients `ZMod 2`, faces listed after their proper faces. The test
minimises no radius. Which violation is reported depends on the enumeration order.
-/

set_option autoImplicit false

namespace TDA.Persistence

open CategoryTheory TDA.Simplicial TDA.Filtration
open scoped NNReal ENNReal

namespace RatGradedInput

open RatGrid F2GridRep

variable {m m' n : ℕ}

/-- Outcome of the end-to-end erosion test of two rationally graded inputs. -/
inductive ErosionResult (n : ℕ) where
  /-- The first input is not valid. -/
  | invalidFirst
  /-- The first input is valid and the second is not. -/
  | invalidSecond
  /-- Both inputs are valid and the radius is negative. -/
  | negativeRadius
  /-- Both inequalities hold at every comparable pair of breakpoint grades. -/
  | pass
  /-- An inequality fails. -/
  | fail (w : F2GridRep.ErosionFailure n)
  deriving DecidableEq, Repr

/-- Validate both inputs and the radius, generate both F₂ grid representations in degree `p`,
and run the existing fixed-radius test on them. -/
def runErosion (xs : RatGradedInput m n) (ys : RatGradedInput m' n) (p : ℕ) (e : ℚ) :
    ErosionResult n :=
  if ¬ Valid xs then .invalidFirst
  else if ¬ Valid ys then .invalidSecond
  else if e < 0 then .negativeRadius
  else
    match erosionFailure? (toF2GridRep xs p) (toF2GridRep ys p) e with
    | none => .pass
    | some w => .fail w

/-- On valid input and a nonnegative radius, the end-to-end run is the existing test on the
generated representations. The `.invalid` branch is unreachable here: both generated
representations are valid (`toF2GridRep_valid`) and the radius is nonnegative. -/
theorem runErosion_eq_of_valid {xs : RatGradedInput m n} {ys : RatGradedInput m' n}
    (hx : Valid xs) (hy : Valid ys) (p : ℕ) {e : ℚ} (he : 0 ≤ e) :
    runErosion xs ys p e =
      match F2GridRep.runErosion (toF2GridRep xs p) (toF2GridRep ys p) e with
      | .invalid => .negativeRadius
      | .pass => .pass
      | .fail w => .fail w := by
  have hv : (toF2GridRep xs p).Valid ∧ (toF2GridRep ys p).Valid ∧ 0 ≤ e :=
    ⟨toF2GridRep_valid hx p, toF2GridRep_valid hy p, he⟩
  unfold runErosion F2GridRep.runErosion
  simp only [hx, hy, not_lt.mpr he, hv, not_true_eq_false, ↓reduceIte]
  cases erosionFailure? (toF2GridRep xs p) (toF2GridRep ys p) e <;> rfl

/-- The run reports the first input exactly when it fails validation. -/
theorem runErosion_eq_invalidFirst_iff (xs : RatGradedInput m n) (ys : RatGradedInput m' n)
    (p : ℕ) (e : ℚ) : runErosion xs ys p e = .invalidFirst ↔ ¬ Valid xs := by
  unfold runErosion
  split_ifs <;> (try split) <;> simp_all

/-- The run reports the second input exactly when the first is valid and the second is not. -/
theorem runErosion_eq_invalidSecond_iff (xs : RatGradedInput m n) (ys : RatGradedInput m' n)
    (p : ℕ) (e : ℚ) : runErosion xs ys p e = .invalidSecond ↔ Valid xs ∧ ¬ Valid ys := by
  unfold runErosion
  split_ifs <;> (try split) <;> simp_all

/-- The run reports invalid input exactly when one of the two inputs fails validation. -/
theorem runErosion_eq_invalid_iff (xs : RatGradedInput m n) (ys : RatGradedInput m' n)
    (p : ℕ) (e : ℚ) :
    (runErosion xs ys p e = .invalidFirst ∨ runErosion xs ys p e = .invalidSecond) ↔
      ¬ (Valid xs ∧ Valid ys) := by
  rw [runErosion_eq_invalidFirst_iff, runErosion_eq_invalidSecond_iff]
  tauto

/-- The run reports a negative radius exactly when both inputs are valid and the radius is
negative. -/
theorem runErosion_eq_negativeRadius_iff (xs : RatGradedInput m n) (ys : RatGradedInput m' n)
    (p : ℕ) (e : ℚ) :
    runErosion xs ys p e = .negativeRadius ↔ Valid xs ∧ Valid ys ∧ e < 0 := by
  unfold runErosion
  split_ifs <;> (try split) <;> simp_all

/-- **Pass.** The run passes exactly when both inputs are valid, the radius is nonnegative and
weak-pair rank erosion holds at that radius between the actual degree-`p` homology modules. -/
theorem runErosion_eq_pass_iff (xs : RatGradedInput m n) (ys : RatGradedInput m' n) (p : ℕ)
    (e : ℚ) :
    runErosion xs ys p e = .pass ↔ ∃ (hx : Valid xs) (hy : Valid ys) (he : 0 ≤ e),
      RankErosion (radius e he) (homology xs hx p) (homology ys hy p) := by
  constructor
  · intro h
    have hx : Valid xs := by
      by_contra hx
      rw [(runErosion_eq_invalidFirst_iff xs ys p e).mpr hx] at h
      exact absurd h (by simp)
    have hy : Valid ys := by
      by_contra hy
      rw [(runErosion_eq_invalidSecond_iff xs ys p e).mpr ⟨hx, hy⟩] at h
      exact absurd h (by simp)
    have he : 0 ≤ e := by
      by_contra he
      rw [(runErosion_eq_negativeRadius_iff xs ys p e).mpr ⟨hx, hy, not_le.mp he⟩] at h
      exact absurd h (by simp)
    refine ⟨hx, hy, he, ?_⟩
    rw [runErosion_eq_of_valid hx hy p he] at h
    have hpass : F2GridRep.runErosion (toF2GridRep xs p) (toF2GridRep ys p) e = .pass := by
      revert h
      cases F2GridRep.runErosion (toF2GridRep xs p) (toF2GridRep ys p) e <;> simp
    obtain ⟨hR, hS, he', hE⟩ := (F2GridRep.runErosion_eq_pass_iff _ _ e).mp hpass
    exact (rankErosion_lan_toF2GridRep_iff hx hy p _).mp hE
  · rintro ⟨hx, hy, he, hE⟩
    rw [runErosion_eq_of_valid hx hy p he,
      (F2GridRep.runErosion_eq_pass_iff _ _ e).mpr
        ⟨toF2GridRep_valid hx p, toF2GridRep_valid hy p, he,
          (rankErosion_lan_toF2GridRep_iff hx hy p _).mpr hE⟩]

/-- A reported failure of the end-to-end run is a reported failure of the existing test on the
generated representations. -/
theorem runErosion_eq_fail_iff {xs : RatGradedInput m n} {ys : RatGradedInput m' n}
    {p : ℕ} {e : ℚ} {w : F2GridRep.ErosionFailure n} :
    runErosion xs ys p e = .fail w ↔ ∃ (_ : Valid xs) (_ : Valid ys),
      F2GridRep.runErosion (toF2GridRep xs p) (toF2GridRep ys p) e = .fail w := by
  constructor
  · intro h
    have hx : Valid xs := by
      by_contra hx
      rw [(runErosion_eq_invalidFirst_iff xs ys p e).mpr hx] at h
      exact absurd h (by simp)
    have hy : Valid ys := by
      by_contra hy
      rw [(runErosion_eq_invalidSecond_iff xs ys p e).mpr ⟨hx, hy⟩] at h
      exact absurd h (by simp)
    have he : 0 ≤ e := by
      by_contra he
      rw [(runErosion_eq_negativeRadius_iff xs ys p e).mpr ⟨hx, hy, not_le.mp he⟩] at h
      exact absurd h (by simp)
    refine ⟨hx, hy, ?_⟩
    rw [runErosion_eq_of_valid hx hy p he] at h
    revert h
    cases F2GridRep.runErosion (toF2GridRep xs p) (toF2GridRep ys p) e <;> simp
  · rintro ⟨hx, hy, h⟩
    obtain ⟨-, -, he, -⟩ := F2GridRep.runErosion_eq_fail _ _ e w h
    rw [runErosion_eq_of_valid hx hy p he, h]

/-- **Failure.** A reported failure is a violation by the actual homology modules: both inputs
are valid, the radius is nonnegative, the two recorded grades are comparable grades of the
breakpoint grid, the recorded ranks are the ranks of the widened structure map of one actual
homology module and of the structure map of the other between the recorded grades, the first
exceeds the second, and `RankErosion` fails. -/
theorem runErosion_eq_fail {xs : RatGradedInput m n} {ys : RatGradedInput m' n} {p : ℕ}
    {e : ℚ} {w : F2GridRep.ErosionFailure n} (h : runErosion xs ys p e = .fail w) :
    ∃ (hx : Valid xs) (hy : Valid ys) (he : 0 ≤ e) (hst : w.source ≤ w.target),
      w.source ∈ (erosionBreakpoints (gridValues xs) (gridValues ys) e).points ∧
      w.target ∈ (erosionBreakpoints (gridValues xs) (gridValues ys) e).points ∧
      w.narrowRank < w.wideRank ∧
      (w.firstWide = true →
        w.wideRank = rankOfStructureMap (homology xs hx p)
            (erosionWide_le (radius e he) (realGrade_le_iff.mpr hst)) ∧
          w.narrowRank = rankOfStructureMap (homology ys hy p) (realGrade_le_iff.mpr hst)) ∧
      (w.firstWide = false →
        w.wideRank = rankOfStructureMap (homology ys hy p)
            (erosionWide_le (radius e he) (realGrade_le_iff.mpr hst)) ∧
          w.narrowRank = rankOfStructureMap (homology xs hx p) (realGrade_le_iff.mpr hst)) ∧
      ¬ RankErosion (radius e he) (homology xs hx p) (homology ys hy p) := by
  obtain ⟨hx, hy, hrun⟩ := runErosion_eq_fail_iff.mp h
  obtain ⟨_, _, he, hst, hsm, htm, hlt, h₁, h₂, hfail⟩ :=
    F2GridRep.runErosion_eq_fail _ _ e w hrun
  refine ⟨hx, hy, he, hst, hsm, htm, hlt, fun hf => ?_, fun hf => ?_, fun hE => hfail
    ((rankErosion_lan_toF2GridRep_iff hx hy p _).mpr hE)⟩
  · obtain ⟨hw, hn⟩ := h₁ hf
    exact ⟨hw.trans (rankOfStructureMap_iso _ (toF2GridRep_lanIso hx p)),
      hn.trans (rankOfStructureMap_iso _ (toF2GridRep_lanIso hy p))⟩
  · obtain ⟨hw, hn⟩ := h₂ hf
    exact ⟨hw.trans (rankOfStructureMap_iso _ (toF2GridRep_lanIso hy p)),
      hn.trans (rankOfStructureMap_iso _ (toF2GridRep_lanIso hx p))⟩

/-- For valid input and a nonnegative radius, the run passes exactly when the erosion distance
of the actual homology modules is at most the radius. -/
theorem runErosion_eq_pass_iff_rankErosionDistance_le {xs : RatGradedInput m n}
    {ys : RatGradedInput m' n} (hx : Valid xs) (hy : Valid ys) (p : ℕ) {e : ℚ} (he : 0 ≤ e) :
    runErosion xs ys p e = .pass ↔
      rankErosionDistance (homology xs hx p) (homology ys hy p) ≤
        ((radius e he : ℝ≥0) : ℝ≥0∞) := by
  rw [GradedFree.finitelyPresented_rankErosionDistance_le_iff_rankErosion
    (finiteSimplicialHomology_finitelyPresented (ZMod 2) _ p)
    (finiteSimplicialHomology_finitelyPresented (ZMod 2) _ p), runErosion_eq_pass_iff]
  exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨hx, hy, he, h⟩⟩

/-- With at least one coordinate, for valid input and a nonnegative radius, the run passes
exactly when strict-pair erosion holds between the actual homology modules. -/
theorem runErosion_eq_pass_iff_strictRankErosion [NeZero n] {xs : RatGradedInput m n}
    {ys : RatGradedInput m' n} (hx : Valid xs) (hy : Valid ys) (p : ℕ) {e : ℚ} (he : 0 ≤ e) :
    runErosion xs ys p e = .pass ↔
      StrictRankErosion (radius e he) (homology xs hx p) (homology ys hy p) := by
  rw [GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion
    (finiteSimplicialHomology_finitelyPresented (ZMod 2) _ p)
    (finiteSimplicialHomology_finitelyPresented (ZMod 2) _ p), runErosion_eq_pass_iff]
  exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨hx, hy, he, h⟩⟩

/-- A passing run: both inputs are valid, both erosion predicates hold between the actual
homology modules at the radius, and both erosion distances are at most the radius. Nothing
follows for the interleaving distance. -/
theorem runErosion_eq_pass_certificate {xs : RatGradedInput m n} {ys : RatGradedInput m' n}
    {p : ℕ} {e : ℚ} (h : runErosion xs ys p e = .pass) :
    ∃ (hx : Valid xs) (hy : Valid ys) (he : 0 ≤ e),
      RankErosion (radius e he) (homology xs hx p) (homology ys hy p) ∧
      StrictRankErosion (radius e he) (homology xs hx p) (homology ys hy p) ∧
      rankErosionDistance (homology xs hx p) (homology ys hy p) ≤
        ((radius e he : ℝ≥0) : ℝ≥0∞) ∧
      strictRankErosionDistance (homology xs hx p) (homology ys hy p) ≤
        ((radius e he : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨hx, hy, he, hE⟩ := (runErosion_eq_pass_iff xs ys p e).mp h
  exact ⟨hx, hy, he, hE, hE.strict, rankErosionDistance_le_of_erosion hE,
    strictRankErosionDistance_le_of_erosion hE.strict⟩

/-- A failing run: both inputs are valid, erosion fails between the actual homology modules at
the radius, the radius is strictly below their erosion distance, and that is at most their
interleaving distance. -/
theorem runErosion_eq_fail_certificate {xs : RatGradedInput m n} {ys : RatGradedInput m' n}
    {p : ℕ} {e : ℚ} {w : F2GridRep.ErosionFailure n} (h : runErosion xs ys p e = .fail w) :
    ∃ (hx : Valid xs) (hy : Valid ys) (he : 0 ≤ e),
      ¬ RankErosion (radius e he) (homology xs hx p) (homology ys hy p) ∧
      ((radius e he : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance (homology xs hx p) (homology ys hy p) ∧
      rankErosionDistance (homology xs hx p) (homology ys hy p) ≤
        coordinateInterleavingDistance (homology xs hx p) (homology ys hy p) := by
  obtain ⟨hx, hy, he, -, -, -, -, -, -, hfail⟩ := runErosion_eq_fail h
  exact ⟨hx, hy, he, hfail, GradedFree.finitelyPresented_rankErosion_failure_certificate
    (finiteSimplicialHomology_finitelyPresented (ZMod 2) _ p)
    (finiteSimplicialHomology_finitelyPresented (ZMod 2) _ p) hfail⟩

/-- A failing run with at least one coordinate: strict-pair erosion fails between the actual
homology modules at the radius, which is strictly below their strict-pair distance. -/
theorem runErosion_eq_fail_strict_certificate [NeZero n] {xs : RatGradedInput m n}
    {ys : RatGradedInput m' n} {p : ℕ} {e : ℚ} {w : F2GridRep.ErosionFailure n}
    (h : runErosion xs ys p e = .fail w) :
    ∃ (hx : Valid xs) (hy : Valid ys) (he : 0 ≤ e),
      ¬ StrictRankErosion (radius e he) (homology xs hx p) (homology ys hy p) ∧
      ((radius e he : ℝ≥0) : ℝ≥0∞) <
        strictRankErosionDistance (homology xs hx p) (homology ys hy p) := by
  obtain ⟨hx, hy, he, -, -, -, -, -, -, hfail⟩ := runErosion_eq_fail h
  have hfx := finiteSimplicialHomology_finitelyPresented (ZMod 2) (toGraded xs hx) p
  have hfy := finiteSimplicialHomology_finitelyPresented (ZMod 2) (toGraded ys hy) p
  have hstrict : ¬ StrictRankErosion (radius e he) (homology xs hx p) (homology ys hy p) :=
    fun hs => hfail
      ((GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion hfx hfy _).mp hs)
  exact ⟨hx, hy, he, hstrict,
    GradedFree.finitelyPresented_lt_strictRankErosionDistance_of_not_strictRankErosion
      hfx hfy hstrict⟩

private theorem rankErosion_of_complex_eq {C C' : FiniteComplex m} (hC : C = C')
    (g : FiniteGraded C n) (g' : FiniteGraded C' n) (q : ℕ) {δ : ℝ≥0}
    (herr : ∀ (s : TotalFace C.toPre) (hs : s.val ∈ C'.toPre) (i : Fin n),
      |g.grade s i - g'.grade ⟨s.val, hs⟩ i| ≤ (δ : ℝ)) :
    RankErosion δ (finiteSimplicialHomology (ZMod 2) g q)
      (finiteSimplicialHomology (ZMod 2) g' q) := by
  subst hC
  exact finiteSimplicialHomology_rankErosion (ZMod 2) g g' q fun s i => herr s s.property i

/-- Two valid inputs with the same face list whose grades of each face differ by at most a
rational `d` in every coordinate satisfy erosion at radius `d` in every degree: the grade-error
bound of the actual homology modules. -/
theorem rankErosion_homology_of_faces_eq {xs ys : RatGradedInput m n} (hx : Valid xs)
    (hy : Valid ys) (hf : faces xs = faces ys) (p : ℕ) {d : ℚ} (hd : 0 ≤ d)
    (herror : ∀ e ∈ xs, ∀ f ∈ ys, e.1 = f.1 → ∀ i, |e.2 i - f.2 i| ≤ d) :
    RankErosion (radius d hd) (homology xs hx p) (homology ys hy p) := by
  have hC : toComplex xs hx = toComplex ys hy := by
    cases hcx : toComplex xs hx
    cases hcy : toComplex ys hy
    have h1 : (toComplex xs hx).faces = (toComplex ys hy).faces := by
      change (faces xs).toFinset = (faces ys).toFinset
      rw [hf]
    rw [hcx, hcy] at h1
    simp only at h1
    subst h1
    rfl
  refine rankErosion_of_complex_eq hC _ _ p fun s hs i => ?_
  obtain ⟨e, he, hes⟩ := mem_faces.mp ((mem_toComplex xs hx s.val).mp s.property)
  obtain ⟨f, hf', hfs⟩ := mem_faces.mp ((mem_toComplex ys hy s.val).mp hs)
  rw [toGraded_grade, toGraded_grade, ← hes, gradeOf_eq hx he, hes, ← hfs, gradeOf_eq hy hf']
  simp only [realGrade_apply, coe_radius]
  rw [← Rat.cast_sub, ← Rat.cast_abs]
  exact_mod_cast herror e he f hf' (hes.trans hfs.symm) i

/-- Under the same hypotheses the run passes at radius `d` in every degree. -/
theorem runErosion_eq_pass_of_faces_eq {xs ys : RatGradedInput m n} (hx : Valid xs)
    (hy : Valid ys) (hf : faces xs = faces ys) (p : ℕ) {d : ℚ} (hd : 0 ≤ d)
    (herror : ∀ e ∈ xs, ∀ f ∈ ys, e.1 = f.1 → ∀ i, |e.2 i - f.2 i| ≤ d) :
    runErosion xs ys p d = .pass :=
  (runErosion_eq_pass_iff xs ys p d).mpr
    ⟨hx, hy, hd, rankErosion_homology_of_faces_eq hx hy hf p hd herror⟩

end RatGradedInput

end TDA.Persistence
