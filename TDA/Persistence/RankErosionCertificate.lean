import TDA.Persistence.RankErosionAttainment
import TDA.Persistence.RankErosionInterleaving
import TDA.Persistence.F2GridErosion

/-!
# Fixed-radius comparison and distance certificates for finitely presented modules

For modules with original finite presentations the weak-pair erosion distance is attained
(`RankErosionAttainment`). With at least one coordinate the strict-pair distance equals the
weak-pair one, so the strict-pair predicate at a radius bounds the weak-pair distance by that
radius, and attainment returns the weak-pair predicate at the same radius: the two predicates
agree at every fixed radius. With no coordinates they do not.

A radius at which erosion fails is a strict lower bound of the erosion distance, and the
erosion distance is at most the interleaving distance. This chain is the certificate of a
failed test.

For the Kan extensions of two valid `F2GridRep`s, which are finitely presented, the executed
test `F2GridRep.runErosion` therefore decides whether the erosion distance is at most the
tested radius. A passing test gives both predicates and upper bounds of both erosion
distances; it does not bound the interleaving distance by that radius. A failing test gives the
certificate, and with at least one coordinate it refutes the strict-pair predicate as well.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k] {n : ℕ}
variable {M N : PModule.{u,0,u} k (Fin n → ℝ)}

namespace GradedFree

/-- For finitely presented modules with at least one coordinate, strict-pair and weak-pair
erosion agree at every fixed radius. -/
theorem finitelyPresented_strictRankErosion_iff_rankErosion [NeZero n]
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    (ε : ℝ≥0) : StrictRankErosion ε M N ↔ RankErosion ε M N := by
  have := finitelyPresented_finiteDimensional M hM
  have := finitelyPresented_finiteDimensional N hN
  refine ⟨fun h => ?_, RankErosion.strict⟩
  rw [← finitelyPresented_rankErosionDistance_le_iff_rankErosion hM hN,
    ← strictRankErosionDistance_eq_rankErosionDistance]
  exact strictRankErosionDistance_le_of_erosion h

/-- Strict-pair erosion attainment: for finitely presented modules, every finite bound of the
strict-pair distance is an admissible radius of the strict-pair predicate. With no coordinates
both sides hold for all modules. -/
theorem finitelyPresented_strictRankErosionDistance_le_iff_strictRankErosion
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    (ε : ℝ≥0) : strictRankErosionDistance M N ≤ (ε : ℝ≥0∞) ↔ StrictRankErosion ε M N := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact iff_of_true ((strictRankErosionDistance_fin_zero M N).le.trans zero_le)
      (strictRankErosion_fin_zero ε M N)
  · have : NeZero n := ⟨hn.ne'⟩
    have := finitelyPresented_finiteDimensional M hM
    have := finitelyPresented_finiteDimensional N hN
    rw [strictRankErosionDistance_eq_rankErosionDistance,
      finitelyPresented_rankErosionDistance_le_iff_rankErosion hM hN,
      finitelyPresented_strictRankErosion_iff_rankErosion hM hN]

/-- For finitely presented modules, a radius at which strict-pair erosion fails is a strict
lower bound of the strict-pair distance. -/
theorem finitelyPresented_lt_strictRankErosionDistance_of_not_strictRankErosion
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    {ε : ℝ≥0} (h : ¬ StrictRankErosion ε M N) :
    (ε : ℝ≥0∞) < strictRankErosionDistance M N :=
  lt_of_not_ge fun hle =>
    h ((finitelyPresented_strictRankErosionDistance_le_iff_strictRankErosion hM hN ε).mp hle)

/-- The certificate of a failed erosion predicate for finitely presented modules: the radius
is strictly below the erosion distance, which is at most the interleaving distance. The second
inequality is `rankErosionDistance_le_coordinateInterleavingDistance`, with finite-dimensional
fibers derived from the presentations. -/
theorem finitelyPresented_rankErosion_failure_certificate
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    {ε : ℝ≥0} (h : ¬ RankErosion ε M N) :
    (ε : ℝ≥0∞) < rankErosionDistance M N ∧
      rankErosionDistance M N ≤ coordinateInterleavingDistance M N := by
  have := finitelyPresented_finiteDimensional M hM
  have := finitelyPresented_finiteDimensional N hN
  exact ⟨finitelyPresented_lt_rankErosionDistance_of_not_rankErosion hM hN h,
    rankErosionDistance_le_coordinateInterleavingDistance M N⟩

/-- For finitely presented modules, a radius at which erosion fails is a strict lower bound of
the interleaving distance, through the erosion distance.

`radius_lt_coordinateInterleavingDistance_of_rank_violation` reaches the same conclusion from
one violated inequality at a named weak pair, for presentations whose generators and relations
are indexed in the universe of the coefficients, by attainment of the interleaving distance.
Here either inequality may fail, the presentations are indexed in `Type`, no instance is
assumed, and the erosion distance lies between the radius and the interleaving distance. The
two universe choices are exchanged by `finitelyPresented_liftIndexUniverse` and
`finitelyPresented_lowerIndexUniverse`. -/
theorem finitelyPresented_lt_coordinateInterleavingDistance_of_not_rankErosion
    (hM : FinitelyPresented.{u,0,0} (R := k) M) (hN : FinitelyPresented.{u,0,0} (R := k) N)
    {ε : ℝ≥0} (h : ¬ RankErosion ε M N) :
    (ε : ℝ≥0∞) < coordinateInterleavingDistance M N :=
  (finitelyPresented_rankErosion_failure_certificate hM hN h).1.trans_le
    (finitelyPresented_rankErosion_failure_certificate hM hN h).2

end GradedFree

namespace F2GridRep

open RatGrid

variable {n : ℕ} (R S : F2GridRep n)

/-- For valid input, the executed test decides whether the erosion distance of the actual Kan
extensions is at most the tested radius. -/
theorem runErosion_eq_pass_iff_rankErosionDistance_le (hR : R.Valid) (hS : S.Valid) {e : ℚ}
    (he : 0 ≤ e) :
    runErosion R S e = .pass ↔
      rankErosionDistance (R.grid.lan.obj (R.toModule hR)) (S.grid.lan.obj (S.toModule hS)) ≤
        ((radius e he : ℝ≥0) : ℝ≥0∞) := by
  rw [GradedFree.finitelyPresented_rankErosionDistance_le_iff_rankErosion
    (R.finitelyPresented_lan_toModule hR) (S.finitelyPresented_lan_toModule hS),
    runErosion_eq_pass_iff]
  exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨hR, hS, he, h⟩⟩

/-- For valid input with at least one coordinate, the executed test decides strict-pair
erosion of the actual Kan extensions at the tested radius. -/
theorem runErosion_eq_pass_iff_strictRankErosion [NeZero n] (hR : R.Valid) (hS : S.Valid)
    {e : ℚ} (he : 0 ≤ e) :
    runErosion R S e = .pass ↔
      StrictRankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
        (S.grid.lan.obj (S.toModule hS)) := by
  rw [GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion
    (R.finitelyPresented_lan_toModule hR) (S.finitelyPresented_lan_toModule hS),
    runErosion_eq_pass_iff]
  exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨hR, hS, he, h⟩⟩

/-- A passing test: the input is valid, both erosion predicates hold for the actual Kan
extensions at the tested radius, and both erosion distances are at most that radius. The
interleaving distance need not be at most that radius: in `RankErosionCertificateExamples` the
test `arms_zero` passes at radius `0` and `arms_nonseparation` gives a nonzero interleaving
distance. -/
theorem runErosion_eq_pass_certificate (e : ℚ) (h : runErosion R S e = .pass) :
    ∃ (hR : R.Valid) (hS : S.Valid) (he : 0 ≤ e),
      RankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
        (S.grid.lan.obj (S.toModule hS)) ∧
      StrictRankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
        (S.grid.lan.obj (S.toModule hS)) ∧
      rankErosionDistance (R.grid.lan.obj (R.toModule hR)) (S.grid.lan.obj (S.toModule hS)) ≤
        ((radius e he : ℝ≥0) : ℝ≥0∞) ∧
      strictRankErosionDistance (R.grid.lan.obj (R.toModule hR))
          (S.grid.lan.obj (S.toModule hS)) ≤ ((radius e he : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨hR, hS, he, hE⟩ := (runErosion_eq_pass_iff R S e).mp h
  exact ⟨hR, hS, he, hE, hE.strict, rankErosionDistance_le_of_erosion hE,
    strictRankErosionDistance_le_of_erosion hE.strict⟩

/-- A failing test: the input is valid, erosion fails for the actual Kan extensions at the
tested radius, the radius is strictly below their erosion distance, and the erosion distance
is at most their interleaving distance. -/
theorem runErosion_eq_fail_certificate (e : ℚ) (w : ErosionFailure n)
    (h : runErosion R S e = .fail w) :
    ∃ (hR : R.Valid) (hS : S.Valid) (he : 0 ≤ e),
      ¬ RankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
        (S.grid.lan.obj (S.toModule hS)) ∧
      ((radius e he : ℝ≥0) : ℝ≥0∞) <
        rankErosionDistance (R.grid.lan.obj (R.toModule hR))
          (S.grid.lan.obj (S.toModule hS)) ∧
      rankErosionDistance (R.grid.lan.obj (R.toModule hR)) (S.grid.lan.obj (S.toModule hS)) ≤
        coordinateInterleavingDistance (R.grid.lan.obj (R.toModule hR))
          (S.grid.lan.obj (S.toModule hS)) := by
  obtain ⟨hR, hS, he, _, _, _, _, _, _, hfail⟩ := runErosion_eq_fail R S e w h
  exact ⟨hR, hS, he, hfail, GradedFree.finitelyPresented_rankErosion_failure_certificate
    (R.finitelyPresented_lan_toModule hR) (S.finitelyPresented_lan_toModule hS) hfail⟩

/-- A failing test with at least one coordinate: strict-pair erosion fails for the actual Kan
extensions at the tested radius, which is strictly below their strict-pair distance. With no
coordinates strict-pair erosion holds for all modules. -/
theorem runErosion_eq_fail_strict_certificate [NeZero n] (e : ℚ) (w : ErosionFailure n)
    (h : runErosion R S e = .fail w) :
    ∃ (hR : R.Valid) (hS : S.Valid) (he : 0 ≤ e),
      ¬ StrictRankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
        (S.grid.lan.obj (S.toModule hS)) ∧
      ((radius e he : ℝ≥0) : ℝ≥0∞) <
        strictRankErosionDistance (R.grid.lan.obj (R.toModule hR))
          (S.grid.lan.obj (S.toModule hS)) := by
  obtain ⟨hR, hS, he, _, _, _, _, _, _, hfail⟩ := runErosion_eq_fail R S e w h
  have hstrict : ¬ StrictRankErosion (radius e he) (R.grid.lan.obj (R.toModule hR))
      (S.grid.lan.obj (S.toModule hS)) := fun hs => hfail
    ((GradedFree.finitelyPresented_strictRankErosion_iff_rankErosion
      (R.finitelyPresented_lan_toModule hR) (S.finitelyPresented_lan_toModule hS) _).mp hs)
  exact ⟨hR, hS, he, hstrict,
    GradedFree.finitelyPresented_lt_strictRankErosionDistance_of_not_strictRankErosion
      (R.finitelyPresented_lan_toModule hR) (S.finitelyPresented_lan_toModule hS) hstrict⟩

end F2GridRep

end TDA.Persistence
