import TDA.Persistence.ERankQTame
import TDA.Persistence.ERankErosionExamples
import TDA.Persistence.RealInterleavingRankObstruction

/-!
# Extended ranks of q-tame modules: fixtures

The real ephemeral module `realEphemeral` has the infinite-dimensional fibre `ℕ →₀ ℚ` at
every real grade, the identity on the diagonal and zero structure maps across strict
inequalities. It is q-tame but not pointwise finite-dimensional. Its one-coordinate module
has finite extended rank on every strict pair and extended rank `⊤` on the diagonal, so the
strictness in the q-tame consumer cannot be dropped. At every positive radius it is
interleaved with zero, so the local finite-image bound applies through the zero middle fibre.
-/

set_option autoImplicit false

namespace TDA.Persistence.ERankQTameExamples

open CategoryTheory TDA.Persistence CoordinateRealBridge
open TDA.Persistence.ERankErosionExamples (ephemeralInfinite)
open scoped ZeroObject NNReal ENNReal

/-- The real ephemeral module: the one-coordinate ephemeral module with fibre `ℕ →₀ ℚ`,
read on the real line. -/
noncomputable abbrev realEphemeral : PModule.{0,0,0} ℚ ℝ :=
  reindex diagonal (ephemeralInfinite (n := 1))

/-- Across a strict inequality the structure map of `realEphemeral` has extended rank `0`. -/
theorem eRank_realEphemeral_of_lt {a b : ℝ} (hab : a < b) :
    eRankOfStructureMap realEphemeral hab.le = 0 :=
  ERankErosionExamples.eRankOfStructureMap_ephemeral_of_ne _ (diagonal.monotone' hab.le)
    fun h => hab.ne (congrFun h 0)

/-- The real ephemeral module is q-tame. -/
theorem realEphemeral_qTame : realEphemeral.QTame :=
  (PModule.qTame_iff_eRankOfStructureMap_ne_top _).mpr fun _ _ hab => by
    rw [eRank_realEphemeral_of_lt hab]
    exact ENat.zero_ne_top

/-- No fibre of the real ephemeral module is finite-dimensional. -/
theorem realEphemeral_not_finiteDimensional (t : ℝ) :
    ¬ FiniteDimensional ℚ (realEphemeral.obj t) := by
  intro h
  have htop := ERankErosionExamples.eRank_ephemeralInfinite_self (diagonal t)
  rw [eRankOfStructureMap_self] at htop
  change (Module.rank ℚ (realEphemeral.obj t)).toENat = ⊤ at htop
  rw [← Module.finrank_eq_rank, Cardinal.toENat_nat] at htop
  exact ENat.natCast_ne_top _ htop

/-- The real ephemeral module is q-tame and not pointwise finite-dimensional. -/
theorem realEphemeral_qTame_not_pfd :
    realEphemeral.QTame ∧ ¬ ∀ t, FiniteDimensional ℚ (realEphemeral.obj t) :=
  ⟨realEphemeral_qTame, fun h => realEphemeral_not_finiteDimensional 0 (h 0)⟩

/-- On the diagonal the one-coordinate module of `realEphemeral` has extended rank `⊤`. -/
theorem eRank_fromReal_realEphemeral_self (a : Fin 1 → ℝ) :
    eRankOfStructureMap (fromReal realEphemeral) (le_refl a) = ⊤ := by
  rw [eRankOfStructureMap_self]
  change (Module.rank ℚ (ℕ →₀ ℚ)).toENat = ⊤
  simp

/-- The q-tame consumer on a module that is not pointwise finite-dimensional. -/
example {a b : Fin 1 → ℝ} (hab : a < b) :
    eRankOfStructureMap (fromReal realEphemeral) hab.le ≠ ⊤ :=
  realEphemeral_qTame.eRankOfStructureMap_fromReal_ne_top hab

/-- The strictness hypothesis cannot be dropped: the diagonal has extended rank `⊤`. -/
example : ¬ ∀ (a b : Fin 1 → ℝ) (hab : a ≤ b),
    eRankOfStructureMap (fromReal realEphemeral) hab ≠ ⊤ :=
  fun h => h 0 0 le_rfl (eRank_fromReal_realEphemeral_self 0)

/-- Across a strict inequality the structure map of `realEphemeral` is zero. -/
theorem structureMap_realEphemeral_of_lt {a b : ℝ} (hab : a < b) :
    structureMap realEphemeral hab.le = 0 := by
  apply ModuleCat.hom_ext
  change structureMapLinear (ephemeralInfinite (n := 1)) (diagonal.monotone' hab.le) = _
  rw [ERankErosionExamples.structureMapLinear_idempotentModule_of_ne _ _ _ _
    fun h => hab.ne (congrFun h 0)]
  rfl

/-- At every positive radius the real ephemeral module is interleaved with zero. -/
theorem nonempty_realInterleaving_realEphemeral_zero {ε : ℝ≥0} (hε : 0 < ε) :
    Nonempty (RealInterleaving ε realEphemeral (0 : PModule.{0,0,0} ℚ ℝ)) := by
  refine RealInterleaving.nonempty_realInterleaving_of_structureMap_eq_zero ε
    (fun t _ => structureMap_realEphemeral_of_lt ?_) (fun t h => ?_)
  · have : (0 : ℝ) < ((ε + ε : ℝ≥0) : ℝ) := by positivity
    linarith
  · exact (Functor.zero_obj _).eq_of_tgt _ _

/-- The local finite-image bound through the finite-dimensional middle fibre of zero, on a
module whose fibres are infinite-dimensional. -/
example {ε : ℝ≥0} (hε : 0 < ε) (a : ℝ) :
    eRankOfStructureMap realEphemeral
        (show a ≤ (a + (ε : ℝ)) + (ε : ℝ) from
          (le_add_of_nonneg_right ε.coe_nonneg).trans
            (le_add_of_nonneg_right ε.coe_nonneg)) ≠ ⊤ := by
  obtain ⟨i⟩ := nonempty_realInterleaving_realEphemeral_zero hε
  have : FiniteDimensional ℚ ((0 : PModule.{0,0,0} ℚ ℝ).obj (a + (ε : ℝ))) :=
    have : Subsingleton ((0 : PModule.{0,0,0} ℚ ℝ).obj (a + (ε : ℝ))) :=
      ModuleCat.subsingleton_of_isZero (Functor.zero_obj _)
    inferInstance
  exact i.eRankOfStructureMap_ne_top a

/-- A real interleaving gives extended-rank erosion of the one-coordinate modules. -/
example {ε : ℝ≥0} (hε : 0 < ε) :
    ERankErosion ε (fromReal realEphemeral) (fromReal (0 : PModule.{0,0,0} ℚ ℝ)) := by
  obtain ⟨i⟩ := nonempty_realInterleaving_realEphemeral_zero hε
  exact i.eRankErosion

/-- The extended erosion distance is bounded by the real interleaving distance. -/
example : eRankErosionDistance (fromReal realEphemeral) (fromReal (0 : PModule.{0,0,0} ℚ ℝ)) ≤
    realInterleavingDistance realEphemeral 0 :=
  eRankErosionDistance_fromReal_le_realInterleavingDistance _ _

end TDA.Persistence.ERankQTameExamples
