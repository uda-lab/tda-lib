import TDA.Persistence.RealInterleavingDistance
import TDA.Persistence.RealIntervalInterleaving
import Mathlib.Tactic.Linarith

/-!
# Infinite and unattained real interleaving distances

The ephemeral module has a nonzero fiber only at time zero. Its functor maps
give positive-parameter witnesses with zero, while its nonzero fiber excludes attainment.
-/

set_option autoImplicit false

namespace TDA.Persistence.RealInterleavingDistanceExamples

open CategoryTheory CategoryTheory.Limits RealShift
open scoped NNReal ENNReal ZeroObject

private noncomputable def pointFiber (t : ℝ) : Submodule ℚ ℚ :=
  if t = 0 then ⊤ else ⊥

private noncomputable def pointMap {s t : ℝ} (_h : s ≤ t) :
    pointFiber s →ₗ[ℚ] pointFiber t := by
  classical
  exact if h : s = 0 ∧ t = 0 then
    Submodule.inclusion (by simp [pointFiber, h.1, h.2]) else 0

private noncomputable def ephemeral : PModule.{0,0,0} ℚ ℝ where
  obj t := ModuleCat.of ℚ (pointFiber t)
  map f := ModuleCat.ofHom (pointMap (leOfHom f))
  map_id t := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases ht : t = 0
    · simp [pointMap, ht]
    · have hx : (x : ℚ) = 0 := by
        simpa only [pointFiber, if_neg ht, Submodule.mem_bot] using x.property
      simp [pointMap, ht, hx]
  map_comp {s t r} f g := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases hs : s = 0
    · by_cases hr : r = 0
      · have ht : t = 0 := le_antisymm (by simpa [hr] using leOfHom g)
          (by simpa [hs] using leOfHom f)
        simp [pointMap, hs, ht, hr]
      · simp [pointMap, hr]
    · simp [pointMap, hs]

private theorem ephemeral_not_isZero : ¬ IsZero ephemeral := by
  intro h
  have hs : Subsingleton (pointFiber 0) := ModuleCat.isZero_iff_subsingleton.mp (h.obj 0)
  let one : pointFiber 0 := ⟨1, by simp [pointFiber]⟩
  have heq := congrArg (fun x : pointFiber 0 => (x : ℚ)) (hs.elim one 0)
  exact (one_ne_zero : (1 : ℚ) ≠ 0) heq

private theorem ephemeral_transition_zero (ε : ℝ≥0) (hε : 0 < ε) :
    transition (ε + ε) ephemeral = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hn : ¬ (t = 0 ∧ t + ((ε + ε : ℝ≥0) : ℝ) = 0) := by
    rintro ⟨ht, he⟩
    have hp : (0 : ℝ) < ε := hε
    simp only [NNReal.coe_add, ht, zero_add] at he
    linarith
  have hn' : ¬ (t = 0 ∧ t + ((ε : ℝ) + (ε : ℝ)) = 0) := by
    simpa only [NNReal.coe_add] using hn
  simp [transition, structureMap, ephemeral, pointMap, hn']
  rfl

/-- Every positive parameter admits zero comparison maps for the ephemeral module. -/
theorem ephemeral_positive_interleaving (ε : ℝ≥0) (hε : 0 < ε) :
    Nonempty (RealInterleaving ε ephemeral 0) :=
  (RealInterleaving.nonempty_zero_iff ε ephemeral).mpr (ephemeral_transition_zero ε hε)

/-- The ephemeral module is not naturally isomorphic to zero. -/
theorem ephemeral_not_iso_zero : IsEmpty (ephemeral ≅ 0) :=
  ⟨fun e => ephemeral_not_isZero ((isZero_zero _).of_iso e)⟩

/-- Zero distance need not admit a zero-interleaving. -/
theorem ephemeral_distance_unattained :
    realInterleavingDistance ephemeral 0 = 0 ∧ IsEmpty (RealInterleaving 0 ephemeral 0) := by
  refine ⟨realInterleavingDistance_eq_zero_iff.mpr ephemeral_positive_interleaving, ?_⟩
  exact ⟨fun i => ephemeral_not_iso_zero.false i.toIso⟩

/-- An essential interval has infinite distance to zero over a nontrivial field. -/
theorem essential_distance_top (b : ℝ) :
    realInterleavingDistance (RealBarcode.intervalModule (k := ℚ) (b, ⊤)) 0 = ⊤ :=
  realInterleavingDistance_eq_top_iff.mpr fun ε =>
    not_nonempty_iff.mp (RealBarcode.essential_not_interleaved_zero ε b)

/-- Strict approximation at the zero extended bound has no witnesses. -/
theorem strict_zero (M N : PModule.{0,0,0} ℚ ℝ) :
    ¬ ∃ ε : ℝ≥0, (ε : ℝ≥0∞) < 0 ∧ Nonempty (RealInterleaving ε M N) := by
  rw [← realInterleavingDistance_lt_iff]
  exact not_lt_of_ge bot_le

/-- At the infinite bound, strict approximation is precisely existence of a finite witness. -/
theorem strict_top (M N : PModule.{0,0,0} ℚ ℝ) :
    realInterleavingDistance M N < ⊤ ↔ ∃ ε : ℝ≥0, Nonempty (RealInterleaving ε M N) := by
  simp only [realInterleavingDistance_lt_iff, ENNReal.coe_lt_top, true_and]

/-- The unconditional triangle law includes an infinite summand. -/
theorem infinite_triangle (M N P : PModule.{0,0,0} ℚ ℝ)
    (h : realInterleavingDistance M N = ⊤) :
    realInterleavingDistance M P ≤ realInterleavingDistance M N +
      realInterleavingDistance N P := by
  simp [h]

private noncomputable def unit : PModule.{0,0,0} ℚ ℝ :=
  (Functor.const ℝ).obj (ModuleCat.of ℚ ℚ)

/-- Unequal finite parameters compose on a module with nonzero fibers. -/
noncomputable def unequal_composition : RealInterleaving (1 + 2) unit unit :=
  (RealInterleaving.refl 1 unit).trans (RealInterleaving.refl 2 unit)

/-- Enlargement also applies at the zero and equality boundaries. -/
noncomputable def zero_enlargement : RealInterleaving 1 unit unit :=
  ((RealInterleaving.ofIso (Iso.refl unit)).mono (show 0 ≤ (1 : ℝ≥0) from zero_le)).mono le_rfl

end TDA.Persistence.RealInterleavingDistanceExamples
