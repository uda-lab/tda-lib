import TDA.Persistence.RealInterleaving
import TDA.Persistence.RealBarcode
import Mathlib.Tactic.Linarith

/-!
# Real interleaving boundary examples

At epsilon one, `[0,2)` interleaves with zero while `[0,3)` does not. The essential
interval `[0,∞)` cannot interleave with zero at any finite parameter over a field,
whose coefficients are nontrivial. These are statements about structure maps.
-/

set_option autoImplicit false

namespace TDA.Persistence.RealInterleavingExamples

open CategoryTheory CategoryTheory.Limits RealShift
open scoped NNReal ZeroObject

private noncomputable def constantUnit : PModule.{0,0,0} ℚ ℝ :=
  (Functor.const ℝ).obj (ModuleCat.of ℚ ℚ)

/-- The zero-interleaving example really has nonzero fibers. -/
theorem constantUnit_not_isZero : ¬ IsZero constantUnit := by
  intro h
  have : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp (h.obj 0)
  exact (zero_ne_one : (0 : ℚ) ≠ 1) (Subsingleton.elim _ _)

/-- Zero interleaving applies to a nonzero module, with both conversions checked. -/
noncomputable def constantZeroInterleaving : RealInterleaving 0 constantUnit constantUnit :=
  RealInterleaving.zeroEquivIso.symm (Iso.refl constantUnit)

/-- The constructed zero witness converts back to the original natural isomorphism. -/
theorem constant_zero_roundtrip :
    RealInterleaving.zeroEquivIso constantZeroInterleaving = Iso.refl constantUnit :=
  RealInterleaving.zeroEquivIso.apply_symm_apply _

section Intervals

variable {k : Type*} [Field k]

private theorem interval_map_eq_zero (p : ℝ × WithTop ℝ) {s t : ℝ} (h : s ≤ t)
    (hn : ¬ (RealBarcode.alive p s ∧ RealBarcode.alive p t)) :
    structureMap (RealBarcode.intervalModule (k := k) p) h = 0 := by
  classical
  by_cases hs : RealBarcode.alive p s
  · have ht : ¬ RealBarcode.alive p t := fun ht => hn ⟨hs, ht⟩
    have : Subsingleton ((RealBarcode.intervalModule (k := k) p).obj t) := by
      change Subsingleton (RealBarcode.fiber (k := k) p t)
      rw [RealBarcode.fiber, if_neg ht]
      infer_instance
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_tgt _ _
  · have : Subsingleton ((RealBarcode.intervalModule (k := k) p).obj s) := by
      change Subsingleton (RealBarcode.fiber (k := k) p s)
      rw [RealBarcode.fiber, if_neg hs]
      infer_instance
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

-- Evaluating the map on coefficient one makes the nontrivial coefficient
-- hypothesis explicit; a dimension comparison alone would not identify that map.
private theorem interval_map_ne_zero (p : ℝ × WithTop ℝ) {s t : ℝ} (h : s ≤ t)
    (hs : RealBarcode.alive p s) (ht : RealBarcode.alive p t) :
    structureMap (RealBarcode.intervalModule (k := k) p) h ≠ 0 := by
  classical
  let x : RealBarcode.fiber (k := k) p s := ⟨1, by simp [RealBarcode.fiber, hs]⟩
  have hcoeff : (show RealBarcode.fiber (k := k) p t from
      (structureMap (RealBarcode.intervalModule p) h).hom x).val = 1 := by
    change (((if hp : RealBarcode.alive p s ∧ RealBarcode.alive p t then
        Submodule.inclusion (show RealBarcode.fiber (k := k) p s ≤ RealBarcode.fiber p t by
          simp [RealBarcode.fiber, hp.1, hp.2]) else 0) x)).val = 1
    rw [dif_pos ⟨hs, ht⟩]
    rfl
  intro heq
  have hx := congrArg (fun f : (RealBarcode.intervalModule (k := k) p).obj s ⟶
      (RealBarcode.intervalModule p).obj t =>
      (show RealBarcode.fiber (k := k) p t from f.hom x).val) heq
  rw [hcoeff] at hx
  exact one_ne_zero hx

/-- At the exact length `2ε`, the half-open finite interval has zero double-shift map. -/
theorem short_interval_transition_zero :
    transition (1 + 1) (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ))) = 0 := by
  apply NatTrans.ext
  funext t
  change structureMap (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ)))
    (le_add_of_nonneg_right (NNReal.coe_nonneg (1 + 1))) = 0
  apply interval_map_eq_zero _ (le_add_of_nonneg_right (NNReal.coe_nonneg (1 + 1)))
  rintro ⟨hs, ht⟩
  have hb := hs.1
  have hd := WithTop.coe_lt_coe.mp ht.2
  norm_num at hd
  linarith

/-- `[0,2)` and zero are one-interleaved, including the length-equals-`2ε` boundary. -/
theorem short_interval_one_interleaved :
    Nonempty (RealInterleaving 1 (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ))) 0) :=
  (RealInterleaving.nonempty_zero_iff _ _).mpr short_interval_transition_zero

/-- `[0,3)` is not one-interleaved with zero; the parameter here is specifically one. -/
theorem long_interval_not_one_interleaved :
    ¬ Nonempty (RealInterleaving 1
      (RealBarcode.intervalModule (k := k) (0, (3 : WithTop ℝ))) 0) := by
  intro h
  have hz := (RealInterleaving.nonempty_zero_iff _ _).mp h
  have h0 := congrArg (fun f => f.app (0 : ℝ)) hz
  change structureMap (RealBarcode.intervalModule (k := k) (0, (3 : WithTop ℝ)))
    (show (0 : ℝ) ≤ 0 + ((1 + 1 : ℝ≥0) : ℝ) from by positivity) = 0 at h0
  exact interval_map_ne_zero (s := 0) (t := 0 + ((1 + 1 : ℝ≥0) : ℝ)) _ _
    (by norm_num [RealBarcode.alive])
    ⟨by positivity, WithTop.coe_lt_coe.mpr (by norm_num)⟩ h0

/-- A field has `0 ≠ 1`, so the essential interval cannot interleave with zero at any
finite nonnegative parameter. No shift by infinity occurs in this statement. -/
theorem essential_interval_not_interleaved (ε : ℝ≥0) :
    ¬ Nonempty (RealInterleaving ε (RealBarcode.intervalModule (k := k) (0, ⊤)) 0) := by
  intro h
  have hz := (RealInterleaving.nonempty_zero_iff _ _).mp h
  have h0 := congrArg (fun f => f.app (0 : ℝ)) hz
  change structureMap (RealBarcode.intervalModule (k := k) (0, ⊤))
    (show (0 : ℝ) ≤ 0 + ((ε + ε : ℝ≥0) : ℝ) from by positivity) = 0 at h0
  exact interval_map_ne_zero (s := 0) (t := 0 + ((ε + ε : ℝ≥0) : ℝ)) _ _
    ⟨le_rfl, WithTop.coe_lt_top _⟩
    ⟨by positivity, WithTop.coe_lt_top _⟩ h0

end Intervals

end TDA.Persistence.RealInterleavingExamples
