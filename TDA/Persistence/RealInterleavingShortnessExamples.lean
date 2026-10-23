import TDA.Persistence.RealInterleavingShortness
import TDA.Persistence.RealIntervalInterleaving

/-!
# Sharpness of real interleaving defect shortness

Zero maps give a one-interleaving of `[0,2)` with itself. Both defects
are two-trivial but fail to be one-trivial. A zero-parameter witness over the
integers also checks the ring-valued boundary of the general result.
-/

set_option autoImplicit false

namespace TDA.Persistence.RealInterleavingShortnessExamples

open CategoryTheory CategoryTheory.Limits RealShift RealBarcode
open scoped NNReal ZeroObject

private noncomputable def threshold : PModule.{0,0,0} ℚ ℝ :=
  RealBarcode.intervalModule (0, (2 : WithTop ℝ))

private theorem threshold_two_zero : transition (1 + 1) threshold = 0 :=
  (transition_eq_zero_iff 1 0 2).mpr (by norm_num)

private noncomputable def zeroMaps : RealInterleaving 1 threshold threshold where
  φ := 0
  ψ := 0
  φ_ψ := by rw [zero_comp, threshold_two_zero]
  ψ_φ := by rw [zero_comp, threshold_two_zero]

private theorem transition_zero_of_iso {A B : PModule.{0,0,0} ℚ ℝ}
    (e : A ≅ B) (δ : ℝ≥0) (h : transition δ A = 0) : transition δ B = 0 := by
  apply (cancel_epi e.hom).mp
  rw [comp_zero, transition_naturality, h, zero_comp]

-- interval maps preserve coefficient one while both parameters are alive.
private theorem threshold_map_nonzero {a b : ℝ} (hab : a ≤ b)
    (ha : alive (0, (2 : WithTop ℝ)) a) (hb : alive (0, (2 : WithTop ℝ)) b) :
    structureMap threshold hab ≠ 0 := by
  let x : fiber (k := ℚ) (0, (2 : WithTop ℝ)) a :=
    ⟨1, by simp [fiber, ha]⟩
  intro h
  have hx := congrArg (fun f : threshold.obj a ⟶ threshold.obj b =>
    (show fiber (k := ℚ) (0, (2 : WithTop ℝ)) b from f.hom x).val) h
  change (show fiber (k := ℚ) (0, (2 : WithTop ℝ)) b from
    ((RealBarcode.intervalModule (0, (2 : WithTop ℝ))).map
      (homOfLE hab)).hom x).val = 0 at hx
  rw [map_val] at hx
  simp only [if_pos hb, x, one_ne_zero] at hx

private theorem threshold_one_nonzero : transition 1 threshold ≠ 0 := by
  intro h
  have ht := congrArg (fun f => f.app (0 : ℝ)) h
  change structureMap threshold (show (0 : ℝ) ≤ 0 + (1 : ℝ) by norm_num) = 0 at ht
  exact threshold_map_nonzero _ (by norm_num [alive]) (by norm_num [alive]) ht

private theorem shifted_threshold_one_nonzero :
    transition 1 ((shift 1).obj threshold) ≠ 0 := by
  intro h
  have ht := congrArg (fun f => f.app (-1 : ℝ)) h
  change structureMap threshold
    (show (-1 : ℝ) + 1 ≤ (-1 + 1) + 1 by norm_num) = 0 at ht
  exact threshold_map_nonzero _ (by norm_num [alive]) (by norm_num [alive]) ht

/-- Both defects attain the factor-two threshold: their two-transitions
vanish, while their one-transitions are nonzero. In particular both objects are nonzero. -/
theorem defects_threshold :
    transition (1 + 1) (kernel zeroMaps.φ) = 0 ∧
    transition (1 + 1) (cokernel zeroMaps.φ) = 0 ∧
    transition 1 (kernel zeroMaps.φ) ≠ 0 ∧
    transition 1 (cokernel zeroMaps.φ) ≠ 0 := by
  refine ⟨zeroMaps.kernel_transition_eq_zero, zeroMaps.cokernel_transition_eq_zero, ?_, ?_⟩
  · intro h
    exact threshold_one_nonzero
      (transition_zero_of_iso kernelZeroIsoSource 1 h)
  · intro h
    exact shifted_threshold_one_nonzero
      (transition_zero_of_iso cokernelZeroIsoTarget 1 h)

private noncomputable def integerConstant : PModule.{0,0,0} ℤ ℝ :=
  (Functor.const ℝ).obj (ModuleCat.of ℤ ℤ)

private noncomputable def integerWitness : RealInterleaving 0 integerConstant integerConstant :=
  RealInterleaving.ofIso (Iso.refl _)

private theorem isZero_of_zero_double_transition {A : PModule.{0,0,0} ℤ ℝ}
    (h : transition (0 + 0) A = 0) : IsZero A := by
  apply (IsZero.iff_id_eq_zero A).mpr
  have hz : transition 0 A = 0 := by
    rw [← transition_congr (show (0 : ℝ≥0) + 0 = 0 from zero_add 0) A, h, zero_comp]
  have ht := transition_zero A
  rw [hz, zero_comp] at ht
  exact ht.symm

/-- A zero-interleaving over the integers has zero defects,
even though its source and target have nonzero fibers. -/
theorem integer_zero_parameter :
    ¬ IsZero integerConstant ∧ IsZero (kernel integerWitness.φ) ∧
      IsZero (cokernel integerWitness.φ) := by
  refine ⟨?_, isZero_of_zero_double_transition integerWitness.kernel_transition_eq_zero,
    isZero_of_zero_double_transition integerWitness.cokernel_transition_eq_zero⟩
  intro h
  have hs : Subsingleton ℤ := ModuleCat.isZero_iff_subsingleton.mp (h.obj 0)
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (Subsingleton.elim _ _)

end TDA.Persistence.RealInterleavingShortnessExamples
