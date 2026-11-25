import TDA.Persistence.RealIntervalObservation
import TDA.Persistence.RealIntervalExamples
import TDA.Persistence.RealBarcodeRank

/-!
# Strict crossing counts for concrete real persistence modules

These examples count occurrences in each module's actual selected scalar
decomposition through its structure map, rather than supplying a barcode.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

namespace TDA.Persistence.RealIntervalObservationExamples

open TDA.Persistence.RealIntervalDecomposition
open CategoryTheory
open scoped Classical ZeroObject

variable {k : Type u} [Field k]

/-- A convex interval module's actual selected scalar decomposition has one
crossing occurrence exactly when both endpoints belong to its support. -/
theorem interval_crossing_card (S : Set ℝ) (hS : S.OrdConnected)
    (s t : ℝ) (hst : s < t) :
    Nat.card {j : ScalarIndex (SupportInterval.module (k := k) S hS) //
      s ∈ scalarSupport (SupportInterval.module (k := k) S hS) j ∧
      t ∈ scalarSupport (SupportInterval.module (k := k) S hS) j} =
        if s ∈ S ∧ t ∈ S then 1 else 0 := by
  classical
  let M := SupportInterval.module (k := k) S hS
  letI : ∀ p, FiniteDimensional k (M.obj p) := fun p => by
    change FiniteDimensional k (SupportInterval.fiber (k := k) S p)
    infer_instance
  rw [← persistenceImage_finrank_eq_scalar_crossing M s t hst]
  let f := structureMapLinear M hst.le
  change Module.finrank k (LinearMap.range f) = _
  by_cases h : s ∈ S ∧ t ∈ S
  · rw [if_pos h]
    have hf : Function.Surjective f := by
      intro y
      let x : SupportInterval.fiber (k := k) S s :=
        ⟨(y : k), by simp [SupportInterval.fiber, h.1]⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      simpa [f, h.2, x] using (SupportInterval.structureMap_val
        (k := k) S hS hst.le x)
    rw [LinearMap.range_eq_top.mpr hf, finrank_top]
    change Module.finrank k (SupportInterval.fiber (k := k) S t) = 1
    rw [show SupportInterval.fiber (k := k) S t = ⊤ by
      simp [SupportInterval.fiber, h.2]]
    rw [finrank_top]
    exact Module.finrank_self k
  · rw [if_neg h]
    have hf : f = 0 :=
      SupportInterval.structureMap_eq_zero_of_not_mem (k := k) S hS hst.le h
    rw [hf, LinearMap.range_zero]
    exact finrank_bot k _

/-- The zero persistence module has no strict crossing occurrence. -/
theorem zero_crossing_card (s t : ℝ) (hst : s < t) :
    Nat.card {j : ScalarIndex (0 : PModule.{u,0,u} k ℝ) //
      s ∈ scalarSupport (0 : PModule.{u,0,u} k ℝ) j ∧
      t ∈ scalarSupport (0 : PModule.{u,0,u} k ℝ) j} = 0 := by
  letI : ∀ p, FiniteDimensional k ((0 : PModule.{u,0,u} k ℝ).obj p) :=
    fun p => by
      letI : Subsingleton ((0 : PModule.{u,0,u} k ℝ).obj p) :=
        ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
      exact FiniteDimensional.of_injective
        (0 : ((0 : PModule.{u,0,u} k ℝ).obj p) →ₗ[k] k)
        (by intro x y _; subsingleton)
  rw [← persistenceImage_finrank_eq_scalar_crossing (0 : PModule.{u,0,u} k ℝ) s t hst]
  have hzero : structureMapLinear (0 : PModule.{u,0,u} k ℝ) hst.le = 0 := by
    letI : Subsingleton ((0 : PModule.{u,0,u} k ℝ).obj t) :=
      ModuleCat.subsingleton_of_isZero (Functor.zero_obj t)
    apply LinearMap.ext
    intro x
    subsingleton
  unfold persistenceImage
  rw [hzero, LinearMap.range_zero]
  exact finrank_bot k _

/-- The whole-line rational module has exactly one actual crossing occurrence. -/
theorem wholeLine_crossing_card (s t : ℝ) (hst : s < t) :
    Nat.card {j : ScalarIndex RealIntervalExamples.wholeLine //
      s ∈ scalarSupport RealIntervalExamples.wholeLine j ∧
      t ∈ scalarSupport RealIntervalExamples.wholeLine j} = 1 := by
  simpa only [Set.mem_univ, and_self, ite_true] using
    (interval_crossing_card (k := ℚ) (Set.univ : Set ℝ)
      Set.ordConnected_univ s t hst)

/-- A finite half-open interval crosses 0→1 once in its actual scalar family. -/
theorem finiteInterval_inside_crossing_card :
    Nat.card {j : ScalarIndex (RealBarcode.intervalModule (k := ℚ)
      (0, (2 : WithTop ℝ))) //
      (0 : ℝ) ∈ scalarSupport (RealBarcode.intervalModule (k := ℚ)
        (0, (2 : WithTop ℝ))) j ∧
      (1 : ℝ) ∈ scalarSupport (RealBarcode.intervalModule (k := ℚ)
        (0, (2 : WithTop ℝ))) j} = 1 := by
  letI : ∀ p, FiniteDimensional ℚ
      ((RealBarcode.intervalModule (k := ℚ) (0, (2 : WithTop ℝ))).obj p) :=
    fun p => by change FiniteDimensional ℚ (RealBarcode.fiber (k := ℚ)
      (0, (2 : WithTop ℝ)) p); infer_instance
  rw [← persistenceImage_finrank_eq_scalar_crossing
    (RealBarcode.intervalModule (k := ℚ) (0, (2 : WithTop ℝ))) 0 1 (by norm_num)]
  rw [RealBarcode.intervalImage_rank]
  norm_num [RealBarcode.alive]

/-- The same actual finite interval has no crossing occurrence at 0→3. -/
theorem finiteInterval_outside_crossing_card :
    Nat.card {j : ScalarIndex (RealBarcode.intervalModule (k := ℚ)
      (0, (2 : WithTop ℝ))) //
      (0 : ℝ) ∈ scalarSupport (RealBarcode.intervalModule (k := ℚ)
        (0, (2 : WithTop ℝ))) j ∧
      (3 : ℝ) ∈ scalarSupport (RealBarcode.intervalModule (k := ℚ)
        (0, (2 : WithTop ℝ))) j} = 0 := by
  letI : ∀ p, FiniteDimensional ℚ
      ((RealBarcode.intervalModule (k := ℚ) (0, (2 : WithTop ℝ))).obj p) :=
    fun p => by change FiniteDimensional ℚ (RealBarcode.fiber (k := ℚ)
      (0, (2 : WithTop ℝ)) p); infer_instance
  rw [← persistenceImage_finrank_eq_scalar_crossing
    (RealBarcode.intervalModule (k := ℚ) (0, (2 : WithTop ℝ))) 0 3 (by norm_num)]
  rw [RealBarcode.intervalImage_rank]
  rw [if_neg]
  intro h
  have ht : ((3 : ℝ) : WithTop ℝ) < (2 : WithTop ℝ) := h.2.2
  have hle : (2 : WithTop ℝ) ≤ ((3 : ℝ) : WithTop ℝ) :=
    WithTop.coe_le_coe.mpr (by norm_num)
  exact (not_lt_of_ge hle) ht

end TDA.Persistence.RealIntervalObservationExamples
