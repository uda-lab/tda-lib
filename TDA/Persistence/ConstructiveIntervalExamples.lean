import TDA.Persistence.FiniteBarcode
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# Executable finite interval and list-barcode consumers

All data definitions in this module compile without `noncomputable`. The examples
apply the actual structure maps and both components of the enumeration isomorphism.
-/

namespace TDA.Persistence.ConstructiveIntervalExamples

open CategoryTheory

def A : FiniteInterval 5 := ⟨1, 4, by decide, by decide⟩
def B : FiniteInterval 5 := ⟨0, 5, by decide, by decide⟩
def unitInterval : FiniteInterval 1 := ⟨0, 1, by decide, by decide⟩

/-- A computable generic-field client; an inactive fiber admits only zero. -/
def scalar {N : ℕ} {k : Type*} [Field k] (I : FiniteInterval N) (i : Fin N) (c : k) :
    I.fiber (k := k) i :=
  if h : I.alive i then ⟨c, by simp [FiniteInterval.fiber, h]⟩ else 0

def action {N : ℕ} {k : Type*} [Field k] (I : FiniteInterval N)
    (i j : Fin N) (hij : i ≤ j) (c : k) : k :=
  Subtype.val (structureMapLinear (intervalModule (k := k) I) hij (scalar I i c))

def composedAction {N : ℕ} {k : Type*} [Field k] (I : FiniteInterval N)
    (i j ℓ : Fin N) (hij : i ≤ j) (hjℓ : j ≤ ℓ) (c : k) : k :=
  Subtype.val (structureMapLinear (intervalModule (k := k) I) hjℓ
    (structureMapLinear (intervalModule (k := k) I) hij (scalar I i c)))

/-- Birth/interior identity, excluded death, inactive source, and the final observed index. -/
theorem rational_actions :
    action A 1 2 (by decide) (7 : ℚ) = 7 ∧
    action A 2 3 (by decide) (7 : ℚ) = 7 ∧
    action A 1 4 (by decide) (7 : ℚ) = 0 ∧
    action A 0 1 (by decide) (7 : ℚ) = 0 ∧
    action B 0 4 (by decide) (7 : ℚ) = 7 ∧
    action unitInterval 0 0 le_rfl (7 : ℚ) = 7 := by decide +kernel

theorem binary_actions :
    action A 1 2 (by decide) (1 : ZMod 2) = 1 ∧
    action A 2 4 (by decide) (1 : ZMod 2) = 0 ∧
    action A 0 3 (by decide) (1 : ZMod 2) = 0 ∧
    action B 0 4 (by decide) (1 : ZMod 2) = 1 ∧
    action unitInterval 0 0 le_rfl (1 : ZMod 2) = 1 := by decide +kernel

/-- Self and composition are checked on nonzero live values and on a dying value. -/
theorem rational_structure_laws :
    action A 2 2 le_rfl (7 : ℚ) = 7 ∧
    composedAction A 1 2 3 (by decide) (by decide) (7 : ℚ) = action A 1 3 (by decide) 7 ∧
    composedAction A 1 2 4 (by decide) (by decide) (7 : ℚ) = action A 1 4 (by decide) 7 := by
  constructor
  · decide +kernel
  constructor
  · have h := structureMapLinear_comp (intervalModule (k := ℚ) A)
      (show (1 : Fin 5) ≤ 2 by decide) (show (2 : Fin 5) ≤ 3 by decide)
    exact (congrArg (fun L => Subtype.val (L (scalar A 1 (7 : ℚ)))) h).symm
  · have h := structureMapLinear_comp (intervalModule (k := ℚ) A)
      (show (1 : Fin 5) ≤ 2 by decide) (show (2 : Fin 5) ≤ 4 by decide)
    exact (congrArg (fun L => Subtype.val (L (scalar A 1 (7 : ℚ)))) h).symm

def source : List (FiniteInterval 5) := [A, B, A]
def target : List (FiniteInterval 5) := [A, A, B]

theorem reorder : source.Perm target := List.Perm.cons A (List.Perm.swap A B [])

def vector {N : ℕ} {k : Type*} [Field k] (xs : List (FiniteInterval N))
    (i : Fin N) (c : Fin xs.length → k) : (barcodeModuleOfList (k := k) xs).obj i :=
  fun t => scalar (xs.get t) i (c t)

def values {N : ℕ} {k : Type*} [Field k] (xs : List (FiniteInterval N))
    (i : Fin N) (x : (barcodeModuleOfList (k := k) xs).obj i) : List k :=
  List.ofFn fun t => Subtype.val (x t)

def forward {N : ℕ} {k : Type*} [Field k] {xs ys : List (FiniteInterval N)}
    (h : xs.Perm ys) (i : Fin N) (c : Fin xs.length → k) : List k :=
  values ys i (((barcodeEnumerationNatIso (k := k) h).hom.app i).hom (vector xs i c))

def inverse {N : ℕ} {k : Type*} [Field k] {xs ys : List (FiniteInterval N)}
    (h : xs.Perm ys) (i : Fin N) (c : Fin ys.length → k) : List k :=
  values xs i (((barcodeEnumerationNatIso (k := k) h).inv.app i).hom (vector ys i c))

def sourceCoefficients : Fin source.length → ℚ := ![2, 5, 7]
def targetCoefficients : Fin target.length → ℚ := ![11, 13, 17]

/-- The two equal A intervals retain their respective first and second occurrences. -/
theorem repeated_coordinate_actions :
    List.ofFn (fun t : Fin source.length => (reorder.idxBij t).val) = [0, 2, 1] ∧
    forward reorder 1 sourceCoefficients = [2, 7, 5] ∧
    inverse reorder 1 targetCoefficients = [11, 17, 13] ∧
    forward reorder 2 sourceCoefficients = [2, 7, 5] := by decide +kernel

theorem binary_permutation_actions :
    forward reorder 1 (![1, 1, 0] : Fin 3 → ZMod 2) = [1, 0, 1] ∧
    inverse reorder 1 (![1, 0, 1] : Fin 3 → ZMod 2) = [1, 1, 0] := by decide +kernel

def naturalityLeft : List ℚ :=
  values target 4 (structureMapLinear (barcodeModuleOfList target) (show (2 : Fin 5) ≤ 4 by decide)
    (((barcodeEnumerationNatIso reorder).hom.app 2).hom (vector source 2 sourceCoefficients)))

def naturalityRight : List ℚ :=
  values target 4 (((barcodeEnumerationNatIso reorder).hom.app 4).hom
    (structureMapLinear (barcodeModuleOfList source) (show (2 : Fin 5) ≤ 4 by decide)
      (vector source 2 sourceCoefficients)))

/-- Naturality crosses the death of both A occurrences while B survives at death=N. -/
theorem permutation_naturality : naturalityLeft = [0, 0, 5] ∧ naturalityLeft = naturalityRight := by
  constructor
  · decide +kernel
  · have h := (barcodeEnumerationNatIso (k := ℚ) reorder).hom.naturality
      (homOfLE (show (2 : Fin 5) ≤ 4 by decide))
    have hv := congrArg (fun g => g.hom (vector source 2 sourceCoefficients)) h
    exact (congrArg (values target 4) hv).symm

theorem equalSwap : ([A, A] : List (FiniteInterval 5)).Perm [A, A] := List.Perm.swap A A []

/-- A swap proof of equal values still induces the identity nth-occurrence correspondence. -/
theorem equal_swap_actions :
    List.ofFn (fun t : Fin 2 => (equalSwap.idxBij t).val) = [0, 1] ∧
    forward equalSwap 2 (![2, 7] : Fin 2 → ℚ) = [2, 7] ∧
    inverse equalSwap 2 (![11, 13] : Fin 2 → ℚ) = [11, 13] := by decide +kernel

/-- Empty index and coordinate families are evaluated without creating an interval on Fin 0. -/
def emptyZeroComponents : List (List ℚ) :=
  List.ofFn fun i : Fin 0 => forward (k := ℚ) (List.Perm.refl ([] : List (FiniteInterval 0))) i
    (fun t => Fin.elim0 t)

theorem empty_and_single_stage :
    emptyZeroComponents = [] ∧
    forward (k := ℚ) (List.Perm.refl ([] : List (FiniteInterval 5))) 2 (fun t => Fin.elim0 t) = [] ∧
    inverse (k := ZMod 2) (List.Perm.refl ([] : List (FiniteInterval 1))) 0 (fun t => Fin.elim0 t) = [] ∧
    forward (List.Perm.refl [unitInterval, unitInterval]) 0 (![2, 7] : Fin 2 → ℚ) = [2, 7] := by
  decide +kernel

-- Explicit instance-binder compatibility is part of the existing public rank interface.
example {N : ℕ} {k : Type*} [Field k] (I : FiniteInterval N) {i j : Fin N} (hij : i ≤ j)
    [decAlive : Decidable (I.alive i ∧ I.alive j)] :
    Module.finrank k (LinearMap.range (intervalMap (k := k) I hij)) =
      @ite ℕ (I.alive i ∧ I.alive j) decAlive 1 0 :=
  @intervalMap_finrank_range N k _ I i j hij decAlive

end TDA.Persistence.ConstructiveIntervalExamples
