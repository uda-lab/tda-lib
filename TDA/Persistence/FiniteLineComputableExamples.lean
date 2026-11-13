import TDA.Persistence.MatrixSequenceExamples

/-!
# Executable chronological paths and matrix composites

These ordinary data definitions apply the public finite-line and matrix APIs.
The consumers keep coefficient equality out of the generic input assumptions.
-/

namespace TDA.Persistence.FiniteLineComputableExamples

open CategoryTheory
open scoped Matrix

def pathLength {N : ℕ} (i j : Fin N) (h : i ≤ j) : ℕ :=
  (FiniteLine.path (i := ⟨i⟩) (j := ⟨j⟩) h).length

def fromFinLength {N : ℕ} (i j : Fin N) (h : i ≤ j) : ℕ :=
  ((FiniteLine.fromFin (N := N)).map (homOfLE h)).length

def inverseEquivalenceLength {N : ℕ} (i j : Fin N) (h : i ≤ j) : ℕ :=
  ((FiniteLine.pathEquivalence N).inverse.map (homOfLE h)).length

/-- Right multiplication is left-linear even over a noncommutative ring. -/
def rightMultiply {R : Type*} [Ring R] (c : R) : ModuleCat.of R R ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom
    { toFun := fun x => x * c
      map_add' := fun x y => add_mul x y c
      map_smul' := fun a x => mul_assoc a x c }

def scalarModule {R : Type*} [Ring R] {N : ℕ} (c : Fin N → R) : PModule R (Fin N) :=
  FiniteLine.moduleOfAdjacent (fun _ => ModuleCat.of R R)
    (fun i _ _ => rightMultiply (c i))

def scalarAction {R : Type*} [Ring R] {N : ℕ} (c : Fin N → R)
    {i j : Fin N} (h : i ≤ j) (x : R) : R :=
  structureMapLinear (scalarModule c) h x

def representationAction {R : Type*} [Ring R] {N : ℕ} (c : Fin N → R)
    {i j : Fin N} (h : i ≤ j) (x : R) : R :=
  structureMapLinear ((FiniteLine.representationEquivalence R N).functor.obj
    (FiniteLine.toFin ⋙ scalarModule c)) h x

def recoveryAction {R : Type*} [Ring R] {N : ℕ} (c : Fin N → R)
    (i : Fin N) (x : R) : R :=
  ((FiniteLine.adjacentRecovery (scalarModule c)).hom.app i).hom x

def integerFactors : Fin 5 → ℤ := fun i => (i.val : ℤ) + 2

theorem path_observations :
    pathLength (2 : Fin 5) 2 le_rfl = 0 ∧
    pathLength (2 : Fin 5) 3 (by decide) = 1 ∧
    pathLength (0 : Fin 5) 4 (by decide) = 4 ∧
    fromFinLength (0 : Fin 5) 4 (by decide) = 4 ∧
    inverseEquivalenceLength (1 : Fin 5) 4 (by decide) = 3 ∧
    pathLength (0 : Fin 1) 0 le_rfl = 0 := by decide +kernel

theorem integer_actions :
    scalarAction integerFactors (i := 2) (j := 2) le_rfl 5 = 5 ∧
    scalarAction integerFactors (i := 1) (j := 2) (by decide) 5 = 15 ∧
    scalarAction integerFactors (i := 0) (j := 3) (by decide) 5 = 120 ∧
    scalarAction integerFactors (i := 0) (j := 4) (by decide) 5 = 600 ∧
    representationAction integerFactors (i := 0) (j := 3) (by decide) 5 = 120 ∧
    recoveryAction integerFactors 2 5 = 5 := by decide +kernel

/-- Observe a finite matrix in target-row/source-column order. -/
def entries {R : Type*} {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) : List (List R) :=
  List.ofFn fun row => List.ofFn (M row)

def compositeEntries {R : Type*} [CommRing R] {N : ℕ} (A : MatrixSequence R N)
    {i j : Fin N} (h : i ≤ j) : List (List R) := entries (A.compositeMatrix h)

def mapValues {R : Type*} [CommRing R] {N : ℕ} (A : MatrixSequence R N)
    {i j : Fin N} (h : i ≤ j) (x : Fin (A.dim i) → R) : List R :=
  List.ofFn (structureMapLinear A.toPModule h x)

theorem rational_rectangular_actions :
    compositeEntries MatrixSequenceExamples.compositeZero (i := 0) (j := 2) (by decide) =
      [[0]] ∧
    compositeEntries MatrixSequenceExamples.compositeIdentity (i := 0) (j := 2) (by decide) =
      [[1]] ∧
    compositeEntries (MatrixSequenceExamples.threeStage 2 3) (i := 0) (j := 2) (by decide) =
      [[2]] ∧
    mapValues (MatrixSequenceExamples.threeStage 2 3) (i := 0) (j := 1) (by decide) ![5] =
      [5, 0] ∧
    mapValues (MatrixSequenceExamples.threeStage 2 3) (i := 1) (j := 2) (by decide) ![5, 7] =
      [31] ∧
    mapValues (MatrixSequenceExamples.threeStage 2 3) (i := 0) (j := 2) (by decide) ![5] =
      [10] := by decide +kernel

/-- Two noncommuting F₂ shears make chronological order observable. -/
def binaryShears : MatrixSequence (ZMod 2) 3 where
  dim _ := 2
  step i _ _ := if i.val = 0 then !![1, 1; 0, 1] else !![1, 0; 1, 1]

theorem binary_chronology :
    compositeEntries binaryShears (i := 0) (j := 2) (by decide) = [[1, 1], [1, 0]] ∧
    entries ((show Matrix (Fin 2) (Fin 2) (ZMod 2) from binaryShears.step 0 1 (by decide)) *
      (show Matrix (Fin 2) (Fin 2) (ZMod 2) from binaryShears.step 1 2 (by decide))) =
      [[0, 1], [1, 1]] ∧
    mapValues binaryShears (i := 0) (j := 1) (by decide) ![0, 1] = [1, 1] ∧
    mapValues binaryShears (i := 0) (j := 2) (by decide) ![0, 1] = [1, 0] := by decide +kernel

/-- Both rectangular transitions are nonzero, but their F₂ composite cancels. -/
def binaryRectangular : MatrixSequence (ZMod 2) 3 where
  dim i := if i.val = 1 then 2 else 1
  step i j _ := match i, j with
    | ⟨0, _⟩, ⟨1, _⟩ => !![1; 1]
    | ⟨1, _⟩, ⟨_ + 2, _⟩ => !![1, 1]
    | _, _ => 0

theorem binary_rectangular_actions :
    entries (binaryRectangular.step 0 1 (by decide)) = [[1], [1]] ∧
    entries (binaryRectangular.step 1 2 (by decide)) = [[1, 1]] ∧
    compositeEntries binaryRectangular (i := 0) (j := 2) (by decide) = [[0]] ∧
    mapValues binaryRectangular (i := 0) (j := 2) (by decide) ![1] = [0] := by decide +kernel

/-- A nonempty source and target separated by a zero-dimensional stage. -/
def zeroIntermediate : MatrixSequence ℚ 3 where
  dim i := match i.val with | 0 => 2 | 1 => 0 | _ => 3
  step _ _ _ := 0

theorem zero_intermediate_actions :
    entries (zeroIntermediate.step 0 1 (by decide)) = [] ∧
    entries (zeroIntermediate.step 1 2 (by decide)) = [[], [], []] ∧
    compositeEntries zeroIntermediate (i := 0) (j := 2) (by decide) =
      [[0, 0], [0, 0], [0, 0]] ∧
    mapValues zeroIntermediate (i := 0) (j := 2) (by decide) ![5, 7] = [0, 0, 0] := by
  decide +kernel

def emptyEquivalenceVertices : List ℕ :=
  List.ofFn fun i : Fin 0 => ((FiniteLine.pathEquivalence 0).inverse.obj i).index.val

def emptyRepresentationValues : List ℤ :=
  List.ofFn fun i : Fin 0 => representationAction (N := 0) (fun t => Fin.elim0 t)
    (i := i) (j := i) le_rfl 7

def emptyMatrixValues : List (List ℚ) :=
  List.ofFn fun i : Fin 0 => mapValues MatrixSequenceExamples.empty
    (i := i) (j := i) le_rfl (fun _ => Fin.elim0 i)

theorem empty_and_singleton_actions :
    emptyEquivalenceVertices = [] ∧ emptyRepresentationValues = [] ∧ emptyMatrixValues = [] ∧
    compositeEntries MatrixSequenceExamples.oneStagePair (i := 0) (j := 0) le_rfl =
      [[1, 0], [0, 1]] ∧
    mapValues MatrixSequenceExamples.oneStagePair (i := 0) (j := 0) le_rfl ![3, 7] = [3, 7] := by
  decide +kernel

end TDA.Persistence.FiniteLineComputableExamples
