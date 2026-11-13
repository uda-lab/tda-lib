import TDA.Persistence.Reduction.FiniteInputCycleSynthesis
import TDA.Persistence.Reduction.FiniteInputCycleFillingCorrectness

/-!
# Executable homology-class lifts

Enumerate source homology coordinates, synthesize a source cycle, and fill the
remaining target boundary. Zero target coordinates select the zero source cycle.
The search is exponential in source homology dimension and intended for small groups.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

private def binaryVectors (n : ℕ) : List (Vector (ZMod 2) n) :=
  Vector.ofFnM (m := List) (fun _ => [0, 1])

private theorem binaryVectors_complete {n : ℕ} (coefficients : Fin n → ZMod 2) :
    Vector.ofFn coefficients ∈ binaryVectors n := by
  induction n with
  | zero => simp [binaryVectors, Vector.ofFnM_zero]
  | succ n ih =>
    rw [binaryVectors, Vector.ofFnM_succ, Vector.ofFn_succ]
    have hc : coefficients (Fin.last n) = 0 ∨ coefficients (Fin.last n) = 1 :=
      (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide +kernel) _
    have hp := ih (fun i => coefficients i.castSucc)
    change Vector.ofFn (fun i => coefficients i.castSucc) ∈ _ at hp
    simp only [List.bind_eq_flatMap, List.pure_def, List.mem_flatMap]
    refine ⟨_, hp, ?_⟩
    change coefficients ⟨n, by omega⟩ = 0 ∨ coefficients ⟨n, by omega⟩ = 1 at hc
    rcases hc with hc | hc <;> simp [hc]

private def coordinateLift {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Fin m → ZMod 2) : Option (Vector (ZMod 2) n) :=
  if w = 0 then some (Vector.replicate n 0)
  else (binaryVectors n).find? (fun coefficients => decide (M.mulVec (fun i => coefficients[i]) = w))

private theorem coordinateLift_solution {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Fin m → ZMod 2) (coefficients : Vector (ZMod 2) n)
    (hc : coordinateLift M w = some coefficients) :
    M.mulVec (fun i => coefficients[i]) = w := by
  unfold coordinateLift at hc
  split_ifs at hc with hw
  · cases Option.some.inj hc
    funext r
    change (∑ j : Fin n, M r j * (Vector.replicate n (0 : ZMod 2))[j]) = w r
    simp [hw]
  · have hs := List.find?_some hc
    exact of_decide_eq_true hs

private theorem coordinateLift_exists_iff {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (w : Fin m → ZMod 2) :
    (∃ coefficients, coordinateLift M w = some coefficients) ↔
      ∃ coefficients : Fin n → ZMod 2, M.mulVec coefficients = w := by
  constructor
  · rintro ⟨coefficients, hc⟩
    exact ⟨_, coordinateLift_solution M w coefficients hc⟩
  · rintro ⟨coefficients, hc⟩
    unfold coordinateLift
    split_ifs with hw
    · exact ⟨_, rfl⟩
    · rw [← Option.isSome_iff_exists, List.find?_isSome]
      refine ⟨Vector.ofFn coefficients, binaryVectors_complete coefficients, ?_⟩
      simpa using hc

/-- Executable selected source coordinates, searching in source Betti dimension. -/
def homologyLiftCoefficients (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2) :
    Option (Vector (ZMod 2) (activeRepresentatives xs p a).length) :=
  let sourceRecords := activeRepresentatives xs p a
  let targetRecords := activeRepresentatives ys p b
  let normal := normalCoordinateVector ys w
  let target := Vector.ofFn fun i : Fin targetRecords.length => normal[(targetRecords.get i).birthIndex]
  let columns := Vector.ofFn fun j : Fin sourceRecords.length =>
    normalCoordinateVector ys (vertexVector xs ys a f (chainVector (sourceRecords.get j).cycle))
  let matrix := Vector.ofFn fun i : Fin targetRecords.length =>
    Vector.ofFn fun j : Fin sourceRecords.length => columns[j][(targetRecords.get i).birthIndex]
  coordinateLift (fun i j => matrix[i][j]) (fun i => target[i])

private theorem homologyLiftCoefficients_eq (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2) :
    homologyLiftCoefficients xs ys p a b f w =
      coordinateLift (homologyMapMatrix xs ys p a b f) (rawCycleCoordinates ys p b w) := by
  have he : (fun i : BasisIndex ys p b =>
      (Vector.ofFn fun j : BasisIndex ys p b => (normalCoordinateVector ys w)[(basisRecord ys p b j).birthIndex])[i]) =
      rawCycleCoordinates ys p b w := by
    funext i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    rfl
  dsimp only [homologyLiftCoefficients]
  simpa only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, basisRecord, homologyMapMatrix] using
    congrArg (coordinateLift (homologyMapMatrix xs ys p a b f)) he

/-- Explicit finite search normal form, with the zero target convention first. -/
theorem homologyLiftCoefficients_eq_search (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2) :
    homologyLiftCoefficients xs ys p a b f w =
      if rawCycleCoordinates ys p b w = 0 then some (Vector.replicate _ 0)
      else (Vector.ofFnM (m := List) (fun _ => [0, 1])).find?
        (fun coefficients => decide ((homologyMapMatrix xs ys p a b f).mulVec
          (fun i => coefficients[i]) = rawCycleCoordinates ys p b w)) := by
  rw [homologyLiftCoefficients_eq]
  rfl

/-- Every selected coefficient vector solves the induced homology matrix equation. -/
theorem homologyLiftCoefficients_solution (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2)
    (coefficients : Vector (ZMod 2) (activeRepresentatives xs p a).length)
    (hc : homologyLiftCoefficients xs ys p a b f w = some coefficients) :
    (homologyMapMatrix xs ys p a b f).mulVec (fun i => coefficients[i]) = rawCycleCoordinates ys p b w :=
  coordinateLift_solution _ _ coefficients ((homologyLiftCoefficients_eq xs ys p a b f w) ▸ hc)

/-- A unique matrix solution identifies the selected coefficients without unfolding the search. -/
theorem homologyLiftCoefficients_of_unique (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2)
    (coefficients : Vector (ZMod 2) (activeRepresentatives xs p a).length)
    (hc : (homologyMapMatrix xs ys p a b f).mulVec (fun i => coefficients[i]) = rawCycleCoordinates ys p b w)
    (hu : ∀ v, (homologyMapMatrix xs ys p a b f).mulVec v = rawCycleCoordinates ys p b w →
      v = (fun i => coefficients[i])) :
    homologyLiftCoefficients xs ys p a b f w = some coefficients := by
  obtain ⟨selected, hs⟩ := (coordinateLift_exists_iff _ _).mpr ⟨_, hc⟩
  have he := hu _ (coordinateLift_solution _ _ selected hs)
  have hv : selected = coefficients := by
    ext i hi
    exact congrFun he ⟨i, hi⟩
  rw [homologyLiftCoefficients_eq, ← hv]
  exact hs

/-- Coefficients follow the unchanged source query order; supports use original face indices. -/
structure HomologyLiftResult (sourceFaces targetFaces sourceDimension : ℕ) where
  coefficients : Vector (ZMod 2) sourceDimension
  sourceCycle : List (Fin sourceFaces)
  bounding : List (Fin targetFaces)
  deriving DecidableEq, Repr

/-- The selected witness associated with a solution in source homology coordinates. -/
def homologyLiftResult (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (coefficients : Vector (ZMod 2) (activeRepresentatives xs p a).length)
    (w : Fin ys.length → ZMod 2) :
    HomologyLiftResult xs.length ys.length (activeRepresentatives xs p a).length :=
  let source := Vector.ofFn (cycleSynthesis xs p a (fun i => coefficients[i]))
  let image := Vector.ofFn (vertexVector xs ys a f (fun i => source[i]))
  ⟨coefficients, supportChain (fun i => source[i]), fillingSupport ys p b (w - fun i => image[i])⟩

/-- The stored output has the exact synthesis and residual-filling characteristic. -/
theorem homologyLiftResult_eq (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (coefficients : Vector (ZMod 2) (activeRepresentatives xs p a).length)
    (w : Fin ys.length → ZMod 2) :
    homologyLiftResult xs ys p a b f coefficients w =
      let v := cycleSynthesis xs p a (fun i => coefficients[i])
      ⟨coefficients, supportChain v, fillingSupport ys p b (w - vertexVector xs ys a f v)⟩ := by
  simp only [homologyLiftResult, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- Validate geometry and target cycle, then search for a homology preimage with a chain certificate. -/
def runHomologyLift (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2) :
    Option (HomologyLiftResult xs.length ys.length (activeRepresentatives xs p a).length) :=
  if VertexMapInput xs ys a b f ∧ CycleInput ys p b w then
    (homologyLiftCoefficients xs ys p a b f w).map
      (fun coefficients => homologyLiftResult xs ys p a b f coefficients w)
  else none

/-- Exact successful output, retaining the deterministic finite search selection. -/
theorem runHomologyLift_eq_some_iff (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2)
    (out : HomologyLiftResult xs.length ys.length (activeRepresentatives xs p a).length) :
    runHomologyLift xs ys p a b f w = some out ↔
      VertexMapInput xs ys a b f ∧ CycleInput ys p b w ∧
      ∃ coefficients, homologyLiftCoefficients xs ys p a b f w =
          some coefficients ∧ out = homologyLiftResult xs ys p a b f coefficients w := by
  simp only [runHomologyLift]
  split_ifs with h
  · simp [h, eq_comm]
  · constructor
    · intro he; cases he
    · rintro ⟨hm, hw, _⟩
      exact (h ⟨hm, hw⟩).elim

theorem runHomologyLift_exists_iff (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2) :
    (∃ out, runHomologyLift xs ys p a b f w = some out) ↔
      VertexMapInput xs ys a b f ∧ CycleInput ys p b w ∧
      ∃ coefficients, (homologyMapMatrix xs ys p a b f).mulVec coefficients = rawCycleCoordinates ys p b w := by
  simp only [runHomologyLift_eq_some_iff]
  constructor
  · rintro ⟨out, hm, hw, coefficients, hc, _⟩
    exact ⟨hm, hw, (coordinateLift_exists_iff _ _).mp ⟨coefficients, (homologyLiftCoefficients_eq xs ys p a b f w) ▸ hc⟩⟩
  · rintro ⟨hm, hw, hc⟩
    obtain ⟨coefficients, hc⟩ := (coordinateLift_exists_iff _ _).mpr hc
    exact ⟨_, hm, hw, coefficients, (homologyLiftCoefficients_eq xs ys p a b f w).symm ▸ hc, rfl⟩

theorem runHomologyLift_eq_none_iff (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (w : Fin ys.length → ZMod 2) :
    runHomologyLift xs ys p a b f w = none ↔
      ¬ (VertexMapInput xs ys a b f ∧ CycleInput ys p b w ∧
        ∃ coefficients, (homologyMapMatrix xs ys p a b f).mulVec coefficients = rawCycleCoordinates ys p b w) := by
  rw [← runHomologyLift_exists_iff]
  cases runHomologyLift xs ys p a b f w <;> simp

/-- Every admitted null target selects zero source coefficients, even when the map has a kernel. -/
theorem runHomologyLift_null (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (hm : VertexMapInput xs ys a b f) (w : Fin ys.length → ZMod 2)
    (hw : CycleInput ys p b w) (hz : rawCycleCoordinates ys p b w = 0) :
    runHomologyLift xs ys p a b f w =
      some ⟨Vector.replicate _ 0, [], fillingSupport ys p b w⟩ := by
  have hs : cycleSynthesis xs p a (fun _ => 0) = 0 := (cycleSynthesis xs p a).map_zero
  simp [runHomologyLift, hm, hw, homologyLiftCoefficients_eq, coordinateLift, hz,
    homologyLiftResult_eq, Fin.getElem_fin, hs, vertexVector, supportChain]

/-- Zero targets have empty source and bounding supports, in every degree and threshold. -/
theorem runHomologyLift_zero (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (hm : VertexMapInput xs ys a b f) :
    runHomologyLift xs ys p a b f (0 : Fin ys.length → ZMod 2) =
      some ⟨Vector.replicate _ 0, [], []⟩ := by
  rw [runHomologyLift_null xs ys p a b f hm 0 (cycleInput_zero ys p b)
    ((rawCycleCoordinates ys p b).map_zero), fillingSupport_zero]

end TDA.Persistence.Reduction.FiniteInput
