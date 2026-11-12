import TDA.Persistence.Reduction.FiniteInputVertexMap

/-! Executable induced-map matrices in the ordered computed sublevel bases. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

/-- Target-query rows and source-query columns, with finite-vector storage for normal-coordinate columns. -/
def homologyMapMatrix (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    Matrix (BasisIndex ys p b) (BasisIndex xs p a) (ZMod 2) :=
  let columns := Vector.ofFn fun j : BasisIndex xs p a =>
    normalCoordinateVector ys (vertexVector xs ys a f (chainVector (basisRecord xs p a j).cycle))
  fun i j => columns[j][(basisRecord ys p b i).birthIndex]

theorem homologyMapMatrix_apply (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (i : BasisIndex ys p b) (j : BasisIndex xs p a) :
    homologyMapMatrix xs ys p a b f i j =
      rawCycleCoordinates ys p b (vertexVector xs ys a f (chainVector (basisRecord xs p a j).cycle)) i := by
  simp only [homologyMapMatrix, Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

/-- Nested rows for execution and display; the source query specifies the width when there are no rows. -/
def homologyMapRows (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) : List (List (ZMod 2)) :=
  List.ofFn fun i => List.ofFn fun j => homologyMapMatrix xs ys p a b f i j

/-- The displayed rows use exactly the two existing ordered record lists. -/
theorem homologyMapRows_eq_map (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    homologyMapRows xs ys p a b f =
      (activeRepresentatives ys p b).map (fun ri =>
        (activeRepresentatives xs p a).map (fun rj =>
          (normalCoordinateVector ys (vertexVector xs ys a f (chainVector rj.cycle)))[ri.birthIndex])) := by
  have hi (i : BasisIndex ys p b) := List.ofFn_getElem_eq_map (activeRepresentatives xs p a)
    (fun rj => (normalCoordinateVector ys (vertexVector xs ys a f (chainVector rj.cycle)))[(basisRecord ys p b i).birthIndex])
  have ho := List.ofFn_getElem_eq_map (activeRepresentatives ys p b) (fun ri =>
    (activeRepresentatives xs p a).map (fun rj =>
      (normalCoordinateVector ys (vertexVector xs ys a f (chainVector rj.cycle)))[ri.birthIndex]))
  calc
    homologyMapRows xs ys p a b f = List.ofFn (fun i : BasisIndex ys p b =>
        (activeRepresentatives xs p a).map (fun rj =>
          (normalCoordinateVector ys (vertexVector xs ys a f (chainVector rj.cycle)))[(basisRecord ys p b i).birthIndex])) := by
      unfold homologyMapRows
      apply congrArg List.ofFn
      funext i
      rw [← hi i]
      apply congrArg List.ofFn
      funext j
      rw [homologyMapMatrix_apply]
      rfl
    _ = _ := ho

/-- Validate both complexes and every admitted face image, then return the induced-map coefficients. -/
def runHomologyMap (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    Option (List (List (ZMod 2))) :=
  if VertexMapInput xs ys a b f then some (homologyMapRows xs ys p a b f) else none

theorem runHomologyMap_eq_some_iff (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (out : List (List (ZMod 2))) :
    runHomologyMap xs ys p a b f = some out ↔
      VertexMapInput xs ys a b f ∧ out = homologyMapRows xs ys p a b f := by
  simp only [runHomologyMap]
  split_ifs with h <;> simp [h, eq_comm]

theorem runHomologyMap_eq_none_iff (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    runHomologyMap xs ys p a b f = none ↔ ¬ VertexMapInput xs ys a b f := by
  simp [runHomologyMap]

theorem runHomologyMap_row_count (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (out : List (List (ZMod 2))) (hout : runHomologyMap xs ys p a b f = some out) :
    out.length = (activeRepresentatives ys p b).length := by
  rw [(runHomologyMap_eq_some_iff xs ys p a b f out).mp hout |>.2]
  exact List.length_ofFn

theorem runHomologyMap_column_count (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (out : List (List (ZMod 2))) (hout : runHomologyMap xs ys p a b f = some out)
    (row : List (ZMod 2)) (hrow : row ∈ out) :
    row.length = (activeRepresentatives xs p a).length := by
  rw [(runHomologyMap_eq_some_iff xs ys p a b f out).mp hout |>.2] at hrow
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  exact List.length_ofFn

/-- The executable entry at each original query position is the typed matrix entry. -/
theorem runHomologyMap_get (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (out : List (List (ZMod 2))) (hout : runHomologyMap xs ys p a b f = some out)
    (i : BasisIndex ys p b) (j : BasisIndex xs p a) :
    (out[i.val]?).bind (fun row => row[j.val]?) = some (homologyMapMatrix xs ys p a b f i j) := by
  rw [(runHomologyMap_eq_some_iff xs ys p a b f out).mp hout |>.2]
  simp [homologyMapRows, i.isLt, j.isLt]

end TDA.Persistence.Reduction.FiniteInput
