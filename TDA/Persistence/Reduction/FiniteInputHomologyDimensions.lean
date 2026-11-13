import TDA.Persistence.Reduction.FiniteInputHomologyMapCorrectness
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Nat.Log

/-!
# Executable dimensions of finite induced homology maps

Count distinct images of all source F₂ coordinates. The base-two logarithm
is the image dimension; rank-nullity supplies the kernel dimension.
Enumeration is exponential in source Betti dimension.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

private def coordinateImages {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Finset (Fin m → ZMod 2) :=
  Finset.univ.image M.mulVec

private theorem mem_coordinateImages {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) :
    v ∈ coordinateImages M ↔ v ∈ LinearMap.range M.mulVecLin := by
  simp [coordinateImages, LinearMap.mem_range]

private theorem coordinateImages_card {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (coordinateImages M).card = 2 ^ Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := by
  classical
  let e : ↥(coordinateImages M) ≃ LinearMap.range M.mulVecLin :=
    Equiv.subtypeEquivRight (mem_coordinateImages M)
  calc
    (coordinateImages M).card = Fintype.card (LinearMap.range M.mulVecLin) := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr e
    _ = _ := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- Image and kernel dimensions of a finite F₂ homology map. -/
structure HomologyMapDimensions where
  rank : ℕ
  nullity : ℕ
  deriving DecidableEq, Repr

/-- Compute dimensions from the existing ordered homology-coordinate matrix.
The matrix is materialized before enumerating source coordinates. -/
def homologyMapDimensions (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    HomologyMapDimensions :=
  let sourceRecords := activeRepresentatives xs p a
  let targetRecords := activeRepresentatives ys p b
  let columns := Vector.ofFn fun j : Fin sourceRecords.length =>
    normalCoordinateVector ys (vertexVector xs ys a f (chainVector (sourceRecords.get j).cycle))
  let matrix := Vector.ofFn fun i : Fin targetRecords.length =>
    Vector.ofFn fun j : Fin sourceRecords.length => columns[j][(targetRecords.get i).birthIndex]
  let rank := Nat.log 2 (coordinateImages (fun i j => matrix[i][j])).card
  ⟨rank, sourceRecords.length - rank⟩

/-- A characteristic formula in terms of the existing induced-map matrix. -/
theorem homologyMapDimensions_eq (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    homologyMapDimensions xs ys p a b f =
      let rank := Nat.log 2 (Finset.univ.image (homologyMapMatrix xs ys p a b f).mulVec).card
      ⟨rank, (activeRepresentatives xs p a).length - rank⟩ := by
  simp only [homologyMapDimensions, coordinateImages, homologyMapMatrix,
    Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, basisRecord]

/-- The enumerated image contains exactly `2^rank` distinct vectors, including zero. -/
theorem homologyMap_image_card (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    (Finset.univ.image (homologyMapMatrix xs ys p a b f).mulVec).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (homologyMapMatrix xs ys p a b f).mulVecLin) :=
  coordinateImages_card _

theorem homologyMapDimensions_rank (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    (homologyMapDimensions xs ys p a b f).rank =
      Module.finrank (ZMod 2) (LinearMap.range (homologyMapMatrix xs ys p a b f).mulVecLin) := by
  rw [homologyMapDimensions_eq, homologyMap_image_card]
  exact Nat.log_pow (b := 2) (by decide) _

theorem homologyMapDimensions_nullity (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    (homologyMapDimensions xs ys p a b f).nullity =
      Module.finrank (ZMod 2) (LinearMap.ker (homologyMapMatrix xs ys p a b f).mulVecLin) := by
  have hr := (homologyMapMatrix xs ys p a b f).mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  rw [homologyMapDimensions_eq, homologyMap_image_card, Nat.log_pow (b := 2) (by decide)]
  dsimp only
  omega

theorem homologyMapDimensions_rank_nullity (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    (homologyMapDimensions xs ys p a b f).rank +
      (homologyMapDimensions xs ys p a b f).nullity = (activeRepresentatives xs p a).length := by
  rw [homologyMapDimensions_rank, homologyMapDimensions_nullity]
  simpa using (homologyMapMatrix xs ys p a b f).mulVecLin.finrank_range_add_finrank_ker

/-- Validate both simplex lists and every admitted face image before returning dimensions. -/
def runHomologyDimensions (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    Option HomologyMapDimensions :=
  if VertexMapInput xs ys a b f then some (homologyMapDimensions xs ys p a b f) else none

theorem runHomologyDimensions_eq_some_iff (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ)
    (out : HomologyMapDimensions) :
    runHomologyDimensions xs ys p a b f = some out ↔
      VertexMapInput xs ys a b f ∧ out = homologyMapDimensions xs ys p a b f := by
  simp only [runHomologyDimensions]
  split_ifs with h <;> simp [h, eq_comm]

theorem runHomologyDimensions_eq_none_iff (xs ys : Input) (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) :
    runHomologyDimensions xs ys p a b f = none ↔ ¬ VertexMapInput xs ys a b f := by
  simp [runHomologyDimensions]

end TDA.Persistence.Reduction.FiniteInput
