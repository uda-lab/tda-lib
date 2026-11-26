import TDA.Persistence.MatrixSequenceReal

/-!
# Client statements for matrix-sequence persistence modules

Regression fixtures for #1263, family 5 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
imports only the public module.

* A structure map across two steps is the product of the two adjacent matrices, later matrix
  on the left, and acts on a vector by that product.
* Matrix presentations related by stagewise inverse matrices have the same barcode.
* The barcode of a presentation in supplied bases is the rank barcode of the module, for
  every choice of bases.
* The real module of a zero-initial sequence over a critical grid is the realization of its
  real diagram.
-/

namespace TDA.Persistence.MatrixSequenceClientExamples

/-- The structure map across two steps is the product of the adjacent matrices. -/
theorem compositeMatrix_two_steps {R : Type} [CommRing R] {N : ℕ}
    (A : TDA.Persistence.MatrixSequence R N) (i j l : Fin N)
    (hij : i.val + 1 = j.val) (hjl : j.val + 1 = l.val) :
    A.compositeMatrix (show i ≤ l by omega) = A.step j l hjl * A.step i j hij := by
  rw [A.compositeMatrix_succ (show i ≤ j by omega) hjl, A.compositeMatrix_adjacent i j hij]

/-- It acts on a coordinate vector by that product. -/
theorem structureMap_two_steps_apply {R : Type} [CommRing R] {N : ℕ}
    (A : TDA.Persistence.MatrixSequence R N) (i j l : Fin N)
    (hij : i.val + 1 = j.val) (hjl : j.val + 1 = l.val) (x : Fin (A.dim i) → R) :
    TDA.Persistence.structureMapLinear A.toPModule (show i ≤ l by omega) x =
      Matrix.mulVec (A.step j l hjl * A.step i j hij) x := by
  rw [A.structureMapLinear_apply, compositeMatrix_two_steps A i j l hij hjl]

/-- Stagewise inverse matrices commuting with the steps preserve the barcode. -/
theorem barcode_eq_of_inverse_matrices {k : Type} [Field k] {N : ℕ}
    (A B : TDA.Persistence.MatrixSequence k N)
    (P : ∀ i, Matrix (Fin (B.dim i)) (Fin (A.dim i)) k)
    (Q : ∀ i, Matrix (Fin (A.dim i)) (Fin (B.dim i)) k)
    (hP : ∀ i j (h : i.val + 1 = j.val), B.step i j h * P i = P j * A.step i j h)
    (hQ : ∀ i j (h : i.val + 1 = j.val), A.step i j h * Q i = Q j * B.step i j h)
    (hQP : ∀ i, Q i * P i = 1) (hPQ : ∀ i, P i * Q i = 1) : A.barcode = B.barcode :=
  TDA.Persistence.MatrixSequence.barcode_eq_of_inverse_homs A B ⟨P, hP⟩ ⟨Q, hQ⟩
    (TDA.Persistence.MatrixSequence.Hom.ext hQP) (TDA.Persistence.MatrixSequence.Hom.ext hPQ)

/-- The barcode in supplied bases is the rank barcode of the module. -/
theorem barcode_ofBases_eq_rankBarcode {k : Type} [Field k] {N : ℕ}
    (M : TDA.Persistence.PModule.{0, 0, 0} k (Fin N)) [∀ i, FiniteDimensional k (M.obj i)]
    (d : Fin N → ℕ) (b : ∀ i, Module.Basis (Fin (d i)) k (M.obj i)) :
    (TDA.Persistence.MatrixSequence.ofBases M d b).barcode = TDA.Persistence.rankBarcode M :=
  TDA.Persistence.MatrixSequence.barcode_ofBases M d b

/-- Two choices of bases give the same barcode. -/
theorem barcode_ofBases_eq_of_bases {k : Type} [Field k] {N : ℕ}
    (M : TDA.Persistence.PModule.{0, 0, 0} k (Fin N)) (d e : Fin N → ℕ)
    (b : ∀ i, Module.Basis (Fin (d i)) k (M.obj i))
    (c : ∀ i, Module.Basis (Fin (e i)) k (M.obj i)) :
    (TDA.Persistence.MatrixSequence.ofBases M d b).barcode =
      (TDA.Persistence.MatrixSequence.ofBases M e c).barcode :=
  TDA.Persistence.MatrixSequence.barcode_basisChange M d e b c

/-- Over a critical grid, the real module of a zero-initial sequence is the realization of
its real diagram, and that diagram is positive. -/
theorem realModule_realization {k : Type} [Field k] {n : ℕ}
    (A : TDA.Persistence.MatrixSequence k (n + 1)) (c : Fin n ↪o ℝ) (hA : A.dim 0 = 0) :
    (A.realDiagram c).IsPositive ∧
      Nonempty (A.realModule c ≅
        TDA.Persistence.RealBarcode.realize (k := k) (A.realDiagram c)) :=
  ⟨TDA.Persistence.FiniteConstructible.moduleDiagram_isPositive c (A.realModule c) _,
    ⟨A.realBarcodeIso c hA⟩⟩

end TDA.Persistence.MatrixSequenceClientExamples
