import TDA.Persistence.FiniteDecomposition
import TDA.Persistence.RealBarcodeRankUniqueness
import TDA.Persistence.SublevelConstructible
import TDA.Persistence.RealIntervalDecomposition

/-!
# Client statements of interval decomposition and barcode uniqueness

Regression fixtures for #1252, family 3 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
imports only public modules.

* Finite chains: the barcode of a pointwise finite-dimensional module exists and is unique,
  isomorphic modules have the same barcode, and equal structure-map ranks give an isomorphism.
* The real line: two positive barcode realizations of one module agree, isomorphic sublevel
  modules have equal diagrams, and a positive realization of a finite-constructible module
  is its module diagram.
* Pointwise finite-dimensional real modules have an interval decomposition.
-/

namespace TDA.Persistence.BarcodeUniquenessClientExamples

/-- A pointwise finite-dimensional module on a finite chain has exactly one barcode. -/
theorem existsUnique_barcode {N : ℕ} {k : Type} [Field k]
    (M : TDA.Persistence.PModule.{0, 0, 0} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (M.obj i)] :
    ∃! B : Multiset (TDA.Persistence.FiniteInterval N),
      Nonempty (M ≅ TDA.Persistence.barcodeModule (k := k) B) := by
  obtain ⟨B, ⟨e⟩⟩ := TDA.Persistence.exists_barcode_decomposition M
  exact ⟨B, ⟨e⟩, fun C ⟨f⟩ => TDA.Persistence.barcode_decomposition_unique M C B f e⟩

/-- Isomorphic modules with given interval decompositions have the same barcode. The
library statement asks for finite-dimensional fibers of the decomposed module. -/
theorem barcode_eq_of_iso {N : ℕ} {k : Type} [Field k]
    (M L : TDA.Persistence.PModule.{0, 0, 0} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (M.obj i)]
    (B C : Multiset (TDA.Persistence.FiniteInterval N)) (g : M ≅ L)
    (e : M ≅ TDA.Persistence.barcodeModule (k := k) B)
    (f : L ≅ TDA.Persistence.barcodeModule (k := k) C) : B = C :=
  TDA.Persistence.barcode_decomposition_unique M B C e (g ≪≫ f)

/-- Equal ranks of all structure maps give a natural isomorphism. -/
theorem nonempty_iso_of_ranks {N : ℕ} {k : Type} [Field k]
    (M L : TDA.Persistence.PModule.{0, 0, 0} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (M.obj i)] [∀ i : Fin N, FiniteDimensional k (L.obj i)]
    (h : ∀ (i j : Fin N) (hij : i ≤ j),
      TDA.Persistence.structureMapRank M i j hij = TDA.Persistence.structureMapRank L i j hij) :
    Nonempty (M ≅ L) :=
  (TDA.Persistence.nonempty_iso_iff_structureMapRank_eq M L).2 h

/-- Two positive barcode realizations of one real module are the same diagram. -/
theorem real_barcode_unique {k : Type} [Field k]
    (M : TDA.Persistence.PModule.{0, 0, 0} k ℝ) (D E : TDA.Persistence.Diagram ℝ)
    (hD : D.IsPositive) (hE : E.IsPositive)
    (e : M ≅ TDA.Persistence.RealBarcode.realize (k := k) D)
    (f : M ≅ TDA.Persistence.RealBarcode.realize (k := k) E) : D = E :=
  TDA.Persistence.RealBarcode.realization_unique D E hD hE e f

/-- Filters on finite complexes with isomorphic sublevel modules have equal diagrams. The
two complexes and their vertex types are unrelated. -/
theorem dgm_eq_of_sublevelModule_iso {m m' : ℕ}
    {K : PreAbstractSimplicialComplex (Fin m)} [Fintype (TDA.Simplicial.TotalFace K)]
    {K' : PreAbstractSimplicialComplex (Fin m')} [Fintype (TDA.Simplicial.TotalFace K')]
    (k : Type) [Field k] (f : TDA.Filtration.FilterFunction K ℝ)
    (g : TDA.Filtration.FilterFunction K' ℝ) (n : ℕ)
    (e : TDA.Persistence.sublevelModule k f n ≅ TDA.Persistence.sublevelModule k g n) :
    TDA.Persistence.dgm k f n = TDA.Persistence.dgm k g n :=
  TDA.Persistence.RealBarcode.realization_unique _ _
    (TDA.Persistence.dgm_isPositive k f n) (TDA.Persistence.dgm_isPositive k g n)
    (TDA.Persistence.sublevelModuleRealizationIso k n f)
    (e ≪≫ TDA.Persistence.sublevelModuleRealizationIso k n g)

/-- A positive realization of a finite-constructible module is its module diagram. -/
theorem moduleDiagram_eq_of_realization {n : ℕ} {k : Type} [Field k] (c : Fin n ↪o ℝ)
    (M : TDA.Persistence.PModule.{0, 0, 0} k ℝ)
    (hM : TDA.Persistence.FiniteConstructible.IsConstructible c M)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i)))
    (D : TDA.Persistence.Diagram ℝ) (hD : D.IsPositive)
    (e : M ≅ TDA.Persistence.RealBarcode.realize (k := k) D) :
    TDA.Persistence.FiniteConstructible.moduleDiagram c M hfd = D :=
  TDA.Persistence.RealBarcode.realization_unique _ _
    (TDA.Persistence.FiniteConstructible.moduleDiagram_isPositive c M hfd) hD
    (TDA.Persistence.FiniteConstructible.barcodeRealizationIso c M hM hfd) e

/-- A pointwise finite-dimensional real module is an algebraic sum of interval modules on
nonempty order-connected supports, finitely many of them active at each parameter. -/
theorem exists_real_interval_decomposition {k : Type} [Field k]
    (M : TDA.Persistence.PModule.{0, 0, 0} k ℝ) [∀ t, FiniteDimensional k (M.obj t)] :
    ∃ (J : Type) (I : J → Set ℝ) (hI : ∀ j, (I j).OrdConnected),
      (∀ j, (I j).Nonempty) ∧
      Nonempty (M ≅ TDA.Persistence.AlgebraicFamily.familyModule
        (fun j => TDA.Persistence.SupportInterval.module (k := k) (I j) (hI j))) ∧
      ∀ t, Set.Finite {j | t ∈ I j} :=
  TDA.Persistence.RealIntervalDecomposition.exists_interval_decomposition M

end TDA.Persistence.BarcodeUniquenessClientExamples
