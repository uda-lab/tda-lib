import TDA.Persistence.SublevelConstructible

/-!
# Client statements of the interleaving and bottleneck isometry

Regression fixtures for #1259, family 4 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
imports only the public module.

* Finite-constructible real modules: an interleaving bounds the bottleneck distance of the
  module diagrams, a bottleneck distance below a bound yields an interleaving below it, and a
  bottleneck distance above `ε` excludes an `ε`-interleaving.
* Filters on two finite complexes: an interleaving of the sublevel modules bounds the
  bottleneck distance of the diagrams.
* The triangle inequality for three filters on three complexes.
-/

namespace TDA.Persistence.InterleavingIsometryClientExamples

/-- An `ε`-interleaving of finite-constructible modules bounds the bottleneck distance of
their module diagrams by `ε`. The two critical grids are unrelated. -/
theorem bottleneck_le_of_interleaving {k : Type} [Field k] {n m : ℕ}
    {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ} {M N : TDA.Persistence.PModule.{0, 0, 0} k ℝ}
    (hM : TDA.Persistence.FiniteConstructible.IsConstructible c M)
    (hN : TDA.Persistence.FiniteConstructible.IsConstructible d N)
    (hfdM : ∀ j, FiniteDimensional k (M.obj (c j)))
    (hfdN : ∀ j, FiniteDimensional k (N.obj (d j)))
    {ε : NNReal} (i : TDA.Persistence.RealInterleaving ε M N) :
    TDA.Persistence.bottleneck
        (TDA.Persistence.FiniteConstructible.moduleDiagram c M hfdM)
        (TDA.Persistence.FiniteConstructible.moduleDiagram d N hfdN) ≤ (ε : ENNReal) :=
  TDA.Persistence.FiniteConstructible.bottleneck_le_of_interleaving hM hN hfdM hfdN i

/-- A bottleneck distance below `r` yields an interleaving at some parameter below `r`. -/
theorem exists_interleaving_of_bottleneck_lt {k : Type} [Field k] {n m : ℕ}
    {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ} {M N : TDA.Persistence.PModule.{0, 0, 0} k ℝ}
    (hM : TDA.Persistence.FiniteConstructible.IsConstructible c M)
    (hN : TDA.Persistence.FiniteConstructible.IsConstructible d N)
    (hfdM : ∀ j, FiniteDimensional k (M.obj (c j)))
    (hfdN : ∀ j, FiniteDimensional k (N.obj (d j))) {r : ENNReal}
    (h : TDA.Persistence.bottleneck
        (TDA.Persistence.FiniteConstructible.moduleDiagram c M hfdM)
        (TDA.Persistence.FiniteConstructible.moduleDiagram d N hfdN) < r) :
    ∃ ε : NNReal, (ε : ENNReal) < r ∧ Nonempty (TDA.Persistence.RealInterleaving ε M N) := by
  rw [TDA.Persistence.FiniteConstructible.bottleneck_eq_distance hM hN hfdM hfdN] at h
  exact TDA.Persistence.realInterleavingDistance_lt_iff.mp h

/-- A bottleneck distance above `ε` excludes an `ε`-interleaving. -/
theorem isEmpty_interleaving_of_lt_bottleneck {k : Type} [Field k] {n m : ℕ}
    {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ} {M N : TDA.Persistence.PModule.{0, 0, 0} k ℝ}
    (hM : TDA.Persistence.FiniteConstructible.IsConstructible c M)
    (hN : TDA.Persistence.FiniteConstructible.IsConstructible d N)
    (hfdM : ∀ j, FiniteDimensional k (M.obj (c j)))
    (hfdN : ∀ j, FiniteDimensional k (N.obj (d j))) {ε : NNReal}
    (h : (ε : ENNReal) < TDA.Persistence.bottleneck
        (TDA.Persistence.FiniteConstructible.moduleDiagram c M hfdM)
        (TDA.Persistence.FiniteConstructible.moduleDiagram d N hfdN)) :
    IsEmpty (TDA.Persistence.RealInterleaving ε M N) :=
  ⟨fun i => absurd
    (TDA.Persistence.FiniteConstructible.bottleneck_le_of_interleaving hM hN hfdM hfdN i)
    (not_le.mpr h)⟩

/-- Filters on two finite complexes with interleaved sublevel modules have diagrams within
the interleaving parameter. -/
theorem dgm_bottleneck_le_of_sublevelInterleaving {a b : ℕ}
    {K : PreAbstractSimplicialComplex (Fin a)} [Fintype (TDA.Simplicial.TotalFace K)]
    {L : PreAbstractSimplicialComplex (Fin b)} [Fintype (TDA.Simplicial.TotalFace L)]
    (k : Type) [Field k] (f : TDA.Filtration.FilterFunction K ℝ)
    (g : TDA.Filtration.FilterFunction L ℝ) (n : ℕ) {ε : NNReal}
    (i : TDA.Persistence.RealInterleaving ε (TDA.Persistence.sublevelModule k f n)
      (TDA.Persistence.sublevelModule k g n)) :
    TDA.Persistence.bottleneck (TDA.Persistence.dgm k f n) (TDA.Persistence.dgm k g n) ≤
      (ε : ENNReal) :=
  TDA.Persistence.bottleneck_dgm_le_of_sublevelInterleaving k n f g i

/-- The triangle inequality for the diagrams of three filters on three finite complexes,
through the interleaving distance of the sublevel modules. -/
theorem dgm_bottleneck_triangle {a b c : ℕ}
    {K : PreAbstractSimplicialComplex (Fin a)} [Fintype (TDA.Simplicial.TotalFace K)]
    {L : PreAbstractSimplicialComplex (Fin b)} [Fintype (TDA.Simplicial.TotalFace L)]
    {P : PreAbstractSimplicialComplex (Fin c)} [Fintype (TDA.Simplicial.TotalFace P)]
    (k : Type) [Field k] (f : TDA.Filtration.FilterFunction K ℝ)
    (g : TDA.Filtration.FilterFunction L ℝ) (h : TDA.Filtration.FilterFunction P ℝ) (n : ℕ) :
    TDA.Persistence.bottleneck (TDA.Persistence.dgm k f n) (TDA.Persistence.dgm k h n) ≤
      TDA.Persistence.bottleneck (TDA.Persistence.dgm k f n) (TDA.Persistence.dgm k g n) +
        TDA.Persistence.bottleneck (TDA.Persistence.dgm k g n) (TDA.Persistence.dgm k h n) := by
  rw [TDA.Persistence.bottleneck_dgm_eq_realInterleavingDistance k n f h,
    TDA.Persistence.bottleneck_dgm_eq_realInterleavingDistance k n f g,
    TDA.Persistence.bottleneck_dgm_eq_realInterleavingDistance k n g h]
  exact TDA.Persistence.realInterleavingDistance_triangle _ _ _

end TDA.Persistence.InterleavingIsometryClientExamples
