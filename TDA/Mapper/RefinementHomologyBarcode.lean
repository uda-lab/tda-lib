import TDA.Mapper.RefinementHomology
import TDA.Mapper.GraphPL
import TDA.Simplicial.FiniteDimensionalHomology
import TDA.Persistence.FiniteDecomposition

/-!
# Barcodes of finite Mapper homology modules

Let `f : C(X, Y)` be continuous, let `cover q : Index q → Set Y` be cover families along a
preorder with a selected refinement `r h` on every comparison `h : q ≤ t`, and fix linear orders
on the component-index types and a degree `n`.  If every Mapper complex `mapper f (cover q)` has
finitely many `n`-faces, then every value of `mapperHomologyPModule k f cover r n` over a field
`k` is finite-dimensional.

On a finite chain `Fin N`, with the field, the domain and the index types in one universe `u`,
the canonical rank barcode of the module is `mapperBarcode`: a multiset of half-open intervals
`[birth, death)` with `death ≤ N`.  The bar
`[b, N)` records a class that survives to the last observed stage; it does not assert an
infinite lifetime.  The barcode does not depend on the selected refinements, the module is
naturally isomorphic to the realization of its barcode, the rank of every structure map counts
the bars alive at both ends, and two such modules are isomorphic exactly when their barcodes
agree.  For a `CoherentCoverTower` the same ranks are those of the homology maps of the strict
Mapper maps.

For the piecewise-linear height of a finite graph and finitely many open-interval labels at
every stage, the face-finiteness hypothesis holds by `GraphPL.finite_mapperFaces`, so the
barcode is available without further assumptions.  Coverage of the height range is not needed.

The decomposition is the finite-chain interval decomposition of `TDA.Persistence`.  Nothing is
claimed for real-indexed or q-tame Mapper modules, for stability of Mapper barcodes, for a change
of the component orders, for multinerve Mapper, or for an executable barcode extraction.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence

noncomputable section

universe u v w p c

section FiniteDimensional

variable {X : Type u} {Y : Type v} {P : Type p}
  [TopologicalSpace X] [TopologicalSpace Y] [Preorder P]

/-- Every value of a Mapper homology module over a field is finite-dimensional when the
Mapper complexes have finitely many faces in the given degree. -/
instance mapperHomologyPModule_finiteDimensional (k : Type c) [Field k] (f : C(X, Y))
    {Index : P → Type w} (cover : (q : P) → Index q → Set Y)
    [∀ q, LinearOrder (ComponentIndex f (cover q))]
    (r : ∀ {q t : P}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ)
    [∀ q, Finite (Face (mapper f (cover q)) n)] (q : P) :
    FiniteDimensional k ((mapperHomologyPModule k f cover r n).obj q) :=
  simplicialHomology_finiteDimensional (mapper f (cover q)) k n

end FiniteDimensional

section Barcode

variable {N : ℕ} {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (f : C(X, Y)) {Index : Fin N → Type u}
  (cover : (q : Fin N) → Index q → Set Y) [∀ q, LinearOrder (ComponentIndex f (cover q))]
  (r : ∀ {q t : Fin N}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ)
  [∀ q, Finite (Face (mapper f (cover q)) n)]

/-- The barcode of the degree-`n` Mapper homology module on the finite chain `Fin N`. -/
def mapperBarcode : Multiset (FiniteInterval N) :=
  rankBarcode (mapperHomologyPModule k f cover r n)

/-- The Mapper barcode does not depend on the selected refinements. -/
theorem mapperBarcode_eq (r' : ∀ {q t : Fin N}, q ≤ t → Refinement (cover q) (cover t)) :
    mapperBarcode k f cover r n = mapperBarcode k f cover r' n :=
  rankBarcode_eq_of_iso (eqToIso (mapperHomologyPModule_eq k f cover r n r'))

/-- The Mapper homology module is naturally isomorphic to the realization of its barcode. -/
theorem nonempty_mapperBarcodeIso :
    Nonempty (mapperHomologyPModule k f cover r n ≅
      barcodeModule (k := k) (mapperBarcode k f cover r n)) :=
  nonempty_rankBarcodeIso _

/-- The rank of the homology map of a selected refinement between stages `q ≤ t` is the number
of bars alive at both stages. -/
theorem finrank_range_mapperHomologyMap {q t : Fin N} (h : q ≤ t) :
    Module.finrank k (LinearMap.range (mapperHomologyMap k f (r h) n).hom) =
      (mapperBarcode k f cover r n).countP (fun I => I.birth ≤ q.val ∧ t.val < I.death) :=
  (structureMapRank_rankBarcode (mapperHomologyPModule k f cover r n) q t h).symm.trans
    (rank_barcodeMap _ q t h)

/-- A multiset of intervals is the Mapper barcode exactly when it counts the rank of every
homology map of a selected refinement. -/
theorem mapperBarcode_eq_iff (B : Multiset (FiniteInterval N)) :
    mapperBarcode k f cover r n = B ↔
      ∀ (q t : Fin N) (h : q ≤ t),
        Module.finrank k (LinearMap.range (mapperHomologyMap k f (r h) n).hom) =
          B.countP (fun I => I.birth ≤ q.val ∧ t.val < I.death) := by
  constructor
  · rintro rfl q t h
    exact finrank_range_mapperHomologyMap k f cover r n h
  · intro hB
    calc mapperBarcode k f cover r n = rankBarcode (barcodeModule (k := k) B) :=
          (rankBarcode_eq_iff _ _).2 fun q t h =>
            (hB q t h).trans (rank_barcodeMap B q t h).symm
      _ = B := rankBarcode_barcodeModule B

variable {X' : Type u} {Y' : Type w} [TopologicalSpace X'] [TopologicalSpace Y']
  (f' : C(X', Y')) {Index' : Fin N → Type u} (cover' : (q : Fin N) → Index' q → Set Y')
  [∀ q, LinearOrder (ComponentIndex f' (cover' q))]
  (r' : ∀ {q t : Fin N}, q ≤ t → Refinement (cover' q) (cover' t)) (m : ℕ)
  [∀ q, Finite (Face (mapper f' (cover' q)) m)]

/-- Two finite Mapper homology modules on `Fin N` are isomorphic exactly when their barcodes
agree. -/
theorem nonempty_iso_iff_mapperBarcode_eq :
    Nonempty (mapperHomologyPModule k f cover r n ≅ mapperHomologyPModule k f' cover' r' m) ↔
      mapperBarcode k f cover r n = mapperBarcode k f' cover' r' m :=
  nonempty_iso_iff_rankBarcode_eq _ _

end Barcode

namespace CoherentCoverTower

variable {N : ℕ} {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (k : Type u) [Field k] (T : CoherentCoverTower.{v, u, 0} Y (Fin N)) (f : C(X, Y))
  [∀ q, LinearOrder (ComponentIndex f (T.cover q))] (n : ℕ)
  [∀ q, Finite (Face (mapper f (T.cover q)) n)]

/-- The rank of the homology map of the strict Mapper map of a coherent cover tower between
stages `q ≤ t` is the number of bars of its Mapper barcode alive at both stages. -/
theorem finrank_range_simplicialHomologyMap {q t : Fin N} (h : q ≤ t) :
    Module.finrank k (LinearMap.range (simplicialHomologyMap k (T.mapperMap f h) n).hom) =
      (mapperBarcode k f T.cover T.refinement n).countP
        (fun I => I.birth ≤ q.val ∧ t.val < I.death) := by
  rw [← T.structureMap_mapperHomologyPModule k f n h]
  exact finrank_range_mapperHomologyMap k f T.cover T.refinement n h

end CoherentCoverTower

namespace GraphPL

/-- For a finite graph and finitely many interval labels, the graph-PL Mapper complex has
finitely many faces in every degree. -/
instance finite_mapperFace {V : Type v} {I : Type w} [Finite V] [Finite I]
    (G : SimpleGraph V) (h : V → ℝ) (U : I → TDA.Reeb.OpenInterval) (n : ℕ) :
    Finite (Face (mapper (TDA.Reeb.GraphPL.plHeight G h) (fun i => (U i : Set ℝ))) n) :=
  have := finite_mapperFaces G h U
  faceFiniteOfTotalFinite _ n

end GraphPL

-- The graph-PL instance discharges the finiteness hypothesis of `mapperBarcode`.
example {N : ℕ} {V : Type u} [Finite V] (G : SimpleGraph V) (h : V → ℝ)
    {Index : Fin N → Type u} [∀ q, Finite (Index q)]
    (cover : (q : Fin N) → Index q → TDA.Reeb.OpenInterval)
    [∀ q, LinearOrder (ComponentIndex (TDA.Reeb.GraphPL.plHeight G h)
      (fun i => (cover q i : Set ℝ)))]
    (r : ∀ {q t : Fin N}, q ≤ t →
      Refinement (fun i => (cover q i : Set ℝ)) (fun i => (cover t i : Set ℝ)))
    (k : Type u) [Field k] (n : ℕ) :
    Nonempty (mapperHomologyPModule k (TDA.Reeb.GraphPL.plHeight G h)
        (fun q i => (cover q i : Set ℝ)) r n ≅
      barcodeModule (k := k)
        (mapperBarcode k (TDA.Reeb.GraphPL.plHeight G h)
          (fun q i => (cover q i : Set ℝ)) r n)) :=
  nonempty_mapperBarcodeIso _ _ _ _ _

end

end TDA.Mapper
