import TDA.Mapper.Tower
import TDA.Simplicial.ContiguityHomotopy
import TDA.Persistence.Basic

/-!
# Homology maps and persistence modules of Mapper refinements

A selected refinement `r : Refinement U V` of target families induces the
Mapper vertex map `mapperMap f r` and therefore a map on the ordered-chain
simplicial homology of `mapper f U` into that of `mapper f V`, over any ring
and in every degree.  The ambient vertex types `ComponentIndex f U` and
`ComponentIndex f V` carry supplied linear orders and lie in one universe, as
the signed chain model requires; nothing is assumed about openness, coverage,
multiplicity, finiteness, or the vertex orders beyond their existence.

Two selected refinements between the same families induce contiguous vertex
maps, so the signed prism of `TDA.Simplicial.ContiguityHomotopy` is a chain
homotopy between their chain maps and their homology maps are equal.  Hence a
self-refinement induces the identity on homology and the composite of two
induced maps is the map induced by any refinement between the outer families.

Along a preorder, cover families with a selected refinement on every
comparison give a persistence module whose value at `p` is the homology of
`mapper f (U p)` and whose structure maps are the induced maps.  The functor
laws hold without identity or composition equations on the selectors, and the
module does not depend on which refinements were selected.  The strict
`CoherentCoverTower` supplies such choices and its simplicial maps induce the
same structure maps.

No multinerve statement, Nerve Lemma, reconstruction, stability estimate,
barcode or tameness result is included, and nothing is claimed about changing
the vertex orders.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence

noncomputable section

universe u v w p c

variable {X : Type u} {Y : Type v} {P : Type p}
  [TopologicalSpace X] [TopologicalSpace Y] [Preorder P]
variable (R : Type c) [Ring R]

section Refinement

variable (f : C(X, Y)) {I J K : Type w} {U : I → Set Y} {V : J → Set Y} {W : K → Set Y}
  [LinearOrder (ComponentIndex f U)] [LinearOrder (ComponentIndex f V)]
  [LinearOrder (ComponentIndex f W)]

/-- The map on simplicial homology induced by a selected refinement of target
families. -/
def mapperHomologyMap (r : Refinement U V) (n : ℕ) :
    simplicialHomology (mapper f U) R n ⟶ simplicialHomology (mapper f V) R n :=
  simplicialHomologyMap R (mapperMap f r) n

/-- The induced homology map is the homology map of the Mapper vertex map. -/
theorem mapperHomologyMap_def (r : Refinement U V) (n : ℕ) :
    mapperHomologyMap R f r n = simplicialHomologyMap R (mapperMap f r) n :=
  rfl

/-- The identity refinement induces the identity on homology. -/
theorem mapperHomologyMap_id (n : ℕ) :
    mapperHomologyMap R f (Refinement.id U) n =
      𝟙 (simplicialHomology (mapper f U) R n) := by
  rw [mapperHomologyMap_def, mapperMap_id, simplicialHomologyMap_id]

/-- Composition of refinements induces composition of homology maps. -/
theorem mapperHomologyMap_comp (r : Refinement U V) (s : Refinement V W) (n : ℕ) :
    mapperHomologyMap R f (Refinement.comp r s) n =
      mapperHomologyMap R f r n ≫ mapperHomologyMap R f s n := by
  rw [mapperHomologyMap_def, mapperMap_comp, simplicialHomologyMap_comp]
  rfl

/-- The signed prism chain homotopy between the chain maps of two selected
refinements of the same families. -/
def mapperChainHomotopy (r s : Refinement U V) :
    Homotopy (simplicialChainMap R (mapperMap f r)) (simplicialChainMap R (mapperMap f s)) :=
  Contiguous.chainHomotopy R (mapperMap_contiguous f r s)

/-- The degree-raising component of the refinement homotopy is minus the signed
prism of the contiguous Mapper maps. -/
@[simp]
theorem mapperChainHomotopy_hom_succ (r s : Refinement U V) (n : ℕ) :
    (mapperChainHomotopy R f r s).hom n (n + 1) =
      ModuleCat.ofHom (-Contiguous.prismMap R (mapperMap_contiguous f r s) n) :=
  Contiguous.chainHomotopy_hom_succ R _ n

/-- Two selected refinements of the same families induce the same homology map. -/
theorem mapperHomologyMap_eq (r s : Refinement U V) (n : ℕ) :
    mapperHomologyMap R f r n = mapperHomologyMap R f s n :=
  Contiguous.simplicialHomologyMap_eq R (mapperMap_contiguous f r s) n

/-- Every refinement of a family into itself induces the identity on homology. -/
@[simp]
theorem mapperHomologyMap_eq_id (r : Refinement U U) (n : ℕ) :
    mapperHomologyMap R f r n = 𝟙 (simplicialHomology (mapper f U) R n) := by
  rw [mapperHomologyMap_eq R f r (Refinement.id U), mapperHomologyMap_id]

/-- The composite of two induced homology maps is the map induced by any
refinement between the outer families. -/
theorem mapperHomologyMap_comp_eq (r : Refinement U V) (s : Refinement V W)
    (t : Refinement U W) (n : ℕ) :
    mapperHomologyMap R f r n ≫ mapperHomologyMap R f s n = mapperHomologyMap R f t n := by
  rw [← mapperHomologyMap_comp, mapperHomologyMap_eq R f (Refinement.comp r s) t]

end Refinement

section Tower

variable (f : C(X, Y)) {Index : P → Type w} (cover : (q : P) → Index q → Set Y)
  [∀ q, LinearOrder (ComponentIndex f (cover q))]

/-- The Mapper homology persistence module of cover families along a preorder
with a selected refinement on every comparison.  The selectors need not satisfy
identity or composition equations. -/
def mapperHomologyPModule
    (r : ∀ {q t : P}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ) :
    PModule.{c, p, max (max w u) c} R P where
  obj q := simplicialHomology (mapper f (cover q)) R n
  map h := mapperHomologyMap R f (r (leOfHom h)) n
  map_id _ := mapperHomologyMap_eq_id R f _ n
  map_comp _ _ := (mapperHomologyMap_comp_eq R f _ _ _ n).symm

variable (r : ∀ {q t : P}, q ≤ t → Refinement (cover q) (cover t)) (n : ℕ)

/-- The value at a parameter is the homology of the Mapper complex of its family. -/
@[simp]
theorem mapperHomologyPModule_obj (q : P) :
    (mapperHomologyPModule R f cover r n).obj q = simplicialHomology (mapper f (cover q)) R n :=
  rfl

/-- The structure map of a comparison is the homology map of its selected refinement. -/
@[simp]
theorem structureMap_mapperHomologyPModule {q t : P} (h : q ≤ t) :
    structureMap (mapperHomologyPModule R f cover r n) h = mapperHomologyMap R f (r h) n :=
  rfl

/-- The linear structure map of a comparison is the underlying linear map of the
homology map of its selected refinement. -/
@[simp]
theorem structureMapLinear_mapperHomologyPModule {q t : P} (h : q ≤ t) :
    structureMapLinear (mapperHomologyPModule R f cover r n) h =
      (mapperHomologyMap R f (r h) n).hom :=
  rfl

/-- The persistence module does not depend on the selected refinements. -/
theorem mapperHomologyPModule_eq
    (r' : ∀ {q t : P}, q ≤ t → Refinement (cover q) (cover t)) :
    mapperHomologyPModule R f cover r n = mapperHomologyPModule R f cover r' n := by
  exact CategoryTheory.Functor.hext (fun _ => rfl)
    (fun _ _ _ => heq_of_eq (mapperHomologyMap_eq R f _ _ n))

end Tower

namespace CoherentCoverTower

variable (T : CoherentCoverTower Y P) (f : C(X, Y))
  [∀ q, LinearOrder (ComponentIndex f (T.cover q))]

/-- The refinements of a coherent cover tower give a persistence module whose
structure maps are the homology maps of the tower's strict Mapper maps. -/
theorem structureMap_mapperHomologyPModule (n : ℕ) {q t : P} (h : q ≤ t) :
    structureMap (mapperHomologyPModule R f T.cover T.refinement n) h =
      simplicialHomologyMap R (T.mapperMap f h) n :=
  rfl

end CoherentCoverTower

end

end TDA.Mapper
