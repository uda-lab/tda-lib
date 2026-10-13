import TDA.Mapper.Refinement
import TDA.Simplicial.Contiguity

/-!
# Coherent towers of ordinary Mapper complexes

A coherent cover tower supplies an indexed family at every point of a preorder,
a selected refinement along every comparison, and strict identity and
composition equations for the underlying selectors.  The index types may vary
with the preorder point but all live in one fixed universe.

Ordinary Mapper sends this data to complexes and simplicial vertex maps with
strict identity and composition laws.  The coherence is supplied data; it is
not inferred from arbitrary choices of refinement selectors.
-/

namespace TDA.Mapper

open TDA.Topology
open TDA.Simplicial

noncomputable section

universe u v w p

variable {X : Type u} {Y : Type v} {P : Type p}
  [TopologicalSpace X] [TopologicalSpace Y] [Preorder P]

/-- A coherent tower of indexed cover families over a preorder.

The dependent index types may vary with the preorder point, but they are
restricted to one common universe `Type w`.  Identity and composition are
strict equations of the supplied selector functions.
-/
structure CoherentCoverTower (Y : Type v) (P : Type p) [Preorder P] where
  /-- The index type at a preorder point. -/
  Index : P → Type w
  /-- The indexed family at a preorder point. -/
  cover : (q : P) → Index q → Set Y
  /-- The selected refinement attached to a comparison. -/
  refinement : ∀ {q r : P}, q ≤ r → Refinement (cover q) (cover r)
  /-- Reflexive comparisons use the identity selector. -/
  selector_refl : ∀ q,
    (refinement (q := q) (r := q) (le_refl q)).selector = id
  /-- Selectors compose strictly along transitive comparisons. -/
  selector_trans : ∀ {q r t : P} (h : q ≤ r) (k : r ≤ t),
    (refinement k).selector ∘ (refinement h).selector =
      (refinement (h.trans k)).selector

namespace CoherentCoverTower

variable (T : CoherentCoverTower Y P)

/-- The ordinary Mapper complex at a point of a coherent cover tower. -/
def mapperComplex (f : C(X, Y)) (q : P) :
    PreAbstractSimplicialComplex (ComponentIndex f (T.cover q)) :=
  mapper f (T.cover q)

/-- The Mapper vertex map attached to a comparison in a coherent cover tower. -/
def mapperMap (f : C(X, Y)) {q r : P} (h : q ≤ r) :
    VertexMap (T.mapperComplex f q) (T.mapperComplex f r) :=
  TDA.Mapper.mapperMap f (T.refinement h)

/-- A coherent cover tower induces the identity Mapper map on reflexive
comparisons. -/
theorem mapperMap_refl (f : C(X, Y)) (q : P) :
    T.mapperMap f (le_refl q) = VertexMap.id (T.mapperComplex f q) := by
  have hrefinement : T.refinement (q := q) (r := q) (le_refl q) =
      Refinement.id (T.cover q) := by
    apply Refinement.ext
    intro i
    exact congrFun (T.selector_refl q) i
  unfold mapperMap
  rw [hrefinement]
  exact TDA.Mapper.mapperMap_id f (T.cover q)

/-- Mapper maps of a coherent cover tower compose strictly. -/
theorem mapperMap_trans (f : C(X, Y)) {q r t : P}
    (h : q ≤ r) (k : r ≤ t) :
    VertexMap.comp (T.mapperMap f h) (T.mapperMap f k) =
      T.mapperMap f (h.trans k) := by
  have hrefinement : Refinement.comp (T.refinement h) (T.refinement k) =
      T.refinement (h.trans k) := by
    apply Refinement.ext
    intro i
    exact congrFun (T.selector_trans h k) i
  change VertexMap.comp
      (TDA.Mapper.mapperMap f (T.refinement h))
      (TDA.Mapper.mapperMap f (T.refinement k)) =
    TDA.Mapper.mapperMap f (T.refinement (h.trans k))
  rw [← TDA.Mapper.mapperMap_comp, hrefinement]

end CoherentCoverTower

/-- Any two selected target-cover refinements induce contiguous Mapper maps. -/
theorem mapperMap_contiguous (f : C(X, Y))
    {I : Type w} {J : Type p} {U : I → Set Y} {V : J → Set Y}
    (R S : Refinement U V) :
    Contiguous (TDA.Mapper.mapperMap f R) (TDA.Mapper.mapperMap f S) := by
  exact nerveMap_contiguous (componentRefinement f R) (componentRefinement f S)

end

end TDA.Mapper
