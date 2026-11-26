import TDA.Mapper.GraphPL
import TDA.Mapper.MultiNerveRefinement

/-!
# Client statements of the Mapper face and projection formulas

Regression fixtures for #1286, family 12 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance. The
client holds a decidable equality on the component indices (a hypothesis of the statement) and
writes the finite images and pairs of component indices with it; every proof is a direct
application of a library theorem.

* The faces of ordinary Mapper: adjacency in the one-skeleton and the description of faces under
  multiplicity at most two.
* The relabelling of Mapper faces by the incidence components of a graph-PL height.
* The labels of an intersection of component members, for cover families indexed by `Fin 3`.
* The support and the projection of the image of a multinerve Mapper cell.
-/

namespace TDA.Mapper.ComponentIndexClientExamples

section Basic

variable {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U : I → Set Y)
  [DecidableEq (ComponentIndex f U)]

/-- Adjacency in the Mapper one-skeleton, with the pair of components written by the client. -/
theorem adj_iff (a b : MapperVertex f U) :
    (mapperOneSkeleton f U).Adj a b ↔
      a ≠ b ∧ ({a.1, b.1} : Finset (ComponentIndex f U)) ∈ mapper f U :=
  mapperOneSkeleton_adj_iff f U a b

/-- Faces of Mapper under multiplicity at most two. -/
theorem mem_mapper_iff (hmult : CoverMultiplicityAtMost f U 2) (s : Finset (ComponentIndex f U)) :
    s ∈ mapper f U ↔
      (∃ a : MapperVertex f U, s = {a.1}) ∨
        ∃ a b : MapperVertex f U, (mapperOneSkeleton f U).Adj a b ∧ s = {a.1, b.1} :=
  mem_mapper_iff_supported_singleton_or_adjacent_pair f U hmult s

end Basic

section GraphPL

variable {V I : Type*} (G : SimpleGraph V) (h : V → ℝ) (U : I → TDA.Reeb.OpenInterval)

/-- Relabelling a Mapper face by the incidence components of a graph-PL height. -/
theorem mem_mapper_iff_incidenceMapper_image
    [DecidableEq (GraphPL.IncidenceComponentIndex G h U)]
    (s : Finset (ComponentIndex (TDA.Reeb.GraphPL.plHeight G h) (fun i => (U i : Set ℝ)))) :
    s ∈ mapper (TDA.Reeb.GraphPL.plHeight G h) (fun i => (U i : Set ℝ)) ↔
      s.image (GraphPL.componentIndexEquiv G h U) ∈ GraphPL.incidenceMapper G h U :=
  GraphPL.mem_mapper_iff_incidenceMapper_image G h U s

/-- Relabelling an incidence-labelled face back to a Mapper face. -/
theorem mem_incidenceMapper_iff_mapper_image_symm
    [DecidableEq (ComponentIndex (TDA.Reeb.GraphPL.plHeight G h) (fun i => (U i : Set ℝ)))]
    (s : Finset (GraphPL.IncidenceComponentIndex G h U)) :
    s ∈ GraphPL.incidenceMapper G h U ↔
      s.image (GraphPL.componentIndexEquiv G h U).symm ∈
        mapper (TDA.Reeb.GraphPL.plHeight G h) (fun i => (U i : Set ℝ)) :=
  GraphPL.mem_incidenceMapper_iff_mapper_image_symm G h U s

end GraphPL

section MultiNerve

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))

/-- The labels of an intersection of component members lie in the target members, for a cover
family indexed by `Fin 3`. -/
theorem fin_three_interMember_subset_preimage (U : Fin 3 → Set Y)
    (s : Finset (ComponentIndex f U)) :
    TDA.Topology.interMember (componentCover f U) s ⊆
      f ⁻¹' ⋂ i ∈ s.image Sigma.fst, U i :=
  componentCover_interMember_subset_preimage f U s

variable {I J : Type*} {U : I → Set Y} {V : J → Set Y} [DecidableEq (ComponentIndex f V)]

/-- The support of the image of a multinerve Mapper cell. -/
theorem support_image (R : TDA.Topology.Refinement U V) (c : multiNerveMapper f U) :
    (multiNerveMapperMap f R c).support =
      c.support.image (componentRefinement f R).selector :=
  support_multiNerveMapperMap f R c

/-- The projection of the image of a multinerve Mapper cell. -/
theorem projection_image (R : TDA.Topology.Refinement U V) (c : multiNerveMapper f U) :
    (multiNerveMapper_projection f V (multiNerveMapperMap f R c)).1 =
      (multiNerveMapper_projection f U c).1.image (mapperMap f R) :=
  multiNerveMapper_projection_multiNerveMapperMap f R c

end MultiNerve

end TDA.Mapper.ComponentIndexClientExamples
