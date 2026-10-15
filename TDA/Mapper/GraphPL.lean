import TDA.Mapper.Refinement
import TDA.Reeb.GraphPLComponents
import TDA.Topology.PathComponents
import Mathlib.Data.Finite.Sigma

/-!
# Ordinary Mapper on finite graph realizations

For a piecewise-linear height on a graph realization, the path-component labels of ordinary
Mapper are relabelled by connected components of the graph-PL incidence graphs.  The relabelling
preserves and reflects every finite face and is natural for selected refinements of interval
families.  Finiteness is stated only when both the graph vertex type and the interval-label type
are finite.
-/

namespace TDA.Mapper.GraphPL

open Finset Set SimpleGraph
open TDA.Simplicial TDA.Topology
open TDA.Reeb
open TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval

noncomputable section

universe u v w

variable {V : Type u} {I : Type v} {J : Type w}

local instance (α : Type*) : DecidableEq α := Classical.decEq α

/-- Mapper labels expressed as connected components of the graph-PL incidence graph in each
interval. -/
def IncidenceComponentIndex (G : SimpleGraph V) (h : V → ℝ) (U : I → OpenInterval) :=
  Σ i, (cellGraph G h (U i)).ConnectedComponent

/-- The graph-PL comparison, assembled over all interval labels. -/
def componentIndexEquiv (G : SimpleGraph V) (h : V → ℝ) (U : I → OpenInterval) :
    ComponentIndex (plHeight G h) (fun i => (U i : Set ℝ)) ≃
      IncidenceComponentIndex G h U :=
  Equiv.sigmaCongrRight fun i => preimageComponentsEquiv G h (U i)

/-- The actual component-cover members, relabelled by incidence-graph components. -/
def incidenceComponentCover (G : SimpleGraph V) (h : V → ℝ) (U : I → OpenInterval) :
    CoverFamily (Realization G) (IncidenceComponentIndex G h U) :=
  fun a => componentCover (plHeight G h) (fun i => (U i : Set ℝ))
    ((componentIndexEquiv G h U).symm a)

/-- Ordinary Mapper after relabelling its vertices by incidence-graph components. -/
def incidenceMapper (G : SimpleGraph V) (h : V → ℝ) (U : I → OpenInterval) :
    PreAbstractSimplicialComplex (IncidenceComponentIndex G h U) :=
  nerve (incidenceComponentCover G h U)

/-- Coverage of the actual realization-height range gives full coverage by the relabelled
component members. -/
theorem incidenceComponentCover_covers (G : SimpleGraph V) (h : V → ℝ)
    (U : I → OpenInterval)
    (hU : Covers (fun i => (U i : Set ℝ)) (Set.range (plHeight G h))) :
    Covers (incidenceComponentCover G h U) Set.univ := by
  intro x hx
  obtain ⟨a, ha⟩ := componentCover_covers_range (plHeight G h)
    (fun i => (U i : Set ℝ)) hU x hx
  refine ⟨componentIndexEquiv G h U a, ?_⟩
  simpa [incidenceComponentCover] using ha

/-- The incidence relabelling preserves and reflects every finite Mapper face. -/
theorem mem_mapper_iff_incidenceMapper_image (G : SimpleGraph V) (h : V → ℝ)
    (U : I → OpenInterval)
    (s : Finset (ComponentIndex (plHeight G h) (fun i => (U i : Set ℝ)))) :
    s ∈ mapper (plHeight G h) (fun i => (U i : Set ℝ)) ↔
      s.image (componentIndexEquiv G h U) ∈ incidenceMapper G h U := by
  constructor
  · intro hs
    obtain ⟨hsn, x, hx⟩ := (mem_mapper_iff _ _ s).1 hs
    apply (mem_nerve_iff _ _).2
    refine ⟨Finset.image_nonempty.mpr hsn, x, ?_⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    simpa [incidenceComponentCover] using hx a ha
  · intro hs
    obtain ⟨hsn, x, hx⟩ := (mem_nerve_iff _ _).1 hs
    apply (mem_mapper_iff _ _ s).2
    refine ⟨Finset.image_nonempty.mp hsn, x, ?_⟩
    intro a ha
    have hmem := hx (componentIndexEquiv G h U a)
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    simpa [incidenceComponentCover] using hmem

/-- Conversely, inverse relabelling preserves and reflects every incidence-labelled face. -/
theorem mem_incidenceMapper_iff_mapper_image_symm (G : SimpleGraph V) (h : V → ℝ)
    (U : I → OpenInterval) (s : Finset (IncidenceComponentIndex G h U)) :
    s ∈ incidenceMapper G h U ↔
      s.image (componentIndexEquiv G h U).symm ∈
        mapper (plHeight G h) (fun i => (U i : Set ℝ)) := by
  constructor
  · intro hs
    obtain ⟨hsn, x, hx⟩ := (mem_nerve_iff _ _).1 hs
    apply (mem_mapper_iff _ _ _).2
    refine ⟨Finset.image_nonempty.mpr hsn, x, ?_⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simpa [incidenceComponentCover] using hx b hb
  · intro hs
    obtain ⟨hsn, x, hx⟩ := (mem_mapper_iff _ _ _).1 hs
    apply (mem_nerve_iff _ _).2
    refine ⟨Finset.image_nonempty.mp hsn, x, ?_⟩
    intro b hb
    have hmem := hx ((componentIndexEquiv G h U).symm b)
      (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    simpa [incidenceComponentCover] using hmem

/-- The selected refinement map written on incidence-component labels. -/
def incidenceRefinementMap (G : SimpleGraph V) (h : V → ℝ)
    {U : I → OpenInterval} {W : J → OpenInterval}
    (R : Refinement (fun i => (U i : Set ℝ)) (fun j => (W j : Set ℝ))) :
    IncidenceComponentIndex G h U → IncidenceComponentIndex G h W :=
  fun a => ⟨R.selector a.1,
    a.2.map (cellInclusion G h (OpenInterval.le_iff_subset.2 (R.subset a.1)))⟩

/-- The graph-PL component comparison conjugates the actual Mapper refinement map to the
incidence-component refinement map. -/
@[simp] theorem componentIndexEquiv_mapperMap (G : SimpleGraph V) (h : V → ℝ)
    {U : I → OpenInterval} {W : J → OpenInterval}
    (R : Refinement (fun i => (U i : Set ℝ)) (fun j => (W j : Set ℝ)))
    (a : ComponentIndex (plHeight G h) (fun i => (U i : Set ℝ))) :
    componentIndexEquiv G h W (mapperMap (plHeight G h) R a) =
      incidenceRefinementMap G h R (componentIndexEquiv G h U a) := by
  rcases a with ⟨i, c⟩
  let hUW : U i ≤ W (R.selector i) := OpenInterval.le_iff_subset.2 (R.subset i)
  change (⟨R.selector i, preimageComponentsEquiv G h (W (R.selector i))
      (componentRefinementMap (plHeight G h) R i c)⟩ :
        IncidenceComponentIndex G h W) =
    ⟨R.selector i,
      (preimageComponentsEquiv G h (U i) c).map (cellInclusion G h hUW)⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  change preimageComponentsEquiv G h (W (R.selector i))
      (TDA.Topology.componentMap (refinementInclusion (plHeight G h) R i) c) =
    (preimageComponentsEquiv G h (U i) c).map (cellInclusion G h hUW)
  rw [show refinementInclusion (plHeight G h) R i =
      TDA.Reeb.preimageInclusion (plHeight G h) (toOpens_le_iff.2 hUW) by
    ext x
    rfl]
  exact preimageComponentsEquiv_componentMap G h hUW c

/-- The selected refinement induces a simplicial vertex map between the incidence-labelled
Mapper nerves. -/
def incidenceMapperMap (G : SimpleGraph V) (h : V → ℝ)
    {U : I → OpenInterval} {W : J → OpenInterval}
    (R : Refinement (fun i => (U i : Set ℝ)) (fun j => (W j : Set ℝ))) :
    VertexMap (incidenceMapper G h U) (incidenceMapper G h W) where
  toFun := incidenceRefinementMap G h R
  map_face s hs := by
    have hs' := (mem_incidenceMapper_iff_mapper_image_symm G h U s).1 hs
    have hm := (mapperMap (plHeight G h) R).map_face _ hs'
    have ht := (mem_mapper_iff_incidenceMapper_image G h W _).1 hm
    rw [Finset.image_image, Finset.image_image] at ht
    have hfun : ((componentIndexEquiv G h W) ∘ (mapperMap (plHeight G h) R)) ∘
        (componentIndexEquiv G h U).symm = incidenceRefinementMap G h R := by
      funext a
      simpa using componentIndexEquiv_mapperMap G h R
        ((componentIndexEquiv G h U).symm a)
    rw [hfun] at ht
    exact ht

@[simp] theorem incidenceMapperMap_apply (G : SimpleGraph V) (h : V → ℝ)
    {U : I → OpenInterval} {W : J → OpenInterval}
    (R : Refinement (fun i => (U i : Set ℝ)) (fun j => (W j : Set ℝ)))
    (a : IncidenceComponentIndex G h U) :
    incidenceMapperMap G h R a = incidenceRefinementMap G h R a := rfl

/-- A finite graph and finitely many interval labels give finitely many actual Mapper component
indices. -/
theorem finite_componentIndex [Finite V] [Finite I] (G : SimpleGraph V) (h : V → ℝ)
    (U : I → OpenInterval) :
    Finite (ComponentIndex (plHeight G h) (fun i => (U i : Set ℝ))) := by
  change Finite (Σ i, ZerothHomotopy
    {p : Realization G // plHeight G h p ∈ U i})
  let _ (i : I) : Finite
      (ZerothHomotopy {p : Realization G // plHeight G h p ∈ U i}) :=
    finite_zerothHomotopy G h (U i)
  infer_instance

/-- Under the same two finiteness hypotheses, the supported Mapper vertex type is finite. -/
theorem finite_mapperVertex [Finite V] [Finite I] (G : SimpleGraph V) (h : V → ℝ)
    (U : I → OpenInterval) :
    Finite (MapperVertex (plHeight G h) (fun i => (U i : Set ℝ))) := by
  let _ := finite_componentIndex G h U
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Under the same two finiteness hypotheses, the subtype of actual finite Mapper faces is
finite. -/
theorem finite_mapperFaces [Finite V] [Finite I] (G : SimpleGraph V) (h : V → ℝ)
    (U : I → OpenInterval) :
    Finite {s : Finset (ComponentIndex (plHeight G h) (fun i => (U i : Set ℝ))) //
      s ∈ mapper (plHeight G h) (fun i => (U i : Set ℝ))} := by
  let _ := finite_componentIndex G h U
  let _ : Fintype (ComponentIndex (plHeight G h) (fun i => (U i : Set ℝ))) :=
    Fintype.ofFinite _
  exact Finite.of_injective Subtype.val Subtype.val_injective

end

end TDA.Mapper.GraphPL
