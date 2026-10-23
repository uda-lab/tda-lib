import TDA.Topology.MultiNerveMap
import TDA.Topology.MultiNerveExamples

/-!
# Multinerve refinement-map fixtures

A discrete control for `TDA.Topology.MultiNerveMap`. On the discrete space `Bool`, the family of
singletons `{false}` and `{true}` refines to the one-member family `Set.univ` by the constant
selector. The ordinary nerve map identifies the two vertices, so it is not injective. The
multinerve map sends the two vertex cells to two distinct cells over `{()}`, represented by
`false` and `true`, because distinct points of a discrete space lie in distinct path
components. The identity refinement fixes each vertex cell.
-/

namespace TDA.Topology.MultiNerveMapExamples

open Finset Set
open TDA.Topology.MultiNerveCell
open TDA.Topology.MultiNerveExamples (singletonFamily)

noncomputable section

/-- In a discrete space, the carrier of every multinerve cell has at most one point: a path is
constant. -/
theorem carrier_subsingleton_of_discrete {X I : Type*} [TopologicalSpace X] [DiscreteTopology X]
    {V : CoverFamily X I} (a : MultiNerveCell V) : a.carrier.Subsingleton := by
  rintro x ⟨hx, hcx⟩ y ⟨hy, hcy⟩
  obtain ⟨γ⟩ := Quotient.exact (hcx.trans hcy.symm)
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace unitInterval)
    γ.continuous (x := 0) (y := 1)
  rw [γ.source, γ.target] at h
  exact congrArg Subtype.val h

/-- The one-member full family on the discrete Boolean space. -/
def fullFamily : CoverFamily Bool Unit := fun _ => Set.univ

/-- The refinement of the singleton family to the full family by the constant selector. -/
def collapseRefinement : Refinement singletonFamily fullFamily where
  selector _ := ()
  subset _ := Set.subset_univ _

private theorem mem_interMember_singleton (b : Bool) :
    b ∈ interMember singletonFamily {b} := by
  rw [interMember_singleton]
  exact Set.mem_singleton b

/-- The vertex cell of the singleton family over `{b}`. -/
def pointCell (b : Bool) : MultiNerveCell singletonFamily :=
  MultiNerveCell.mk {b} (Finset.singleton_nonempty b)
    (ZerothHomotopy.mk ⟨b, mem_interMember_singleton b⟩)

/-- The ordinary nerve map identifies both vertices, so it is not injective. -/
theorem collapse_nerveMap_not_injective :
    nerveMap collapseRefinement false = nerveMap collapseRefinement true ∧
      ¬ Function.Injective (nerveMap collapseRefinement) := by
  have h : nerveMap collapseRefinement false = nerveMap collapseRefinement true := rfl
  exact ⟨h, fun hinj => Bool.false_ne_true (hinj h)⟩

/-- The multinerve map keeps what the nerve map collapses: the two distinct vertex cells go to
two distinct cells over `{()}`, represented by `false` and `true`. -/
theorem collapse_multiNerveMap_separates :
    pointCell false ≠ pointCell true ∧
      (∀ b, (multiNerveMap collapseRefinement (pointCell b)).support = {()}) ∧
      (∀ b, b ∈ (multiNerveMap collapseRefinement (pointCell b)).carrier) ∧
      multiNerveMap collapseRefinement (pointCell false) ≠
        multiNerveMap collapseRefinement (pointCell true) := by
  have hmem : ∀ b, b ∈ (multiNerveMap collapseRefinement (pointCell b)).carrier :=
    fun b => ⟨_, rfl⟩
  refine ⟨fun h => ?_, fun b => Finset.eq_singleton_iff_nonempty_unique_mem.2
    ⟨support_nonempty _, fun _ _ => rfl⟩, hmem, fun h => ?_⟩
  · have hs := congrArg MultiNerveCell.support h
    exact Bool.false_ne_true (Finset.singleton_inj.1 hs)
  · have hf := hmem false
    rw [h] at hf
    exact Bool.false_ne_true (carrier_subsingleton_of_discrete _ hf (hmem true))

/-- The identity refinement fixes a vertex cell. -/
theorem multiNerveMap_id_pointCell (b : Bool) :
    multiNerveMap (Refinement.id singletonFamily) (pointCell b) = pointCell b :=
  congrFun multiNerveMap_id (pointCell b)

end

end TDA.Topology.MultiNerveMapExamples
