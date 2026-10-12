import TDA.Filtration.OrderChamber
import TDA.Filtration.CompatibleOrderTransfer

set_option autoImplicit false

universe u v w

namespace TDA.Filtration

variable {V : Type u} {β : Type v} {X : Type w}
variable [TopologicalSpace X] [LinearOrder β] [TopologicalSpace β]
  [OrderClosedTopology β]
variable {K : PreAbstractSimplicialComplex V}

theorem FilterFunction.exists_open_orderingEquivalent_of_mem_orderChamber
    [Finite (TDA.Simplicial.TotalFace K)]
    (F : X → FilterFunction K β)
    (hF : ∀ s : TDA.Simplicial.TotalFace K,
      Continuous (fun x => (F x).value s))
    {x₀ : X}
    (hx₀ : x₀ ∈ orderChamber (fun x s => (F x).value s)) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ orderChamber (fun x s => (F x).value s) ∧
      ∀ x ∈ U, OrderingEquivalent (F x₀) (F x) := by
  obtain ⟨U, hUo, hxU, hUc, hUe⟩ :=
    exists_open_le_iff_of_mem_orderChamber
      (fun x s => (F x).value s) hF hx₀
  exact ⟨U, hUo, hxU, hUc, fun x hx s t => hUe x hx s t⟩

theorem CompatibleOrder.exists_open_sameEnum_of_mem_orderChamber
    [Fintype (TDA.Simplicial.TotalFace K)]
    (F : X → FilterFunction K β)
    (hF : ∀ s : TDA.Simplicial.TotalFace K,
      Continuous (fun x => (F x).value s))
    {x₀ : X}
    (hx₀ : x₀ ∈ orderChamber (fun x s => (F x).value s))
    (e : CompatibleOrder (F x₀)) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ orderChamber (fun x s => (F x).value s) ∧
      ∀ x ∈ U, ∃ d : CompatibleOrder (F x), d.enum = e.enum := by
  obtain ⟨U, hUo, hxU, hUc, hUe⟩ :=
    FilterFunction.exists_open_orderingEquivalent_of_mem_orderChamber F hF hx₀
  refine ⟨U, hUo, hxU, hUc, ?_⟩
  intro x hx
  let h : OrderingEquivalent (F x₀) (F x) := hUe x hx
  exact ⟨e.transferOfOrderingEquivalent h,
    e.transferOfOrderingEquivalent_enum h⟩

end TDA.Filtration
