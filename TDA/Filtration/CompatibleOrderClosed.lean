import TDA.Filtration.CompatibleOrderTransfer
import Mathlib.Topology.Order.OrderClosed

set_option autoImplicit false

universe u v w
namespace TDA.Filtration
variable {V : Type u} {α : Type v} {X : Type w}
variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
variable [TopologicalSpace X]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]
variable {f0 : FilterFunction K α}

/-- The parameters where the supplied actual-face enumeration remains compatible form a
closed set when every face grade varies continuously. -/
theorem CompatibleOrder.isClosed_compatible_locus
    (e : CompatibleOrder f0) (F : X → FilterFunction K α)
    (hF : ∀ s : TDA.Simplicial.TotalFace K,
      Continuous (fun x => (F x).value s)) :
    IsClosed {x : X | ∃ d : CompatibleOrder (F x), d.enum = e.enum} := by
  have hclosed : IsClosed {x : X | Monotone ((F x).value ∘ e.enum)} := by
    have hpair : ∀ i j : Fin (Fintype.card (TDA.Simplicial.TotalFace K)),
        IsClosed {x : X | i ≤ j → (F x).value (e.enum i) ≤ (F x).value (e.enum j)} := by
      intro i j
      by_cases hij : i ≤ j
      · simpa only [hij, true_implies] using
          (isClosed_le (hF (e.enum i)) (hF (e.enum j)))
      · simp only [hij, false_implies, Set.ofPred_true, isClosed_univ]
    have h := isClosed_iInter (fun i => isClosed_iInter (hpair i))
    convert h using 1
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    change Monotone ((F x).value ∘ e.enum) ↔
      ∀ i j, i ≤ j → (F x).value (e.enum i) ≤ (F x).value (e.enum j)
    rfl
  convert hclosed using 1
  ext x
  constructor
  · rintro ⟨d, hd⟩
    change Monotone ((F x).value ∘ e.enum)
    rw [← hd]
    exact d.monotone
  · intro hm
    change Monotone ((F x).value ∘ e.enum) at hm
    exact ⟨e.transfer hm, rfl⟩

end TDA.Filtration
