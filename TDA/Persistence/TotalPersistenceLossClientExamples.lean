import TDA.Persistence.TotalPersistenceRegularity
import TDA.Persistence.SublevelLossDerivative
import TDA.Filtration.CompatibleOrderExistence

/-!
# Client statements for total persistence as a differentiable loss

Regression fixtures for #1270, family 8 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance.

* A `C¹` family of real filters on a finite complex whose face order is constant on an open
  set: the squared total persistence of its degree-`p` diagram is `C¹` near every parameter
  of that set.
* The squared total persistence of an ordered presentation is the sum of the squared
  endpoint differences.
-/

namespace TDA.Persistence.TotalPersistenceLossClientExamples

/-- The squared total persistence of a `C¹` filter family with constant face order is `C¹`
near the base parameter. -/
theorem squaredTotalPersistence_c1_near {m : ℕ} {K : PreAbstractSimplicialComplex (Fin m)}
    [Fintype (TDA.Simplicial.TotalFace K)] (k : Type) [Field k]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → TDA.Filtration.FilterFunction K ℝ) {x₀ : E} (p : ℕ) {U : Set E}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hF : ∀ s : TDA.Simplicial.TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (hord : ∀ x ∈ U, TDA.Filtration.OrderingEquivalent (F x₀) (F x)) :
    ∃ N : Set E, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ U ∧
      ContDiffOn ℝ 1 (fun x => (TDA.Persistence.dgm k (F x) p).totalPersistence 2) N := by
  obtain ⟨e⟩ := TDA.Filtration.exists_compatibleOrder (F x₀)
  exact TDA.Persistence.sublevelDiagramScalarLoss_c1_neighborhood k F e p hU hx₀ hF hord _
    (TDA.Persistence.totalPersistence_c1ThroughAllRepresentatives (by decide) (by decide) _)

/-- The squared total persistence of an ordered presentation. -/
theorem squaredTotalPersistence_orderedQ (m n : ℕ)
    (z : TDA.Persistence.DiagramCoordinates m n) :
    (TDA.Persistence.orderedQ m n z).totalPersistence 2 =
      ∑ i : Fin m, ((z.1 i).2 - (z.1 i).1) ^ 2 := by
  rw [TDA.Persistence.totalPersistence_orderedQ (by decide)]
  exact Finset.sum_congr rfl fun i _ => sq_abs _

end TDA.Persistence.TotalPersistenceLossClientExamples
