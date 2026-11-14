import TDA.Persistence.ConstructibleQTame
import TDA.Persistence.FiniteDiagramQTame

/-!
# Finite-constructible and canonical q-tame diagrams

A zero-left, right-continuous finite-constructible module with finite-dimensional
critical fibers has the same decorated diagram as its canonical finite barcode.
Finite births and deaths use minus cuts; essential deaths use the infinity cut.
The locally finite bottleneck is therefore the existing finite bottleneck.
-/

set_option autoImplicit false
universe u
namespace TDA.Persistence.FiniteConstructible
open RectangleMeasure
open scoped Classical

variable {k : Type u} [Field k] {n m : ℕ}
variable (c : Fin n ↪o ℝ) (M : PModule.{u,0,u} k ℝ)
    (hM : IsConstructible c M) (hfd : ∀ i, FiniteDimensional k (M.obj (c i)))

/-- Every canonical multiplicity is the number of corresponding barcode occurrences.
Q-tameness and rank semantics follow from constructibility and critical-fiber finiteness. -/
theorem moduleExtendedDiagramMultiplicity_eq_count (p : Cut ℝ × Cut ℝ) :
    moduleExtendedDiagramMultiplicity M (qTame_of_isConstructible c M hM hfd) p =
      ((moduleDiagram c M hfd).points.map diagramDecoratedPoint).count p :=
  FiniteDiagramQTame.moduleExtendedDiagramMultiplicity_eq_count M
    (qTame_of_isConstructible c M hM hfd) (moduleDiagram c M hfd)
    (moduleDiagram_rank c M hM hfd) (moduleDiagram_isPositive c M hfd) p

/-- The canonical locally finite diagram is the occurrence-preserving finite embedding. -/
theorem ofQModule_eq_toLocallyFinite :
    LocallyFiniteDecoratedDiagram.ofQModule (qTame_of_isConstructible c M hM hfd) =
      (moduleDiagram c M hfd).toLocallyFinite (moduleDiagram_isPositive c M hfd) :=
  FiniteDiagramQTame.ofQModule_eq_toLocallyFinite M
    (qTame_of_isConstructible c M hM hfd) (moduleDiagram c M hfd)
    (moduleDiagram_rank c M hM hfd) (moduleDiagram_isPositive c M hfd)

variable (d : Fin m ↪o ℝ) (N : PModule.{u,0,u} k ℝ)
    (hN : IsConstructible d N) (hfdN : ∀ i, FiniteDimensional k (N.obj (d i)))

/-- Every finite barcode matching transports to the canonical diagrams, preserving cost.
The equivalence supplies the reverse transport as well. -/
noncomputable def ofQModuleMatchingEquiv :
    {e : OccurrenceMatching (moduleDiagram c M hfd).finiteOccurrences
        (moduleDiagram d N hfdN).finiteOccurrences
        (moduleDiagram c M hfd).essentialOccurrences
        (moduleDiagram d N hfdN).essentialOccurrences ≃
      OccurrenceMatching
        (LocallyFiniteDecoratedDiagram.ofQModule (qTame_of_isConstructible c M hM hfd)).finiteOccurrences
        (LocallyFiniteDecoratedDiagram.ofQModule (qTame_of_isConstructible d N hN hfdN)).finiteOccurrences
        (LocallyFiniteDecoratedDiagram.ofQModule (qTame_of_isConstructible c M hM hfd)).essentialOccurrences
        (LocallyFiniteDecoratedDiagram.ofQModule (qTame_of_isConstructible d N hN hfdN)).essentialOccurrences //
      ∀ A, LocallyFiniteDecoratedDiagram.matchingCost (e A) =
        A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1)} := by
  rw [ofQModule_eq_toLocallyFinite c M hM hfd,
    ofQModule_eq_toLocallyFinite d N hN hfdN]
  exact ⟨Diagram.toLocallyFiniteMatchingEquiv _ _
    (moduleDiagram_isPositive c M hfd) (moduleDiagram_isPositive d N hfdN),
    Diagram.toLocallyFiniteMatchingEquiv_cost _ _
      (moduleDiagram_isPositive c M hfd) (moduleDiagram_isPositive d N hfdN)⟩

/-- Finite and locally finite bottlenecks agree by canonical diagram identification.
The critical grids may differ and essential multiplicities may force infinite distance. -/
theorem ofQModule_bottleneck_eq_finite :
    (LocallyFiniteDecoratedDiagram.ofQModule (qTame_of_isConstructible c M hM hfd)).bottleneck
      (LocallyFiniteDecoratedDiagram.ofQModule (qTame_of_isConstructible d N hN hfdN)) =
      bottleneck (moduleDiagram c M hfd) (moduleDiagram d N hfdN) := by
  rw [ofQModule_eq_toLocallyFinite c M hM hfd,
    ofQModule_eq_toLocallyFinite d N hN hfdN]
  exact bottleneck_toLocallyFinite _ _ (moduleDiagram_isPositive c M hfd)
    (moduleDiagram_isPositive d N hfdN)

end TDA.Persistence.FiniteConstructible
