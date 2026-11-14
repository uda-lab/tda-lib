import TDA.Persistence.FiniteDiagramQTame
import TDA.Persistence.RipsQTameDiagram
import TDA.Persistence.RipsGromovHausdorff
import TDA.Persistence.SublevelConstructible
import TDA.Persistence.SublevelDiagram

/-!
# Compatibility of finite Rips diagrams with the q-tame multiplicity

On a finite metric space, the decorated multiplicity constructed from the q-tame
Rips module agrees occurrence-by-occurrence with the existing finite Rips diagram.
Finite deaths use the closed diameter filtration's usual half-open bar endpoints;
essential occurrences remain on the actual death-at-infinity boundary.
-/

universe u v

namespace TDA.Persistence.Rips

open TDA.Filtration TDA.Persistence.RectangleMeasure
open scoped Classical

variable {X : Type u} [LinearOrder X] [MetricSpace X]

/-- The decorated endpoint of a finite Rips diagram occurrence. -/
noncomputable abbrev diagramOccurrence := diagramDecoratedPoint

@[simp] theorem diagramOccurrence_finite (b d : ℝ) :
    diagramOccurrence (b, (d : WithTop ℝ)) = (minusCut b, minusCut d) := rfl

@[simp] theorem diagramOccurrence_essential (b : ℝ) :
    diagramOccurrence (b, (⊤ : WithTop ℝ)) = (minusCut b, infinityCut) := rfl

/-- On a finite metric space, the canonical decorated multiplicity counts the
occurrences of its finite Rips diagram, including essential bars. -/
theorem qTameDiagramMultiplicity_eq_diagramOccurrenceCount
    (k : Type u) [Field k] [Fintype X] (n : ℕ) (p : Cut ℝ × Cut ℝ) :
    qTameDiagramMultiplicity k (Set.finite_univ.totallyBounded :
      TotallyBounded (Set.univ : Set X)) n p =
      ((diagram k X n).points.map diagramOccurrence).count p := by
  classical
  let f := Rips.filter (inferInstance : MetricSpace X)
  let M := sublevelModule k f n
  let hQ := qTame_of_totallyBounded (X := X) k Set.finite_univ.totallyBounded n
  apply FiniteDiagramQTame.moduleExtendedDiagramMultiplicity_eq_count M hQ
    (diagram k X n) _ (diagram_isPositive k X n) p
  intro s t hst
  convert rank_sublevelHomologyMap k f n s t hst using 1 <;>
    simp only [M, f, persistenceImage, structureMapLinear, sublevelModule,
      simplicialHomologyPModule_structureMap, diagram_eq_dgm k X n]; rfl

end TDA.Persistence.Rips
