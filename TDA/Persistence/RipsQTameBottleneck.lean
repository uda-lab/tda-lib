import TDA.Persistence.LocallyFiniteDiagramBottleneck
import TDA.Persistence.RipsQTameFiniteCompatibility

/-!
# Finite Rips diagrams inside the q-tame bottleneck interface

For a finite metric space, the q-tame multiplicity from the actual Rips module
agrees with the occurrence count of the existing full finite diagram.  The
locally finite bottleneck therefore restricts to that finite diagram's existing
bottleneck.  No metric stability or sampling estimate is asserted here.
-/

universe u v

namespace TDA.Persistence.Rips

open TDA.Filtration TDA.Persistence.RectangleMeasure

noncomputable section

variable {X : Type u} [LinearOrder X] [MetricSpace X]

local instance : DecidableEq (Cut ℝ) := Classical.decEq _

private theorem count_decEq_irrel {α : Type*} (a : α) (s : Multiset α)
    [DecidableEq α] :
    @Multiset.count α (Classical.decEq α) a s = Multiset.count a s := by
  have hdec : Classical.decEq α = (inferInstance : DecidableEq α) := Subsingleton.elim _ _
  rw [hdec]

/-- The occurrence endpoint convention used by the generic decorated-diagram
embedding is definitionally the convention already used by the Rips API. -/
@[simp] theorem genericDiagramOccurrence_eq_diagramOccurrence
    (p : ℝ × WithTop ℝ) :
    TDA.Persistence.diagramDecoratedPoint p = diagramOccurrence p := rfl

/-- Canonical decorated diagram of the q-tame Rips module on a totally bounded
space. The finite consumer below instantiates total boundedness from finiteness. -/
noncomputable def qTameLocallyFiniteDiagram (k : Type v) [Field k]
    (hX : TotallyBounded (Set.univ : Set X)) (n : ℕ) :
    LocallyFiniteDecoratedDiagram :=
  LocallyFiniteDecoratedDiagram.ofQModule
    (M := sublevelModule k (Rips.filter (inferInstance : MetricSpace X)) n)
    (qTame_of_totallyBounded k hX n)

/-- The finite Rips q-tame multiplicity equals the embedded finite diagram's
decorated multiplicity pointwise. This uses the established finite compatibility
theorem and the definitional endpoint-convention bridge above. -/
theorem qTameLocallyFiniteDiagram_multiplicity_eq (k : Type u) [Field k]
    [Fintype X] (n : ℕ) (p : Cut ℝ × Cut ℝ) :
    (qTameLocallyFiniteDiagram k
      (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).multiplicity p =
      ((diagram k X n).toLocallyFinite (diagram_isPositive k X n)).multiplicity p := by
  have hleft :
      (qTameLocallyFiniteDiagram k
        (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).multiplicity p =
        qTameDiagramMultiplicity k
          (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n p := rfl
  have hright :
      ((diagram k X n).toLocallyFinite (diagram_isPositive k X n)).multiplicity p =
        ((diagram k X n).points.map TDA.Persistence.diagramDecoratedPoint).count p := by
    unfold Diagram.toLocallyFinite
    exact count_decEq_irrel p _
  have hmap : TDA.Persistence.diagramDecoratedPoint = diagramOccurrence := by
    funext q
    exact genericDiagramOccurrence_eq_diagramOccurrence q
  rw [hleft, hright]
  rw [hmap]
  exact qTameDiagramMultiplicity_eq_diagramOccurrenceCount (X := X) k n p

private theorem qTameLocallyFiniteDiagram_eq_finite (k : Type u) [Field k]
    [Fintype X] (n : ℕ) :
    qTameLocallyFiniteDiagram k
        (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n =
      (diagram k X n).toLocallyFinite (diagram_isPositive k X n) := by
  apply LocallyFiniteDecoratedDiagram.ext
  funext p
  exact qTameLocallyFiniteDiagram_multiplicity_eq k n p

/- Concrete finite consumer: the q-tame Rips bottleneck between finite metric
spaces is exactly the existing bottleneck between their full finite diagrams. -/
theorem qTameLocallyFiniteDiagram_bottleneck_eq_finite
    {X Y : Type u} [LinearOrder X] [MetricSpace X] [Fintype X]
    [LinearOrder Y] [MetricSpace Y] [Fintype Y]
    (k : Type u) [Field k] (n : ℕ) :
    (qTameLocallyFiniteDiagram (X := X) k
      (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set X)) n).bottleneck
      (qTameLocallyFiniteDiagram (X := Y) k
        (Set.finite_univ.totallyBounded : TotallyBounded (Set.univ : Set Y)) n) =
      bottleneck (diagram k X n) (diagram k Y n) := by
  rw [qTameLocallyFiniteDiagram_eq_finite (X := X) k n,
    qTameLocallyFiniteDiagram_eq_finite (X := Y) k n]
  exact bottleneck_toLocallyFinite (diagram k X n) (diagram k Y n)
    (diagram_isPositive k X n) (diagram_isPositive k Y n)

end
end TDA.Persistence.Rips
