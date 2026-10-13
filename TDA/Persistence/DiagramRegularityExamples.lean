import TDA.Persistence.DiagramRegularity
import TDA.Persistence.DiagramCalculusExamples

/-! Boundary cases for uniform regularity and diagonal restrictions. -/

namespace TDA.Persistence
open scoped ContDiff

/-- The signed endpoint loss is regular through every finite presentation at
every order, including zero, finite orders, and the smooth index `∞`. -/
theorem signedFiniteEndpointDifference_cr_all (r : ℕ∞ω) (D : Diagram ℝ) :
    CrThroughAllRepresentatives r signedFiniteEndpointDifference D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
  apply contDiffOn_univ.mpr
  have hs : ContDiff ℝ r (fun w : DiagramCoordinates m n =>
      ∑ i : Fin m, ((w.1 i).2 - (w.1 i).1)) := by
    apply ContDiff.sum
    intro i _
    fun_prop
  simpa [Function.comp_def, signedFiniteEndpointDifference_orderedQ] using hs

/-- The zero-dimensional ordered coordinate space has a constant lift at
every regularity index. -/
def emptyDiagramCrLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ∞ω) :
    LocalCrDiagramLift r (fun _ : E => orderedQ 0 0 (Fin.elim0, Fin.elim0)) 0 0 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := fun _ => (Fin.elim0, Fin.elim0)
  factorization := by intro _ _; rfl
  regular := contDiff_const.contDiffOn

/-- Two essential coordinates may have the same moving real birth value;
the finite block is empty. -/
def repeatedEssentialCoordinates (t : ℝ) : DiagramCoordinates 0 2 :=
  (Fin.elim0, fun _ => t)

theorem repeatedEssentialCoordinates_contDiff (r : ℕ∞ω) :
    ContDiff ℝ r repeatedEssentialCoordinates := by
  apply ContDiff.prodMk
  · exact contDiff_const
  · apply contDiff_pi.mpr
    intro i
    exact contDiff_id

theorem repeatedEssentialCoordinates_equal_births (t : ℝ) :
    (repeatedEssentialCoordinates t).2 0 =
      (repeatedEssentialCoordinates t).2 1 := rfl

/-- At order zero the scalar conclusion gives continuity, with no derivative
claim, even for an empty coordinate block. -/
theorem emptyDiagram_scalar_continuous (V : Diagram ℝ → ℝ) (x : ℝ)
    (hV : CrThroughAllRepresentatives 0 V
      (orderedQ 0 0 (Fin.elim0, Fin.elim0))) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      ContinuousOn (fun _ : ℝ => V (orderedQ 0 0 (Fin.elim0, Fin.elim0))) U := by
  obtain ⟨U, hU, hx, _, hc⟩ := localLift_scalar_continuousOn
    (fun _ : ℝ => orderedQ 0 0 (Fin.elim0, Fin.elim0)) V 0 0
    (emptyDiagramCrLift 0) x (Set.mem_univ x) hV
  exact ⟨U, hU, hx, hc⟩

/-- The absolute endpoint loss restricts to the constant zero function on
a diagonal coordinate line. -/
theorem absoluteLoss_diagonal_restriction (t : ℝ) :
    absoluteFiniteEndpointDifference
      (orderedQ 1 0 (diagonalInsertion 0 1 0
        ((Fin.elim0, Fin.elim0), fun _ => t))) = 0 := by
  have h : orderedQ 1 0 (diagonalInsertion 0 1 0
      ((Fin.elim0, Fin.elim0), fun _ => t)) =
      orderedQ 0 0 (Fin.elim0, Fin.elim0) := by
    simpa using orderedQ_diagonalInsertion 0 1 0
      ((Fin.elim0, Fin.elim0), fun _ => t)
  rw [h]
  simp [absoluteFiniteEndpointDifference_orderedQ]

/-- Smoothness of that restriction does not certify `C¹` on an ambient
neighborhood of the diagonal representative. -/
theorem absoluteLoss_diagonal_not_ambient_c1 :
    (ContDiff ℝ (∞ : ℕ∞ω) (fun t : ℝ =>
      absoluteFiniteEndpointDifference
        (orderedQ 1 0 (diagonalInsertion 0 1 0
          ((Fin.elim0, Fin.elim0), fun _ => t))))) ∧
      ¬ CrThroughAllRepresentatives 1 absoluteFiniteEndpointDifference
        (orderedQ 0 0 (Fin.elim0, Fin.elim0)) := by
  constructor
  · have h : (fun t : ℝ => absoluteFiniteEndpointDifference
        (orderedQ 1 0 (diagonalInsertion 0 1 0
          ((Fin.elim0, Fin.elim0), fun _ => t)))) = fun _ => 0 := by
      funext t
      exact absoluteLoss_diagonal_restriction t
    rw [h]
    exact contDiff_const
  · exact absoluteFiniteEndpointDifference_not_c1_empty

end TDA.Persistence
