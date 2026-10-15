import TDA.Persistence.DiagramCalculus

namespace TDA.Persistence

/-- Signed finite endpoint-difference sum. Essential points contribute zero.
Reversed finite pairs contribute negative values. -/
def signedFiniteEndpointDifference (D : Diagram ℝ) : ℝ :=
  (D.points.map fun p => match p.2 with
    | none => 0
    | some d => d - p.1).sum

/-- Sum of absolute finite endpoint differences. -/
def absoluteFiniteEndpointDifference (D : Diagram ℝ) : ℝ :=
  (D.points.map fun p => match p.2 with
    | none => 0
    | some d => |d - p.1|).sum

private theorem sum_filter_offDiagonal (f : ℝ × ℝ → ℝ)
    (hf : ∀ p, p.1 = p.2 → f p = 0) (l : List (ℝ × ℝ)) :
    ((l.filter fun p => p.1 ≠ p.2).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    by_cases hp : p.1 = p.2
    · simpa [hp, hf p hp] using ih
    · simpa [hp] using congrArg (fun a : ℝ => f p + a) ih

theorem signedFiniteEndpointDifference_orderedQ (m n : ℕ)
    (z : DiagramCoordinates m n) :
    signedFiniteEndpointDifference (orderedQ m n z) =
      ∑ i : Fin m, ((z.1 i).2 - (z.1 i).1) := by
  classical
  have h := sum_filter_offDiagonal (fun p : ℝ × ℝ => p.2 - p.1)
    (by intro p hp; simp [hp]) (List.ofFn z.1)
  simpa [signedFiniteEndpointDifference, orderedQ, List.sum_ofFn,
    Finset.sum_sub_distrib, Function.comp_def] using h

theorem absoluteFiniteEndpointDifference_orderedQ (m n : ℕ)
    (z : DiagramCoordinates m n) :
    absoluteFiniteEndpointDifference (orderedQ m n z) =
      ∑ i : Fin m, |(z.1 i).2 - (z.1 i).1| := by
  classical
  have h := sum_filter_offDiagonal (fun p : ℝ × ℝ => |p.2 - p.1|)
    (by intro p hp; simp [hp]) (List.ofFn z.1)
  simpa [absoluteFiniteEndpointDifference, orderedQ, List.sum_ofFn,
    Function.comp_def] using h

/-- The signed loss is `C¹` through every representative of every diagram,
including representatives with deleted diagonal pairs. -/
theorem signedFiniteEndpointDifference_c1_all (D : Diagram ℝ) :
    C1ThroughAllRepresentatives signedFiniteEndpointDifference D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
  apply contDiffOn_univ.mpr
  have hs : ContDiff ℝ 1 (fun w : DiagramCoordinates m n =>
      ∑ i : Fin m, ((w.1 i).2 - (w.1 i).1)) := by
    apply ContDiff.sum
    intro i _
    fun_prop
  simpa [Function.comp_def, signedFiniteEndpointDifference_orderedQ] using hs

/-- Any chosen ordered representative gives a constant smooth lift of the
constant diagram map, with the whole parameter space as its neighborhood. -/
def constantDiagramLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m n : ℕ) (z : DiagramCoordinates m n) :
    LocalDiagramLift (fun _ : E => orderedQ m n z) m n where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := fun _ => z
  factorization := by intro x hx; rfl
  smooth := contDiff_const.contDiffOn

/-- Every constant diagram-valued map has a constant ordered lift. -/
theorem constantDiagram_hasLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Diagram ℝ) :
    ∃ m n, Nonempty (LocalDiagramLift (fun _ : E => D) m n) := by
  obtain ⟨m, n, z, hz⟩ := orderedQ_surjective D
  subst D
  exact ⟨m, n, ⟨constantDiagramLift m n z⟩⟩

/-- The zero-coordinate presentation gives a constant lift of the empty diagram. -/
def emptyDiagramLift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LocalDiagramLift (fun _ : E => orderedQ 0 0 (Fin.elim0, Fin.elim0)) 0 0 :=
  constantDiagramLift 0 0 (Fin.elim0, Fin.elim0)

/-- An essential birth remains a variable even when the finite block is empty. -/
theorem essentialOnly_coordinates_vary :
    orderedQ 0 1 (Fin.elim0, fun _ => (0 : ℝ)) ≠
      orderedQ 0 1 (Fin.elim0, fun _ => (1 : ℝ)) := by
  intro h
  have hc := congrArg (fun D : Diagram ℝ => D.points.count (0, (⊤ : WithTop ℝ))) h
  simp [orderedQ_count_essential] at hc

/-- Finite endpoint coordinates remain variables when there are no essential points. -/
theorem finiteOnly_coordinates_vary :
    orderedQ 1 0 (fun _ => ((0 : ℝ), 1), Fin.elim0) ≠
      orderedQ 1 0 (fun _ => ((0 : ℝ), 2), Fin.elim0) := by
  intro h
  have hc := congrArg (fun D : Diagram ℝ =>
    D.points.count ((0 : ℝ), ((1 : ℝ) : WithTop ℝ))) h
  rw [orderedQ_count_finite 1 0 _ 0 1,
    orderedQ_count_finite 1 0 _ 0 1] at hc
  simp at hc

private def onePair (t : ℝ) : DiagramCoordinates 1 0 :=
  (fun _ => (0, t), Fin.elim0)

/-- For one finite pair, the signed loss has birth weight `-1` and death
weight `+1`, even if the pair is reversed or diagonal. -/
theorem signedFiniteEndpointDifference_onePair_fderiv (p : ℝ × ℝ) :
    fderiv ℝ
      (fun q : ℝ × ℝ => signedFiniteEndpointDifference
        (orderedQ 1 0 (fun _ => q, Fin.elim0))) p =
      (ContinuousLinearMap.snd ℝ ℝ ℝ) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
  have hfun : (fun q : ℝ × ℝ => signedFiniteEndpointDifference
        (orderedQ 1 0 (fun _ => q, Fin.elim0))) =
      (fun q => q.2 - q.1) := by
    funext q
    simp [signedFiniteEndpointDifference_orderedQ]
  rw [hfun]
  exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.sub
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).fderiv

private theorem onePair_zero_is_empty :
    orderedQ 1 0 (onePair 0) = orderedQ 0 0 (Fin.elim0, Fin.elim0) := by
  apply Diagram.ext
  simp [orderedQ, onePair]

/-- The absolute loss fails the all-presentations condition at the empty
diagram.  The one-pair diagonal presentation exposes `|t|`. -/
theorem absoluteFiniteEndpointDifference_not_c1_empty :
    ¬ C1ThroughAllRepresentatives absoluteFiniteEndpointDifference
        (orderedQ 0 0 (Fin.elim0, Fin.elim0)) := by
  intro h
  obtain ⟨W, hWopen, hzW, hW⟩ := h 1 0 (onePair 0) onePair_zero_is_empty
  have hg : DifferentiableAt ℝ
      (absoluteFiniteEndpointDifference ∘ orderedQ 1 0) (onePair 0) :=
    (hW.contDiffAt (hWopen.mem_nhds hzW)).differentiableAt_one
  have hc : DifferentiableAt ℝ onePair 0 := by
    unfold onePair
    fun_prop
  have hcurve := hg.comp 0 hc
  apply not_differentiableAt_abs_zero
  simpa [Function.comp_def, absoluteFiniteEndpointDifference_orderedQ,
    onePair] using hcurve

end TDA.Persistence
