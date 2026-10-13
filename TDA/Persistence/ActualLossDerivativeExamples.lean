import TDA.Persistence.ActualLossDerivative
import TDA.Persistence.DiagramCalculusExamples
import TDA.Persistence.SublevelDiagramExamples
import TDA.Simplicial.AttachmentExamples

/-! Concrete scalar losses and actual sublevel examples. -/

set_option autoImplicit false
universe u v

namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration

/-- Sum the real births of essential bars. Infinity is not a coordinate. -/
noncomputable def essentialBirthSum (D : Diagram ℝ) : ℝ :=
  (essentialPart D.points).sum

theorem essentialBirthSum_orderedQ (m n : ℕ) (z : DiagramCoordinates m n) :
    essentialBirthSum (orderedQ m n z) = ∑ i : Fin n, z.2 i := by
  classical
  rw [essentialBirthSum, essentialPart_orderedQ]
  simp [List.sum_ofFn]

/-- Essential birth sum is smooth through *every* ordered representative. -/
theorem essentialBirthSum_c1_all (D : Diagram ℝ) :
    C1ThroughAllRepresentatives essentialBirthSum D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, ?_⟩
  apply contDiffOn_univ.mpr
  have hs : ContDiff ℝ 1 (fun w : DiagramCoordinates m n => ∑ i : Fin n, w.2 i) := by
    apply ContDiff.sum
    intro i _
    fun_prop
  simpa [Function.comp_def, essentialBirthSum_orderedQ] using hs

/-- The actual degree-zero diagram of one moving vertex has essential-birth
loss equal to its simplex value. -/
theorem singleton_essential_loss (x : ℝ) :
    essentialBirthSum (dgm (ZMod 2) (Examples.singletonFilter x) 0) = x := by
  have hd : dgm (ZMod 2) (Examples.singletonFilter x) 0 =
      orderedQ 0 1 (Fin.elim0, fun _ => x) := by
    apply Diagram.ext
    rw [Examples.singleton_points]
    simp [orderedQ]
  rw [hd, essentialBirthSum_orderedQ]
  simp

/-- Consequently its genuine scalar derivative is `1`. -/
theorem singleton_essential_loss_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      essentialBirthSum (dgm (ZMod 2) (Examples.singletonFilter t) 0)) 1 x := by
  have hf : (fun t : ℝ =>
      essentialBirthSum (dgm (ZMod 2) (Examples.singletonFilter t) 0)) =
      (fun t : ℝ => t) := by
    funext t
    exact singleton_essential_loss t
  rw [hf]
  exact hasDerivAt_id x

/-- The sole actual face receives coefficient `+1` in the essential-birth
loss, for a compatible full-template presentation. -/
theorem singleton_essential_face_coefficient :
    ∃ e : CompatibleOrder (Examples.singletonFilter (0 : ℝ)),
      ∀ s : TotalFace (singletonFace (0 : Fin 2)),
        faceLossCoefficient (ZMod 2) Examples.singletonFilter e 0
          essentialBirthSum s = 1 := by
  let F : ℝ → FilterFunction (singletonFace (0 : Fin 2)) ℝ :=
    Examples.singletonFilter
  obtain ⟨e⟩ := exists_compatibleOrder (F 0)
  have hF : ∀ s : TotalFace (singletonFace (0 : Fin 2)),
      ContDiffOn ℝ 1 (fun x : ℝ => (F x).value s) Set.univ := by
    intro s
    change ContDiffOn ℝ 1 (fun x : ℝ => x) Set.univ
    exact contDiffOn_id
  have horder : ∀ x ∈ (Set.univ : Set ℝ),
      OrderingEquivalent (F 0) (F x) := by
    intro x _ s t
    simp [F, Examples.singletonFilter]
  have hm : Fintype.card (TotalFace (singletonFace (0 : Fin 2))) = 1 := by
    decide
  letI : Unique (TotalFace (singletonFace (0 : Fin 2))) :=
    Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hm)
  have hD := actualPHScalarLoss_fderiv (ZMod 2) F e 0
    isOpen_univ (Set.mem_univ (0 : ℝ)) hF horder
    essentialBirthSum (essentialBirthSum_c1_all _)
  have hf : (fun x : ℝ => essentialBirthSum (dgm (ZMod 2) (F x) 0)) =
      (fun x : ℝ => x) := by
    funext x
    exact singleton_essential_loss x
  rw [hf] at hD
  refine ⟨e, fun s => ?_⟩
  have hs := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) hD
  have hsd : s = default := Subsingleton.elim _ _
  subst s
  have hface : fderiv ℝ (fun x : ℝ => (F x).value default) 0 1 = 1 := by
    change fderiv ℝ (fun x : ℝ => x) 0 1 = 1
    simp
  simpa [F, Finset.sum_apply, smul_apply, hface] using hs.symm

/-- The linear expression underlying signed finite persistence, on the full
ordered coordinate space (including diagonal pairs). -/
noncomputable def signedCoordinateFunctional (m n : ℕ) :
    DiagramCoordinates m n →L[ℝ] ℝ :=
  let finiteBlock : DiagramCoordinates m n →L[ℝ] (Fin m → ℝ × ℝ) :=
    ContinuousLinearMap.fst ℝ _ _
  ∑ i : Fin m,
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.proj i).comp finiteBlock)) -
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.proj i).comp finiteBlock)))

theorem signedCoordinateFunctional_apply (m n : ℕ)
    (z : DiagramCoordinates m n) :
    signedCoordinateFunctional m n z =
      ∑ i : Fin m, ((z.1 i).2 - (z.1 i).1) := by
  simp [signedCoordinateFunctional, Finset.sum_apply]

theorem signedFiniteEndpointDifference_fderiv_full (m n : ℕ)
    (z : DiagramCoordinates m n) :
    fderiv ℝ (signedFiniteEndpointDifference ∘ orderedQ m n) z =
      signedCoordinateFunctional m n := by
  have hf : (signedFiniteEndpointDifference ∘ orderedQ m n) =
      signedCoordinateFunctional m n := by
    funext w
    rw [Function.comp_apply, signedFiniteEndpointDifference_orderedQ,
      signedCoordinateFunctional_apply]
  rw [hf]
  exact (signedCoordinateFunctional m n).hasFDerivAt.fderiv

/-- Birth and death weights stay nonzero even at a diagonal ordered pair. -/
theorem signed_finite_birth_slot_coefficient
    {V : Type u} [LinearOrder V] {K : PreAbstractSimplicialComplex V}
    [Fintype (TotalFace K)] (k : Type u) [Field k]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → FilterFunction K ℝ) {x₀ : E}
    (e : CompatibleOrder (F x₀)) (p : ℕ)
    (i : Fin (faceLiftCounts k F e p).1) :
    faceLossSlotCoefficient k F e p signedFiniteEndpointDifference (.inl (.inl i)) = -1 := by
  unfold faceLossSlotCoefficient
  rw [signedFiniteEndpointDifference_fderiv_full]
  rw [signedCoordinateFunctional_apply]
  rw [Finset.sum_eq_single i]
  · simp [faceLossUnit, faceLossSlotPack]
  · intro j _ hji
    simp [faceLossUnit, faceLossSlotPack, hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem signed_finite_death_slot_coefficient
    {V : Type u} [LinearOrder V] {K : PreAbstractSimplicialComplex V}
    [Fintype (TotalFace K)] (k : Type u) [Field k]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → FilterFunction K ℝ) {x₀ : E}
    (e : CompatibleOrder (F x₀)) (p : ℕ)
    (i : Fin (faceLiftCounts k F e p).1) :
    faceLossSlotCoefficient k F e p signedFiniteEndpointDifference (.inl (.inr i)) = 1 := by
  unfold faceLossSlotCoefficient
  rw [signedFiniteEndpointDifference_fderiv_full]
  rw [signedCoordinateFunctional_apply]
  rw [Finset.sum_eq_single i]
  · simp [faceLossUnit, faceLossSlotPack]
  · intro j _ hji
    simp [faceLossUnit, faceLossSlotPack, hji]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- In the actual tied edge family every full-template finite pair is diagonal.
The signed loss cancels identically, even though its ambient birth and death
weights are `-1` and `+1` by the preceding theorems. -/
theorem moving_tied_edge_signed_loss_zero (x : ℝ) :
    signedFiniteEndpointDifference
      (dgm (ZMod 2) (Examples.movingTiedEdgeFilter x) 0) = 0 := by
  obtain ⟨m, n, L, hL, _⟩ := Examples.moving_tied_edge_lift
  obtain ⟨hfactor, hdiag⟩ := hL x
  rw [hfactor, signedFiniteEndpointDifference_orderedQ]
  simp [hdiag]

theorem moving_tied_edge_signed_loss_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => signedFiniteEndpointDifference
      (dgm (ZMod 2) (Examples.movingTiedEdgeFilter t) 0)) 0 x := by
  have hf : (fun t : ℝ => signedFiniteEndpointDifference
      (dgm (ZMod 2) (Examples.movingTiedEdgeFilter t) 0)) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact moving_tied_edge_signed_loss_zero t
  rw [hf]
  exact hasDerivAt_const x 0

/-- For each retained finite pair of the actual tied-edge template, the two
nonzero ambient weights cancel after composition with equal face-value paths. -/
theorem moving_tied_edge_pair_contributions_cancel
    (e : CompatibleOrder (Examples.movingTiedEdgeFilter (0 : ℝ)))
    (i : Fin (faceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1) :
    faceLossSlotCoefficient (ZMod 2) Examples.movingTiedEdgeFilter e 0
        signedFiniteEndpointDifference (.inl (.inl i)) *
      fderiv ℝ (fun x : ℝ => (Examples.movingTiedEdgeFilter x).value
        (faceLossSlotFace (ZMod 2) Examples.movingTiedEdgeFilter e 0
          (.inl (.inl i)))) 0 1 +
    faceLossSlotCoefficient (ZMod 2) Examples.movingTiedEdgeFilter e 0
        signedFiniteEndpointDifference (.inl (.inr i)) *
      fderiv ℝ (fun x : ℝ => (Examples.movingTiedEdgeFilter x).value
        (faceLossSlotFace (ZMod 2) Examples.movingTiedEdgeFilter e 0
          (.inl (.inr i)))) 0 1 = 0 := by
  rw [signed_finite_birth_slot_coefficient,
    signed_finite_death_slot_coefficient]
  have hb : fderiv ℝ (fun x : ℝ => (Examples.movingTiedEdgeFilter x).value
      (faceLossSlotFace (ZMod 2) Examples.movingTiedEdgeFilter e 0
        (.inl (.inl i)))) 0 1 = 1 := by
    change fderiv ℝ (fun x : ℝ => x) 0 1 = 1
    simp
  have hd : fderiv ℝ (fun x : ℝ => (Examples.movingTiedEdgeFilter x).value
      (faceLossSlotFace (ZMod 2) Examples.movingTiedEdgeFilter e 0
        (.inl (.inr i)))) 0 1 = 1 := by
    change fderiv ℝ (fun x : ℝ => x) 0 1 = 1
    simp
  rw [hb, hd]
  norm_num

/-- A genuine retained finite pair exists in this tied actual filtration, with
both nonzero ambient weights and zero composed contribution. -/
theorem moving_tied_edge_nonvacuous_cancellation :
    ∃ (e : CompatibleOrder (Examples.movingTiedEdgeFilter (0 : ℝ)))
      (i : Fin (faceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1),
      faceLossSlotCoefficient (ZMod 2) Examples.movingTiedEdgeFilter e 0
        signedFiniteEndpointDifference (.inl (.inl i)) = -1 ∧
      faceLossSlotCoefficient (ZMod 2) Examples.movingTiedEdgeFilter e 0
        signedFiniteEndpointDifference (.inl (.inr i)) = 1 ∧
      faceLossSlotCoefficient (ZMod 2) Examples.movingTiedEdgeFilter e 0
          signedFiniteEndpointDifference (.inl (.inl i)) *
        fderiv ℝ (fun x : ℝ => (Examples.movingTiedEdgeFilter x).value
          (faceLossSlotFace (ZMod 2) Examples.movingTiedEdgeFilter e 0
            (.inl (.inl i)))) 0 1 +
      faceLossSlotCoefficient (ZMod 2) Examples.movingTiedEdgeFilter e 0
          signedFiniteEndpointDifference (.inl (.inr i)) *
        fderiv ℝ (fun x : ℝ => (Examples.movingTiedEdgeFilter x).value
          (faceLossSlotFace (ZMod 2) Examples.movingTiedEdgeFilter e 0
            (.inl (.inr i)))) 0 1 = 0 := by
  obtain ⟨e, hpos⟩ := Examples.moving_tied_edge_has_finite_slot
  let i : Fin (faceLiftCounts (ZMod 2) Examples.movingTiedEdgeFilter e 0).1 :=
    ⟨0, hpos⟩
  exact ⟨e, i, signed_finite_birth_slot_coefficient _ _ e 0 i,
    signed_finite_death_slot_coefficient _ _ e 0 i,
    moving_tied_edge_pair_contributions_cancel e i⟩

end TDA.Persistence
