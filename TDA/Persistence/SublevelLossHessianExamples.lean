import TDA.Persistence.DiagramSecondOrderCalculus
import TDA.Persistence.SublevelLossDerivativeExamples

/-! Nonlinear losses, persistent diagonal cancellation, and presentation changes. -/

set_option autoImplicit false
universe u v

namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration

/-- Square of the total real essential birth. -/
noncomputable def squaredEssentialBirthSum (D : Diagram ℝ) : ℝ :=
  (essentialBirthSum D) ^ 2

/-- Square of signed finite endpoint differences; reversed and diagonal pairs
are included in the ambient coordinate polynomial. -/
def squaredSignedFiniteEndpointDifference (D : Diagram ℝ) : ℝ :=
  (signedFiniteEndpointDifference D) ^ 2

theorem squaredEssentialBirthSum_orderedQ (m n : ℕ) (z : DiagramCoordinates m n) :
    squaredEssentialBirthSum (orderedQ m n z) = (∑ i : Fin n, z.2 i) ^ 2 := by
  rw [squaredEssentialBirthSum, essentialBirthSum_orderedQ]

theorem squaredSignedFiniteEndpointDifference_orderedQ (m n : ℕ)
    (z : DiagramCoordinates m n) :
    squaredSignedFiniteEndpointDifference (orderedQ m n z) =
      (∑ i : Fin m, ((z.1 i).2 - (z.1 i).1)) ^ 2 := by
  rw [squaredSignedFiniteEndpointDifference, signedFiniteEndpointDifference_orderedQ]

/-- Essential birth sum as a continuous linear functional. -/
noncomputable def essentialBirthFunctional (m n : ℕ) :
    DiagramCoordinates m n →L[ℝ] ℝ :=
  ∑ i : Fin n, (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)

theorem essentialBirthFunctional_apply (m n : ℕ) (z : DiagramCoordinates m n) :
    essentialBirthFunctional m n z = ∑ i : Fin n, z.2 i := by
  simp [essentialBirthFunctional, Finset.sum_apply]

/-- Squaring a real linear functional has a genuine first derivative. -/
theorem squareLinear_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] ℝ) (z : E) :
    HasFDerivAt (fun w => (A w) ^ 2) ((2 * A z) • A) z := by
  simpa using A.hasFDerivAt.pow 2

theorem squareLinear_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] ℝ) (z : E) :
    fderiv ℝ (fun w => (A w) ^ 2) z = (2 * A z) • A :=
  (squareLinear_hasFDerivAt A z).fderiv

/-- The derivative of the derivative exists even when the linear functional
vanishes at the base point. -/
theorem squareLinear_hasFDerivAt_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] ℝ) (z : E) :
    HasFDerivAt (fun w => fderiv ℝ (fun q => (A q) ^ 2) w)
      (((2 : ℝ) • A).smulRight A) z := by
  simp_rw [squareLinear_fderiv]
  exact (A.hasFDerivAt.const_mul 2).smul_const A

theorem squareLinear_secondFDeriv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] ℝ) (z h k : E) :
    fderiv ℝ (fun w => fderiv ℝ (fun q => (A q) ^ 2) w) z h k =
      2 * A h * A k := by
  rw [(squareLinear_hasFDerivAt_fderiv A z).fderiv]
  simp [ContinuousLinearMap.smulRight_apply, mul_assoc]

theorem squaredSignedFiniteEndpointDifference_hasFDerivAt (m n : ℕ)
    (z : DiagramCoordinates m n) :
    HasFDerivAt (squaredSignedFiniteEndpointDifference ∘ orderedQ m n)
      ((2 * signedCoordinateFunctional m n z) • signedCoordinateFunctional m n) z := by
  simpa [Function.comp_def, squaredSignedFiniteEndpointDifference_orderedQ,
    signedCoordinateFunctional_apply] using squareLinear_hasFDerivAt
      (signedCoordinateFunctional m n) z

theorem squaredSignedFiniteEndpointDifference_secondFDeriv_apply (m n : ℕ)
    (z h k : DiagramCoordinates m n) :
    fderiv ℝ (fun w => fderiv ℝ
      (squaredSignedFiniteEndpointDifference ∘ orderedQ m n) w) z h k =
      2 * signedCoordinateFunctional m n h * signedCoordinateFunctional m n k := by
  have hf : (squaredSignedFiniteEndpointDifference ∘ orderedQ m n) =
      (fun w => (signedCoordinateFunctional m n w) ^ 2) := by
    funext w
    simp [Function.comp_def, squaredSignedFiniteEndpointDifference_orderedQ,
      signedCoordinateFunctional_apply]
  rw [hf]
  exact squareLinear_secondFDeriv_apply _ _ _ _

/-- Global coordinate polynomials establish C² at every representative,
including added diagonal pairs and reversed pairs. -/
theorem essentialBirthSum_c2_all (D : Diagram ℝ) :
    C2ThroughAllRepresentatives essentialBirthSum D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, contDiffOn_univ.mpr ?_⟩
  have hf : (essentialBirthSum ∘ orderedQ m n) = essentialBirthFunctional m n := by
    funext w
    rw [Function.comp_apply, essentialBirthSum_orderedQ, essentialBirthFunctional_apply]
  rw [hf]
  exact (essentialBirthFunctional m n).contDiff

theorem squaredEssentialBirthSum_c2_all (D : Diagram ℝ) :
    C2ThroughAllRepresentatives squaredEssentialBirthSum D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, contDiffOn_univ.mpr ?_⟩
  have hs : ContDiff ℝ 2 (fun w : DiagramCoordinates m n => ∑ i : Fin n, w.2 i) := by
    apply ContDiff.sum
    intro i _
    fun_prop
  simpa [Function.comp_def, squaredEssentialBirthSum_orderedQ] using hs.pow 2

theorem signedFiniteEndpointDifference_c2_all (D : Diagram ℝ) :
    C2ThroughAllRepresentatives signedFiniteEndpointDifference D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, contDiffOn_univ.mpr ?_⟩
  have hf : (signedFiniteEndpointDifference ∘ orderedQ m n) = signedCoordinateFunctional m n := by
    funext w
    rw [Function.comp_apply, signedFiniteEndpointDifference_orderedQ,
      signedCoordinateFunctional_apply]
  rw [hf]
  exact (signedCoordinateFunctional m n).contDiff

theorem squaredSignedFiniteEndpointDifference_c2_all (D : Diagram ℝ) :
    C2ThroughAllRepresentatives squaredSignedFiniteEndpointDifference D := by
  intro m n z _
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ z, contDiffOn_univ.mpr ?_⟩
  simpa [Function.comp_def, squaredSignedFiniteEndpointDifference_orderedQ,
    signedCoordinateFunctional_apply] using (signedCoordinateFunctional m n).contDiff.pow 2

/-- The genuine derivative of a quadratic curve valued in any real normed space. -/
theorem quadraticCurve_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ →L[ℝ] E) (x : ℝ) :
    fderiv ℝ (fun t : ℝ => R (t ^ 2)) x = (2 * x) • R := by
  have hq := squareLinear_hasFDerivAt (ContinuousLinearMap.id ℝ ℝ) x
  have hc := R.hasFDerivAt.comp x hq
  simpa [ContinuousLinearMap.comp_smul, Function.comp_def] using hc.fderiv

theorem quadraticCurve_secondFDeriv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ →L[ℝ] E) (x h k : ℝ) :
    fderiv ℝ (fderiv ℝ (fun t : ℝ => R (t ^ 2))) x h k = R (2 * h * k) := by
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => t ^ 2) x := by fun_prop
  rw [secondDerivative_linear_postcomp R (fun t : ℝ => t ^ 2) x hc]
  change R (fderiv ℝ (fderiv ℝ (fun t : ℝ => t ^ 2)) x h k) = _
  exact congrArg R (squareLinear_secondFDeriv_apply (ContinuousLinearMap.id ℝ ℝ) x h k)

/-- The nonlinear singleton family has face value `t²`. -/
def nonlinearSingletonFilter (t : ℝ) := Examples.singletonFilter (t ^ 2)

theorem nonlinear_singleton_scalar_loss (t : ℝ) :
    squaredEssentialBirthSum (dgm (ZMod 2) (nonlinearSingletonFilter t) 0) = t ^ 4 := by
  rw [squaredEssentialBirthSum, nonlinearSingletonFilter, singleton_essential_loss]
  ring

noncomputable def singletonBirthLinear : ℝ →L[ℝ] DiagramCoordinates 0 1 :=
  (0 : ℝ →L[ℝ] (Fin 0 → ℝ × ℝ)).prod
    (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)

theorem singletonBirthLinear_apply (t : ℝ) :
    singletonBirthLinear t = (Fin.elim0, fun _ => t) := by
  apply Prod.ext
  · funext i
    exact Fin.elim0 i
  · ext i
    simp [singletonBirthLinear]

/-- A nonlinear singleton lift, with no finite pairs. -/
noncomputable def nonlinearSingletonLift :
    LocalC2DiagramLift (fun t : ℝ => dgm (ZMod 2) (nonlinearSingletonFilter t) 0) 0 1 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := fun t => singletonBirthLinear (t ^ 2)
  factorization := by
    intro t _
    apply Diagram.ext
    rw [nonlinearSingletonFilter, Examples.singleton_points, singletonBirthLinear_apply]
    simp [orderedQ]
  smooth := by fun_prop
  smooth_two := by fun_prop

/-- Both terms of the ordinary chain expression are needed in this family:
the coordinate Hessian gives `8` and parametrization curvature gives `4`. -/
theorem nonlinear_singleton_chain_terms :
    fderiv ℝ (fderiv ℝ (squaredEssentialBirthSum ∘ orderedQ 0 1))
        (nonlinearSingletonLift.coordinates 1)
        (fderiv ℝ nonlinearSingletonLift.coordinates 1 1)
        (fderiv ℝ nonlinearSingletonLift.coordinates 1 1) = 8 ∧
    fderiv ℝ (squaredEssentialBirthSum ∘ orderedQ 0 1)
        (nonlinearSingletonLift.coordinates 1)
        (fderiv ℝ (fderiv ℝ nonlinearSingletonLift.coordinates) 1 1 1) = 4 := by
  have hf : (squaredEssentialBirthSum ∘ orderedQ 0 1) =
      (fun w => (essentialBirthFunctional 0 1 w) ^ 2) := by
    funext w
    simp [Function.comp_def, squaredEssentialBirthSum_orderedQ, essentialBirthFunctional_apply]
  have h1 := quadraticCurve_fderiv singletonBirthLinear 1
  have h2 := quadraticCurve_secondFDeriv_apply singletonBirthLinear 1 1 1
  change fderiv ℝ (fderiv ℝ (squaredEssentialBirthSum ∘ orderedQ 0 1))
      (singletonBirthLinear (1 ^ 2))
      (fderiv ℝ (fun t => singletonBirthLinear (t ^ 2)) 1 1)
      (fderiv ℝ (fun t => singletonBirthLinear (t ^ 2)) 1 1) = 8 ∧
    fderiv ℝ (squaredEssentialBirthSum ∘ orderedQ 0 1)
      (singletonBirthLinear (1 ^ 2))
      (fderiv ℝ (fderiv ℝ (fun t => singletonBirthLinear (t ^ 2))) 1 1 1) = 4
  rw [hf, h1, h2, squareLinear_secondFDeriv_apply, squareLinear_fderiv]
  norm_num [essentialBirthFunctional_apply, singletonBirthLinear_apply]

/-- This is the second derivative of the diagram scalar loss, identified
through the general second-order theorem rather than a detached polynomial computation. -/
theorem nonlinear_singleton_second_derivative :
    fderiv ℝ (fderiv ℝ (squaredEssentialBirthSum ∘
      (fun t : ℝ => dgm (ZMod 2) (nonlinearSingletonFilter t) 0))) 1 1 1 = 12 := by
  rw [localLift_scalar_second_fderiv _ _ 0 1 nonlinearSingletonLift 1
    (Set.mem_univ _) (squaredEssentialBirthSum_c2_all _), secondDerivativeChain_apply]
  rw [nonlinear_singleton_chain_terms.1, nonlinear_singleton_chain_terms.2]
  norm_num

/-- A nonlinear tied edge retains every full-template pair even though the diagram
removes their diagonal evaluations. -/
def nonlinearTiedEdgeFilter (t : ℝ) := Examples.movingTiedEdgeFilter (t ^ 2)

theorem nonlinear_tied_edge_signed_loss_zero (t : ℝ) :
    signedFiniteEndpointDifference (dgm (ZMod 2) (nonlinearTiedEdgeFilter t) 0) = 0 :=
  moving_tied_edge_signed_loss_zero (t ^ 2)

theorem nonlinear_tied_edge_squared_loss_zero (t : ℝ) :
    squaredSignedFiniteEndpointDifference (dgm (ZMod 2) (nonlinearTiedEdgeFilter t) 0) = 0 := by
  rw [squaredSignedFiniteEndpointDifference, nonlinear_tied_edge_signed_loss_zero]
  norm_num

/-- Nonzero linear endpoint coefficients cancel against the equal, nonzero face
second derivatives of the quadratic tied-edge family. -/
theorem nonlinear_tied_edge_pair_curvature_cancel
    (e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ)))
    (i : Fin (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1) :
    faceLossSlotCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
      signedFiniteEndpointDifference (.inl (.inl i)) = -1 ∧
    faceLossSlotCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
      signedFiniteEndpointDifference (.inl (.inr i)) = 1 ∧
    faceLossSlotCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
        signedFiniteEndpointDifference (.inl (.inl i)) *
      fderiv ℝ (fderiv ℝ (fun t : ℝ => (nonlinearTiedEdgeFilter t).value
        (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i))))) 1 1 1 +
    faceLossSlotCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
        signedFiniteEndpointDifference (.inl (.inr i)) *
      fderiv ℝ (fderiv ℝ (fun t : ℝ => (nonlinearTiedEdgeFilter t).value
        (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inr i))))) 1 1 1 = 0 := by
  rw [signed_finite_birth_slot_coefficient, signed_finite_death_slot_coefficient]
  change -1 = -1 ∧ 1 = 1 ∧
    -1 * fderiv ℝ (fderiv ℝ (fun t : ℝ => t ^ 2)) 1 1 1 +
      1 * fderiv ℝ (fderiv ℝ (fun t : ℝ => t ^ 2)) 1 1 1 = 0
  rw [show (fun t : ℝ => t ^ 2) =
    (fun t => (ContinuousLinearMap.id ℝ ℝ t) ^ 2) from rfl,
    squareLinear_secondFDeriv_apply]
  norm_num

/-- The quadratic tied edge has a genuinely nonempty finite template block. -/
theorem nonlinear_tied_edge_has_finite_slot :
    ∃ e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ)),
      0 < (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1 := by
  obtain ⟨e₀, hpos⟩ := Examples.moving_tied_edge_has_finite_slot
  let e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ)) :=
    e₀.transfer (by intro i j _; change (0 : ℝ) ^ 2 ≤ 0 ^ 2; exact le_rfl)
  refine ⟨e, ?_⟩
  change 0 < (faceTemplatePairs (ZMod 2) e 0).toList.length
  have heq : faceTemplatePairs (ZMod 2) e 0 = faceTemplatePairs (ZMod 2) e₀ 0 :=
    faceTemplatePairs_transfer (ZMod 2) e₀ (nonlinearTiedEdgeFilter 0)
      (by intro i j _; change (0 : ℝ) ^ 2 ≤ 0 ^ 2; exact le_rfl) 0
  rw [heq]
  exact hpos

/-- The full tied coordinate curve retains all finite and essential coordinates. -/
noncomputable def tiedFullLinear (m n : ℕ) : ℝ →L[ℝ] DiagramCoordinates m n :=
  (ContinuousLinearMap.pi fun _ : Fin m =>
      (ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)).prod
    (ContinuousLinearMap.pi fun _ : Fin n => ContinuousLinearMap.id ℝ ℝ)

theorem tiedFullLinear_apply (m n : ℕ) (t : ℝ) :
    tiedFullLinear m n t = (fun _ => (t, t), fun _ => t) := by
  ext i <;> simp [tiedFullLinear]

theorem nonlinear_tied_edge_fixed_lift
    (e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ))) (t : ℝ) :
    fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 t =
      tiedFullLinear (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
        (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2 (t ^ 2) := by
  rw [tiedFullLinear_apply]
  rfl

noncomputable def nonlinearTiedEdgeLift
    (e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ))) :
    LocalC2DiagramLift (fun t : ℝ => dgm (ZMod 2) (nonlinearTiedEdgeFilter t) 0)
      (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
      (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2 where
  carrier := Set.univ
  isOpen_carrier := isOpen_univ
  coordinates := fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0
  factorization := fixedFaceLift_factorization (ZMod 2) nonlinearTiedEdgeFilter e 0
    (fun _ _ _ _ => by simp [nonlinearTiedEdgeFilter, Examples.movingTiedEdgeFilter])
  smooth := by
    have hf : fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 =
        fun t => tiedFullLinear (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
          (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2 (t ^ 2) :=
      funext (nonlinear_tied_edge_fixed_lift e)
    rw [hf]
    fun_prop
  smooth_two := by
    have hf : fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 =
        fun t => tiedFullLinear (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
          (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2 (t ^ 2) :=
      funext (nonlinear_tied_edge_fixed_lift e)
    rw [hf]
    fun_prop

/-- The ambient Hessian at a retained birth direction equals `2`, including at
a diagonal evaluation. -/
theorem nonlinear_tied_edge_ambient_birth_hessian
    (e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ)))
    (i : Fin (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1) :
    fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      orderedQ (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
        (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2))
      (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 0)
      (faceLossUnit (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i)))
      (faceLossUnit (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i))) = 2 := by
  rw [squaredSignedFiniteEndpointDifference_secondFDeriv_apply]
  have ha : signedCoordinateFunctional _ _
      (faceLossUnit (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i))) = -1 := by
    rw [signedCoordinateFunctional_apply, Finset.sum_eq_single i]
    · simp [faceLossUnit, faceLossSlotPack]
    · intro j _ hji
      simp [faceLossUnit, faceLossSlotPack, hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [ha]
  norm_num

/-- Equal endpoint derivatives annihilate the nonzero ambient squared-loss Hessian. -/
theorem nonlinear_tied_edge_hessian_pullback_zero
    (e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ))) (t h k : ℝ) :
    fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      orderedQ (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
        (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2))
      (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 t)
      (fderiv ℝ (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0) t h)
      (fderiv ℝ (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0) t k) = 0 := by
  have hf : fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 =
      fun t => tiedFullLinear (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
        (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2 (t ^ 2) :=
    funext (nonlinear_tied_edge_fixed_lift e)
  rw [squaredSignedFiniteEndpointDifference_secondFDeriv_apply, hf, quadraticCurve_fderiv]
  simp [signedCoordinateFunctional_apply, tiedFullLinear_apply]

/-- The scalar squared loss has a genuine zero second derivative on the tied edge. -/
theorem nonlinear_tied_edge_squared_second_derivative (t : ℝ) :
    HasFDerivAt (𝕜 := ℝ) (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      (fun x : ℝ => dgm (ZMod 2) (nonlinearTiedEdgeFilter x) 0))) 0 t := by
  have hf : (squaredSignedFiniteEndpointDifference ∘
      (fun x : ℝ => dgm (ZMod 2) (nonlinearTiedEdgeFilter x) 0)) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext x
    exact nonlinear_tied_edge_squared_loss_zero x
  rw [hf]
  have hdf : fderiv ℝ (fun _ : ℝ => (0 : ℝ)) =
      (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) := by
    funext x
    exact fderiv_const_apply (𝕜 := ℝ) 0
  rw [hdf]
  exact hasFDerivAt_const _ _

/-- The retained birth and death faces have nonzero existing β coefficients,
and their face-curvature contributions cancel. -/
theorem nonlinear_tied_edge_face_curvature_cancel
    (e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ)))
    (i : Fin (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1) :
    faceLossCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
      signedFiniteEndpointDifference
      (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i))) = -1 ∧
    faceLossCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
      signedFiniteEndpointDifference
      (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inr i))) = 1 ∧
    faceLossCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
        signedFiniteEndpointDifference
        (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i))) *
      fderiv ℝ (fderiv ℝ (fun t : ℝ => (nonlinearTiedEdgeFilter t).value
        (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i))))) 1 1 1 +
    faceLossCoefficient (ZMod 2) nonlinearTiedEdgeFilter e 0
        signedFiniteEndpointDifference
        (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inr i))) *
      fderiv ℝ (fderiv ℝ (fun t : ℝ => (nonlinearTiedEdgeFilter t).value
        (faceLossSlotFace (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inr i))))) 1 1 1 = 0 := by
  simp_rw [faceLossCoefficient_selected]
  exact nonlinear_tied_edge_pair_curvature_cancel e i

/-- Nonempty template coordinates witness a nonzero ambient Hessian whose
pullback along the persistently diagonal quadratic family is zero. -/
theorem nonlinear_tied_edge_nonvacuous_hessian_cancellation :
    ∃ (e : CompatibleOrder (nonlinearTiedEdgeFilter (0 : ℝ)))
      (i : Fin (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1),
    fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      orderedQ (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
        (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2))
      (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 0)
      (faceLossUnit (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i)))
      (faceLossUnit (ZMod 2) nonlinearTiedEdgeFilter e 0 (.inl (.inl i))) = 2 ∧
    fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      orderedQ (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1
        (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).2))
      (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0 1)
      (fderiv ℝ (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0) 1 1)
      (fderiv ℝ (fixedFaceLift (ZMod 2) nonlinearTiedEdgeFilter e 0) 1 1) = 0 := by
  obtain ⟨e, hpos⟩ := nonlinear_tied_edge_has_finite_slot
  let i : Fin (faceLiftCounts (ZMod 2) nonlinearTiedEdgeFilter e 0).1 := ⟨0, hpos⟩
  exact ⟨e, i, nonlinear_tied_edge_ambient_birth_hessian e i,
    nonlinear_tied_edge_hessian_pullback_zero e 1 1 1⟩

/-- The signed scalar loss also has a genuine zero second derivative. -/
theorem nonlinear_tied_edge_signed_second_derivative (t : ℝ) :
    HasFDerivAt (𝕜 := ℝ) (fderiv ℝ (signedFiniteEndpointDifference ∘
      (fun x : ℝ => dgm (ZMod 2) (nonlinearTiedEdgeFilter x) 0))) 0 t := by
  have hf : (signedFiniteEndpointDifference ∘
      (fun x : ℝ => dgm (ZMod 2) (nonlinearTiedEdgeFilter x) 0)) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext x
    exact nonlinear_tied_edge_signed_loss_zero x
  rw [hf]
  have hdf : fderiv ℝ (fun _ : ℝ => (0 : ℝ)) =
      (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ)) := by
    funext x
    exact fderiv_const_apply (𝕜 := ℝ) 0
  rw [hdf]
  exact hasFDerivAt_const _ _

end TDA.Persistence
