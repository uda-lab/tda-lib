import TDA.Persistence.SublevelLossHessian
import TDA.Persistence.SublevelLossHessianExamples

/-! The nonlinear singleton fixture exercises the face-scattered Hessian,
including its separate gradient and curvature sums. -/

set_option autoImplicit false

namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration

noncomputable section

local instance : Unique (TotalFace (singletonFace (0 : Fin 2))) :=
  Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp (by decide))

private theorem singleton_squared_face_smooth
    (s : TotalFace (singletonFace (0 : Fin 2))) :
    ContDiffOn ℝ 2 (fun t : ℝ => (nonlinearSingletonFilter t).value s) Set.univ := by
  change ContDiffOn ℝ 2 (fun t : ℝ => t ^ 2) Set.univ
  fun_prop

private theorem singleton_squared_ordering (t : ℝ) (_ : t ∈ (Set.univ : Set ℝ)) :
    OrderingEquivalent (nonlinearSingletonFilter 1) (nonlinearSingletonFilter t) := by
  intro s r
  simp [nonlinearSingletonFilter, Examples.singletonFilter]

private theorem singleton_squared_face_first
    (s : TotalFace (singletonFace (0 : Fin 2))) :
    fderiv ℝ (fun t : ℝ => (nonlinearSingletonFilter t).value s) 1 1 = 2 := by
  change fderiv ℝ (fun t : ℝ => (ContinuousLinearMap.id ℝ ℝ t) ^ 2) 1 1 = 2
  rw [squareLinear_fderiv]
  norm_num

private theorem singleton_squared_face_second
    (s : TotalFace (singletonFace (0 : Fin 2))) :
    fderiv ℝ (fderiv ℝ (fun t : ℝ => (nonlinearSingletonFilter t).value s)) 1 1 1 = 2 := by
  change fderiv ℝ (fderiv ℝ (fun t : ℝ => (ContinuousLinearMap.id ℝ ℝ t) ^ 2)) 1 1 1 = 2
  rw [squareLinear_secondFDeriv_apply]
  norm_num

/-- The existing first-order coefficient and the scattered second-order coefficient
are both `2` at `t = 1`, for any compatible order of the singleton. -/
theorem nonlinear_singleton_face_coefficients
    (e : CompatibleOrder (nonlinearSingletonFilter (1 : ℝ)))
    (s r : TotalFace (singletonFace (0 : Fin 2))) :
    faceLossCoefficient (ZMod 2) nonlinearSingletonFilter e 0 squaredEssentialBirthSum s = 2 ∧
    faceLossHessianCoefficient (ZMod 2) nonlinearSingletonFilter e 0
      squaredEssentialBirthSum s r = 2 := by
  have hD := sublevelDiagramScalarLoss_c2_fderiv (ZMod 2) nonlinearSingletonFilter e 0
    isOpen_univ (Set.mem_univ (1 : ℝ)) singleton_squared_face_smooth
    singleton_squared_ordering squaredEssentialBirthSum (squaredEssentialBirthSum_c2_all _)
  have hf : (fun t : ℝ => squaredEssentialBirthSum
      (dgm (ZMod 2) (nonlinearSingletonFilter t) 0)) = (fun t : ℝ => t ^ 4) :=
    funext nonlinear_singleton_scalar_loss
  rw [hf] at hD
  have hp : HasFDerivAt (fun t : ℝ => t ^ 4)
      ((4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1 := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) (1 : ℝ)).pow 4
  rw [hp.fderiv] at hD
  have hfirst : 4 = faceLossCoefficient (ZMod 2) nonlinearSingletonFilter e 0
      squaredEssentialBirthSum default * 2 := by
    simpa only [Finset.univ_unique, Finset.sum_singleton, smul_apply,
      smul_eq_mul, ContinuousLinearMap.id_apply, singleton_squared_face_first, mul_one] using
      congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) hD
  have hb : faceLossCoefficient (ZMod 2) nonlinearSingletonFilter e 0
      squaredEssentialBirthSum default = 2 := by linarith
  have hH := sublevelDiagramScalarLoss_second_fderiv (ZMod 2) nonlinearSingletonFilter e 0
    isOpen_univ (Set.mem_univ (1 : ℝ)) singleton_squared_face_smooth
    singleton_squared_ordering squaredEssentialBirthSum (squaredEssentialBirthSum_c2_all _)
  have hval := congrArg (fun A : ℝ →L[ℝ] ℝ →L[ℝ] ℝ => A 1 1) hH
  rw [faceCoordinateLossHessian_apply] at hval
  have hscalar := nonlinear_singleton_second_derivative
  change fderiv ℝ (fderiv ℝ (fun t : ℝ => squaredEssentialBirthSum
    (dgm (ZMod 2) (nonlinearSingletonFilter t) 0))) 1 1 1 = 12 at hscalar
  rw [hscalar] at hval
  have hsecond : 12 = faceLossHessianCoefficient (ZMod 2) nonlinearSingletonFilter e 0
      squaredEssentialBirthSum default default * 2 * 2 + 2 * 2 := by
    simpa only [Finset.univ_unique, Finset.sum_singleton, singleton_squared_face_first,
      singleton_squared_face_second, hb] using hval
  have hg : faceLossHessianCoefficient (ZMod 2) nonlinearSingletonFilter e 0
      squaredEssentialBirthSum default default = 2 := by linarith
  simpa only [Subsingleton.elim s default, Subsingleton.elim r default] using And.intro hb hg

/-- The double sum in the face formula is `8`, and the face-curvature
single sum is `4`; omitting the latter would give the wrong second derivative. -/
theorem nonlinear_singleton_face_hessian_terms
    (e : CompatibleOrder (nonlinearSingletonFilter (1 : ℝ))) :
    (∑ s : TotalFace (singletonFace (0 : Fin 2)),
      ∑ r : TotalFace (singletonFace (0 : Fin 2)),
      faceLossHessianCoefficient (ZMod 2) nonlinearSingletonFilter e 0
        squaredEssentialBirthSum s r *
        fderiv ℝ (fun t : ℝ => (nonlinearSingletonFilter t).value s) 1 1 *
        fderiv ℝ (fun t : ℝ => (nonlinearSingletonFilter t).value r) 1 1) = 8 ∧
    (∑ s : TotalFace (singletonFace (0 : Fin 2)),
      faceLossCoefficient (ZMod 2) nonlinearSingletonFilter e 0 squaredEssentialBirthSum s *
        fderiv ℝ (fderiv ℝ (fun t : ℝ => (nonlinearSingletonFilter t).value s)) 1 1 1) = 4 := by
  have hc := nonlinear_singleton_face_coefficients e default default
  simp only [Finset.univ_unique, Finset.sum_singleton, singleton_squared_face_first,
    singleton_squared_face_second, hc.1, hc.2]
  norm_num

/-- The face-scattered bilinear form evaluates to `12`. -/
theorem nonlinear_singleton_face_hessian
    (e : CompatibleOrder (nonlinearSingletonFilter (1 : ℝ))) :
    faceCoordinateLossHessian (ZMod 2) nonlinearSingletonFilter e 0 squaredEssentialBirthSum 1 1 = 12 := by
  rw [faceCoordinateLossHessian_apply, (nonlinear_singleton_face_hessian_terms e).1,
    (nonlinear_singleton_face_hessian_terms e).2]
  norm_num

/-- The face-scattered form is a genuine derivative of the scalar derivative map. -/
theorem nonlinear_singleton_face_hasFDerivAt
    (e : CompatibleOrder (nonlinearSingletonFilter (1 : ℝ))) :
    HasFDerivAt (fderiv ℝ (fun t : ℝ => squaredEssentialBirthSum
      (dgm (ZMod 2) (nonlinearSingletonFilter t) 0)))
      (faceCoordinateLossHessian (ZMod 2) nonlinearSingletonFilter e 0 squaredEssentialBirthSum) 1 :=
  sublevelDiagramScalarLoss_hasFDerivAt_fderiv (ZMod 2) nonlinearSingletonFilter e 0
    isOpen_univ (Set.mem_univ (1 : ℝ)) singleton_squared_face_smooth
    singleton_squared_ordering squaredEssentialBirthSum (squaredEssentialBirthSum_c2_all _)

/-- A compatible template exists, and its face form is the genuine Hessian
with value `12` on the two unit directions. -/
theorem nonlinear_singleton_face_example :
    ∃ e : CompatibleOrder (nonlinearSingletonFilter (1 : ℝ)),
      faceCoordinateLossHessian (ZMod 2) nonlinearSingletonFilter e 0 squaredEssentialBirthSum 1 1 = 12 ∧
      HasFDerivAt (fderiv ℝ (fun t : ℝ => squaredEssentialBirthSum
        (dgm (ZMod 2) (nonlinearSingletonFilter t) 0)))
        (faceCoordinateLossHessian (ZMod 2) nonlinearSingletonFilter e 0 squaredEssentialBirthSum) 1 := by
  obtain ⟨e⟩ := exists_compatibleOrder (nonlinearSingletonFilter (1 : ℝ))
  exact ⟨e, nonlinear_singleton_face_hessian e,
    nonlinear_singleton_face_hasFDerivAt e⟩

end
end TDA.Persistence
