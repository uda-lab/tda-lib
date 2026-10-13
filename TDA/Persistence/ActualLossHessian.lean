import TDA.Persistence.ActualLossDerivative
import TDA.Persistence.DiagramSecondOrderCalculus
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Hessians of actual persistence losses

The full fixed template, including diagonal finite pairs, is selected linearly
from all actual face values. Its scalar Hessian scatters to a face-gradient
double sum and a face-curvature single sum. No ambient inner product is used.
-/

set_option autoImplicit false

universe u v
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration Topology

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : E → FilterFunction K ℝ) {x₀ : E}
variable (e : CompatibleOrder (F x₀)) (p : ℕ)

/-- The fixed full-template lift is C² on the original chamber domain. -/
theorem fixedFaceLift_contDiffOn_two {U : Set E}
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U) :
    ContDiffOn ℝ 2 (fixedFaceLift k F e p) U := by
  apply ContDiffOn.prodMk
  · apply contDiffOn_pi.mpr
    intro i
    exact (hF (e.enum ((faceTemplatePairs k e p).toList.get i).1)).prodMk
      (hF (e.enum ((faceTemplatePairs k e p).toList.get i).2))
  · apply contDiffOn_pi.mpr
    intro i
    exact hF (e.enum ((faceTemplateEssential k e p).toList.get i))

/-- The C² actual lift retains the same carrier and whole-carrier factorization. -/
noncomputable def actualFaceLossC2Lift {U : Set E} (hU : IsOpen U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x)) :
    LocalC2DiagramLift (fun x => dgm k (F x) p)
      (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2 where
  carrier := U
  isOpen_carrier := hU
  coordinates := fixedFaceLift k F e p
  factorization := fixedFaceLift_factorization k F e p horder
  smooth := fixedFaceLift_contDiffOn k F e p (fun s => (hF s).of_le (by norm_num))
  smooth_two := fixedFaceLift_contDiffOn_two k F e p hF

/-- The ambient full-template Hessian entry, with first direction before second. -/
noncomputable def faceLossSlotHessian (W : Diagram ℝ → ℝ)
    (j l : FaceLossSlot k F e p) : ℝ :=
  fderiv ℝ (fderiv ℝ (W ∘ orderedQ (faceLiftCounts k F e p).1
    (faceLiftCounts k F e p).2)) (fixedFaceLift k F e p x₀)
      (faceLossUnit k F e p j) (faceLossUnit k F e p l)

/-- Scatter the coordinate Hessian using the existing linear face selection. -/
noncomputable def faceLossHessianCoefficient (W : Diagram ℝ → ℝ)
    (s t : TotalFace K) : ℝ :=
  fderiv ℝ (fderiv ℝ (W ∘ orderedQ (faceLiftCounts k F e p).1
    (faceLiftCounts k F e p).2)) (fixedFaceLift k F e p x₀)
      (faceValueSelection k F e p (Pi.single (M := fun _ : TotalFace K => ℝ) s 1))
      (faceValueSelection k F e p (Pi.single (M := fun _ : TotalFace K => ℝ) t 1))

/-- Selected face entries are exactly the corresponding ambient Hessian entries. -/
theorem faceLossHessianCoefficient_selected (W : Diagram ℝ → ℝ)
    (j l : FaceLossSlot k F e p) :
    faceLossHessianCoefficient k F e p W
      (faceLossSlotFace k F e p j) (faceLossSlotFace k F e p l) =
      faceLossSlotHessian k F e p W j l := by
  unfold faceLossHessianCoefficient faceLossSlotHessian
  rw [faceValueSelection_single_eq_unit, faceValueSelection_single_eq_unit]

/-- An unused face has a zero row in the scattered Hessian. -/
theorem faceLossHessianCoefficient_unused_left (W : Diagram ℝ → ℝ)
    (s t : TotalFace K) (hs : s ∉ Set.range (faceLossSlotFace k F e p)) :
    faceLossHessianCoefficient k F e p W s t = 0 := by
  unfold faceLossHessianCoefficient
  rw [faceValueSelection_single_eq_zero k F e p s hs]
  simp

/-- An unused face has a zero column in the scattered Hessian. -/
theorem faceLossHessianCoefficient_unused_right (W : Diagram ℝ → ℝ)
    (s t : TotalFace K) (ht : t ∉ Set.range (faceLossSlotFace k F e p)) :
    faceLossHessianCoefficient k F e p W s t = 0 := by
  unfold faceLossHessianCoefficient
  rw [faceValueSelection_single_eq_zero k F e p t ht]
  simp

/-- The explicit curried continuous bilinear form: gradient interactions plus
curvature of the face-value parametrization. -/
noncomputable def actualFaceLossHessian (W : Diagram ℝ → ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (∑ s : TotalFace K, ∑ t : TotalFace K,
    faceLossHessianCoefficient k F e p W s t •
      (fderiv ℝ (fun x => (F x).value s) x₀).smulRight
        (fderiv ℝ (fun x => (F x).value t) x₀)) +
  ∑ s : TotalFace K, faceLossCoefficient k F e p W s •
    fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀

/-- Evaluation gives the face-gradient double sum and face-curvature single sum. -/
theorem actualFaceLossHessian_apply (W : Diagram ℝ → ℝ) (h q : E) :
    actualFaceLossHessian k F e p W h q =
      (∑ s : TotalFace K, ∑ t : TotalFace K,
        faceLossHessianCoefficient k F e p W s t *
          fderiv ℝ (fun x => (F x).value s) x₀ h *
          fderiv ℝ (fun x => (F x).value t) x₀ q) +
      ∑ s : TotalFace K, faceLossCoefficient k F e p W s *
        fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀ h q := by
  classical
  simp [actualFaceLossHessian, ContinuousLinearMap.smulRight_apply, mul_assoc]

private theorem bilinearFunctional_face_sum {I : Type*} [Fintype I] [DecidableEq I]
    (T : (I → ℝ) →L[ℝ] (I → ℝ) →L[ℝ] ℝ) (a b : I → ℝ) :
    T a b = ∑ i : I, ∑ j : I,
      T (Pi.single (M := fun _ : I => ℝ) i 1)
        (Pi.single (M := fun _ : I => ℝ) j 1) * a i * b j := by
  classical
  change (T.flip b) a = _
  rw [linearFunctional_face_sum (T.flip b) a]
  apply Finset.sum_congr rfl
  intro i _
  change T (Pi.single i 1) b * a i = _
  rw [linearFunctional_face_sum (T (Pi.single i 1)) b, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [LinearOrder V] in
/-- Second derivatives of the full face-value vector are the face second derivatives. -/
theorem allFaceValues_second_fderiv_apply {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (s : TotalFace K) (h q : E) :
    fderiv ℝ (fderiv ℝ (allFaceValues F)) x₀ h q s =
      fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀ h q := by
  have hG := (contDiffOn_pi.mpr hF).contDiffAt (hU.mem_nhds hx)
  have heq := secondDerivative_linear_postcomp
    (ContinuousLinearMap.proj s : (TotalFace K → ℝ) →L[ℝ] ℝ)
    (allFaceValues F) x₀ hG
  simpa only [Function.comp_def, allFaceValues, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply] using
    (congrArg (fun A => A h q) heq).symm

/-- Linear face selection commutes with the full second derivative. -/
theorem fixedFaceLift_second_fderiv_eq_selection {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U) :
    fderiv ℝ (fderiv ℝ (fixedFaceLift k F e p)) x₀ =
      (ContinuousLinearMap.compL ℝ E (TotalFace K → ℝ)
        (DiagramCoordinates (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2)
          (faceValueSelection k F e p)).comp
            (fderiv ℝ (fderiv ℝ (allFaceValues F)) x₀) := by
  have hG := (contDiffOn_pi.mpr hF).contDiffAt (hU.mem_nhds hx)
  simpa only [Function.comp_def, ← fixedFaceLift_eq_selection] using
    secondDerivative_linear_postcomp (faceValueSelection k F e p)
      (allFaceValues F) x₀ hG

/-- Every selected slot, including a diagonal endpoint, has its face second derivative. -/
theorem fixedFaceLift_slot_second_derivative {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (j : FaceLossSlot k F e p) (h q : E) :
    faceLossSlotRead k F e p j
      (fderiv ℝ (fderiv ℝ (fixedFaceLift k F e p)) x₀ h q) =
      fderiv ℝ (fderiv ℝ (fun x => (F x).value (faceLossSlotFace k F e p j)))
        x₀ h q := by
  rw [fixedFaceLift_second_fderiv_eq_selection k F e p hU hx hF]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  have hs : faceLossSlotRead k F e p j
      (faceValueSelection k F e p (fderiv ℝ (fderiv ℝ (allFaceValues F)) x₀ h q)) =
      fderiv ℝ (fderiv ℝ (allFaceValues F)) x₀ h q (faceLossSlotFace k F e p j) := by
    rcases j with ((i | i) | i) <;> rfl
  rw [hs, allFaceValues_second_fderiv_apply F hU hx hF]

/-- The scalar loss is C² on an open neighborhood contained in the original chamber. -/
theorem actualPHScalarLoss_c2_neighborhood (e : CompatibleOrder (F x₀)) (p : ℕ) {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    ∃ N : Set E, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ U ∧
      ContDiffOn ℝ 2 (fun x => W (dgm k (F x) p)) N := by
  exact localLift_scalar_c2 (fun x => dgm k (F x) p) W
    (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2
    (actualFaceLossC2Lift k F e p hU hF horder) x₀ hx hW

/-- C² losses retain exactly the merged first-order face coefficient convention. -/
theorem actualPHScalarLoss_c2_fderiv {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    fderiv ℝ (fun x => W (dgm k (F x) p)) x₀ =
      ∑ s : TotalFace K, faceLossCoefficient k F e p W s •
        fderiv ℝ (fun x => (F x).value s) x₀ :=
  actualPHScalarLoss_fderiv k F e p hU hx
    (fun s => (hF s).of_le (by norm_num)) horder W hW.c1

/-- Scattering the full chain expression gives the explicit face bilinear form. -/
theorem secondDerivativeChain_eq_actualFaceLossHessian {U : Set E}
    (hU : IsOpen U) (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (W : Diagram ℝ → ℝ) :
    secondDerivativeChain
      (W ∘ orderedQ (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2)
      (fixedFaceLift k F e p) x₀ = actualFaceLossHessian k F e p W := by
  classical
  let D := fderiv ℝ (W ∘ orderedQ (faceLiftCounts k F e p).1
    (faceLiftCounts k F e p).2) (fixedFaceLift k F e p x₀)
  let H := fderiv ℝ (fderiv ℝ (W ∘ orderedQ (faceLiftCounts k F e p).1
    (faceLiftCounts k F e p).2)) (fixedFaceLift k F e p x₀)
  let R := faceValueSelection k F e p
  let G := fderiv ℝ (allFaceValues F) x₀
  let J := fderiv ℝ (fderiv ℝ (allFaceValues F)) x₀
  have hFone : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U :=
    fun s => (hF s).of_le (by norm_num)
  ext h q
  rw [secondDerivativeChain_apply, actualFaceLossHessian_apply,
    fixedFaceLift_fderiv_eq_selection k F e p hU hx hFone,
    fixedFaceLift_second_fderiv_eq_selection k F e p hU hx hF]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  change H (R (G h)) (R (G q)) + D (R (J h q)) = _
  have hexp : H (R (G h)) (R (G q)) =
      ∑ s : TotalFace K, ∑ t : TotalFace K,
        faceLossHessianCoefficient k F e p W s t * G h s * G q t := by
    let T : (TotalFace K → ℝ) →L[ℝ] (TotalFace K → ℝ) →L[ℝ] ℝ :=
      ((ContinuousLinearMap.compL ℝ (TotalFace K → ℝ) _ ℝ).flip R).comp (H.comp R)
    exact bilinearFunctional_face_sum T (G h) (G q)
  have hcurv : D (R (J h q)) =
      ∑ s : TotalFace K, faceLossCoefficient k F e p W s * J h q s := by
    change (D.comp R) (J h q) = _
    rw [linearFunctional_face_sum (D.comp R) (J h q)]
    apply Finset.sum_congr rfl
    intro s _
    rw [faceLossCoefficient_eq_basis k F e p W s]
    rfl
  rw [hexp, hcurv]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [allFaceValues_fderiv_apply F hU hx hFone,
      allFaceValues_fderiv_apply F hU hx hFone]
  · apply Finset.sum_congr rfl
    intro s _
    rw [allFaceValues_second_fderiv_apply F hU hx hF]

/-- The derivative map of the actual scalar loss genuinely has the face Hessian
as its Fréchet derivative. Both gradient and face-curvature terms are retained. -/
theorem actualPHScalarLoss_hasFDerivAt_fderiv {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    HasFDerivAt (fderiv ℝ (fun x => W (dgm k (F x) p)))
      (actualFaceLossHessian k F e p W) x₀ := by
  have hc := localLift_scalar_hasFDerivAt_fderiv
    (fun x => dgm k (F x) p) W
    (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2
    (actualFaceLossC2Lift k F e p hU hF horder) x₀ hx hW
  change HasFDerivAt (fderiv ℝ (fun x => W (dgm k (F x) p)))
    (secondDerivativeChain
      (W ∘ orderedQ (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2)
        (fixedFaceLift k F e p) x₀) x₀ at hc
  rwa [secondDerivativeChain_eq_actualFaceLossHessian k F e p hU hx hF W] at hc

/-- The ordinary second derivative equals the face Hessian by derivative uniqueness. -/
theorem actualPHScalarLoss_second_fderiv {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    fderiv ℝ (fderiv ℝ (fun x => W (dgm k (F x) p))) x₀ =
      actualFaceLossHessian k F e p W :=
  (actualPHScalarLoss_hasFDerivAt_fderiv k F e p hU hx hF horder W hW).fderiv

/-- The scattered coordinate Hessian is symmetric under C² loss regularity. -/
theorem faceLossHessianCoefficient_symmetric {U : Set E} (hx : x₀ ∈ U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) (s t : TotalFace K) :
    faceLossHessianCoefficient k F e p W s t =
      faceLossHessianCoefficient k F e p W t s := by
  obtain ⟨N, hNo, hzN, hN⟩ := hW (faceLiftCounts k F e p).1
    (faceLiftCounts k F e p).2 (fixedFaceLift k F e p x₀)
    (fixedFaceLift_factorization k F e p horder x₀ hx).symm
  exact (hN.contDiffAt (hNo.mem_nhds hzN)).isSymmSndFDerivAt (by norm_num) _ _

/-- Symmetry of the final bilinear form follows from scalar C² regularity. -/
theorem actualFaceLossHessian_symmetric {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) (h q : E) :
    actualFaceLossHessian k F e p W h q = actualFaceLossHessian k F e p W q h := by
  rw [← actualPHScalarLoss_second_fderiv k F e p hU hx hF horder W hW]
  obtain ⟨N, hNo, hxN, _, hN⟩ := actualPHScalarLoss_c2_neighborhood
    k F e p hU hx hF horder W hW
  exact (hN.contDiffAt (hNo.mem_nhds hxN)).isSymmSndFDerivAt (by norm_num) h q

private theorem finiteFaceHessian_norm_bound {I : Type*} [Fintype I]
    (γ : I → I → ℝ) (β : I → ℝ) (A : I → E →L[ℝ] ℝ)
    (J : I → E →L[ℝ] E →L[ℝ] ℝ) :
    ‖(∑ i : I, ∑ j : I, γ i j • (A i).smulRight (A j)) + ∑ i : I, β i • J i‖ ≤
      (∑ i : I, ∑ j : I, |γ i j| * ‖A i‖ * ‖A j‖) + ∑ i : I, |β i| * ‖J i‖ := by
  classical
  have hdouble : ‖∑ i : I, ∑ j : I, γ i j • (A i).smulRight (A j)‖ ≤
      ∑ i : I, ∑ j : I, |γ i j| * ‖A i‖ * ‖A j‖ := by
    refine le_trans (norm_sum_le (E := E →L[ℝ] E →L[ℝ] ℝ) Finset.univ
      (fun i => ∑ j : I, γ i j • (A i).smulRight (A j))) ?_
    apply Finset.sum_le_sum
    intro i _
    calc
      ‖∑ j : I, γ i j • (A i).smulRight (A j)‖ ≤
        ∑ j : I, ‖γ i j • (A i).smulRight (A j)‖ := norm_sum_le (E := E →L[ℝ] E →L[ℝ] ℝ) _ _
      _ ≤ ∑ j : I, |γ i j| * ‖(A i).smulRight (A j)‖ := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Real.norm_eq_abs] using
          ContinuousLinearMap.opNorm_smul_le (γ i j) ((A i).smulRight (A j))
      _ = _ := by simp only [ContinuousLinearMap.norm_smulRight_apply, mul_assoc]
  have hsingle : ‖∑ i : I, β i • J i‖ ≤ ∑ i : I, |β i| * ‖J i‖ := by
    calc
      ‖∑ i : I, β i • J i‖ ≤ ∑ i : I, ‖β i • J i‖ := norm_sum_le (E := E →L[ℝ] E →L[ℝ] ℝ) _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le (β i) (J i)
  exact (norm_add_le
    (∑ i : I, ∑ j : I, γ i j • (A i).smulRight (A j))
    (∑ i : I, β i • J i)).trans (add_le_add hdouble hsingle)

/-- The operator norm of the face form is bounded termwise, including empty sums. -/
theorem actualFaceLossHessian_norm_bound (W : Diagram ℝ → ℝ) :
    ‖actualFaceLossHessian k F e p W‖ ≤
      (∑ s : TotalFace K, ∑ t : TotalFace K,
        |faceLossHessianCoefficient k F e p W s t| *
          ‖fderiv ℝ (fun x => (F x).value s) x₀‖ *
          ‖fderiv ℝ (fun x => (F x).value t) x₀‖) +
      ∑ s : TotalFace K, |faceLossCoefficient k F e p W s| *
        ‖fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀‖ := by
  exact finiteFaceHessian_norm_bound
    (faceLossHessianCoefficient k F e p W) (faceLossCoefficient k F e p W)
    (fun s => fderiv ℝ (fun x => (F x).value s) x₀)
    (fun s => fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀)

/-- Quantitative bound for the genuine ordinary scalar second derivative. -/
theorem actualPHScalarLoss_second_norm_bound {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    ‖fderiv ℝ (fderiv ℝ (fun x => W (dgm k (F x) p))) x₀‖ ≤
      (∑ s : TotalFace K, ∑ t : TotalFace K,
        |faceLossHessianCoefficient k F e p W s t| *
          ‖fderiv ℝ (fun x => (F x).value s) x₀‖ *
          ‖fderiv ℝ (fun x => (F x).value t) x₀‖) +
      ∑ s : TotalFace K, |faceLossCoefficient k F e p W s| *
        ‖fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀‖ := by
  rw [actualPHScalarLoss_second_fderiv k F e p hU hx hF horder W hW]
  exact actualFaceLossHessian_norm_bound k F e p W

/-- Compatible template choices yield the same final scalar Hessian, without
identifying the ambient coefficient arrays. -/
theorem actualPHScalarLoss_second_derivative_independent
    (e' : CompatibleOrder (F x₀)) {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    actualFaceLossHessian k F e p W = actualFaceLossHessian k F e' p W := by
  rw [← actualPHScalarLoss_second_fderiv k F e p hU hx hF horder W hW,
    ← actualPHScalarLoss_second_fderiv k F e' p hU hx hF horder W hW]

/-- Arbitrary admissible C² lifts, including redundant diagonal coordinates and
different counts, determine the same final scalar Hessian. -/
theorem actualPHScalarLoss_any_c2_lifts_independent
    (W : Diagram ℝ → ℝ) (m n m' n' : ℕ)
    (L : LocalC2DiagramLift (fun x => dgm k (F x) p) m n)
    (L' : LocalC2DiagramLift (fun x => dgm k (F x) p) m' n')
    (hx : x₀ ∈ L.carrier) (hx' : x₀ ∈ L'.carrier)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    secondDerivativeChain (W ∘ orderedQ m n) L.coordinates x₀ =
      secondDerivativeChain (W ∘ orderedQ m' n') L'.coordinates x₀ :=
  localLift_scalar_second_derivative_independent (fun x => dgm k (F x) p)
    W m n m' n' L L' x₀ hx hx' hW

/-- Vanishing face second derivatives remove exactly the curvature summand. -/
theorem actualFaceLossHessian_of_face_second_deriv_zero
    (W : Diagram ℝ → ℝ)
    (hzero : ∀ s : TotalFace K, fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀ = 0) :
    actualFaceLossHessian k F e p W =
      ∑ s : TotalFace K, ∑ t : TotalFace K,
        faceLossHessianCoefficient k F e p W s t •
          (fderiv ℝ (fun x => (F x).value s) x₀).smulRight
            (fderiv ℝ (fun x => (F x).value t) x₀) := by
  classical
  simp [actualFaceLossHessian, hzero]

/-- Scalar Hessian pullback when all face-value curvatures vanish at the point. -/
theorem actualPHScalarLoss_second_fderiv_of_face_second_deriv_zero
    {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p))
    (hzero : ∀ s : TotalFace K, fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀ = 0) :
    fderiv ℝ (fderiv ℝ (fun x => W (dgm k (F x) p))) x₀ =
      ∑ s : TotalFace K, ∑ t : TotalFace K,
        faceLossHessianCoefficient k F e p W s t •
          (fderiv ℝ (fun x => (F x).value s) x₀).smulRight
            (fderiv ℝ (fun x => (F x).value t) x₀) := by
  rw [actualPHScalarLoss_second_fderiv k F e p hU hx hF horder W hW]
  exact actualFaceLossHessian_of_face_second_deriv_zero k F e p W hzero

omit [LinearOrder V] [Fintype (TotalFace K)] in
/-- Persistent ties give equal first derivatives, so full-template terms can cancel. -/
theorem tiedFaceValues_fderiv_eq {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U)
    (s t : TotalFace K) (htie : ∀ x ∈ U, (F x).value s = (F x).value t) :
    fderiv ℝ (fun x => (F x).value s) x₀ =
      fderiv ℝ (fun x => (F x).value t) x₀ := by
  have heq : (fun x => (F x).value s) =ᶠ[𝓝 x₀] (fun x => (F x).value t) := by
    filter_upwards [hU.mem_nhds hx] with x hxU
    exact htie x hxU
  exact heq.fderiv_eq

omit [LinearOrder V] [Fintype (TotalFace K)] in
/-- Persistent ties also give equal second derivatives; no ambient coefficient
vanishing is asserted. -/
theorem tiedFaceValues_second_fderiv_eq {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U)
    (s t : TotalFace K) (htie : ∀ x ∈ U, (F x).value s = (F x).value t) :
    fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀ =
      fderiv ℝ (fderiv ℝ (fun x => (F x).value t)) x₀ := by
  have heq : (fun x => (F x).value s) =ᶠ[𝓝 x₀] (fun x => (F x).value t) := by
    filter_upwards [hU.mem_nhds hx] with x hxU
    exact htie x hxU
  exact heq.fderiv.fderiv_eq

/-- The empty actual complex has zero scalar Hessian and empty face sums. -/
theorem actualPHScalarLoss_empty_second_fderiv (hm : faceCount K = 0)
    {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    fderiv ℝ (fderiv ℝ (fun x => W (dgm k (F x) p))) x₀ = 0 := by
  obtain ⟨e⟩ := exists_compatibleOrder (F x₀)
  have : IsEmpty (TotalFace K) := Fintype.card_eq_zero_iff.mp hm
  rw [actualPHScalarLoss_second_fderiv k F e p hU hx hF horder W hW]
  simp [actualFaceLossHessian]

/-- The basis-selection definition is also the unambiguous selected-slot scatter. -/
theorem faceLossHessianCoefficient_eq_scatter (W : Diagram ℝ → ℝ)
    (s t : TotalFace K) :
    faceLossHessianCoefficient k F e p W s t =
      if hs : s ∈ Set.range (faceLossSlotFace k F e p) then
        if ht : t ∈ Set.range (faceLossSlotFace k F e p) then
          faceLossSlotHessian k F e p W (Classical.choose hs) (Classical.choose ht)
        else 0
      else 0 := by
  classical
  split_ifs with hs ht
  · simpa only [Classical.choose_spec hs, Classical.choose_spec ht] using
      faceLossHessianCoefficient_selected k F e p W
        (Classical.choose hs) (Classical.choose ht)
  · exact faceLossHessianCoefficient_unused_right k F e p W s t ht
  · exact faceLossHessianCoefficient_unused_left k F e p W s t hs

omit [LinearOrder V] [Fintype (TotalFace K)] in
/-- An affine face-value parametrization on an open neighborhood has zero face curvature. -/
theorem affineFaceValues_second_fderiv_zero {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U) (A : TotalFace K → E →L[ℝ] ℝ) (b : TotalFace K → ℝ)
    (haff : ∀ s : TotalFace K, ∀ x ∈ U, (F x).value s = b s + A s x)
    (s : TotalFace K) :
    fderiv ℝ (fderiv ℝ (fun x => (F x).value s)) x₀ = 0 := by
  have heq : (fun x => (F x).value s) =ᶠ[𝓝 x₀] (fun x => b s + A s x) := by
    filter_upwards [hU.mem_nhds hx] with x hxU
    exact haff s x hxU
  have hd : fderiv ℝ (fun x => (F x).value s) =ᶠ[𝓝 x₀] (fun _ => A s) := by
    refine heq.fderiv.trans (Filter.Eventually.of_forall ?_)
    intro x
    exact ((A s).hasFDerivAt.const_add (b s)).fderiv
  rw [hd.fderiv_eq]
  exact fderiv_const_apply (A s)

/-- For a genuinely affine family on the chamber, the Hessian is the ordinary
pullback of the ambient coordinate Hessian, with no face-curvature term. -/
theorem actualPHScalarLoss_affine_second_fderiv {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U) (A : TotalFace K → E →L[ℝ] ℝ) (b : TotalFace K → ℝ)
    (haff : ∀ s : TotalFace K, ∀ x ∈ U, (F x).value s = b s + A s x)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C2ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    fderiv ℝ (fderiv ℝ (fun x => W (dgm k (F x) p))) x₀ =
      ∑ s : TotalFace K, ∑ t : TotalFace K,
        faceLossHessianCoefficient k F e p W s t • (A s).smulRight (A t) := by
  classical
  have hF : ∀ s : TotalFace K, ContDiffOn ℝ 2 (fun x => (F x).value s) U := by
    intro s
    apply ((contDiff_const.add (A s).contDiff).contDiffOn).congr
    intro x hxU
    exact haff s x hxU
  rw [actualPHScalarLoss_second_fderiv_of_face_second_deriv_zero
    k F e p hU hx hF horder W hW
      (affineFaceValues_second_fderiv_zero F hU hx A b haff)]
  have hd : ∀ s : TotalFace K, fderiv ℝ (fun x => (F x).value s) x₀ = A s := by
    intro s
    have heq : (fun x => (F x).value s) =ᶠ[𝓝 x₀] (fun x => b s + A s x) := by
      filter_upwards [hU.mem_nhds hx] with x hxU
      exact haff s x hxU
    rw [heq.fderiv_eq]
    exact ((A s).hasFDerivAt.const_add (b s)).fderiv
  simp only [hd]

end TDA.Persistence
