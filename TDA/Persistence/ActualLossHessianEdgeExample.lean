import TDA.Persistence.ActualLossHessianExamples

/-! An actual positive edge bar with a nonlinear death coordinate. -/

namespace TDA.Persistence.LossExamples
open TDA.Simplicial TDA.Filtration
open Examples

/-- The open parameter box on which the edge filtration has fixed strict order. -/
def nonlinearEdgeBox : Set (ℝ × ℝ) :=
  {x | |x.1| < 1 / 4 ∧ |x.2| < 1 / 4}

/-- A globally valid filtration; the maximum only extends the death grade
outside the open box used for differentiation. -/
def nonlinearEdgeFilter (x : ℝ × ℝ) : FilterFunction edgeK ℝ where
  value := fun s =>
    if s.val = ({0} : Finset (Fin 2)) then 0
    else if s.val = ({1} : Finset (Fin 2)) then 1 + x.1
    else max 0 (max (1 + x.1) (3 + x.2 + x.1 ^ 2))
  mono := by
    intro τ σ hsub
    rcases edge_face_cases τ with hτ | hτ | hτ <;>
      rcases edge_face_cases σ with hσ | hσ | hσ <;>
      simp [hτ, hσ, Finset.subset_iff] at hsub ⊢
    all_goals norm_num [Finset.ext_iff] at *

private theorem nonlinearEdgeBox_bounds (x : ℝ × ℝ) (hx : x ∈ nonlinearEdgeBox) :
    0 < 1 + x.1 ∧ 1 + x.1 < 3 + x.2 + x.1 ^ 2 := by
  obtain ⟨hs, ht⟩ := hx
  obtain ⟨hs₁, hs₂⟩ := abs_lt.mp hs
  obtain ⟨ht₁, ht₂⟩ := abs_lt.mp ht
  constructor <;> nlinarith [sq_nonneg x.1]

private theorem nonlinearEdgeFilter_value (x : ℝ × ℝ) (hx : x ∈ nonlinearEdgeBox)
    (s : TotalFace edgeK) :
    (nonlinearEdgeFilter x).value s =
      if s.val = ({0} : Finset (Fin 2)) then 0
      else if s.val = ({1} : Finset (Fin 2)) then 1 + x.1
      else 3 + x.2 + x.1 ^ 2 := by
  obtain ⟨hb, hd⟩ := nonlinearEdgeBox_bounds x hx
  simp only [nonlinearEdgeFilter, max_eq_right hd.le,
    max_eq_right (le_trans hb.le hd.le)]

/-- Each actual face value is `C²` throughout the original open box. -/
theorem nonlinearEdgeFilter_contDiffOn (σ : TotalFace edgeK) :
    ContDiffOn ℝ 2 (fun x => (nonlinearEdgeFilter x).value σ) nonlinearEdgeBox := by
  have hs : ContDiff ℝ 2 (fun x : ℝ × ℝ =>
      if σ.val = ({0} : Finset (Fin 2)) then 0
      else if σ.val = ({1} : Finset (Fin 2)) then 1 + x.1
      else 3 + x.2 + x.1 ^ 2) := by
    split_ifs <;> fun_prop
  apply hs.contDiffOn.congr
  intro x hx
  exact nonlinearEdgeFilter_value x hx σ

/-- No change of face order occurs anywhere in the parameter box. -/
theorem nonlinearEdgeFilter_ordering (x y : ℝ × ℝ)
    (hx : x ∈ nonlinearEdgeBox) (hy : y ∈ nonlinearEdgeBox) :
    OrderingEquivalent (nonlinearEdgeFilter x) (nonlinearEdgeFilter y) := by
  intro σ τ
  rw [nonlinearEdgeFilter_value x hx σ, nonlinearEdgeFilter_value x hx τ,
    nonlinearEdgeFilter_value y hy σ, nonlinearEdgeFilter_value y hy τ]
  obtain ⟨hb, hd⟩ := nonlinearEdgeBox_bounds x hx
  obtain ⟨hb', hd'⟩ := nonlinearEdgeBox_bounds y hy
  rcases edge_face_cases σ with hσ | hσ | hσ <;>
    rcases edge_face_cases τ with hτ | hτ | hτ <;>
    norm_num [hσ, hτ, Finset.ext_iff] <;> constructor <;> intro h <;> linarith

/-- The diagram is transported from the existing actual edge homology
calculation, retaining one essential class and one positive finite bar. -/
theorem nonlinearEdgeFilter_points (x : ℝ × ℝ) (hx : x ∈ nonlinearEdgeBox) :
    (dgm (ZMod 2) (nonlinearEdgeFilter x) 0).points =
      ({(0, (⊤ : WithTop ℝ)),
        (1 + x.1, ((3 + x.2 + x.1 ^ 2 : ℝ) : WithTop ℝ))} :
        Multiset (ℝ × WithTop ℝ)) := by
  let φ : ℝ → ℝ := fun a => if a = 2 then 0 else if a = 5 then 1 + x.1
    else 3 + x.2 + x.1 ^ 2
  have hφ : StrictMonoOn φ (Set.range edgeFilter.value) := by
    rintro a ⟨σ, rfl⟩ b ⟨τ, rfl⟩ hlt
    obtain ⟨hb, hd⟩ := nonlinearEdgeBox_bounds x hx
    rcases edge_face_cases σ with hσ | hσ | hσ <;>
      rcases edge_face_cases τ with hτ | hτ | hτ <;>
      norm_num [edgeFilter, hσ, hτ, φ, Finset.ext_iff] at hlt <;>
      norm_num [edgeFilter, hσ, hτ, φ, Finset.ext_iff]
    all_goals linarith
  have hvalue : ∀ s : TotalFace edgeK,
      (nonlinearEdgeFilter x).value s = φ (edgeFilter.value s) := by
    intro s
    rw [nonlinearEdgeFilter_value x hx]
    rcases edge_face_cases s with hs | hs | hs <;>
      norm_num [edgeFilter, hs, φ, Finset.ext_iff]
  rw [dgm_points_map_of_strictMonoOn (ZMod 2) edgeFilter
    (nonlinearEdgeFilter x) φ hφ hvalue 0, edge_points]
  norm_num [φ]

/-- The full ordered presentation of this actual edge diagram. -/
def nonlinearEdgeCoordinates (x : ℝ × ℝ) : DiagramCoordinates 1 1 :=
  (fun _ => (1 + x.1, 3 + x.2 + x.1 ^ 2), fun _ => 0)

/-- Every coordinate is an evaluation at its fixed actual face: finite birth
at the second vertex, death at the edge, and essential birth at the first vertex. -/
theorem nonlinearEdgeCoordinates_faces (x : ℝ × ℝ) (hx : x ∈ nonlinearEdgeBox) :
    (nonlinearEdgeCoordinates x).1 0 =
      ((nonlinearEdgeFilter x).value edge_v1, (nonlinearEdgeFilter x).value edge_e01) ∧
    (nonlinearEdgeCoordinates x).2 0 = (nonlinearEdgeFilter x).value edge_v0 := by
  simp [nonlinearEdgeCoordinates, nonlinearEdgeFilter_value x hx,
    edge_v0, edge_v1, edge_e01, Finset.ext_iff]

/-- Actual factorization throughout the original open box. -/
theorem nonlinearEdgeCoordinates_factorization (x : ℝ × ℝ)
    (hx : x ∈ nonlinearEdgeBox) :
    dgm (ZMod 2) (nonlinearEdgeFilter x) 0 =
      orderedQ 1 1 (nonlinearEdgeCoordinates x) := by
  apply Diagram.ext
  rw [nonlinearEdgeFilter_points x hx]
  have hne := ne_of_lt (nonlinearEdgeBox_bounds x hx).2
  simp only [orderedQ, nonlinearEdgeCoordinates]
  simp [hne]
  exact Multiset.pair_comm _ _

/-- The signed finite loss is the actual death minus birth. -/
theorem nonlinearEdge_signed_loss (x : ℝ × ℝ) (hx : x ∈ nonlinearEdgeBox) :
    signedFiniteEndpointDifference (dgm (ZMod 2) (nonlinearEdgeFilter x) 0) =
      2 + x.2 - x.1 + x.1 ^ 2 := by
  rw [nonlinearEdgeCoordinates_factorization x hx,
    signedFiniteEndpointDifference_orderedQ]
  simp [nonlinearEdgeCoordinates]
  ring

/-- The prescribed box is open. -/
theorem nonlinearEdgeBox_isOpen : IsOpen nonlinearEdgeBox :=
  (isOpen_lt (continuous_fst.abs) continuous_const).inter
    (isOpen_lt (continuous_snd.abs) continuous_const)

/-- The base parameter is inside the prescribed box. -/
theorem nonlinearEdgeBox_zero : (0 : ℝ × ℝ) ∈ nonlinearEdgeBox := by
  norm_num [nonlinearEdgeBox]

/-- The explicit ordered lift is polynomial, so it is globally `C²`. -/
theorem nonlinearEdgeCoordinates_contDiff : ContDiff ℝ 2 nonlinearEdgeCoordinates := by
  unfold nonlinearEdgeCoordinates
  fun_prop

/-- The actual edge family admits this full `C²` ordered presentation. -/
def nonlinearEdgeLift : LocalC2DiagramLift
    (fun x => dgm (ZMod 2) (nonlinearEdgeFilter x) 0) 1 1 where
  carrier := nonlinearEdgeBox
  isOpen_carrier := nonlinearEdgeBox_isOpen
  coordinates := nonlinearEdgeCoordinates
  factorization := nonlinearEdgeCoordinates_factorization
  smooth := nonlinearEdgeCoordinates_contDiff.contDiffOn.of_le (by norm_num)
  smooth_two := nonlinearEdgeCoordinates_contDiff.contDiffOn

private noncomputable def edgeLinearCoordinates :
    (ℝ × ℝ) →L[ℝ] DiagramCoordinates 1 1 :=
  (ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod 0

private def edgeDeathUnit : DiagramCoordinates 1 1 :=
  (fun _ => (0, 1), fun _ => 0)

private noncomputable def edgeDeathDirection :
    (ℝ × ℝ) →L[ℝ] DiagramCoordinates 1 1 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight edgeDeathUnit

private theorem nonlinearEdgeCoordinates_expansion (x : ℝ × ℝ) :
    nonlinearEdgeCoordinates x = nonlinearEdgeCoordinates 0 +
      edgeLinearCoordinates x + x.1 ^ 2 • edgeDeathUnit := by
  ext i <;> simp [nonlinearEdgeCoordinates, edgeLinearCoordinates, edgeDeathUnit]

private theorem nonlinearEdgeCoordinates_hasFDerivAt (x : ℝ × ℝ) :
    HasFDerivAt nonlinearEdgeCoordinates
      (edgeLinearCoordinates + (2 * x.1) • edgeDeathDirection) x := by
  have hs := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := x)
  have hsq := (hs.mul hs).smul_const edgeDeathUnit
  have hh := ((hasFDerivAt_const (nonlinearEdgeCoordinates 0) x).add
    edgeLinearCoordinates.hasFDerivAt).add hsq
  have heq : (fun y : ℝ × ℝ => nonlinearEdgeCoordinates 0 +
      edgeLinearCoordinates y + (y.1 * y.1) • edgeDeathUnit) = nonlinearEdgeCoordinates := by
    funext y
    simpa [pow_two] using (nonlinearEdgeCoordinates_expansion y).symm
  change HasFDerivAt (fun y : ℝ × ℝ => nonlinearEdgeCoordinates 0 +
    edgeLinearCoordinates y + (y.1 * y.1) • edgeDeathUnit) _ x at hh
  rw [heq] at hh
  convert hh using 1 <;> ext h <;>
    simp [edgeDeathDirection, edgeDeathUnit, ContinuousLinearMap.smulRight_apply]
  all_goals ring

private theorem nonlinearEdgeCoordinates_fderiv (x : ℝ × ℝ) :
    fderiv ℝ nonlinearEdgeCoordinates x =
      edgeLinearCoordinates + (2 * x.1) • edgeDeathDirection :=
  (nonlinearEdgeCoordinates_hasFDerivAt x).fderiv

private theorem nonlinearEdgeCoordinates_second_fderiv (x : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ nonlinearEdgeCoordinates) x =
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight edgeDeathDirection := by
  have hs := ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := x)).const_mul 2
  have hh := (hasFDerivAt_const edgeLinearCoordinates x).add
    (hs.smul_const edgeDeathDirection)
  have heq : (fun y : ℝ × ℝ => edgeLinearCoordinates +
      (2 * y.1) • edgeDeathDirection) = fderiv ℝ nonlinearEdgeCoordinates := by
    funext y
    exact (nonlinearEdgeCoordinates_fderiv y).symm
  change HasFDerivAt (fun y : ℝ × ℝ => edgeLinearCoordinates +
    (2 * y.1) • edgeDeathDirection) _ x at hh
  rw [heq] at hh
  simpa using hh.fderiv

/-- The square loss evaluates on the actual diagram to the prescribed polynomial. -/
theorem nonlinearEdge_squared_loss (x : ℝ × ℝ) (hx : x ∈ nonlinearEdgeBox) :
    squaredSignedFiniteEndpointDifference (dgm (ZMod 2) (nonlinearEdgeFilter x) 0) =
      (2 + x.2 - x.1 + x.1 ^ 2) ^ 2 := by
  unfold squaredSignedFiniteEndpointDifference
  rw [nonlinearEdge_signed_loss x hx]

/-- The coordinate-loss part of the genuine chain expression. -/
theorem nonlinearEdge_coordinate_hessian (h k : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘ orderedQ 1 1))
      (nonlinearEdgeCoordinates 0)
      (fderiv ℝ nonlinearEdgeCoordinates 0 h)
      (fderiv ℝ nonlinearEdgeCoordinates 0 k) =
      2 * (h.2 - h.1) * (k.2 - k.1) := by
  rw [squaredSignedFiniteEndpointDifference_secondFDeriv_apply]
  simp [nonlinearEdgeCoordinates_fderiv, edgeLinearCoordinates,
    signedCoordinateFunctional_apply]

/-- The face-parametrization curvature part of the genuine chain expression. -/
theorem nonlinearEdge_curvature_hessian (h k : ℝ × ℝ) :
    fderiv ℝ (squaredSignedFiniteEndpointDifference ∘ orderedQ 1 1)
      (nonlinearEdgeCoordinates 0)
      (fderiv ℝ (fderiv ℝ nonlinearEdgeCoordinates) 0 h k) =
      8 * h.1 * k.1 := by
  rw [(squaredSignedFiniteEndpointDifference_hasFDerivAt 1 1
    (nonlinearEdgeCoordinates 0)).fderiv, nonlinearEdgeCoordinates_second_fderiv]
  simp [signedCoordinateFunctional_apply, nonlinearEdgeCoordinates,
    edgeDeathDirection, edgeDeathUnit]
  ring

/-- The derivative of the actual loss derivative exists, with both terms of
ordinary second-order chain calculus. -/
theorem nonlinearEdge_squared_loss_hasFDerivAt_fderiv :
    HasFDerivAt (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      (fun x => dgm (ZMod 2) (nonlinearEdgeFilter x) 0)))
      (secondDerivativeChain (squaredSignedFiniteEndpointDifference ∘ orderedQ 1 1)
        nonlinearEdgeCoordinates 0) 0 := by
  exact localLift_scalar_hasFDerivAt_fderiv _ _ 1 1 nonlinearEdgeLift 0
    nonlinearEdgeBox_zero (squaredSignedFiniteEndpointDifference_c2_all _)

/-- The actual scalar Hessian, identified by genuine derivative existence. -/
theorem nonlinearEdge_squared_loss_hessian (h k : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      (fun x => dgm (ZMod 2) (nonlinearEdgeFilter x) 0))) 0 h k =
      2 * (h.2 - h.1) * (k.2 - k.1) + 8 * h.1 * k.1 := by
  rw [nonlinearEdge_squared_loss_hasFDerivAt_fderiv.fderiv,
    secondDerivativeChain_apply, nonlinearEdge_coordinate_hessian,
    nonlinearEdge_curvature_hessian]

/-- Parameter-basis entries: the nonlinear face curvature raises `ss` from 2 to 10. -/
theorem nonlinearEdge_squared_loss_hessian_entries :
    let B := fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘
      (fun x => dgm (ZMod 2) (nonlinearEdgeFilter x) 0))) (0 : ℝ × ℝ)
    B (1, 0) (1, 0) = 10 ∧ B (1, 0) (0, 1) = -2 ∧
      B (0, 1) (1, 0) = -2 ∧ B (0, 1) (0, 1) = 2 := by
  simp only [nonlinearEdge_squared_loss_hessian]
  norm_num

/-- The two chain-rule contributions separately have the required parameter entries. -/
theorem nonlinearEdge_hessian_contribution_entries :
    let J := fderiv ℝ nonlinearEdgeCoordinates (0 : ℝ × ℝ)
    let A := fderiv ℝ (fderiv ℝ (squaredSignedFiniteEndpointDifference ∘ orderedQ 1 1))
      (nonlinearEdgeCoordinates 0)
    let C := fun h k => fderiv ℝ (squaredSignedFiniteEndpointDifference ∘ orderedQ 1 1)
      (nonlinearEdgeCoordinates 0) (fderiv ℝ (fderiv ℝ nonlinearEdgeCoordinates) 0 h k)
    (A (J (1, 0)) (J (1, 0)) = 2 ∧ A (J (1, 0)) (J (0, 1)) = -2 ∧
      A (J (0, 1)) (J (1, 0)) = -2 ∧ A (J (0, 1)) (J (0, 1)) = 2) ∧
    (C (1, 0) (1, 0) = 8 ∧ C (1, 0) (0, 1) = 0 ∧
      C (0, 1) (1, 0) = 0 ∧ C (0, 1) (0, 1) = 0) := by
  simp only [nonlinearEdge_coordinate_hessian, nonlinearEdge_curvature_hessian]
  norm_num

end TDA.Persistence.LossExamples
