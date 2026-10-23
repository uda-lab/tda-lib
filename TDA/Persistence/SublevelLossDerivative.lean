import TDA.Persistence.SmoothFaceLift
import TDA.Persistence.FaceEndpointUniqueness
import TDA.Persistence.DiagramCalculus

/-!
# Derivatives of scalar losses on sublevel persistence diagrams

The finite coordinates below are the *full* fixed template.  In particular a
pair tied along the parameter family still has both of its real coordinates.
-/

set_option autoImplicit false

universe u v
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : E → FilterFunction K ℝ) {x₀ : E}
variable (e : CompatibleOrder (F x₀)) (p : ℕ)

/-- One label for every real coordinate in the full degree-`p` template. -/
abbrev FaceLossSlot : Type :=
  (Fin (faceLiftCounts k F e p).1 ⊕ Fin (faceLiftCounts k F e p).1) ⊕
    Fin (faceLiftCounts k F e p).2

/-- The fixed entering-face index for each real coordinate. -/
noncomputable def faceLossSlotIndex (j : FaceLossSlot k F e p) : Fin (faceCount K) :=
  match j with
  | .inl (.inl i) => ((faceTemplatePairs k e p).toList.get i).1
  | .inl (.inr i) => ((faceTemplatePairs k e p).toList.get i).2
  | .inr i => ((faceTemplateEssential k e p).toList.get i)

/-- The entering face for a finite birth, finite death, or essential birth. -/
noncomputable def faceLossSlotFace (j : FaceLossSlot k F e p) : TotalFace K :=
  e.enum (faceLossSlotIndex k F e p j)

private noncomputable def endpointIndexMultiset : Multiset (Fin (faceCount K)) :=
  (faceTemplatePairs k e p).map Prod.fst +
    (faceTemplatePairs k e p).map Prod.snd + faceTemplateEssential k e p

/-- The joint endpoint theorem says that the multiset of all roles has no
repeated face index, even if the corresponding real values coincide. -/
private theorem endpointIndexMultiset_nodup :
    (endpointIndexMultiset k F e p).Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro i
  have h := faceTemplate_endpoint_count_le_one k e i p
  simpa only [endpointIndexMultiset, Multiset.count_add, Multiset.count_map,
    Multiset.countP_eq_card_filter, eq_comm, add_assoc, add_comm, add_left_comm] using h

/-- Every slot in the full template selects a different face. -/
theorem faceLossSlotFace_injective :
    Function.Injective (faceLossSlotFace k F e p) := by
  classical
  let P := faceTemplatePairs k e p
  let C := faceTemplateEssential k e p
  let A := P.map Prod.fst
  let B := P.map Prod.snd
  have hM : (A + B + C).Nodup := endpointIndexMultiset_nodup k F e p
  have hAB : (A + B).Nodup := (Multiset.nodup_add.mp hM).1
  have hA : A.Nodup := (Multiset.nodup_add.mp hAB).1
  have hB : B.Nodup := (Multiset.nodup_add.mp hAB).2.1
  have hC : C.Nodup := (Multiset.nodup_add.mp hM).2.1
  have hABdis : Disjoint A B := (Multiset.nodup_add.mp hAB).2.2
  have hACdis : Disjoint A C :=
    (Multiset.disjoint_add_left.mp (Multiset.nodup_add.mp hM).2.2).1
  have hBCdis : Disjoint B C :=
    (Multiset.disjoint_add_left.mp (Multiset.nodup_add.mp hM).2.2).2
  have hAget : Function.Injective (fun i : Fin P.toList.length => (P.toList.get i).1) := by
    have hd : (P.toList.map Prod.fst).Nodup := by
      have hm : (↑(P.toList.map Prod.fst) : Multiset _) = A := by
        simp only [← Multiset.map_coe, Multiset.coe_toList]
        rfl
      exact Multiset.coe_nodup.mp (hm.symm ▸ hA)
    intro i j hij
    have hij' : (P.toList.map Prod.fst).get
        ⟨i.val, by simpa using i.isLt⟩ =
        (P.toList.map Prod.fst).get ⟨j.val, by simpa using j.isLt⟩ := by
      simpa [List.get, List.getElem_map] using hij
    have hv := congrArg (fun t : Fin (P.toList.map Prod.fst).length => t.val)
      (hd.injective_get hij')
    exact Fin.ext hv
  have hBget : Function.Injective (fun i : Fin P.toList.length => (P.toList.get i).2) := by
    have hd : (P.toList.map Prod.snd).Nodup := by
      have hm : (↑(P.toList.map Prod.snd) : Multiset _) = B := by
        simp only [← Multiset.map_coe, Multiset.coe_toList]
        rfl
      exact Multiset.coe_nodup.mp (hm.symm ▸ hB)
    intro i j hij
    have hij' : (P.toList.map Prod.snd).get
        ⟨i.val, by simpa using i.isLt⟩ =
        (P.toList.map Prod.snd).get ⟨j.val, by simpa using j.isLt⟩ := by
      simpa [List.get, List.getElem_map] using hij
    have hv := congrArg (fun t : Fin (P.toList.map Prod.snd).length => t.val)
      (hd.injective_get hij')
    exact Fin.ext hv
  have hCget : Function.Injective (fun i : Fin C.toList.length => C.toList.get i) := by
    have hd : C.toList.Nodup := by
      have hm : (↑C.toList : Multiset _) = C := by simp
      exact Multiset.coe_nodup.mp (hm.symm ▸ hC)
    exact hd.injective_get
  have hAmem (i : Fin P.toList.length) : (P.toList.get i).1 ∈ A := by
    exact Multiset.mem_map.mpr ⟨P.toList.get i,
      Multiset.mem_toList.mp (List.get_mem P.toList i), rfl⟩
  have hBmem (i : Fin P.toList.length) : (P.toList.get i).2 ∈ B := by
    exact Multiset.mem_map.mpr ⟨P.toList.get i,
      Multiset.mem_toList.mp (List.get_mem P.toList i), rfl⟩
  have hCmem (i : Fin C.toList.length) : C.toList.get i ∈ C :=
    Multiset.mem_toList.mp (List.get_mem C.toList i)
  intro j j' h
  have hi := e.enum.injective h
  rcases j with ((i | i) | i) <;> rcases j' with ((j | j) | j)
  all_goals simp only [faceLossSlotIndex] at hi
  · exact congrArg (fun a => Sum.inl (Sum.inl a)) (hAget hi)
  · exact ((Multiset.disjoint_left.mp hABdis) (hAmem i) (hi ▸ hBmem j)).elim
  · exact ((Multiset.disjoint_left.mp hACdis) (hAmem i) (hi ▸ hCmem j)).elim
  · exact ((Multiset.disjoint_left.mp hABdis) (hAmem j) (hi.symm ▸ hBmem i)).elim
  · exact congrArg (fun a => Sum.inl (Sum.inr a)) (hBget hi)
  · exact ((Multiset.disjoint_left.mp hBCdis) (hBmem i) (hi ▸ hCmem j)).elim
  · exact ((Multiset.disjoint_left.mp hACdis) (hAmem j) (hi.symm ▸ hCmem i)).elim
  · exact ((Multiset.disjoint_left.mp hBCdis) (hBmem j) (hi.symm ▸ hCmem i)).elim
  · exact congrArg Sum.inr (hCget hi)

/-- Read one real coordinate, including the two roles of a diagonal pair. -/
def faceLossSlotRead (j : FaceLossSlot k F e p)
    (z : DiagramCoordinates (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2) : ℝ :=
  match j with
  | .inl (.inl i) => (z.1 i).1
  | .inl (.inr i) => (z.1 i).2
  | .inr i => z.2 i

/-- Pack scalar slot coordinates into the library's ordered presentation. -/
def faceLossSlotPack (w : FaceLossSlot k F e p → ℝ) :
    DiagramCoordinates (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2 :=
  (fun i => (w (.inl (.inl i)), w (.inl (.inr i))), fun i => w (.inr i))

@[simp] theorem faceLossSlotRead_pack (w : FaceLossSlot k F e p → ℝ)
    (j : FaceLossSlot k F e p) :
    faceLossSlotRead k F e p j (faceLossSlotPack k F e p w) = w j := by
  rcases j with ((i | i) | i) <;> rfl

/-- All face values, with the finite-product maximum norm. -/
def allFaceValues (x : E) : TotalFace K → ℝ := fun s => (F x).value s

/-- Selection of the face values into every finite and essential slot. -/
noncomputable def faceValueSelectionLinear :
    (TotalFace K → ℝ) →ₗ[ℝ]
      DiagramCoordinates (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2 where
  toFun v := faceLossSlotPack k F e p (fun j => v (faceLossSlotFace k F e p j))
  map_add' := by
    intro a b
    apply Prod.ext
    · funext i
      apply Prod.ext <;> rfl
    · funext i
      rfl
  map_smul' := by
    intro c a
    apply Prod.ext
    · funext i
      apply Prod.ext <;> rfl
    · funext i
      rfl

private theorem faceValueSelectionLinear_norm_le (v : TotalFace K → ℝ) :
    ‖faceValueSelectionLinear k F e p v‖ ≤ ‖v‖ := by
  apply (norm_prod_le_iff).2
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
    intro i
    apply (norm_prod_le_iff).2
    exact ⟨norm_le_pi_norm v _, norm_le_pi_norm v _⟩
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
    intro i
    exact norm_le_pi_norm v _

/-- Coordinate selection is nonexpansive for the finite-product maximum norms,
including when either coordinate block is empty. -/
noncomputable def faceValueSelection :
    (TotalFace K → ℝ) →L[ℝ]
      DiagramCoordinates (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2 :=
  (faceValueSelectionLinear k F e p).mkContinuous 1 (by
    intro v
    simpa using faceValueSelectionLinear_norm_le k F e p v)

theorem faceValueSelection_norm_le_one : ‖faceValueSelection k F e p‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one (by
    intro v
    simpa using faceValueSelectionLinear_norm_le k F e p v)

/-- The fixed lift is the linear selection of the complete face-value vector. -/
theorem fixedFaceLift_eq_selection (x : E) :
    fixedFaceLift k F e p x =
      faceValueSelection k F e p (allFaceValues F x) := by
  rfl

/-- The standard coordinate unit vector in the full ordered presentation. -/
noncomputable def faceLossUnit (j : FaceLossSlot k F e p) :
    DiagramCoordinates (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2 :=
  faceLossSlotPack k F e p (Pi.single (M := fun _ : FaceLossSlot k F e p => ℝ) j 1)

theorem faceValueSelection_single_eq_unit (j : FaceLossSlot k F e p) :
    faceValueSelection k F e p
      (Pi.single (M := fun _ : TotalFace K => ℝ) (faceLossSlotFace k F e p j) 1) =
      faceLossUnit k F e p j := by
  have hinj := faceLossSlotFace_injective k F e p
  change faceLossSlotPack k F e p
      (fun j' => (Pi.single (M := fun _ : TotalFace K => ℝ)
        (faceLossSlotFace k F e p j) (1 : ℝ))
        (faceLossSlotFace k F e p j')) =
    faceLossSlotPack k F e p
      (Pi.single (M := fun _ : FaceLossSlot k F e p => ℝ) j 1)
  congr 1
  funext j'
  simp only [Pi.single_apply, hinj.eq_iff]

theorem faceValueSelection_single_eq_zero (s : TotalFace K)
    (h : s ∉ Set.range (faceLossSlotFace k F e p)) :
    faceValueSelection k F e p (Pi.single (M := fun _ : TotalFace K => ℝ) s 1) = 0 := by
  change faceLossSlotPack k F e p
      (fun j => (Pi.single (M := fun _ : TotalFace K => ℝ) s (1 : ℝ))
        (faceLossSlotFace k F e p j)) = 0
  have hz : (fun j => (Pi.single (M := fun _ : TotalFace K => ℝ) s (1 : ℝ))
      (faceLossSlotFace k F e p j)) = 0 := by
    funext j
    have hne : s ≠ faceLossSlotFace k F e p j := by
      intro heq
      exact h ⟨j, heq.symm⟩
    simp [Pi.single_apply, hne]
  rw [hz]
  rfl

/-- A selected coordinate differentiates as the corresponding face
value. The formula is valid for every slot, including diagonal pairs. -/
theorem fixedFaceLift_slot_derivative {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (j : FaceLossSlot k F e p) (h : E) :
    faceLossSlotRead k F e p j (fderiv ℝ (fixedFaceLift k F e p) x₀ h) =
      fderiv ℝ (fun x => (F x).value (faceLossSlotFace k F e p j)) x₀ h := by
  have hG : DifferentiableAt ℝ (allFaceValues F) x₀ :=
    ((contDiffOn_pi.mpr hF).contDiffAt (hU.mem_nhds hx)).differentiableAt_one
  have hL : fderiv ℝ (fixedFaceLift k F e p) x₀ =
      (faceValueSelection k F e p).comp (fderiv ℝ (allFaceValues F) x₀) := by
    have hc := ((faceValueSelection k F e p).hasFDerivAt.comp x₀
      hG.hasFDerivAt).fderiv
    simpa only [Function.comp_def, ← fixedFaceLift_eq_selection] using hc
  rw [hL]
  simp only [ContinuousLinearMap.comp_apply]
  have hs : faceLossSlotRead k F e p j
      (faceValueSelection k F e p (fderiv ℝ (allFaceValues F) x₀ h)) =
      (fderiv ℝ (allFaceValues F) x₀ h) (faceLossSlotFace k F e p j) := by
    rcases j with ((i | i) | i) <;> rfl
  rw [hs]
  change (fderiv ℝ (fun x s => (F x).value s) x₀) h
      (faceLossSlotFace k F e p j) = _
  rw [fderiv_pi (fun s =>
    ((hF s).contDiffAt (hU.mem_nhds hx)).differentiableAt_one)]
  rfl

/-- The diagram family carries the merged smooth full-template lift. -/
noncomputable def fixedFaceC1Lift {U : Set E} (hU : IsOpen U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x)) :
    LocalDiagramLift (fun x => dgm k (F x) p)
      (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2 where
  carrier := U
  isOpen_carrier := hU
  coordinates := fixedFaceLift k F e p
  factorization := fixedFaceLift_factorization k F e p horder
  smooth := fixedFaceLift_contDiffOn k F e p hF

/-- The ambient partial derivative at one full-template slot. -/
noncomputable def faceLossSlotCoefficient (W : Diagram ℝ → ℝ)
    (j : FaceLossSlot k F e p) : ℝ :=
  fderiv ℝ (W ∘ orderedQ (faceLiftCounts k F e p).1
    (faceLiftCounts k F e p).2) (fixedFaceLift k F e p x₀)
      (faceLossUnit k F e p j)

/-- Scatter each slot weight to its unique face; unused faces receive zero. -/
noncomputable def faceLossCoefficient (W : Diagram ℝ → ℝ)
    (s : TotalFace K) : ℝ :=
  if h : s ∈ Set.range (faceLossSlotFace k F e p) then
    faceLossSlotCoefficient k F e p W (Classical.choose h)
  else 0

theorem faceLossCoefficient_selected (W : Diagram ℝ → ℝ)
    (j : FaceLossSlot k F e p) :
    faceLossCoefficient k F e p W (faceLossSlotFace k F e p j) =
      faceLossSlotCoefficient k F e p W j := by
  classical
  unfold faceLossCoefficient
  split_ifs with h
  · exact congrArg (faceLossSlotCoefficient k F e p W)
      ((faceLossSlotFace_injective k F e p) (Classical.choose_spec h))
  · exact (h ⟨j, rfl⟩).elim

theorem faceLossCoefficient_unused (W : Diagram ℝ → ℝ) (s : TotalFace K)
    (h : s ∉ Set.range (faceLossSlotFace k F e p)) :
    faceLossCoefficient k F e p W s = 0 := by
  simp [faceLossCoefficient, h]

theorem faceLossCoefficient_eq_basis (W : Diagram ℝ → ℝ)
    (s : TotalFace K) :
    faceLossCoefficient k F e p W s =
      fderiv ℝ (W ∘ orderedQ (faceLiftCounts k F e p).1
        (faceLiftCounts k F e p).2) (fixedFaceLift k F e p x₀)
        (faceValueSelection k F e p
          (Pi.single (M := fun _ : TotalFace K => ℝ) s 1)) := by
  classical
  by_cases hs : s ∈ Set.range (faceLossSlotFace k F e p)
  · obtain ⟨j, rfl⟩ := hs
    rw [faceLossCoefficient_selected, faceValueSelection_single_eq_unit]
    rfl
  · rw [faceLossCoefficient_unused k F e p W s hs,
      faceValueSelection_single_eq_zero k F e p s hs]
    simp

theorem linearFunctional_face_sum {I : Type*} [Fintype I] [DecidableEq I]
    (T : (I → ℝ) →L[ℝ] ℝ) (v : I → ℝ) :
    T v = ∑ i : I, T (Pi.single (M := fun _ : I => ℝ) i 1) * v i := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Face-value derivatives are the coordinates of the derivative of the
complete face-value vector. -/
theorem allFaceValues_fderiv_apply {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (s : TotalFace K) (h : E) :
    fderiv ℝ (allFaceValues F) x₀ h s =
      fderiv ℝ (fun x => (F x).value s) x₀ h := by
  change (fderiv ℝ (fun x t => (F x).value t) x₀) h s = _
  rw [fderiv_pi (fun t =>
    ((hF t).contDiffAt (hU.mem_nhds hx)).differentiableAt_one)]
  rfl

/-- Linear selection commutes with the face-value derivative. -/
theorem fixedFaceLift_fderiv_eq_selection {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U) :
    fderiv ℝ (fixedFaceLift k F e p) x₀ =
      (faceValueSelection k F e p).comp (fderiv ℝ (allFaceValues F) x₀) := by
  have hG : DifferentiableAt ℝ (allFaceValues F) x₀ :=
    ((contDiffOn_pi.mpr hF).contDiffAt (hU.mem_nhds hx)).differentiableAt_one
  have hc := ((faceValueSelection k F e p).hasFDerivAt.comp x₀
    hG.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ← fixedFaceLift_eq_selection] using hc

/-- The scalar PH loss is `C¹` on an open neighborhood contained in
the original weak-order chamber. -/
theorem sublevelDiagramScalarLoss_c1_neighborhood
    (e : CompatibleOrder (F x₀)) (p : ℕ) {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    ∃ N : Set E, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ U ∧
      ContDiffOn ℝ 1 (fun x => W (dgm k (F x) p)) N := by
  obtain ⟨N, hNo, hNx, hNU, hNc⟩ :=
    localLift_scalar_c1 (fun x => dgm k (F x) p) W
      (faceLiftCounts k F e p).1 (faceLiftCounts k F e p).2
      (fixedFaceC1Lift k F e p hU hF horder) x₀ hx hW
  exact ⟨N, hNo, hNx, hNU, hNc⟩

/-- The Fréchet derivative of `x ↦ W (dgm k (F x) p)`, expressed as
a finite sum of derivatives of the face-value functions. -/
theorem sublevelDiagramScalarLoss_hasFDerivAt {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    HasFDerivAt (fun x => W (dgm k (F x) p))
      (∑ s : TotalFace K, faceLossCoefficient k F e p W s •
        fderiv ℝ (fun x => (F x).value s) x₀) x₀ := by
  classical
  let Q := (faceLiftCounts k F e p).1
  let H := (faceLiftCounts k F e p).2
  let D := fderiv ℝ (W ∘ orderedQ Q H) (fixedFaceLift k F e p x₀)
  let R := faceValueSelection k F e p
  let G := fderiv ℝ (allFaceValues F) x₀
  have hchain : HasFDerivAt (fun x => W (dgm k (F x) p))
      (D.comp (fderiv ℝ (fixedFaceLift k F e p) x₀)) x₀ := by
    simpa only [D, Function.comp_def, fixedFaceC1Lift] using
      localLift_scalar_hasFDerivAt (fun x => dgm k (F x) p) W Q H
        (fixedFaceC1Lift k F e p hU hF horder) x₀ hx hW
  have hder : D.comp (fderiv ℝ (fixedFaceLift k F e p) x₀) =
      ∑ s : TotalFace K, faceLossCoefficient k F e p W s •
        fderiv ℝ (fun x => (F x).value s) x₀ := by
    ext h
    rw [fixedFaceLift_fderiv_eq_selection k F e p hU hx hF]
    simp only [ContinuousLinearMap.comp_apply, Finset.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hexp : D (R (G h)) =
        ∑ s : TotalFace K,
          D (R (Pi.single (M := fun _ : TotalFace K => ℝ) s 1)) * (G h) s := by
      simpa only [ContinuousLinearMap.comp_apply] using
        linearFunctional_face_sum (D.comp R) (G h)
    change D (R (G h)) = _
    rw [hexp]
    calc
      (∑ s : TotalFace K,
          D (R (Pi.single (M := fun _ : TotalFace K => ℝ) s 1)) * (G h) s) =
          ∑ s : TotalFace K, faceLossCoefficient k F e p W s *
            fderiv ℝ (fun x => (F x).value s) x₀ h := by
              apply Finset.sum_congr rfl
              intro s _
              rw [faceLossCoefficient_eq_basis k F e p W s,
                allFaceValues_fderiv_apply F hU hx hF s h]
      _ = (∑ s : TotalFace K, faceLossCoefficient k F e p W s •
          fderiv ℝ (fun x => (F x).value s) x₀) h := by
            simp [Finset.sum_apply, smul_apply]
  rw [hder] at hchain
  exact hchain

/-- Equality with `fderiv` follows from the derivative-existence theorem. -/
theorem sublevelDiagramScalarLoss_fderiv {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    fderiv ℝ (fun x => W (dgm k (F x) p)) x₀ =
      ∑ s : TotalFace K, faceLossCoefficient k F e p W s •
        fderiv ℝ (fun x => (F x).value s) x₀ :=
  (sublevelDiagramScalarLoss_hasFDerivAt k F e p hU hx hF horder W hW).fderiv

/-- Quantitative operator-norm bound on the derivative functional. -/
theorem sublevelDiagramScalarLoss_norm_bound {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    ‖fderiv ℝ (fun x => W (dgm k (F x) p)) x₀‖ ≤
      ∑ s : TotalFace K, |faceLossCoefficient k F e p W s| *
        ‖fderiv ℝ (fun x => (F x).value s) x₀‖ := by
  rw [sublevelDiagramScalarLoss_fderiv k F e p hU hx hF horder W hW]
  calc
    ‖∑ s : TotalFace K, faceLossCoefficient k F e p W s •
        fderiv ℝ (fun x => (F x).value s) x₀‖ ≤
      ∑ s : TotalFace K, ‖faceLossCoefficient k F e p W s •
        fderiv ℝ (fun x => (F x).value s) x₀‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, Real.norm_eq_abs]

/-- Compatible template choices yield the same linear functional. This is a
consequence of derivative uniqueness and does not identify ambient coefficient
vectors across presentations. -/
theorem sublevelDiagramScalarLoss_derivative_independent
    (e' : CompatibleOrder (F x₀)) {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    (∑ s : TotalFace K, faceLossCoefficient k F e p W s •
      fderiv ℝ (fun x => (F x).value s) x₀) =
    (∑ s : TotalFace K, faceLossCoefficient k F e' p W s •
      fderiv ℝ (fun x => (F x).value s) x₀) := by
  rw [← sublevelDiagramScalarLoss_fderiv k F e p hU hx hF horder W hW,
    ← sublevelDiagramScalarLoss_fderiv k F e' p hU hx hF horder W hW]

/-- The preceding identity gives equal directional derivatives, including
after a permutation of the fixed occurrence labels. -/
theorem sublevelDiagramScalarLoss_direction_independent
    (e' : CompatibleOrder (F x₀)) {U : Set E} (hU : IsOpen U)
    (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) (h : E) :
    (∑ s : TotalFace K, faceLossCoefficient k F e p W s •
      fderiv ℝ (fun x => (F x).value s) x₀) h =
    (∑ s : TotalFace K, faceLossCoefficient k F e' p W s •
      fderiv ℝ (fun x => (F x).value s) x₀) h := by
  rw [sublevelDiagramScalarLoss_derivative_independent k F e p e' hU hx hF horder W hW]

/-- The empty complex has no face terms in the derivative sum. -/
theorem sublevelDiagramScalarLoss_empty_fderiv (hm : faceCount K = 0)
    {U : Set E} (hU : IsOpen U) (hx : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (W : Diagram ℝ → ℝ)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    fderiv ℝ (fun x => W (dgm k (F x) p)) x₀ = 0 := by
  obtain ⟨e⟩ := exists_compatibleOrder (F x₀)
  have : IsEmpty (TotalFace K) := Fintype.card_eq_zero_iff.mp hm
  simpa using sublevelDiagramScalarLoss_fderiv k F e p hU hx hF horder W hW

/-- More generally, every admissible smooth ordered lift of the same diagram family, including a permutation of fixed occurrence labels, produces
the same derivative functional. -/
theorem sublevelDiagramScalarLoss_any_lifts_independent
    (W : Diagram ℝ → ℝ) (m n m' n' : ℕ)
    (L : LocalDiagramLift (fun x => dgm k (F x) p) m n)
    (L' : LocalDiagramLift (fun x => dgm k (F x) p) m' n')
    (hx : x₀ ∈ L.carrier) (hx' : x₀ ∈ L'.carrier)
    (hW : C1ThroughAllRepresentatives W (dgm k (F x₀) p)) :
    (fderiv ℝ (W ∘ orderedQ m n) (L.coordinates x₀)).comp
        (fderiv ℝ L.coordinates x₀) =
      (fderiv ℝ (W ∘ orderedQ m' n') (L'.coordinates x₀)).comp
        (fderiv ℝ L'.coordinates x₀) :=
  localLift_scalar_derivative_independent (fun x => dgm k (F x) p)
    W m n m' n' L L' x₀ hx hx' hW

end TDA.Persistence
