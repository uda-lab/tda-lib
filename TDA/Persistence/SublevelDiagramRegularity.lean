import TDA.Persistence.SmoothFaceLift
import TDA.Persistence.DiagramRegularity
import Mathlib.Data.List.NodupEquivFin

/-! Fixed regular face coordinates for sublevel persistence diagrams. -/

set_option autoImplicit false

universe u v
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration
open scoped ContDiff

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Each coordinate of the full template is a selected face value. The order
index may be zero, finite, or infinite. -/
theorem fixedFaceLift_contDiffOn_cr (r : ℕ∞ω) (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) {U : Set E}
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ r (fun x => (F x).value s) U) :
    ContDiffOn ℝ r (fixedFaceLift k F e n) U := by
  apply ContDiffOn.prodMk
  · apply contDiffOn_pi.mpr
    intro i
    exact (hF (e.enum ((faceTemplatePairs k e n).toList.get i).1)).prodMk
      (hF (e.enum ((faceTemplatePairs k e n).toList.get i).2))
  · apply contDiffOn_pi.mpr
    intro i
    exact hF (e.enum ((faceTemplateEssential k e n).toList.get i))

/-- The fixed full template is a `Cʳ` lift on the stated open domain. -/
noncomputable def fixedFaceCrLift (r : ℕ∞ω) (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) {U : Set E}
    (hU : IsOpen U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ r (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x)) :
    LocalCrDiagramLift r (fun x => dgm k (F x) n)
      (faceLiftCounts k F e n).1 (faceLiftCounts k F e n).2 where
  carrier := U
  isOpen_carrier := hU
  coordinates := fixedFaceLift k F e n
  factorization := fixedFaceLift_factorization k F e n horder
  regular := fixedFaceLift_contDiffOn_cr k r F e n hF

/-- Scalar losses inherit `Cʳ` regularity from a fixed full template,
provided the loss is regular at every presentation of the base diagram. -/
theorem sublevelDiagram_scalar_contDiffOn_cr (r : ℕ∞ω)
    (F : E → FilterFunction K ℝ) {x₀ : E} {U : Set E}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ r (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (n : ℕ) (Vloss : Diagram ℝ → ℝ)
    (hV : CrThroughAllRepresentatives r Vloss (dgm k (F x₀) n)) :
    ∃ U' : Set E, IsOpen U' ∧ x₀ ∈ U' ∧ U' ⊆ U ∧
      ContDiffOn ℝ r (fun x => Vloss (dgm k (F x) n)) U' := by
  obtain ⟨e⟩ := exists_compatibleOrder (F x₀)
  simpa only [Function.comp_def, fixedFaceCrLift] using
    localLift_scalar_cr r (fun x => dgm k (F x) n) Vloss
      (faceLiftCounts k F e n).1 (faceLiftCounts k F e n).2
      (fixedFaceCrLift k r F e n hU hF horder) x₀ hx₀ hV

/-- Relative chamber membership supplies a neighborhood inside the domain;
face regularity is required only on that domain. -/
theorem sublevelDiagram_scalar_contDiffOn_cr_of_mem_relative_orderChamber
    (r : ℕ∞ω) (F : E → FilterFunction K ℝ) {D : Set E} (hD : IsOpen D)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ r (fun x => (F x).value s) D)
    {x₀ : E} (hx₀ : x₀ ∈ D)
    (hchamber : (⟨x₀, hx₀⟩ : D) ∈
      orderChamber (fun x : D => fun s : TotalFace K => (F x).value s))
    (n : ℕ) (Vloss : Diagram ℝ → ℝ)
    (hV : CrThroughAllRepresentatives r Vloss (dgm k (F x₀) n)) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ D ∧
      ContDiffOn ℝ r (fun x => Vloss (dgm k (F x) n)) U := by
  let G : D → FilterFunction K ℝ := fun x => F x
  have hcont : ∀ s : TotalFace K, Continuous (fun x : D => (G x).value s) := by
    intro s
    exact (hF s).continuousOn.domRestrict
  obtain ⟨W, hWo, hxW, _, hWoEq⟩ :=
    FilterFunction.exists_open_orderingEquivalent_of_mem_orderChamber
      G hcont hchamber
  let U : Set E := Subtype.val '' W
  have hU : IsOpen U := hD.isOpenMap_subtype_val W hWo
  have hxU : x₀ ∈ U := ⟨⟨x₀, hx₀⟩, hxW, rfl⟩
  have hUD : U ⊆ D := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hWoEq y hy
  obtain ⟨U', hU', hxU', hsubset, hs⟩ :=
    sublevelDiagram_scalar_contDiffOn_cr k r F hU hxU
      (fun s => (hF s).mono hUD) horder n Vloss hV
  exact ⟨U', hU', hxU', hsubset.trans hUD, hs⟩

/-- The strict finite index occurrences are selected once at the reference
filter. This is a multiset, so repeated occurrences are retained. -/
noncomputable def strictFacePairs (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) :
    Multiset (Fin (faceCount K) × Fin (faceCount K)) :=
  (faceTemplatePairs k e n).filter
    (fun p => (F x₀).value (e.enum p.1) < (F x₀).value (e.enum p.2))

/-- The strict pair occurrences in the order of the full template. Filtering
the list retains each occurrence, even when two pairs have equal indices. -/
noncomputable def strictFacePairList (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) :
    List (Fin (faceCount K) × Fin (faceCount K)) :=
  (faceTemplatePairs k e n).toList.filter
    (fun p => (F x₀).value (e.enum p.1) < (F x₀).value (e.enum p.2))

/-- Fixed counts after deleting the persistently tied finite slots. -/
noncomputable def strictFaceLiftCounts (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) : ℕ × ℕ :=
  ((strictFacePairList k F e n).length,
    (faceTemplateEssential k e n).toList.length)

/-- The reduced lift uses the fixed strict index list and all essential births. -/
noncomputable def strictFaceLift (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) :
    E → DiagramCoordinates (strictFaceLiftCounts k F e n).1
      (strictFaceLiftCounts k F e n).2 := fun x =>
  (fun i => pairValues (F x) e ((strictFacePairList k F e n).get i),
   fun i => birthValue (F x) e ((faceTemplateEssential k e n).toList.get i))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Every selected strict occurrence reads a fixed full-template slot. -/
private theorem strictFacePairList_sublist (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) :
    List.Sublist (strictFacePairList k F e n) (faceTemplatePairs k e n).toList := by
  exact List.filter_sublist

/-- A fixed index map selects each reduced finite coordinate from the full
template. It is chosen before any parameter is evaluated. -/
noncomputable def strictFaceSlotEmbedding (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) :
    Fin (strictFaceLiftCounts k F e n).1 ↪o
      Fin (faceLiftCounts k F e n).1 :=
  (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (strictFacePairList_sublist k F e n)).choose

/-- Each retained occurrence has a distinct original full-template slot. -/
noncomputable def strictFaceSlotIndex (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ)
    (i : Fin (strictFaceLiftCounts k F e n).1) :
    Fin (faceLiftCounts k F e n).1 :=
  strictFaceSlotEmbedding k F e n i

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem strictFaceSlotIndex_injective (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) :
    Function.Injective (strictFaceSlotIndex k F e n) :=
  (strictFaceSlotEmbedding k F e n).injective

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem strictFaceLift_eq_fixed_projection (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) (x : E) :
    strictFaceLift k F e n x =
      (fun i => (fixedFaceLift k F e n x).1 (strictFaceSlotIndex k F e n i),
        (fixedFaceLift k F e n x).2) := by
  apply Prod.ext
  · funext i
    exact congrArg (pairValues (F x) e)
      ((List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (strictFacePairList_sublist k F e n)).choose_spec i)
  · rfl

/-- Finite coordinate selection preserves `Cʳ`, including when the strict
or essential index list is empty. -/
theorem strictFaceLift_contDiffOn_cr (r : ℕ∞ω) (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) {U : Set E}
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ r (fun x => (F x).value s) U) :
    ContDiffOn ℝ r (strictFaceLift k F e n) U := by
  apply ContDiffOn.prodMk
  · apply contDiffOn_pi.mpr
    intro i
    exact (hF (e.enum ((strictFacePairList k F e n).get i).1)).prodMk
      (hF (e.enum ((strictFacePairList k F e n).get i).2))
  · apply contDiffOn_pi.mpr
    intro i
    exact hF (e.enum ((faceTemplateEssential k e n).toList.get i))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A selected index is strict exactly when its evaluated endpoints are
unequal anywhere in the ordering-equivalent chamber. -/
private theorem strict_iff_unequal (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ)
    (x : E) (horder : OrderingEquivalent (F x₀) (F x))
    (p : Fin (faceCount K) × Fin (faceCount K))
    (hp : p ∈ faceTemplatePairs k e n) :
    ((F x₀).value (e.enum p.1) < (F x₀).value (e.enum p.2)) ↔
      (pairValues (F x) e p).1 ≠ (pairValues (F x) e p).2 := by
  have hpord := (faceTemplatePairs_lt k e n p hp).le
  have hle₀ := e.monotone hpord
  rw [lt_iff_le_and_ne]
  have hne := not_congr (horder.value_eq_iff (e.enum p.1) (e.enum p.2))
  exact ⟨fun h => hne.mp h.2, fun h => ⟨hle₀, hne.mpr h⟩⟩

/-- The strict lift and the full lift represent the same diagram on
the whole order chamber. No values are resorted at the parameter. -/
theorem strictFaceLift_factorization (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ)
    {U : Set E} (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x)) :
    ∀ x ∈ U, dgm k (F x) n =
      orderedQ (strictFaceLiftCounts k F e n).1
        (strictFaceLiftCounts k F e n).2 (strictFaceLift k F e n x) := by
  intro x hx
  rw [fixedFaceLift_factorization k F e n horder x hx]
  apply (orderedQ_eq_iff _ _ _ _ _ _).mpr
  constructor
  · change (Multiset.ofList (List.ofFn (fun i =>
        pairValues (F x) e ((faceTemplatePairs k e n).toList.get i)))).filter
        (fun p => p.1 ≠ p.2) =
      (Multiset.ofList (List.ofFn (fun i =>
        pairValues (F x) e ((strictFacePairList k F e n).get i)))).filter
        (fun p => p.1 ≠ p.2)
    simp only [List.ofFn_comp', List.ofFn_get, ← Multiset.map_coe]
    rw [Multiset.filter_map, Multiset.filter_map]
    rw [show (strictFacePairList k F e n : Multiset _) =
      strictFacePairs k F e n by
        simp only [strictFacePairList, strictFacePairs, ← Multiset.filter_coe,
          Multiset.coe_toList], Multiset.coe_toList]
    unfold strictFacePairs
    rw [Multiset.filter_filter]
    congr 1
    apply Multiset.filter_congr
    intro p hp
    simp only [Function.comp_apply]
    exact ⟨fun h => ⟨h, (strict_iff_unequal k F e n x (horder x hx) p hp).mpr h⟩,
      fun h => h.1⟩
  · simp [strictFaceLift, strictFaceLiftCounts, fixedFaceLift, faceLiftCounts]

/-- The reduced template is a `Cʳ` local lift with fixed counts. -/
noncomputable def strictFaceCrLift (r : ℕ∞ω) (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) {U : Set E}
    (hU : IsOpen U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ r (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x)) :
    LocalCrDiagramLift r (fun x => dgm k (F x) n)
      (strictFaceLiftCounts k F e n).1 (strictFaceLiftCounts k F e n).2 where
  carrier := U
  isOpen_carrier := hU
  coordinates := strictFaceLift k F e n
  factorization := strictFaceLift_factorization k F e n horder
  regular := strictFaceLift_contDiffOn_cr k r F e n hF

end TDA.Persistence
