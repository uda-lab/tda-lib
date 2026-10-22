import TDA.Persistence.FaceOrderTemplate
import TDA.Filtration.OrderChamberFilterFunction
import TDA.Filtration.CompatibleOrderExistence
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

/-!
Fixed face-index occurrences give smooth coordinates for sublevel diagrams.
The lists below enumerate index multisets once, before a parameter is evaluated.
-/

universe u v
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fixed number of finite and essential face-index occurrences. -/
noncomputable def faceLiftCounts {E : Type v} (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) : ℕ × ℕ :=
  ((faceTemplatePairs k e n).toList.length,
    (faceTemplateEssential k e n).toList.length)

/-- Evaluate fixed face-index occurrences, retaining repeated pairs and births. -/
noncomputable def fixedFaceLift (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ) :
    E → (Fin (faceLiftCounts k F e n).1 → ℝ × ℝ) ×
      (Fin (faceLiftCounts k F e n).2 → ℝ) := fun x =>
  (fun i => pairValues (F x) e ((faceTemplatePairs k e n).toList.get i),
   fun i => birthValue (F x) e ((faceTemplateEssential k e n).toList.get i))

/-- A fixed lift represents the degree-`n` sublevel diagram everywhere
that the reference enumeration stays compatible. -/
theorem fixedFaceLift_factorization (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ)
    {U : Set E} (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x)) :
    ∀ x ∈ U, dgm k (F x) n =
      orderedQ (faceLiftCounts k F e n).1 (faceLiftCounts k F e n).2
        (fixedFaceLift k F e n x) := by
  intro x hx
  have hm : Monotone ((F x).value ∘ e.enum) :=
    (horder x hx).monotone_comp e
  rw [← evaluateFaceTemplate_eq_dgm k e (F x) hm n]
  apply evaluateFaceTemplate_eq_orderedQ_of_enumerations k e (F x) hm n
  · simpa only [fixedFaceLift, faceLiftCounts, List.ofFn_comp',
      List.ofFn_get, ← Multiset.map_coe, Multiset.coe_toList]
  · simpa only [fixedFaceLift, faceLiftCounts, List.ofFn_comp',
      List.ofFn_get, ← Multiset.map_coe, Multiset.coe_toList]

/-- The same coordinate map is C¹ on the original neighborhood. -/
theorem fixedFaceLift_contDiffOn (F : E → FilterFunction K ℝ)
    {x₀ : E} (e : CompatibleOrder (F x₀)) (n : ℕ)
    {U : Set E}
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U) :
    ContDiffOn ℝ 1 (fixedFaceLift k F e n) U := by
  apply ContDiffOn.prodMk
  · apply contDiffOn_pi.mpr
    intro i
    exact (hF (e.enum ((faceTemplatePairs k e n).toList.get i).1)).prodMk
      (hF (e.enum ((faceTemplatePairs k e n).toList.get i).2))
  · apply contDiffOn_pi.mpr
    intro i
    exact hF (e.enum ((faceTemplateEssential k e n).toList.get i))

/-- A whole open weak-order neighborhood has one C¹ lift of its diagrams,
with fixed counts and fixed face-index labels. -/
theorem exists_smooth_face_lift (F : E → FilterFunction K ℝ)
    {x₀ : E} {U : Set E} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) U)
    (horder : ∀ x ∈ U, OrderingEquivalent (F x₀) (F x))
    (n : ℕ) :
    ∃ (m l : ℕ) (L : E → (Fin m → ℝ × ℝ) × (Fin l → ℝ)),
      (∀ x ∈ U, dgm k (F x) n = orderedQ m l (L x)) ∧
      ContDiffOn ℝ 1 L U := by
  obtain ⟨e⟩ := exists_compatibleOrder (F x₀)
  exact ⟨(faceLiftCounts k F e n).1, (faceLiftCounts k F e n).2,
    fixedFaceLift k F e n,
    fixedFaceLift_factorization k F e n horder,
    fixedFaceLift_contDiffOn k F e n hF⟩


/-- On an open ambient domain, chamber membership for the restricted family
supplies an ambient neighborhood. No regularity is required beyond the domain. -/
theorem exists_smooth_face_lift_of_mem_relative_orderChamber
    (F : E → FilterFunction K ℝ) {D : Set E} (hD : IsOpen D)
    (hF : ∀ s : TotalFace K, ContDiffOn ℝ 1 (fun x => (F x).value s) D)
    {x₀ : E} (hx₀ : x₀ ∈ D)
    (hchamber : (⟨x₀, hx₀⟩ : D) ∈
      orderChamber (fun x : D => fun s : TotalFace K => (F x).value s))
    (n : ℕ) :
    ∃ (U : Set E), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ D ∧
      ∃ (m l : ℕ) (L : E → (Fin m → ℝ × ℝ) × (Fin l → ℝ)),
        (∀ x ∈ U, dgm k (F x) n = orderedQ m l (L x)) ∧
        ContDiffOn ℝ 1 L U := by
  let G : D → FilterFunction K ℝ := fun x => F x
  have hcont : ∀ s : TotalFace K,
      Continuous (fun x : D => (G x).value s) := by
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
  obtain ⟨m, l, L, hfactor, hsmooth⟩ :=
    exists_smooth_face_lift k F hU hxU (fun s => (hF s).mono hUD)
      horder n
  exact ⟨U, hU, hxU, hUD, m, l, L, hfactor, hsmooth⟩

end TDA.Persistence
