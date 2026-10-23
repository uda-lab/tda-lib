import TDA.Persistence.PersistenceMeasureContent
import TDA.Persistence.DecoratedRectangleTopology
import TDA.Persistence.DecoratedCutEndpoints
import TDA.Persistence.IntegerContentAtoms
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Canonical decorated multiplicities from a q-tame module

Minimum containing-rectangle contents define the module's finite-death decorated
multiplicity. Compact open cut cells yield finite support in every separated rectangle
and exact reconstruction of every rectangle quotient dimension. No interval decomposition
or diagram-existence certificate is supplied as input. Essential boundary points and
algebraic stability are separate results.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory
open scoped Classical

private theorem exists_cutPair_topology :
    ∃ t : TopologicalSpace (Cut ℝ × Cut ℝ),
      (∀ U ∈ separatedRectangleCells, @IsOpen _ t U) ∧
      (∀ U ∈ separatedRectangleCells, @IsCompact _ t U) := by
  let : TopologicalSpace (LowerSet ℝ) := Preorder.topology _
  let : OrderTopology (LowerSet ℝ) := ⟨rfl⟩
  let : TopologicalSpace (Cut ℝ × Cut ℝ) :=
    TopologicalSpace.induced rectangleLowerSetEquiv inferInstance
  let e := (rectangleLowerSetEquiv (α := ℝ)).toHomeomorphOfIsInducing ⟨rfl⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · rintro U (rfl | ⟨a, b, c, d, _, _, _, rfl⟩)
    · exact isOpen_empty
    · exact e.isOpen_image.mp (isOpen_image_rectangleCell a b c d)
  · rintro U (rfl | ⟨a, b, c, d, _, _, _, rfl⟩)
    · exact isCompact_empty
    · exact e.isCompact_image.mp (isCompact_image_rectangleCell a b c d)

private theorem separatedRectangleCells_separate {K : Set (Cut ℝ × Cut ℝ)}
    (hK : K ∈ separatedRectangleCells) (x : Cut ℝ × Cut ℝ) (hx : x ∈ K)
    (y : Cut ℝ × Cut ℝ) (hxy : x ≠ y) :
    ∃ U ∈ separatedRectangleCells, x ∈ U ∧ y ∉ U := by
  rcases hK with rfl | ⟨a, b, c, d, _, hbc, _, rfl⟩
  · exact hx.elim
  · exact exists_rectangleCell_separating hxy hbc hx

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- Canonical finite-death decorated multiplicity, extracted from the module's actual
rectangle content by a minimum over containing rectangles. -/
noncomputable def moduleDiagramMultiplicity (hM : M.QTame) (p : Cut ℝ × Cut ℝ) : ℕ :=
  contentMultiplicity (moduleRectangleContent M hM) p

/-- No positive multiplicity is assigned to a point invisible to every separated rectangle. -/
theorem moduleDiagramMultiplicity_eq_zero_of_not_visible (hM : M.QTame)
    (p : Cut ℝ × Cut ℝ) (hp : ¬ ∃ U ∈ separatedRectangleCells, p ∈ U) :
    moduleDiagramMultiplicity M hM p = 0 := by
  have hempty : {n | ∃ U ∈ separatedRectangleCells, p ∈ U ∧
      moduleRectangleContent M hM U = n} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro n ⟨U, hU, hpU, _⟩
    exact hp ⟨U, hU, hpU⟩
  simp only [moduleDiagramMultiplicity, contentMultiplicity, hempty, Nat.sInf_empty]

/-- Every positive finite-death diagram point is seen by an actual separated rectangle. -/
theorem moduleDiagramMultiplicity_visible_of_pos (hM : M.QTame)
    {p : Cut ℝ × Cut ℝ} (hp : 0 < moduleDiagramMultiplicity M hM p) :
    ∃ U ∈ separatedRectangleCells, p ∈ U := by
  by_contra hn
  have hz := moduleDiagramMultiplicity_eq_zero_of_not_visible M hM p hn
  omega

/-- Positive finite-death diagram points have strictly ordered finite numeric endpoints. -/
theorem moduleDiagramMultiplicity_endpoints_lt (hM : M.QTame)
    {p : Cut ℝ × Cut ℝ} (hp : 0 < moduleDiagramMultiplicity M hM p) :
    cutEndpoint p.1 < cutEndpoint p.2 := by
  obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hp
  rcases hU with rfl | ⟨a, b, c, d, _, hbc, _, rfl⟩
  · exact hpU.elim
  · exact cutEndpoint_lt_of_mem_rectangleCell hbc hpU

/-- Every containing cell bounds the extracted multiplicity by its actual module content. -/
theorem moduleDiagramMultiplicity_le_content (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells)
    {p : Cut ℝ × Cut ℝ} (hp : p ∈ K) :
    moduleDiagramMultiplicity M hM p ≤ moduleRectangleContent M hM K :=
  contentMultiplicity_le _ hK hp

/-- A positive rectangle content produces an actual positive decorated point. -/
theorem exists_moduleDiagram_atom_of_positive (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells)
    (hpos : 0 < moduleRectangleContent M hM K) :
    ∃ p ∈ K, 0 < moduleDiagramMultiplicity M hM p := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cutPair_topology
  let := t
  exact exists_positive_content_atom isSetSemiring_separatedRectangleCells
    (moduleRectangleContent M hM) hOpen hK (hCompact K hK) hpos

/-- Positive decorated multiplicities have finite support in each separated rectangle. -/
theorem moduleDiagramMultiplicity_locally_finite (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells) :
    Set.Finite {p | p ∈ K ∧ 0 < moduleDiagramMultiplicity M hM p} := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cutPair_topology
  let := t
  exact finite_positive_content_support isSetSemiring_separatedRectangleCells
    (moduleRectangleContent M hM) hOpen (separatedRectangleCells_separate hK) hK (hCompact K hK)

/-- The constructed multiplicities reproduce each cell's actual module content exactly. -/
theorem moduleDiagramMultiplicity_content_counts (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ K ∧ 0 < moduleDiagramMultiplicity M hM p) ∧
      moduleRectangleContent M hM K = ∑ p ∈ S, moduleDiagramMultiplicity M hM p := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cutPair_topology
  let := t
  exact content_eq_sum_multiplicity isSetSemiring_separatedRectangleCells
    (moduleRectangleContent M hM) hOpen (separatedRectangleCells_separate hK) hK (hCompact K hK)

/-- Every strict separated persistence rectangle counts exactly the constructed decorated
point multiplicities it contains. -/
theorem moduleDiagramMultiplicity_rectangle_counts (hM : M.QTame) (a b c d : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ rectangleCell a b c d ∧ 0 < moduleDiagramMultiplicity M hM p) ∧
      persistenceMeasureValue M hab.le hbc.le hcd.le =
        ∑ p ∈ S, moduleDiagramMultiplicity M hM p := by
  obtain ⟨S, hS, hcount⟩ := moduleDiagramMultiplicity_content_counts M hM
    (rectangleCell_mem_separatedRectangleCells a b c d hbc)
  exact ⟨S, hS, (moduleRectangleContent_apply M hM a b c d hab hbc hcd).symm.trans hcount⟩

end TDA.Persistence.RectangleMeasure
