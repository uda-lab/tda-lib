import TDA.Persistence.PersistenceMeasureEssentialContent
import TDA.Persistence.DecoratedRectangleTopology
import TDA.Persistence.IntegerContentAtoms
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Essential decorated multiplicities from the module content

The actual essential birth-strip content determines a minimum-cell multiplicity on birth
cuts. It is locally finite and reproduces every finite birth-strip count. These are the
points on the death-at-infinity boundary, without a fictitious module fiber at infinity.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory
open scoped Classical

private theorem exists_cut_topology :
    ∃ t : TopologicalSpace (Cut ℝ), (∀ U ∈ cutCells, @IsOpen _ t U) ∧
      (∀ U ∈ cutCells, @IsCompact _ t U) := by
  let : TopologicalSpace (LowerSet ℝ) := Preorder.topology _
  let : OrderTopology (LowerSet ℝ) := ⟨rfl⟩
  let : TopologicalSpace (Cut ℝ) := TopologicalSpace.induced cutLowerSetEquiv inferInstance
  let e := (cutLowerSetEquiv (α := ℝ)).toHomeomorphOfIsInducing ⟨rfl⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · rintro U ⟨a, b, _, rfl⟩
    exact e.isOpen_image.mp (isOpen_image_cutCell a b)
  · rintro U ⟨a, b, _, rfl⟩
    exact e.isCompact_image.mp (isCompact_image_cutCell a b)

private theorem cutCells_separate {K : Set (Cut ℝ)} (hK : K ∈ cutCells)
    (x : Cut ℝ) (hx : x ∈ K) (y : Cut ℝ) (hxy : x ≠ y) :
    ∃ U ∈ cutCells, x ∈ U ∧ y ∉ U := by
  obtain ⟨a, b, _, rfl⟩ := hK
  obtain ⟨a', b', _, _, hx', hy'⟩ := exists_subcell_separating_cuts hxy hx
  exact ⟨cutCell a' b', cutCell_mem_cutCells _ _, hx', hy'⟩

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- Canonical birth-cut multiplicity on the death-at-infinity boundary. -/
noncomputable def moduleEssentialMultiplicity (hM : M.QTame) (birth : Cut ℝ) : ℕ :=
  contentMultiplicity (essentialCutContent M hM) birth

/-- Positive essential multiplicities have finite support on every finite birth cell. -/
theorem moduleEssentialMultiplicity_locally_finite (hM : M.QTame)
    {K : Set (Cut ℝ)} (hK : K ∈ cutCells) :
    Set.Finite {birth | birth ∈ K ∧ 0 < moduleEssentialMultiplicity M hM birth} := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cut_topology
  let := t
  exact finite_positive_content_support isSetSemiring_cutCells
    (essentialCutContent M hM) hOpen (cutCells_separate hK) hK (hCompact K hK)

/-- The essential multiplicities recover every actual essential birth-cell content. -/
theorem moduleEssentialMultiplicity_content_counts (hM : M.QTame)
    {K : Set (Cut ℝ)} (hK : K ∈ cutCells) :
    ∃ S : Finset (Cut ℝ),
      (∀ birth, birth ∈ S ↔ birth ∈ K ∧ 0 < moduleEssentialMultiplicity M hM birth) ∧
      essentialCutContent M hM K = ∑ birth ∈ S, moduleEssentialMultiplicity M hM birth := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cut_topology
  let := t
  exact content_eq_sum_multiplicity isSetSemiring_cutCells
    (essentialCutContent M hM) hOpen (cutCells_separate hK) hK (hCompact K hK)

/-- Essential strip quotient counts equal the sums of the actual extracted boundary points. -/
theorem moduleEssentialMultiplicity_strip_counts (hM : M.QTame) {a b : ℝ} (hab : a ≤ b) :
    ∃ S : Finset (Cut ℝ),
      (∀ birth, birth ∈ S ↔ birth ∈ cutCell a b ∧ 0 < moduleEssentialMultiplicity M hM birth) ∧
      essentialMeasureValue M hab = ∑ birth ∈ S, moduleEssentialMultiplicity M hM birth := by
  obtain ⟨S, hS, hcount⟩ := moduleEssentialMultiplicity_content_counts M hM
    (cutCell_mem_cutCells a b)
  exact ⟨S, hS, (essentialCutContent_apply M hM hab).symm.trans hcount⟩

/-- A positive essential birth-strip count produces a genuine positive essential atom. -/
theorem exists_moduleEssential_atom_of_positive (hM : M.QTame)
    {K : Set (Cut ℝ)} (hK : K ∈ cutCells) (hpos : 0 < essentialCutContent M hM K) :
    ∃ birth ∈ K, 0 < moduleEssentialMultiplicity M hM birth := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cut_topology
  let := t
  exact exists_positive_content_atom isSetSemiring_cutCells
    (essentialCutContent M hM) hOpen hK (hCompact K hK) hpos

/-- Each containing essential cell bounds its point multiplicities. -/
theorem moduleEssentialMultiplicity_le_content (hM : M.QTame)
    {K : Set (Cut ℝ)} (hK : K ∈ cutCells) {birth : Cut ℝ} (hb : birth ∈ K) :
    moduleEssentialMultiplicity M hM birth ≤ essentialCutContent M hM K :=
  contentMultiplicity_le _ hK hb

/-- A positive essential birth is seen by a finite birth cell. -/
theorem moduleEssentialMultiplicity_visible_of_pos (hM : M.QTame)
    {birth : Cut ℝ} (hb : 0 < moduleEssentialMultiplicity M hM birth) :
    ∃ U ∈ cutCells, birth ∈ U := by
  obtain ⟨n, U, hU, hbU, _⟩ := Nat.nonempty_of_pos_sInf hb
  exact ⟨U, hU, hbU⟩

end TDA.Persistence.RectangleMeasure
