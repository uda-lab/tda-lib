import TDA.Persistence.PersistenceMeasureExtendedDiagram
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Set.Countable

/-!
# Countable support of the extracted decorated diagram

Rational separated rectangles cover the positive finite-death support. Rational birth
cells cover the essential support. Each member has finite support, so the actual global
diagram support is countable, without any finite-total-mass hypothesis.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open Set

private abbrev RationalRectangle :=
  {q : (ℚ × ℚ) × (ℚ × ℚ) // q.1.1 < q.1.2 ∧ q.1.2 < q.2.1 ∧ q.2.1 < q.2.2}

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- Local finiteness and rational rectangle covers imply countable finite-death support. -/
theorem moduleDiagramMultiplicity_countable_support (hM : M.QTame) :
    Set.Countable {p | 0 < moduleDiagramMultiplicity M hM p} := by
  let T : RationalRectangle → Set (Cut ℝ × Cut ℝ) := fun q =>
    {p | p ∈ rectangleCell (q.val.1.1 : ℝ) q.val.1.2 q.val.2.1 q.val.2.2 ∧
      0 < moduleDiagramMultiplicity M hM p}
  have hT : ∀ q, (T q).Finite := by
    intro q
    exact moduleDiagramMultiplicity_locally_finite M hM
      (rectangleCell_mem_separatedRectangleCells _ _ _ _ (by exact_mod_cast q.property.2.1))
  apply (countable_iUnion (fun q => (hT q).countable)).mono
  intro p hp
  obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hp
  rcases hU with rfl | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
  · exact hpU.elim
  · obtain ⟨A, _, hAa⟩ := exists_rat_btwn (show a - 1 < a by linarith)
    obtain ⟨B, hbB, hBmid⟩ := exists_rat_btwn (show b < (b + c) / 2 by linarith)
    obtain ⟨C, hmidC, hCc⟩ := exists_rat_btwn (show (b + c) / 2 < c by linarith)
    obtain ⟨D, hdD, _⟩ := exists_rat_btwn (lt_add_one d)
    have hAB : A < B := by exact_mod_cast (hAa.trans (hab.trans hbB))
    have hBC : B < C := by exact_mod_cast (hBmid.trans hmidC)
    have hCD : C < D := by exact_mod_cast (hCc.trans (hcd.trans hdD))
    let q : RationalRectangle := ⟨((A, B), (C, D)), hAB, hBC, hCD⟩
    refine mem_iUnion.mpr ⟨q, ?_⟩
    exact ⟨⟨⟨Cut.lower_of_le hAa.le hpU.1.1, Cut.upper_of_le hbB.le hpU.1.2⟩,
      ⟨Cut.lower_of_le hCc.le hpU.2.1, Cut.upper_of_le hdD.le hpU.2.2⟩⟩, hp⟩

/-- Essential support is countable by rational birth-cell covers. -/
theorem moduleEssentialMultiplicity_countable_support (hM : M.QTame) :
    Set.Countable {birth | 0 < moduleEssentialMultiplicity M hM birth} := by
  let T : (ℚ × ℚ) → Set (Cut ℝ) := fun q =>
    {birth | birth ∈ cutCell (q.1 : ℝ) q.2 ∧ 0 < moduleEssentialMultiplicity M hM birth}
  have hT : ∀ q, (T q).Finite := by
    intro q
    exact moduleEssentialMultiplicity_locally_finite M hM (cutCell_mem_cutCells _ _)
  apply (countable_iUnion (fun q => (hT q).countable)).mono
  intro birth hb
  obtain ⟨U, hU, hbU⟩ := moduleEssentialMultiplicity_visible_of_pos M hM hb
  obtain ⟨a, b, _, rfl⟩ := hU
  obtain ⟨A, _, hAa⟩ := exists_rat_btwn (show a - 1 < a by linarith)
  obtain ⟨B, hbB, _⟩ := exists_rat_btwn (lt_add_one b)
  exact mem_iUnion.mpr ⟨(A, B), ⟨⟨Cut.lower_of_le hAa.le hbU.1,
    Cut.upper_of_le hbB.le hbU.2⟩, hb⟩⟩

/-- The actual diagram with its essential boundary has countable global positive support. -/
theorem moduleExtendedDiagramMultiplicity_countable_support (hM : M.QTame) :
    Set.Countable {p | 0 < moduleExtendedDiagramMultiplicity M hM p} := by
  have hfinite := moduleDiagramMultiplicity_countable_support M hM
  have hess := (moduleEssentialMultiplicity_countable_support M hM).image
    (fun birth => (birth, infinityCut))
  apply (hfinite.union hess).mono
  intro p hp
  change 0 < moduleExtendedDiagramMultiplicity M hM p at hp
  by_cases hInf : p.2 = infinityCut
  · right
    refine ⟨p.1, ?_, Prod.ext rfl hInf.symm⟩
    change 0 < moduleEssentialMultiplicity M hM p.1
    simpa only [moduleExtendedDiagramMultiplicity, if_pos hInf] using hp
  · left
    change 0 < moduleDiagramMultiplicity M hM p
    simpa only [moduleExtendedDiagramMultiplicity, if_neg hInf] using hp

end TDA.Persistence.RectangleMeasure
