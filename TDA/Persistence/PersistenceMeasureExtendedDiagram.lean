import TDA.Persistence.PersistenceMeasureDiagram
import TDA.Persistence.PersistenceMeasureEssentialDiagram

/-!
# Decorated diagram with the essential boundary

The finite-death multiplicities and the extracted essential birth multiplicities combine
on the existing two-cut point space. Tail rectangles have finite support and count the
actual finite-target image quotient. Tail stabilization excludes arbitrarily late finite
deaths inside a fixed birth strip, so local finiteness includes neighborhoods of infinity.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open Set
open scoped Classical

/-- The upper infinite cut, with every real point in its lower part. -/
noncomputable def infinityCut : Cut ℝ := cutOfLowerSet ⊤

/-- Every finite grade belongs to the lower part of the infinite death cut. -/
@[simp] theorem mem_lower_infinityCut (t : ℝ) : t ∈ infinityCut.lower := by
  simp [infinityCut, cutOfLowerSet]

/-- No finite grade belongs to the upper part of the infinite death cut. -/
@[simp] theorem not_mem_upper_infinityCut (t : ℝ) : t ∉ infinityCut.upper := by
  simp [infinityCut, cutOfLowerSet]

/-- The infinite death cut is excluded from every finite coordinate cell. -/
theorem infinityCut_not_mem_cutCell (a b : ℝ) : infinityCut ∉ cutCell a b :=
  fun h => not_mem_upper_infinityCut b h.2

/-- A tail rectangle has finite birth edges and no upper death edge. -/
def tailRectangleCell (a b c : ℝ) : Set (Cut ℝ × Cut ℝ) :=
  {p | p.1 ∈ cutCell a b ∧ c ∈ p.2.lower}

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- Canonical finite-birth decorated multiplicity, including death at infinity. -/
noncomputable def moduleExtendedDiagramMultiplicity (hM : M.QTame)
    (p : Cut ℝ × Cut ℝ) : ℕ :=
  if p.2 = infinityCut then moduleEssentialMultiplicity M hM p.1
  else moduleDiagramMultiplicity M hM p

/-- Points on the infinite-death boundary have the extracted essential birth multiplicity. -/
@[simp] theorem moduleExtendedDiagramMultiplicity_infinity (hM : M.QTame) (birth : Cut ℝ) :
    moduleExtendedDiagramMultiplicity M hM (birth, infinityCut) =
      moduleEssentialMultiplicity M hM birth := by
  simp [moduleExtendedDiagramMultiplicity]

/-- Finite rectangles retain exactly the finite-death multiplicities. -/
theorem moduleExtendedDiagramMultiplicity_of_mem_rectangleCell (hM : M.QTame)
    {a b c d : ℝ} {p : Cut ℝ × Cut ℝ} (hp : p ∈ rectangleCell a b c d) :
    moduleExtendedDiagramMultiplicity M hM p = moduleDiagramMultiplicity M hM p := by
  have hne : p.2 ≠ infinityCut := by
    intro h
    exact infinityCut_not_mem_cutCell c d (h ▸ hp.2)
  exact if_neg hne

/-- Finite rectangle quotient dimensions are the exact sums of the extended diagram. -/
theorem moduleExtendedDiagramMultiplicity_rectangle_counts (hM : M.QTame)
    (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ rectangleCell a b c d ∧
        0 < moduleExtendedDiagramMultiplicity M hM p) ∧
      persistenceMeasureValue M hab.le hbc.le hcd.le =
        ∑ p ∈ S, moduleExtendedDiagramMultiplicity M hM p := by
  obtain ⟨S, hS, hcount⟩ := moduleDiagramMultiplicity_rectangle_counts M hM a b c d hab hbc hcd
  refine ⟨S, ?_, hcount.trans ?_⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨hpK, hpos⟩ := (hS p).mp hp
      exact ⟨hpK, (moduleExtendedDiagramMultiplicity_of_mem_rectangleCell M hM hpK).symm ▸ hpos⟩
    · rintro ⟨hpK, hpos⟩
      rw [moduleExtendedDiagramMultiplicity_of_mem_rectangleCell M hM hpK] at hpos
      exact (hS p).mpr ⟨hpK, hpos⟩
  · apply Finset.sum_congr rfl
    intro p hp
    exact (moduleExtendedDiagramMultiplicity_of_mem_rectangleCell M hM ((hS p).mp hp).1).symm

/-- Essential birth-strip dimensions count the points on the actual infinite-death boundary. -/
theorem moduleExtendedDiagramMultiplicity_essential_counts (hM : M.QTame)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ S : Finset (Cut ℝ),
      (∀ birth, birth ∈ S ↔ birth ∈ cutCell a b ∧
        0 < moduleExtendedDiagramMultiplicity M hM (birth, infinityCut)) ∧
      essentialMeasureValue M hab =
        ∑ birth ∈ S, moduleExtendedDiagramMultiplicity M hM (birth, infinityCut) := by
  simpa only [moduleExtendedDiagramMultiplicity_infinity] using
    moduleEssentialMultiplicity_strip_counts M hM hab

/-- Every tail rectangle has finite positive support and counts the module's actual tail
image quotient, including its essential points. -/
theorem moduleExtendedDiagramMultiplicity_tail_counts (hM : M.QTame)
    (a b c : ℝ) (hab : a < b) (hbc : b < c) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ tailRectangleCell a b c ∧
        0 < moduleExtendedDiagramMultiplicity M hM p) ∧
      persistenceTailMeasureValue M hab.le hbc.le =
        ∑ p ∈ S, moduleExtendedDiagramMultiplicity M hM p := by
  obtain ⟨c₀, hbc₀, hstable⟩ := PModule.QTame.essentialMeasureValue_eventually M hM hab.le
  let C := max c₀ (c + 1)
  have h₀C : c₀ ≤ C := le_max_left _ _
  have hcC : c < C := (lt_add_one c).trans_le (le_max_right _ _)
  have hbC : b < C := hbc.trans hcC
  have hTail : persistenceTailMeasureValue M hab.le hbC.le = essentialMeasureValue M hab.le :=
    hstable C h₀C
  have hzero : ∀ d (hCd : C ≤ d), persistenceMeasureValue M hab.le hbC.le hCd = 0 := by
    intro d hCd
    let : FiniteDimensional k (persistenceImage M hbC.le) := hM b C hbC
    have h := persistenceMeasureValue_add_tail M hab.le hbC.le hCd
    rw [hstable C h₀C, hstable d (h₀C.trans hCd)] at h
    omega
  have hNoLate : ∀ p : Cut ℝ × Cut ℝ, p.1 ∈ cutCell a b → C ∈ p.2.lower →
      moduleDiagramMultiplicity M hM p = 0 := by
    intro p hpBirth hpC
    by_contra hne
    obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM (Nat.pos_of_ne_zero hne)
    rcases hU with rfl | ⟨e, f, g, d, _, _, _, rfl⟩
    · exact hpU.elim
    · have hCd : C < d := p.2.lower_lt_upper hpC hpU.2.2
      have hpR : p ∈ rectangleCell a b C d := ⟨hpBirth, hpC, hpU.2.2⟩
      have hle := moduleDiagramMultiplicity_le_content M hM
        (rectangleCell_mem_separatedRectangleCells a b C d hbC) hpR
      rw [moduleRectangleContent_apply M hM a b C d hab hbC hCd, hzero d hCd.le] at hle
      omega
  obtain ⟨F, hF, hFcount⟩ := moduleDiagramMultiplicity_rectangle_counts M hM a b c C hab hbc hcC
  obtain ⟨E, hE, hEcount⟩ := moduleEssentialMultiplicity_strip_counts M hM hab.le
  let E' : Finset (Cut ℝ × Cut ℝ) := E.image (fun birth => (birth, infinityCut))
  let S := F ∪ E'
  have hSupport : ∀ p, p ∈ S ↔ p ∈ tailRectangleCell a b c ∧
      0 < moduleExtendedDiagramMultiplicity M hM p := by
    intro p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hpF | hpE
      · obtain ⟨hpR, hpos⟩ := (hF p).mp hpF
        refine ⟨⟨hpR.1, hpR.2.1⟩, ?_⟩
        exact (moduleExtendedDiagramMultiplicity_of_mem_rectangleCell M hM hpR).symm ▸ hpos
      · obtain ⟨birth, hbE, rfl⟩ := Finset.mem_image.mp hpE
        obtain ⟨hbK, hpos⟩ := (hE birth).mp hbE
        exact ⟨⟨hbK, mem_lower_infinityCut c⟩, by simpa using hpos⟩
    · rintro ⟨hpK, hpos⟩
      by_cases hInf : p.2 = infinityCut
      · have hess : 0 < moduleEssentialMultiplicity M hM p.1 := by
          simpa only [moduleExtendedDiagramMultiplicity, if_pos hInf] using hpos
        exact Finset.mem_union_right F (Finset.mem_image.mpr
          ⟨p.1, (hE p.1).mpr ⟨hpK.1, hess⟩, Prod.ext rfl hInf.symm⟩)
      · have hfinite : 0 < moduleDiagramMultiplicity M hM p := by
          simpa only [moduleExtendedDiagramMultiplicity, if_neg hInf] using hpos
        have hpC : C ∈ p.2.upper := by
          rcases p.2.mem_lower_or_upper C with hpC | hpC
          · have hz := hNoLate p hpK.1 hpC
            omega
          · exact hpC
        exact Finset.mem_union_left E' ((hF p).mpr ⟨⟨hpK.1, hpK.2, hpC⟩, hfinite⟩)
  have hFE : Disjoint F E' := by
    apply Finset.disjoint_left.mpr
    intro p hpF hpE
    obtain ⟨birth, _, rfl⟩ := Finset.mem_image.mp hpE
    exact infinityCut_not_mem_cutCell c C ((hF _).mp hpF).1.2
  have hFsum : ∑ p ∈ F, moduleExtendedDiagramMultiplicity M hM p =
      persistenceMeasureValue M hab.le hbc.le hcC.le := by
    rw [hFcount]
    apply Finset.sum_congr rfl
    intro p hpF
    exact moduleExtendedDiagramMultiplicity_of_mem_rectangleCell M hM ((hF p).mp hpF).1
  have hEsum : ∑ p ∈ E', moduleExtendedDiagramMultiplicity M hM p =
      essentialMeasureValue M hab.le := by
    change ∑ p ∈ E.image (fun birth => (birth, infinityCut)),
      moduleExtendedDiagramMultiplicity M hM p = _
    rw [Finset.sum_image (by
      intro x _ y _ hxy
      exact congrArg Prod.fst hxy)]
    simpa only [moduleExtendedDiagramMultiplicity_infinity] using hEcount.symm
  have hsum : ∑ p ∈ S, moduleExtendedDiagramMultiplicity M hM p =
      persistenceTailMeasureValue M hab.le hbc.le := by
    change ∑ p ∈ F ∪ E', moduleExtendedDiagramMultiplicity M hM p = _
    rw [Finset.sum_union hFE, hFsum, hEsum]
    let : FiniteDimensional k (persistenceImage M hbc.le) := hM b c hbc
    have h := persistenceMeasureValue_add_tail M hab.le hbc.le hcC.le
    rw [hTail] at h
    exact h
  exact ⟨S, hSupport, hsum.symm⟩

/-- Local finiteness holds in full tail rectangles, including neighborhoods of infinity. -/
theorem moduleExtendedDiagramMultiplicity_tail_locally_finite (hM : M.QTame)
    (a b c : ℝ) (hab : a < b) (hbc : b < c) :
    Set.Finite {p | p ∈ tailRectangleCell a b c ∧
      0 < moduleExtendedDiagramMultiplicity M hM p} := by
  obtain ⟨S, hS, _⟩ := moduleExtendedDiagramMultiplicity_tail_counts M hM a b c hab hbc
  exact S.finite_toSet.subset (fun p hp => (hS p).mpr hp)

end TDA.Persistence.RectangleMeasure
