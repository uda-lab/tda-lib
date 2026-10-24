import TDA.Persistence.PersistenceMeasureExtendedDiagram

/-!
# A module lower bound is a diagram birth lower bound

If the actual module fibers vanish below `T`, no extracted decorated point is born below
`T`. The proof uses zero crossing maps and the actual rectangle and essential-strip
quotient counts. It applies to infinite-dimensional fibers above the bound.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open Set CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

private theorem crossing_eq_zero_of_isZero {b c : ℝ} (hbc : b ≤ c)
    (hb : IsZero (M.obj b)) : structureMapLinear M hbc = 0 := by
  change (structureMap M hbc).hom = 0
  rw [hb.eq_of_src (structureMap M hbc) 0]
  rfl

/-- A birth cell below a module's zero tail contains no finite-death diagram points. -/
theorem moduleDiagramMultiplicity_zero_below_birth_cell (hM : M.QTame)
    (T : ℝ) (hzero : ∀ t < T, IsZero (M.obj t)) {a b : ℝ} (hbT : b < T)
    {p : Cut ℝ × Cut ℝ} (hpBirth : p.1 ∈ cutCell a b) :
    moduleDiagramMultiplicity M hM p = 0 := by
  by_contra hne
  have hpos := Nat.pos_of_ne_zero hne
  obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hpos
  rcases hU with rfl | ⟨e, f, g, d, _, hfg, hgd, rfl⟩
  · exact hpU.elim
  · have hpB : p.1 ∈ cutCell (max a e) (min b f) := by
      rw [← cutCell_inter]
      exact ⟨hpBirth, hpU.1⟩
    have hgap : min b f < g := (min_le_right _ _).trans_lt hfg
    have hmap := crossing_eq_zero_of_isZero M hgap.le
      (hzero _ ((min_le_left _ _).trans_lt hbT))
    have hle := moduleDiagramMultiplicity_le_content M hM
      (rectangleCell_mem_separatedRectangleCells (max a e) (min b f) g d hgap)
      (show p ∈ rectangleCell (max a e) (min b f) g d from ⟨hpB, hpU.2⟩)
    rw [moduleRectangleContent_apply M hM _ _ _ _ (lt_of_mem_cutCell hpB) hgap hgd,
      persistenceMeasureValue_eq_zero_of_crossing_eq_zero M _ _ _ hmap] at hle
    omega

/-- A birth cell below a module's zero tail contains no essential diagram points. -/
theorem moduleEssentialMultiplicity_zero_below_birth_cell (hM : M.QTame)
    (T : ℝ) (hzero : ∀ t < T, IsZero (M.obj t)) {a b : ℝ} (hbT : b < T)
    {birth : Cut ℝ} (hb : birth ∈ cutCell a b) :
    moduleEssentialMultiplicity M hM birth = 0 := by
  have hab : a < b := lt_of_mem_cutCell hb
  have hcross : b < b + 1 := lt_add_one b
  let : FiniteDimensional k (persistenceImage M hcross.le) := hM b (b + 1) hcross
  have hmap := crossing_eq_zero_of_isZero M hcross.le (hzero b hbT)
  have hImage : persistenceImage M hcross.le = ⊥ := by simp [persistenceImage, hmap]
  have hle := essentialMeasureValue_le_crossing_rank M hab.le hcross
  rw [hImage, finrank_bot] at hle
  have hpoint := moduleEssentialMultiplicity_le_content M hM (cutCell_mem_cutCells a b) hb
  rw [essentialCutContent_apply M hM hab.le] at hpoint
  omega

private theorem exists_cell_below_of_endpoint_lt {birth : Cut ℝ} {a b T : ℝ}
    (hb : birth ∈ cutCell a b) (hT : cutEndpoint birth < T) :
    ∃ a' b', b' < T ∧ birth ∈ cutCell a' b' := by
  let u := (cutEndpoint birth + T) / 2
  have hru : cutEndpoint birth < u := by dsimp [u]; linarith
  have huT : u < T := by dsimp [u]; linarith
  have hBound : BddAbove birth.lower := ⟨b, fun _ ht => (birth.lower_lt_upper ht hb.2).le⟩
  have huNot : u ∉ birth.lower := fun hu => (not_le_of_gt hru) (le_csSup hBound hu)
  have hu := (birth.mem_lower_or_upper u).resolve_left huNot
  exact ⟨a, u, huT, hb.1, hu⟩

/-- For a lower-bounded module, every finite or essential extracted birth respects the bound. -/
theorem moduleExtendedDiagramMultiplicity_birth_lower_bound (hM : M.QTame)
    (T : ℝ) (hzero : ∀ t < T, IsZero (M.obj t)) {p : Cut ℝ × Cut ℝ}
    (hp : 0 < moduleExtendedDiagramMultiplicity M hM p) : T ≤ cutEndpoint p.1 := by
  by_contra hn
  have hrT : cutEndpoint p.1 < T := lt_of_not_ge hn
  by_cases hInf : p.2 = infinityCut
  · have hess : 0 < moduleEssentialMultiplicity M hM p.1 := by
      simpa only [moduleExtendedDiagramMultiplicity, if_pos hInf] using hp
    obtain ⟨U, hU, hpU⟩ := moduleEssentialMultiplicity_visible_of_pos M hM hess
    obtain ⟨a, b, _, rfl⟩ := hU
    obtain ⟨a', b', hb'T, hpB⟩ := exists_cell_below_of_endpoint_lt hpU hrT
    have hz := moduleEssentialMultiplicity_zero_below_birth_cell M hM T hzero hb'T hpB
    omega
  · have hfinite : 0 < moduleDiagramMultiplicity M hM p := by
      simpa only [moduleExtendedDiagramMultiplicity, if_neg hInf] using hp
    obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hfinite
    rcases hU with rfl | ⟨a, b, c, d, _, _, _, rfl⟩
    · exact hpU.elim
    · obtain ⟨a', b', hb'T, hpB⟩ := exists_cell_below_of_endpoint_lt hpU.1 hrT
      have hz := moduleDiagramMultiplicity_zero_below_birth_cell M hM T hzero hb'T hpB
      omega

end TDA.Persistence.RectangleMeasure
