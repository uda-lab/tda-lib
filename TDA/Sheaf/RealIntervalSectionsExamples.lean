import TDA.Sheaf.RealIntervalSections
import TDA.Sheaf.BandThickeningExamples
import TDA.Sheaf.ClientExamples

/-!
# Sections of interval sheaves over order-connected opens: fixtures

Coefficients `ℚ`. The point sheaf `pointSheaf ℚ` has one breakpoint `0` and interval set `{0}`;
with the breakpoints `q2 = (0, 1)`, `Jco` has interval set `[0, 1)` (`intervalSet_q2_Jco`) and
`Joo`, the cell between them, `(0, 1)` (`intervalSet_q2_Joo`). Opens are `ioo a b = (a, b)`.

* Case (a), dimension `1`: the point sheaf over `(-1, 1)` (`finrank_pointSheaf_ioo_neg_one_one`),
  the half-open interval sheaf over `(-1, 1)` (`finrank_Jco_ioo_neg_one_one`), the open interval
  sheaf over `(1/4, 1/2)` (`finrank_Joo_ioo_quarter`); restriction of the half-open interval sheaf
  from `(-1, 1)` to `(-1/2, 1/2)` is an isomorphism (`isIso_Jco_restrict`).
* Case (b), dimension `0`: the point sheaf over `(1, 2)`, which misses `{0}`
  (`finrank_pointSheaf_ioo_one_two`); the half-open interval sheaf over `(-1, 2)`, which contains
  the boundary point `1` (`finrank_Jco_ioo_neg_one_two`); the open interval sheaf over
  `(-1, 1/2)`, which contains the boundary point `0` (`finrank_Joo_ioo_neg_one_half`). So the
  restriction of the open interval sheaf from `(-1, 1/2)` to `(1/4, 1/2)` is not an isomorphism
  (`not_isIso_Joo_restrict`).
* Through the thickening formula at radius `1`: the thickened point sheaf has one-dimensional
  sections over `(0, 1)` (thickened to `(-1, 2) ∋ 0`, `finrank_thickening_pointSheaf_ioo`) and none
  over `(2, 3)` (thickened to `(1, 4)`, `finrank_thickening_pointSheaf_ioo_two_three`); the
  thickened open interval sheaf has no sections over `(1/4, 1/2)` (thickened to `(-3/4, 3/2)`,
  which contains `0`, `finrank_thickening_Joo_ioo_quarter`), while at radius `1/8` it has
  one-dimensional sections there (thickened to `(1/8, 5/8)`,
  `finrank_thickening_eighth_Joo_ioo_quarter`). The whole-line interval sheaf has one-dimensional
  thickened sections over every `(a, b)`, `a < b` (`finrank_thickening_wholeLineSheaf_ioo`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TDA.Persistence TDA.Sheaf
  TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealStratification TDA.Sheaf.RealConstructible
  TDA.Sheaf.BandConvolution TDA.Sheaf.BandThickeningExamples TDA.Sheaf.ClientExamples
  TDA.Sheaf.RealStratificationExamples TDA.Sheaf.RealConstructibleExamples
  TDA.Sheaf.RealIntervalSetsExamples

namespace TDA.Sheaf.RealIntervalSectionsExamples

/-! ### Interval sets -/

/-- The cell between the two breakpoints of `q2`: the vertex `2`. -/
def Joo : FiniteInterval (2 * 2 + 1) := ⟨2, 3, by decide, by decide⟩

/-- The interval set of `Jco` is `[0, 1)`. -/
theorem intervalSet_q2_Jco : intervalSet q2 Jco = Set.Ico 0 1 := by
  rw [intervalSet_eq_Ico q2_strictMono (i := 0) (j := 1) rfl rfl]
  simp [q2]

/-- The interval set of `Joo` is `(0, 1)`. -/
theorem intervalSet_q2_Joo : intervalSet q2 Joo = Set.Ioo 0 1 := by
  rw [intervalSet_eq_Ioo q2_strictMono (i := 0) (j := 1) rfl rfl]
  simp [q2]

/-- Membership in `ioo a b`. -/
theorem mem_ioo {a b x : ℝ} : x ∈ ioo a b ↔ a < x ∧ x < b :=
  Iff.rfl

/-! ### The point sheaf -/

/-- **Case (a).** The point sheaf has one-dimensional sections over `(-1, 1)`. -/
theorem finrank_pointSheaf_ioo_neg_one_one :
    Module.finrank ℚ ((pointSheaf ℚ).presheaf.obj (op (ioo (-1) 1))) = 1 :=
  finrank_sections_extension_interval_eq_one ℚ p₁_strictMono pointSegment (ordConnected_ioo _ _)
    (by rw [intervalSet_pointSegment, closure_singleton]; exact Set.inter_subset_left)
    ⟨0, mem_ioo.2 ⟨by norm_num, by norm_num⟩, by simp [intervalSet_pointSegment]⟩

/-- **Case (b).** The point sheaf has no sections over `(1, 2)`, which misses `0`. -/
theorem finrank_pointSheaf_ioo_one_two :
    Module.finrank ℚ ((pointSheaf ℚ).presheaf.obj (op (ioo 1 2))) = 0 :=
  finrank_sections_extension_interval_eq_zero ℚ p₁_strictMono pointSegment (ordConnected_ioo _ _)
    fun h => by
      obtain ⟨x, hx, hxI⟩ := h.2
      rw [intervalSet_pointSegment, Set.mem_singleton_iff] at hxI
      rw [hxI] at hx
      have h1 := hx.1
      norm_num at h1

/-! ### The half-open interval sheaf of `[0, 1)` -/

/-- The interval sheaf of `[0, 1)`. -/
noncomputable abbrev sheafJco : TopCat.Sheaf (ModuleCat.{0} ℚ) realLine :=
  (extension ℚ q2_strictMono).obj (interval (orient 2) Jco)

/-- `[0, 1)` is relatively closed in `(-1, 1)`. -/
theorem closure_Jco_inter_subset {c : ℝ} (hc : c ≤ 1) :
    closure (intervalSet q2 Jco) ∩ (ioo (-1) c : Set ℝ) ⊆ intervalSet q2 Jco := by
  rw [intervalSet_q2_Jco, closure_Ico zero_ne_one]
  rintro x ⟨⟨h0, -⟩, -, h1⟩
  exact ⟨h0, h1.trans_le hc⟩

/-- **Case (a).** The interval sheaf of `[0, 1)` has one-dimensional sections over `(-1, 1)`. -/
theorem finrank_Jco_ioo_neg_one_one :
    Module.finrank ℚ (sheafJco.presheaf.obj (op (ioo (-1) 1))) = 1 :=
  finrank_sections_extension_interval_eq_one ℚ q2_strictMono Jco (ordConnected_ioo _ _)
    (closure_Jco_inter_subset le_rfl)
    ⟨0, mem_ioo.2 ⟨by norm_num, by norm_num⟩, by simp [intervalSet_q2_Jco]⟩

/-- **Case (b).** The interval sheaf of `[0, 1)` has no sections over `(-1, 2)`: this open
contains the boundary point `1`, which is not in `[0, 1)`. -/
theorem finrank_Jco_ioo_neg_one_two :
    Module.finrank ℚ (sheafJco.presheaf.obj (op (ioo (-1) 2))) = 0 :=
  finrank_sections_extension_interval_eq_zero ℚ q2_strictMono Jco (ordConnected_ioo _ _)
    fun h => by
      have h1 := h.1 (show (1 : ℝ) ∈ closure (intervalSet q2 Jco) ∩ (ioo (-1) 2 : Set ℝ) from
        ⟨by rw [intervalSet_q2_Jco, closure_Ico zero_ne_one]; norm_num,
          mem_ioo.2 ⟨by norm_num, by norm_num⟩⟩)
      rw [intervalSet_q2_Jco] at h1
      exact lt_irrefl _ h1.2

/-- **Restriction in case (a).** For the interval sheaf of `[0, 1)`, restriction from `(-1, 1)` to
`(-1, 1/2)` is an isomorphism. -/
theorem isIso_Jco_restrict :
    IsIso (sheafJco.presheaf.map (homOfLE (show ioo (-1) (1 / 2) ≤ ioo (-1) 1 from
      fun _ hx => ⟨hx.1, hx.2.trans (by norm_num)⟩)).op) :=
  isIso_map_extension_interval ℚ q2_strictMono Jco _ (ordConnected_ioo _ _) (ordConnected_ioo _ _)
    (closure_Jco_inter_subset (by norm_num)) (closure_Jco_inter_subset le_rfl)
    (x := 0) (mem_ioo.2 ⟨by norm_num, by norm_num⟩) (by simp [intervalSet_q2_Jco])

/-! ### The open interval sheaf of `(0, 1)` -/

/-- The interval sheaf of `(0, 1)`. -/
noncomputable abbrev sheafJoo : TopCat.Sheaf (ModuleCat.{0} ℚ) realLine :=
  (extension ℚ q2_strictMono).obj (interval (orient 2) Joo)

/-- An open inside `(0, 1)` meets `(0, 1)` in a relatively closed set. -/
theorem closure_Joo_inter_subset {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    closure (intervalSet q2 Joo) ∩ (ioo a b : Set ℝ) ⊆ intervalSet q2 Joo := by
  rw [intervalSet_q2_Joo]
  rintro x ⟨-, h1, h2⟩
  exact ⟨ha.trans_lt h1, h2.trans_le hb⟩

/-- **Case (a).** The interval sheaf of `(0, 1)` has one-dimensional sections over `(1/4, 1/2)`. -/
theorem finrank_Joo_ioo_quarter :
    Module.finrank ℚ (sheafJoo.presheaf.obj (op (ioo (1 / 4) (1 / 2)))) = 1 :=
  finrank_sections_extension_interval_eq_one ℚ q2_strictMono Joo (ordConnected_ioo _ _)
    (closure_Joo_inter_subset (by norm_num) (by norm_num))
    ⟨1 / 3, mem_ioo.2 ⟨by norm_num, by norm_num⟩,
      by rw [intervalSet_q2_Joo]; exact ⟨by norm_num, by norm_num⟩⟩

/-- `0` lies in the closure of `(0, 1)` and not in `(0, 1)`. -/
theorem zero_mem_closure_Joo :
    (0 : ℝ) ∈ closure (intervalSet q2 Joo) ∧ (0 : ℝ) ∉ intervalSet q2 Joo := by
  rw [intervalSet_q2_Joo, closure_Ioo zero_ne_one]
  exact ⟨⟨le_rfl, zero_le_one⟩, fun h => lt_irrefl _ h.1⟩

/-- **Case (b).** The interval sheaf of `(0, 1)` has no sections over `(-1, 1/2)`, which
contains the boundary point `0`. -/
theorem finrank_Joo_ioo_neg_one_half :
    Module.finrank ℚ (sheafJoo.presheaf.obj (op (ioo (-1) (1 / 2)))) = 0 :=
  finrank_sections_extension_interval_eq_zero ℚ q2_strictMono Joo (ordConnected_ioo _ _)
    fun h => zero_mem_closure_Joo.2
      (h.1 ⟨zero_mem_closure_Joo.1, mem_ioo.2 ⟨by norm_num, by norm_num⟩⟩)

/-- For the interval sheaf of `(0, 1)`, restriction from `(-1, 1/2)` to `(1/4, 1/2)` is not an
isomorphism: the dimensions are `0` and `1`. -/
theorem not_isIso_Joo_restrict :
    ¬ IsIso (sheafJoo.presheaf.map (homOfLE (show ioo (1 / 4) (1 / 2) ≤ ioo (-1) (1 / 2) from
      fun _ hx => ⟨by linarith [hx.1], hx.2⟩)).op) := by
  intro h
  have := (asIso (sheafJoo.presheaf.map (homOfLE (show ioo (1 / 4) (1 / 2) ≤ ioo (-1) (1 / 2) from
      fun _ hx => ⟨by linarith [hx.1], hx.2⟩)).op)).toLinearEquiv.finrank_eq
  rw [finrank_Joo_ioo_neg_one_half, finrank_Joo_ioo_quarter] at this
  exact zero_ne_one this

/-! ### Through the thickening formula -/

/-- The thickened point sheaf has one-dimensional sections over `(0, 1)`: they are the sections
of the point sheaf over `(-1, 2) ∋ 0`. -/
theorem finrank_thickening_pointSheaf_ioo :
    Module.finrank ℚ (((thickening ℚ 1).obj (pointSheaf ℚ)).presheaf.obj (op (ioo 0 1))) = 1 := by
  rw [(thickeningSectionsIso ℚ 1 _ _ (ordConnected_ioo 0 1)).toLinearEquiv.finrank_eq,
    bandOpen_one_ioo]
  exact finrank_sections_extension_interval_eq_one ℚ p₁_strictMono pointSegment
    (ordConnected_ioo _ _)
    (by rw [intervalSet_pointSegment, closure_singleton]; exact Set.inter_subset_left)
    ⟨0, mem_ioo.2 ⟨by norm_num, by norm_num⟩, by simp [intervalSet_pointSegment]⟩

/-- At radius `1`, `(2, 3)` thickens to `(1, 4)`. -/
theorem bandOpen_one_ioo_two_three : bandOpen 1 (ioo 2 3) = ioo 1 4 :=
  Opens.ext ((coe_bandOpen_Ioo zero_le_one (by norm_num)).trans (by norm_num [ioo]))

/-- The thickened point sheaf has no sections over `(2, 3)`: its thickening `(1, 4)` misses
`0`. -/
theorem finrank_thickening_pointSheaf_ioo_two_three :
    Module.finrank ℚ (((thickening ℚ 1).obj (pointSheaf ℚ)).presheaf.obj (op (ioo 2 3))) = 0 := by
  rw [(thickeningSectionsIso ℚ 1 _ _ (ordConnected_ioo 2 3)).toLinearEquiv.finrank_eq,
    bandOpen_one_ioo_two_three]
  exact finrank_sections_extension_interval_eq_zero ℚ p₁_strictMono pointSegment
    (ordConnected_ioo _ _) fun h => by
      obtain ⟨x, hx, hxI⟩ := h.2
      rw [intervalSet_pointSegment, Set.mem_singleton_iff] at hxI
      rw [hxI] at hx
      have h1 := hx.1
      norm_num at h1

/-- The thickened interval sheaf of `(0, 1)` has no sections over `(1/4, 1/2)` at radius `1`: the
thickening `(-3/4, 3/2)` contains the boundary point `0`. -/
theorem finrank_thickening_Joo_ioo_quarter :
    Module.finrank ℚ (((thickening ℚ 1).obj sheafJoo).presheaf.obj
      (op (ioo (1 / 4) (1 / 2)))) = 0 := by
  rw [(thickeningSectionsIso ℚ 1 _ _ (ordConnected_ioo _ _)).toLinearEquiv.finrank_eq,
    bandOpen_one_ioo_quarter]
  exact finrank_sections_extension_interval_eq_zero ℚ q2_strictMono Joo (ordConnected_ioo _ _)
    fun h => zero_mem_closure_Joo.2
      (h.1 ⟨zero_mem_closure_Joo.1, mem_ioo.2 ⟨by norm_num, by norm_num⟩⟩)

/-- At radius `1/8`, `(1/4, 1/2)` thickens to `(1/8, 5/8)`. -/
theorem bandOpen_eighth_ioo_quarter :
    bandOpen (1 / 8) (ioo (1 / 4) (1 / 2)) = ioo (1 / 8) (5 / 8) :=
  Opens.ext ((coe_bandOpen_Ioo (by norm_num) (by norm_num)).trans (by norm_num [ioo]))

/-- At radius `1/8` the thickened interval sheaf of `(0, 1)` has one-dimensional sections over
`(1/4, 1/2)`: the thickening `(1/8, 5/8)` stays inside `(0, 1)`. -/
theorem finrank_thickening_eighth_Joo_ioo_quarter :
    Module.finrank ℚ (((thickening ℚ (1 / 8)).obj sheafJoo).presheaf.obj
      (op (ioo (1 / 4) (1 / 2)))) = 1 := by
  rw [(thickeningSectionsIso ℚ (1 / 8) _ _ (ordConnected_ioo _ _)).toLinearEquiv.finrank_eq,
    bandOpen_eighth_ioo_quarter]
  exact finrank_sections_extension_interval_eq_one ℚ q2_strictMono Joo (ordConnected_ioo _ _)
    (closure_Joo_inter_subset (by norm_num) (by norm_num))
    ⟨1 / 3, mem_ioo.2 ⟨by norm_num, by norm_num⟩,
      by rw [intervalSet_q2_Joo]; exact ⟨by norm_num, by norm_num⟩⟩

/-- The thickened whole-line interval sheaf has one-dimensional sections over every `(a, b)`,
`a < b`, at radius `1`. -/
theorem finrank_thickening_wholeLineSheaf_ioo {a b : ℝ} (hab : a < b) :
    Module.finrank ℚ (((thickening ℚ 1).obj wholeLineSheaf).presheaf.obj (op (ioo a b))) = 1 := by
  rw [(thickeningSectionsIso ℚ 1 _ _ (ordConnected_ioo a b)).toLinearEquiv.finrank_eq]
  refine finrank_sections_extension_interval_eq_one ℚ p₁_strictMono wholeLine
    (ordConnected_bandOpen 1 (ordConnected_ioo a b))
    (by rw [intervalSet_wholeLine]; exact Set.subset_univ _)
    ⟨(a + b) / 2, le_bandOpen zero_le_one _ (mem_ioo.2 ⟨by linarith, by linarith⟩),
      by rw [intervalSet_wholeLine]; exact Set.mem_univ _⟩

end TDA.Sheaf.RealIntervalSectionsExamples
