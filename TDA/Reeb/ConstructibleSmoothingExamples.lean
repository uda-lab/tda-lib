import TDA.Reeb.ConstructibleSmoothing
import TDA.Reeb.RGraphCosheafEquivalenceExamples

/-!
# Fixtures for constructibility under smoothing

Acceptance fixtures for `TDA.Reeb.CriticalValuesShift` and `TDA.Reeb.ConstructibleSmoothing`,
built on the constructible-cosheaf, representation and graph-cosheaf fixtures:

* **`ε = 0`.** The two shifts of every level coincide; the shifted witness of `{0, 2}` has two
  levels, not four, and its range is `{0, 2}`. The smoothed pinch at `ε = 0` is constructible at
  its own levels `{0, 1}`.
* **Collision.** For `{0, 2}` at `ε = 1` the shifts `{-1, 1} ∪ {1, 3}` merge to `{-1, 1, 3}`: the
  witness has three levels, `-1`, `1` and `3`, not four.
* **One level, `ε > 0`.** The shifted set of a one-level list is the pair `{a - ε, a + ε}`, with
  two levels; the smoothed point cosheaf is constructible at `{-1, 1}`.
* **Between shifted levels.** `(1/4, 3/4) ≤ (-1, 1)` meet no shifted level of `{0}` at `ε = 1`.
  The old level `0` lies outside `(1/4, 3/4)` but inside its thickening `(-3/4, 7/4)`; the key
  interval lemma applies and the smoothed inclusion is bijective.
* **Empty source.** `⊥ ≤ (-1, 1)` also meet no shifted level, but the smoothed point cosheaf is
  empty at `⊥` and nonempty at `(-1, 1)`, so its inclusion map is not bijective. The interval rule
  therefore needs a nonempty source.
* **Branching pinch.** The pinch over `{0, 1}`, two edges with a common lower vertex, stays
  constructible after smoothing, at value universe `0` and `1`. Its smoothed value at `⊥` is
  empty. At `ε = 1` the shifted tails are `(-∞, -1)` and `(2, ∞)`, where the smoothed pinch is
  empty, and it is nonempty on `(-∞, 0)`.
* **Bundled functor.** The lifted functor on the pinch graph object, the lifted unit and zero
  comparison as maps of the pinch cosheaf, and the image of the parallel-edge swap, whose
  underlying map is the smoothing of the swap. At `ε = 1/4` the image is not the identity: the
  thickening of `(1/4, 3/4)` is the gap `(0, 1)`, where the swap exchanges the two edges.
-/

open Set CategoryTheory
open scoped NNReal

namespace TDA.Reeb

noncomputable section

open OpenInterval

namespace Examples.ConstructibleSmoothing

open CriticalValues CylinderPresentation FiniteReebData RGraph RGraph.Examples
open TDA.Reeb.Examples.Cylinder
open TDA.Reeb.Examples.Constructible (S1 S1_value pointCosheaf pointCosheaf_nonempty_iff
  pointCosheaf_isConstructibleAt)
open TDA.Reeb.Examples.ConstructibleCylinder (DP pinch_J0_mem_iff)
open TDA.Reeb.Examples.ConstructibleRepresentation (S02 FP FP_isConstructibleAt
  FP_isIntervalCosheaf FPu FPu_isConstructibleAt FPu_isIntervalCosheaf)
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph swapGraph swap_cosheaf_edge)

/-! ### `ε = 0`: duplicate shifts -/

/-- At `ε = 0` the lower and upper shifts of every level coincide. -/
theorem S02_shift_zero_duplicate (i : Fin 2) :
    S02.value i - ((0 : ℝ≥0) : ℝ) = S02.value i + ((0 : ℝ≥0) : ℝ) := by
  simp

/-- At `ε = 0` the deduplicated witness of `S02 = {0, 2}` has two levels, not four. -/
theorem S02_shiftedCount_zero : S02.shiftedCount 0 = 1 := S02.shiftedCount_zero

theorem S02_range_shifted_zero : Set.range (S02.shifted 0).value = {0, 2} := by
  rw [range_shifted_zero]
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [S02]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [S02]⟩
    · exact ⟨1, by simp [S02]⟩

/-! ### `S02 = {0, 2}`, `ε = 1`: collision at `1` -/

/-- The shifts `{-1, 1} ∪ {1, 3}` deduplicate to `{-1, 1, 3}`. -/
theorem S02_shiftedSet_one : S02.shiftedSet 1 = {-1, 1, 3} := by
  ext x
  rw [mem_shiftedSet]
  constructor
  · rintro ⟨i, h | h⟩ <;> fin_cases i <;> norm_num [S02] at h <;> rw [h] <;> norm_num
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨0, Or.inl (by norm_num [S02])⟩
    · exact ⟨0, Or.inr (by norm_num [S02])⟩
    · exact ⟨1, Or.inr (by norm_num [S02])⟩

/-- The collision example has three levels, not `2 · 2 = 4`. -/
theorem S02_shiftedCount_one : S02.shiftedCount 1 = 2 := by
  unfold shiftedCount
  rw [S02_shiftedSet_one, Finset.card_insert_of_notMem (by norm_num),
    Finset.card_insert_of_notMem (by norm_num), Finset.card_singleton]

theorem S02_shifted_one_first : (S02.shifted 1).value 0 = -1 := by
  rw [shifted_value_zero]
  norm_num [S02]

theorem S02_shifted_one_last : (S02.shifted 1).value (Fin.last _) = 3 := by
  rw [shifted_value_last]
  norm_num [S02]

/-- The middle index of the shifted witness of `S02` at `ε = 1`. -/
def S02mid : Fin (S02.shiftedCount 1 + 1) := ⟨1, by rw [S02_shiftedCount_one]; omega⟩

theorem S02_shifted_one_middle : (S02.shifted 1).value S02mid = 1 := by
  have hmem : (S02.shifted 1).value S02mid ∈ Set.range (S02.shifted 1).value := ⟨_, rfl⟩
  rw [range_shifted, S02_shiftedSet_one] at hmem
  have h0 : (S02.shifted 1).value 0 < (S02.shifted 1).value S02mid :=
    (S02.shifted 1).strictMono (by simp [Fin.lt_def, S02mid])
  have h2 : (S02.shifted 1).value S02mid < (S02.shifted 1).value (Fin.last _) :=
    (S02.shifted 1).strictMono (by simp [Fin.lt_def, S02mid, S02_shiftedCount_one])
  rw [S02_shifted_one_first] at h0
  rw [S02_shifted_one_last] at h2
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · linarith
  · exact h
  · linarith

/-! ### Singleton levels and `ε > 0` -/

/-- For one level `a` the shifted set is `{a - ε, a + ε}`. -/
theorem shiftedSet_eq_pair (S : CriticalValues 0) (ε : ℝ≥0) :
    S.shiftedSet ε = {S.value 0 - ε, S.value 0 + ε} := by
  ext x
  rw [mem_shiftedSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, h⟩
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h
  · exact fun h => ⟨0, h⟩

/-- For one level and `ε > 0` the shifted witness has two levels. -/
theorem shiftedCount_eq_one (S : CriticalValues 0) {ε : ℝ≥0} (hε : 0 < ε) :
    S.shiftedCount ε = 1 := by
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  have hne : S.value 0 - ε ≠ S.value 0 + ε := fun h => by linarith
  unfold shiftedCount
  rw [shiftedSet_eq_pair, Finset.card_pair_eq_two_iff.2 hne]

/-- The shifted levels of `S1 = {0}` at `ε = 1` are `-1` and `1`. -/
theorem S1_shifted_one_value (j : Fin (S1.shiftedCount 1 + 1)) :
    (S1.shifted 1).value j = -1 ∨ (S1.shifted 1).value j = 1 := by
  obtain ⟨i, h | h⟩ := (S1.mem_range_shifted_iff 1).1 ⟨j, rfl⟩ <;> rw [h, S1_value] <;> norm_num

theorem S1_shiftedCount_one : S1.shiftedCount 1 = 1 := shiftedCount_eq_one S1 one_pos

/-- The smoothed point cosheaf is constructible at `{-1, 1}`. -/
theorem smoothedPoint_isConstructibleAt :
    (S1.shifted 1).IsConstructibleAt ((smoothing 1).obj pointCosheaf) :=
  pointCosheaf_isConstructibleAt.smoothing 1

/-! ### An interval between shifted levels whose thickening contains an old level -/

theorem between_le : ioo (1 / 4) (3 / 4) ≤ ioo (-1) 1 := fun x hx => by
  rw [mem_ioo] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

/-- Neither `(1/4, 3/4)` nor `(-1, 1)` contains a shifted level of `{0}` at `ε = 1`. -/
theorem between_hits (j : Fin (S1.shiftedCount 1 + 1)) :
    (S1.shifted 1).value j ∈ ioo (1 / 4) (3 / 4) ↔ (S1.shifted 1).value j ∈ ioo (-1) 1 := by
  rcases S1_shifted_one_value j with h | h <;> rw [h, mem_ioo, mem_ioo] <;> norm_num

/-- The old level `0` is not in `(1/4, 3/4)` but is already in its thickening `(-3/4, 7/4)`. -/
theorem between_old_level :
    (0 : ℝ) ∉ ioo (1 / 4) (3 / 4) ∧ (0 : ℝ) ∈ thicken 1 (ioo (1 / 4) (3 / 4)) := by
  refine ⟨fun h => by rw [mem_ioo] at h; linarith [h.1], ?_⟩
  rw [thicken_ioo (by norm_num), mem_ioo]
  norm_num

/-- The key interval lemma applies, and the smoothed inclusion is bijective. -/
theorem between_key :
    ((S1.value 0 ∈ thicken 1 (ioo (1 / 4) (3 / 4))) ↔ S1.value 0 ∈ thicken 1 (ioo (-1) 1)) ∧
      Function.Bijective (((smoothing 1).obj pointCosheaf).map (homOfLE between_le)) :=
  ⟨S1.value_mem_thicken_iff_of_shifted 1 between_le
      ⟨1 / 2, show (1 / 4 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 3 / 4 by norm_num⟩ between_hits 0,
    smoothedPoint_isConstructibleAt.bijective between_le
      ⟨1 / 2, show (1 / 4 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 3 / 4 by norm_num⟩ between_hits⟩

/-! ### The empty source: why the interval rule needs a nonempty source -/

/-- `⊥` and `(-1, 1)` meet the same shifted levels of `{0}` at `ε = 1` (none). -/
theorem emptySource_hits (j : Fin (S1.shiftedCount 1 + 1)) :
    (S1.shifted 1).value j ∈ (⊥ : OpenInterval) ↔ (S1.shifted 1).value j ∈ ioo (-1) 1 := by
  refine iff_of_false (fun h => notMem_empty _ h) ?_
  rcases S1_shifted_one_value j with h | h <;> rw [h, mem_ioo] <;> norm_num

/-- The uncorrected rule fails for the smoothed point cosheaf at the shifted witness: the smoothed inclusion `⊥ ≤ (-1, 1)` is not bijective, since `(-1, 1)` thickens to `(-2, 2)`. -/
theorem emptySource_not_bijective :
    ¬ Function.Bijective (((smoothing 1).obj pointCosheaf).map
      (homOfLE (bot_le : (⊥ : OpenInterval) ≤ ioo (-1) 1))) := by
  intro h
  have hJ : Nonempty (((smoothing 1).obj pointCosheaf).obj (ioo (-1) 1)) := by
    change Nonempty (pointCosheaf.obj (thicken 1 (ioo (-1) 1)))
    rw [pointCosheaf_nonempty_iff, thicken_ioo (by norm_num), mem_ioo]
    norm_num
  obtain ⟨y⟩ := hJ
  obtain ⟨x, -⟩ := h.2 y
  have h0 : (0 : ℝ) ∈ thicken 1 (⊥ : OpenInterval) := (pointCosheaf_nonempty_iff _).1 ⟨x⟩
  rw [thicken_bot] at h0
  exact notMem_empty _ h0

/-! ### The branching pinch: two edges with a common lower vertex -/

/-- DMP Proposition 4.19 on the pinch cosheaf. -/
theorem smoothedPinch_isConstructibleAt (ε : ℝ≥0) :
    (S01.shifted ε).IsConstructibleAt ((smoothing ε).obj FP) :=
  FP_isConstructibleAt.smoothing ε

/-- DMP Theorem 4.18 (constructible half) on the pinch cosheaf. -/
theorem smoothedPinch_isConstructibleCosheaf (ε : ℝ≥0) :
    IsConstructibleCosheaf ((smoothing ε).obj FP) :=
  (IsConstructibleCosheaf.of_isConstructibleAt FP_isConstructibleAt FP_isIntervalCosheaf).smoothing ε

/-- At `ε = 0` the smoothed pinch is constructible at `S01` itself. -/
theorem smoothedPinch_zero_isConstructibleAt : S01.IsConstructibleAt ((smoothing 0).obj FP) :=
  isConstructibleAt_shifted_zero_iff.1 (FP_isConstructibleAt.smoothing 0)

/-- The smoothed value at `⊥` is empty. -/
theorem smoothedPinch_bot_isEmpty (ε : ℝ≥0) : IsEmpty (((smoothing ε).obj FP).obj ⊥) :=
  (isIntervalCosheaf_smoothing FP_isIntervalCosheaf ε).isEmpty_obj_bot

theorem S01_shifted_one_lowerTail : (S01.shifted 1).lowerTail = iio (-1) := by
  rw [lowerTail, shifted_value_zero, S01_value_zero]
  norm_num

theorem S01_shifted_one_upperTail : (S01.shifted 1).upperTail = ioi 2 := by
  rw [upperTail, shifted_value_last]
  norm_num [S01]

/-- Lower tail: the smoothed pinch is empty on `(-∞, -1)`. -/
theorem smoothedPinch_lower_isEmpty : IsEmpty (((smoothing 1).obj FP).obj (iio (-1))) := by
  rw [← S01_shifted_one_lowerTail]
  exact (smoothedPinch_isConstructibleAt 1).isEmpty_lowerTail

/-- Upper tail: the smoothed pinch is empty on `(2, ∞)`. -/
theorem smoothedPinch_upper_isEmpty : IsEmpty (((smoothing 1).obj FP).obj (ioi 2)) := by
  rw [← S01_shifted_one_upperTail]
  exact (smoothedPinch_isConstructibleAt 1).isEmpty_upperTail

/-- The lower tail is sharp: on `(-∞, 0)`, which contains the shifted level `-1`, the smoothed
value is the pinch value on the star `J 0 = (-∞, 1)`, which is nonempty. -/
theorem smoothedPinch_iio_zero_nonempty : Nonempty (((smoothing 1).obj FP).obj (iio 0)) := by
  have h : thicken 1 (iio 0) = S01.J 0 := by
    ext x
    rw [thicken_iio, pinch_J0_mem_iff, mem_iio]
    norm_num
  change Nonempty (FP.obj (thicken 1 (iio 0)))
  rw [h]
  exact ⟨DP.vertexLabel S01 0 (0 : Fin 2)⟩

/-! ### The bundled lift on graph objects -/

/-- The pinch as a graph object. -/
abbrev pinchGraph : RGraphCat := (toRGraph S01).obj DP

/-- The smoothed pinch in `ConstructibleCosheafCat`, through the lift of the smoothing. -/
abbrev smoothedPinchObj (ε : ℝ≥0) : ConstructibleCosheafCat.{0} :=
  (constructibleSmoothing ε).obj (cosheafFunctor.obj pinchGraph)

theorem smoothedPinchObj_obj (ε : ℝ≥0) : (smoothedPinchObj ε).obj = (smoothing ε).obj FP :=
  rfl

/-- The lifted unit on the pinch is `FP` applied to `I ≤ I^ε`. -/
theorem smoothedPinch_unit_app (ε : ℝ≥0) (I : OpenInterval) :
    ((constructibleSmoothingUnit ε).app (cosheafFunctor.obj pinchGraph)).hom.app I =
      FP.map ((thickenUnit ε).app I) :=
  rfl

/-- The lifted zero comparison on the pinch is `FP` applied to `thicken 0 I = I`. -/
theorem smoothedPinch_zeroIso_app (I : OpenInterval) :
    (constructibleSmoothingZeroIso.hom.app (cosheafFunctor.obj pinchGraph)).hom.app I =
      FP.map (thickenZeroIso.hom.app I) :=
  rfl

/-- Underlying-map equality for the image of the edge swap. -/
theorem smoothedSwap_hom (ε : ℝ≥0) :
    ((constructibleSmoothing ε).map (cosheafFunctor.map swapGraph)).hom =
      (smoothing ε).map (cosheafFunctor.map swapGraph).hom :=
  rfl

theorem smoothedSwap_app (ε : ℝ≥0) (I : OpenInterval) :
    ((constructibleSmoothing ε).map (cosheafFunctor.map swapGraph)).hom.app I =
      (cosheafFunctor.map swapGraph).hom.app (thicken ε I) :=
  rfl

/-- A transformation that is the identity at `T` is the identity at any `K = T`. -/
theorem app_eq_id_of_eq {F : OpenInterval ⥤ Type} (α : F ⟶ F) {T K : OpenInterval} (h : T = K)
    (hT : α.app T = 𝟙 _) : α.app K = 𝟙 _ := by
  subst h
  exact hT

/-- The parameter `1/4`. -/
def quarter : ℝ≥0 := ⟨1 / 4, by norm_num⟩

@[simp] theorem coe_quarter : (quarter : ℝ) = 1 / 4 := rfl

/-- `(1/4, 3/4)` thickens by `1/4` to the gap `(0, 1)` of `S01`. -/
theorem quarter_thicken : thicken quarter (ioo (1 / 4) (3 / 4)) = S01.K 0 := by
  ext x
  rw [thicken_ioo (by norm_num), S01.mem_K, mem_ioo, coe_quarter]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, S01_value_zero, S01_value_one]
  norm_num

/-- At `ε = 1/4` the lifted functor keeps the edge swap a non-identity automorphism. -/
theorem smoothedSwap_quarter_ne_id :
    (constructibleSmoothing quarter).map (cosheafFunctor.map swapGraph) ≠ 𝟙 _ := by
  intro h
  have h1 : (cosheafFunctor.map swapGraph).hom.app (thicken quarter (ioo (1 / 4) (3 / 4))) =
      𝟙 _ := congrArg (fun f => f.hom.app (ioo (1 / 4) (3 / 4))) h
  have h2 := app_eq_id_of_eq _ quarter_thicken h1
  have h3 := swap_cosheaf_edge true
  rw [h2] at h3
  exact Bool.false_ne_true ((parallelData.edgeLabel S01 0).injective h3).symm

/-! ### An independent value universe -/

/-- The smoothed universe-`1` pinch is a constructible interval cosheaf. -/
theorem smoothedPinchU_isConstructibleCosheaf (ε : ℝ≥0) :
    IsConstructibleCosheaf ((smoothing ε).obj FPu) :=
  (IsConstructibleCosheaf.of_isConstructibleAt FPu_isConstructibleAt FPu_isIntervalCosheaf).smoothing
    ε

/-- The bundled smoothed universe-`1` pinch. -/
abbrev smoothedPinchUObj (ε : ℝ≥0) : ConstructibleCosheafCat.{1} :=
  (constructibleSmoothing.{1} ε).obj
    ⟨FPu, .of_isConstructibleAt FPu_isConstructibleAt FPu_isIntervalCosheaf⟩

theorem smoothedPinchUObj_obj (ε : ℝ≥0) : (smoothedPinchUObj ε).obj = (smoothing ε).obj FPu :=
  rfl

end Examples.ConstructibleSmoothing

end

end TDA.Reeb
