import TDA.Reeb.IntervalCosheaf

/-!
# Interval cosheaf and smoothing fixtures

Regression fixtures for `TDA.Reeb.isIntervalCosheaf_smoothing` and the interval-chain lemma:

* the empty value of a smoothed interval cosheaf, and the empty cover of `⊥`;
* a cover with an empty member (`cover_bot_member`);
* an unbounded interval, `ℝ = (-∞, 1) ∪ (0, ∞)` (`cover_top`);
* disjoint members whose thickenings overlap, where thickening does not preserve the
  intersection (`disjoint_thicken_overlap`);
* overlapping members whose thickened overlap misses the common overlap of two other thickened
  members, so overlap of indices alone does not give a chain step (`overlap_without_containment`);
* the three-member cover `threeCover` of `(0, 3)`, whose end members are disjoint and are joined
  through the middle member, both for an arbitrary interval cosheaf and for the interval
  component functor of the identity of `ℝ`;
* the interval component functor of a real-valued map, smoothed, and `ε = 0`.
-/

open Set CategoryTheory Limits TDA.Topology
open scoped NNReal

universe u w

namespace TDA.Reeb.Examples

open TDA.Reeb TDA.Reeb.OpenInterval

variable {F : OpenInterval ⥤ Type u}

/-- Empty value transferred: `S_ε F` is empty over `⊥`. -/
example (hF : IsIntervalCosheaf.{w} F) (ε : ℝ≥0) : IsEmpty (((smoothing ε).obj F).obj ⊥) :=
  (isIntervalCosheaf_smoothing hF ε).isEmpty_obj_bot

/-- Empty cover of `⊥`, smoothed. -/
example (hF : IsIntervalCosheaf.{0} F) (ε : ℝ≥0) :
    Nonempty (IsColimit (((smoothing ε).obj F).mapCocone
      (coverCocone (PEmpty.elim : PEmpty.{1} → OpenInterval)
        (le_of_iUnion_eq (J := ⊥) (by simp))))) :=
  isIntervalCosheaf_smoothing hF ε _ ⊥ (by simp)

/-- A cover with an empty member. -/
theorem cover_bot_member (J : OpenInterval) :
    ⋃ b : Bool, ((cond b ⊥ J : OpenInterval) : Set ℝ) = J := by
  ext x
  simp only [mem_iUnion, Bool.exists_bool, cond_false, cond_true, SetLike.mem_coe]
  exact ⟨fun h => h.elim id fun h => (show x ∈ (∅ : Set ℝ) from h).elim, Or.inl⟩

example (hF : IsIntervalCosheaf.{0} F) (ε : ℝ≥0) (J : OpenInterval) :
    Nonempty (IsColimit (((smoothing ε).obj F).mapCocone
      (coverCocone (fun b : Bool => cond b ⊥ J) (le_of_iUnion_eq (cover_bot_member J))))) :=
  isIntervalCosheaf_smoothing hF ε _ _ (cover_bot_member J)

/-- Unbounded interval: `ℝ = (-∞, 1) ∪ (0, ∞)`. -/
theorem cover_top :
    ⋃ b : Bool, ((cond b (iio 1) (ioi 0) : OpenInterval) : Set ℝ) = (⊤ : OpenInterval) := by
  ext x
  simp only [mem_iUnion, Bool.exists_bool, cond_false, cond_true, coe_ioi, coe_iio, mem_Ioi,
    mem_Iio, coe_top, mem_univ, iff_true]
  rcases lt_or_ge x 1 with h | h
  · exact Or.inr h
  · exact Or.inl (by linarith)

example (hF : IsIntervalCosheaf.{0} F) (ε : ℝ≥0) :
    Nonempty (IsColimit (((smoothing ε).obj F).mapCocone
      (coverCocone (fun b : Bool => cond b (iio 1) (ioi 0)) (le_of_iUnion_eq cover_top)))) :=
  isIntervalCosheaf_smoothing hF ε _ _ cover_top

/-- Disjoint members acquire overlap: `(0,1)` and `(2,3)` are disjoint, their `1`-thickenings
meet at `3/2`, and the naive `T_ε (I ⊓ I') = T_ε I ⊓ T_ε I'` fails for them. -/
theorem disjoint_thicken_overlap :
    ((ioo 0 1 ⊓ ioo 2 3 : OpenInterval) : Set ℝ) = ∅ ∧
      (3 / 2 : ℝ) ∈ thicken 1 (ioo 0 1) ⊓ thicken 1 (ioo 2 3) ∧
      thicken 1 (ioo 0 1 ⊓ ioo 2 3) ≠ thicken 1 (ioo 0 1) ⊓ thicken 1 (ioo 2 3) := by
  have h0 : ((ioo 0 1 ⊓ ioo 2 3 : OpenInterval) : Set ℝ) = ∅ := by
    ext x; simp only [coe_inf, coe_ioo, mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, h1⟩, h2, -⟩; linarith
  have hbot : ioo 0 1 ⊓ ioo 2 3 = ⊥ := SetLike.coe_injective (by rw [h0, coe_bot])
  have hmem : (3 / 2 : ℝ) ∈ thicken 1 (ioo 0 1) ⊓ thicken 1 (ioo 2 3) := by
    show (3 / 2 : ℝ) ∈ (thicken 1 (ioo 0 1) : Set ℝ) ∩ thicken 1 (ioo 2 3)
    rw [thicken_ioo (by norm_num), thicken_ioo (by norm_num)]
    simp only [coe_ioo, mem_inter_iff, mem_Ioo, NNReal.coe_one]
    norm_num
  refine ⟨h0, hmem, fun h => ?_⟩
  rw [hbot, thicken_bot] at h
  have : (3 / 2 : ℝ) ∈ (⊥ : OpenInterval) := h ▸ hmem
  exact this

/-- Overlap of indices alone is not enough: `(0,1)` meets `(-5, 1/10)`, but the thickening of
their overlap misses `3/2 ∈ W` for `W = T₁(0,1) ⊓ T₁(2,3)`. -/
theorem overlap_without_containment :
    ((ioo 0 1 ⊓ ioo (-5) (1 / 10) : OpenInterval) : Set ℝ).Nonempty ∧
      ¬ thicken 1 (ioo 0 1) ⊓ thicken 1 (ioo 2 3) ≤ thicken 1 (ioo 0 1 ⊓ ioo (-5) (1 / 10)) := by
  have hinf : ioo 0 1 ⊓ ioo (-5) (1 / 10) = ioo 0 (1 / 10) := by
    ext x
    show x ∈ Ioo (0 : ℝ) 1 ∩ Ioo (-5) (1 / 10) ↔ x ∈ Ioo (0 : ℝ) (1 / 10)
    simp only [mem_inter_iff, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, -⟩, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, by linarith, h2⟩
  refine ⟨⟨1 / 20, by rw [hinf, coe_ioo]; norm_num⟩, fun h => ?_⟩
  have hmem := (disjoint_thicken_overlap).2.1
  have := OpenInterval.le_iff_subset.1 h hmem
  rw [hinf, thicken_ioo (by norm_num)] at this
  simp only [coe_ioo, mem_Ioo, NNReal.coe_one] at this
  norm_num at this

/-- The three-member cover `(0,1), (1/2,5/2), (2,3)` of `(0,3)`. -/
noncomputable def threeCover : Fin 3 → OpenInterval := ![ioo 0 1, ioo (1 / 2) (5 / 2), ioo 2 3]

theorem threeCover_union : ⋃ k, (threeCover k : Set ℝ) = ioo 0 3 := by
  ext x
  simp only [mem_iUnion, Fin.exists_fin_succ, Fin.exists_fin_zero, threeCover,
    Matrix.cons_val_zero, Matrix.cons_val_succ, coe_ioo, mem_Ioo, or_false]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rintro ⟨h1, h2⟩
    by_cases ha : x < 1
    · exact Or.inl ⟨h1, ha⟩
    by_cases hb : x < 5 / 2
    · exact Or.inr (Or.inl ⟨by linarith, hb⟩)
    · exact Or.inr (Or.inr ⟨by linarith, h2⟩)

/-- The chain from `(0,1)` to `(2,3)` through `(1/2,5/2)` exists. -/
example : Relation.ReflTransGen
    (fun k l => thicken 1 (threeCover 0) ⊓ thicken 1 (threeCover 2) ≤
      thicken 1 (threeCover k ⊓ threeCover l)) 0 2 :=
  reflTransGen_thicken_inf threeCover_union 1 0 2

/-- `S_1 F` glues on this cover although its end members are disjoint. -/
example (hF : IsIntervalCosheaf.{0} F) :
    Nonempty (IsColimit (((smoothing 1).obj F).mapCocone
      (coverCocone threeCover (le_of_iUnion_eq threeCover_union)))) :=
  isIntervalCosheaf_smoothing hF 1 _ _ threeCover_union

/-- The interval component functor of a real-valued map, smoothed. -/
example {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) (ε : ℝ≥0) :
    IsIntervalCosheaf.{w} ((smoothing ε).obj (intervalComponents f)) :=
  isIntervalCosheaf_smoothing (intervalComponents_isIntervalCosheaf f) ε

/-- Concrete inhabited instance: `S_1 C_f` for `f = id : ℝ → ℝ` glues on `threeCover`, whose end
members are disjoint. -/
example : Nonempty (IsColimit (((smoothing 1).obj (intervalComponents (ContinuousMap.id ℝ))).mapCocone
    (coverCocone threeCover (le_of_iUnion_eq threeCover_union)))) :=
  isIntervalCosheaf_smoothing (intervalComponents_isIntervalCosheaf.{0, 0} (ContinuousMap.id ℝ)) 1
    _ _ threeCover_union

/-- The body-literal chain on `threeCover`: consecutive members intersect. -/
example : Relation.ReflTransGen
    (fun k l => ((threeCover k ⊓ threeCover l : OpenInterval) : Set ℝ).Nonempty ∧
      thicken 1 (threeCover 0) ⊓ thicken 1 (threeCover 2) ≤
        thicken 1 (threeCover k ⊓ threeCover l)) 0 2 :=
  reflTransGen_thicken_inf_of_nonempty threeCover_union 1 0 2
    ⟨3 / 2, (disjoint_thicken_overlap).2.1⟩

/-- `ε = 0`. -/
example (hF : IsIntervalCosheaf.{w} F) : IsIntervalCosheaf.{w} ((smoothing 0).obj F) :=
  isIntervalCosheaf_smoothing_zero_iff.2 hF

end TDA.Reeb.Examples
