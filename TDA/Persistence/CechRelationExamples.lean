import TDA.Persistence.CechHausdorff
import TDA.Persistence.CechStabilityExamples
import TDA.Persistence.CechEssentialBirth
import TDA.Persistence.LogScaleDiagramComparisonExamples
import Mathlib.Order.Interval.Set.Infinite

/-!
# Ambient Čech relation and sampling examples

Repeated coordinates are labels, not distinct metric points. A three-to-two collapse
preserves the full diagram. Moving a line endpoint gives a nonzero radius-scale bound,
with the finite death and the surviving essential bar retained. The remaining fixtures
cover insufficient budgets, empty labels, proper ambient witnesses and common targets.
-/

namespace TDA.Persistence.Cech.RelationExamples

open TDA.Filtration
open scoped ENNReal NNReal

noncomputable section

def repeated : Fin 3 → ℝ := ![0, 0, 2]
def pair : Fin 2 → ℝ := ![0, 2]
def collapse : Fin 3 → Fin 2 := ![0, 0, 1]

private theorem repeated_eq_pair_collapse (v : Fin 3) : repeated v = pair (collapse v) := by
  fin_cases v <;> norm_num [repeated, pair, collapse]

private theorem collapse_surjective : Function.Surjective collapse := by
  intro w
  fin_cases w
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- Unequal label counts and a many-to-one relation still give a canonical zero interleaving. -/
def collapseInterleaving (R : Type) [Ring R] (n : ℕ) :
    RealInterleaving 0 (sublevelModule R (Cech.filter repeated) n)
      (sublevelModule R (Cech.filter pair) n) :=
  relationInterleaving R repeated pair
    (C := Function.graph collapse) (fun v => ⟨collapse v, rfl⟩)
    (fun w => collapse_surjective w)
    (by rintro v w rfl; simp [repeated_eq_pair_collapse v]) n

theorem collapse_is_many_to_one : collapse 0 = collapse 1 ∧ (0 : Fin 3) ≠ 1 := by
  norm_num [collapse]

private theorem ranges_equal : Set.range repeated = Set.range pair := by
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨collapse v, (repeated_eq_pair_collapse v).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := collapse_surjective w
    exact ⟨v, repeated_eq_pair_collapse v⟩

/-- Coincident labels have no extra finite or essential occurrences. -/
theorem repeated_diagram_eq (k : Type) [Field k] (n : ℕ) :
    dgm k (Cech.filter repeated) n = dgm k (Cech.filter pair) n :=
  dgm_eq_of_range_eq k repeated pair ranges_equal n

theorem repeated_bottleneck_zero (k : Type) [Field k] (n : ℕ) :
    bottleneck (dgm k (Cech.filter repeated) n) (dgm k (Cech.filter pair) n) = 0 := by
  rw [repeated_diagram_eq, bottleneck_self]

private abbrev moved := TDA.Persistence.Cech.Examples.MovedPoint.q

private theorem moved_budget : ∀ v w : Fin 2, (v, w) ∈ Function.graph id →
    dist (pair v) (moved w) ≤ ((1 : ℝ≥0) : ℝ) := by
  rintro v w rfl
  fin_cases v <;> norm_num [pair, TDA.Persistence.Cech.Examples.MovedPoint.q, Real.dist_eq]

/-- The relation bound uses radius time, with no factor of two. -/
theorem moved_bottleneck_le (n : ℕ) :
    bottleneck (dgm (ZMod 2) (Cech.filter pair) n)
      (dgm (ZMod 2) (Cech.filter moved) n) ≤ 1 :=
  bottleneck_dgm_le_of_relation (C := Function.graph id) (ε := 1) pair moved
    (fun v => ⟨v, rfl⟩) (fun v => ⟨v, rfl⟩) moved_budget (ZMod 2) n

/-- Before displacement the finite H₀ death is one and the essential birth is zero. -/
theorem pair_full_h0 :
    (dgm (ZMod 2) (Cech.filter pair) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), ((0 : ℝ), ((1 : ℝ) : WithTop ℝ))} :=
  LogScaleDiagramComparisonExamples.twoPoints_cech_dgm_zero

/-- The shifted configuration's merging edge enters at radius three halves. -/
theorem moved_edge_value :
    (Cech.filter moved).value Cech.Examples.TwoPoints.edgeFace = 3 / 2 :=
  TDA.Persistence.Cech.Examples.MovedPoint.cech_value_q

private theorem singleton_value (p : Fin 2 → ℝ) (v : Fin 2) :
    (Cech.filter p).value ⟨{v}, by simp⟩ = 0 := by
  apply le_antisymm _ (Cech.filter_value_nonneg p _)
  apply (Cech.filter_value_le_radiusAt p _ (p v)).trans
  exact (Cech.radiusAt_le_iff p (p v) {v} 0).2 ⟨le_rfl, by simp⟩

private def movedEdge : FilterFunction TDA.Persistence.Examples.edgeK ℝ where
  value s := (Cech.filter moved).value s
  mono h := (Cech.filter moved).mono h

private theorem movedEdge_dgm (n : ℕ) :
    dgm (ZMod 2) movedEdge n = dgm (ZMod 2) (Cech.filter moved) n := by
  have hI : (TDA.Persistence.Examples.edgeFaces :
      Fintype (TDA.Simplicial.TotalFace TDA.Persistence.Examples.edgeK)) =
      (Rips.fullComplexFintype : Fintype (TDA.Simplicial.TotalFace
        TDA.Persistence.Examples.edgeK)) := Subsingleton.elim _ _
  exact congrArg (fun I => @dgm (Fin 2) _ (ZMod 2) _ ℝ _
    TDA.Persistence.Examples.edgeK I movedEdge n) hI

/-- After displacement the finite death is three halves; the essential bar remains. -/
theorem moved_full_h0 :
    (dgm (ZMod 2) (Cech.filter moved) 0).points =
      {((0 : ℝ), (⊤ : WithTop ℝ)), ((0 : ℝ), ((3 / 2 : ℝ) : WithTop ℝ))} := by
  rw [← movedEdge_dgm 0]
  let φ : ℝ → ℝ := fun x => if x ≤ 5 then 0 else 3 / 2
  have hφ : MonotoneOn φ (Set.range TDA.Persistence.Examples.edgeFilter.value) := by
    intro a _ b _ hab
    by_cases ha : a ≤ 5
    · by_cases hb : b ≤ 5 <;> norm_num [φ, ha, hb]
    · have hb : ¬ b ≤ 5 := fun hb => ha (hab.trans hb)
      simp [φ, ha, hb]
  have hvalue : ∀ s, movedEdge.value s =
      φ (TDA.Persistence.Examples.edgeFilter.value s) := by
    intro s
    change (Cech.filter moved).value s = _
    rcases TDA.Persistence.Examples.edge_face_cases s with hs | hs | hs
    · have he : s = (⟨{0}, by simp⟩ : TDA.Simplicial.TotalFace (Rips.fullComplex (Fin 2))) :=
        Subtype.ext hs
      subst s
      rw [singleton_value]
      norm_num [TDA.Persistence.Examples.edgeFilter, φ]
    · have he : s = (⟨{1}, by simp⟩ : TDA.Simplicial.TotalFace (Rips.fullComplex (Fin 2))) :=
        Subtype.ext hs
      subst s
      rw [singleton_value]
      norm_num [TDA.Persistence.Examples.edgeFilter, φ]
    · have he : s = Cech.Examples.TwoPoints.edgeFace := Subtype.ext hs
      subst s
      rw [moved_edge_value]
      norm_num [TDA.Persistence.Examples.edgeFilter, Cech.Examples.TwoPoints.edgeFace,
        Cech.Examples.TwoPoints.edge, φ, Finset.ext_iff]
  rw [dgm_points_map_of_monotoneOn (ZMod 2)
    TDA.Persistence.Examples.edgeFilter movedEdge φ hφ hvalue 0]
  rw [TDA.Persistence.Examples.edge_points]
  norm_num [φ, Multiset.filter_singleton]

theorem moved_essential_bar :
    essentialPart (dgm (ZMod 2) (Cech.filter moved) 0).points = ({0} : Multiset ℝ) :=
  essentialPart_dgm_zero_eq_singleton (ZMod 2) moved

/-- Budget zero fails for the displaced pair, so the geometric premise has content. -/
theorem moved_budget_zero_fails :
    ¬ (∀ v w : Fin 2, (v, w) ∈ Function.graph id → dist (pair v) (moved w) ≤ (0 : ℝ)) := by
  intro h
  have hb := h 1 1 rfl
  norm_num [pair, TDA.Persistence.Cech.Examples.MovedPoint.q, Real.dist_eq] at hb

theorem proper_ambient_closed_ball_comparison (r : ℝ) :
    (Cech.filter repeated).sublevel r = Cech.complex repeated r :=
  Cech.sublevel_eq_complex repeated r

/-- The punctured line retains the distinction between an infimum and a witness. -/
theorem punctured_sublevel_ne_complex :
    (Cech.filter Cech.Examples.Punctured.pts).sublevel 1 ≠
      Cech.complex Cech.Examples.Punctured.pts 1 :=
  Cech.Examples.Punctured.sublevel_ne_complex

theorem empty_diagrams_eq (p q : Fin 0 → ℝ) (n : ℕ) :
    dgm ℚ (Cech.filter p) n = dgm ℚ (Cech.filter q) n := by
  apply dgm_eq_of_range_eq ℚ p q _ n
  simp

/-- A common target may be infinite, and has no diagram in the sampling statement. -/
theorem common_target_samples (target : Set ℝ) {α β : ℝ≥0∞}
    (hp : Metric.hausdorffEDist (Set.range repeated) target ≤ α)
    (hq : Metric.hausdorffEDist (Set.range moved) target ≤ β) (n : ℕ) :
    bottleneck (dgm ℚ (Cech.filter repeated) n) (dgm ℚ (Cech.filter moved) n) ≤ α + β :=
  bottleneck_dgm_le_sampling_errors ℚ repeated moved target hp hq n

private theorem interval_sample_error {m : ℕ} (hm : 0 < m) (p : Fin m → ℝ)
    (hzero : p ⟨0, hm⟩ = 0) (hbound : ∀ v, p v ∈ Set.Icc (0 : ℝ) 3) :
    Metric.hausdorffEDist (Set.range p) (Set.Icc (0 : ℝ) 3) ≤ 3 := by
  apply Metric.hausdorffEDist_le_of_mem_edist
  · rintro x ⟨v, rfl⟩
    exact ⟨p v, hbound v, by simp⟩
  · intro x hx
    refine ⟨0, ⟨⟨0, hm⟩, hzero⟩, ?_⟩
    rw [edist_dist]
    have hd : dist x 0 ≤ (3 : ℝ) := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hx.1] using hx.2
    exact (ENNReal.ofReal_le_ofReal hd).trans_eq (by norm_num)

/-- An explicit infinite common target with two finite samples and finite error budgets. -/
theorem interval_target_samples (n : ℕ) :
    (Set.Icc (0 : ℝ) 3).Infinite ∧
      bottleneck (dgm ℚ (Cech.filter repeated) n) (dgm ℚ (Cech.filter moved) n) ≤ 6 := by
  constructor
  · exact Set.Icc_infinite (by norm_num)
  · have hp := interval_sample_error (by norm_num : 0 < 3) repeated rfl (by
      intro v; fin_cases v <;> norm_num [repeated])
    have hq := interval_sample_error (by norm_num : 0 < 2) moved rfl (by
      intro v; fin_cases v <;> norm_num [TDA.Persistence.Cech.Examples.MovedPoint.q])
    have h := bottleneck_dgm_le_sampling_errors ℚ repeated moved (Set.Icc (0 : ℝ) 3) hp hq n
    norm_num at h ⊢
    exact h

end
end TDA.Persistence.Cech.RelationExamples
