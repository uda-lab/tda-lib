import TDA.Persistence.DecoratedRectangleCells
import Mathlib.Order.Interval.Set.Basic

/-!
# Finite numeric endpoints of real decorated cuts

A cut seen by a finite cell has a nonempty lower part and a nonempty upper part. The
supremum of its lower part is a genuine real endpoint, and the cut is one of the two
principal decorations at that endpoint. The total supremum function is interpreted only
under these finite-cell hypotheses; it does not encode either infinite endpoint.
-/

namespace TDA.Persistence.RectangleMeasure

open Set

/-- Numeric endpoint of a finite cut, interpreted only when a containing finite cell exists. -/
noncomputable def cutEndpoint (c : Cut ℝ) : ℝ := sSup c.lower

/-- Forgetting the minus decoration recovers its real endpoint. -/
@[simp] theorem cutEndpoint_minusCut (r : ℝ) : cutEndpoint (minusCut r) = r :=
  csSup_Iio

/-- Forgetting the plus decoration recovers the same real endpoint. -/
@[simp] theorem cutEndpoint_plusCut (r : ℝ) : cutEndpoint (plusCut r) = r :=
  csSup_Iic

private theorem bddAbove_lower_of_mem_cutCell {c : Cut ℝ} {a b : ℝ}
    (hc : c ∈ cutCell a b) : BddAbove c.lower :=
  ⟨b, fun _ ht => (c.lower_lt_upper ht hc.2).le⟩

/-- A cut's numeric endpoint lies between any two cell endpoints containing it. -/
theorem cutEndpoint_bounds {c : Cut ℝ} {a b : ℝ} (hc : c ∈ cutCell a b) :
    a ≤ cutEndpoint c ∧ cutEndpoint c ≤ b := by
  have hb := bddAbove_lower_of_mem_cutCell hc
  exact ⟨le_csSup hb hc.1, csSup_le ⟨a, hc.1⟩ (fun _ ht =>
    (c.lower_lt_upper ht hc.2).le)⟩

/-- Every finite cut is exactly the minus or plus decoration of its numeric endpoint. -/
theorem cut_eq_minus_or_plus_of_mem_cutCell {c : Cut ℝ} {a b : ℝ}
    (hc : c ∈ cutCell a b) :
    c = minusCut (cutEndpoint c) ∨ c = plusCut (cutEndpoint c) := by
  have hb := bddAbove_lower_of_mem_cutCell hc
  have hlo : Iio (cutEndpoint c) ⊆ c.lower := by
    intro t ht
    obtain ⟨r, hr, htr⟩ := (lt_csSup_iff hb ⟨a, hc.1⟩).mp ht
    exact Cut.lower_of_le htr.le hr
  have hup : c.lower ⊆ Iic (cutEndpoint c) := fun _ ht => le_csSup hb ht
  rcases mem_Iic_Iio_of_subset_of_subset hlo hup with hplus | hminus
  · exact Or.inr (cut_eq_of_lower_eq hplus)
  · exact Or.inl (cut_eq_of_lower_eq hminus)

/-- Birth and death cuts seen by a separated rectangle have strictly ordered numeric endpoints. -/
theorem cutEndpoint_lt_of_mem_rectangleCell {a b c d : ℝ} (hbc : b < c)
    {birth death : Cut ℝ} (hp : (birth, death) ∈ rectangleCell a b c d) :
    cutEndpoint birth < cutEndpoint death :=
  (cutEndpoint_bounds hp.1).2.trans_lt (hbc.trans_le (cutEndpoint_bounds hp.2).1)

end TDA.Persistence.RectangleMeasure
