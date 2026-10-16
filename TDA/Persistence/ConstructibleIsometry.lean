import TDA.Persistence.ConstructibleInducedMatching
import TDA.Persistence.MatchingInterleavingDistance

/-!
# Isometry for finite-constructible real persistence modules

Returning the actual induced matching's shifted target gives an epsilon-cost
matching of the original diagrams. Every interleaving parameter therefore
bounds the bottleneck. Taking the extended infimum and combining the existing
reverse inequality proves equality, without assuming either infimum is attained.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory
open scoped Classical NNReal ENNReal

namespace RealMatchingBounds

private theorem diagonal_le {D : Diagram ℝ} (hD : D.IsPositive) (ε : ℝ≥0)
    (i : D.finiteOccurrences) (hl : i.1.2 - i.1.1 ≤ (ε : ℝ) + (ε : ℝ)) :
    diagonalCost i.1 ≤ (ε : ℝ≥0∞) := by
  apply ENNReal.ofReal_le_coe.mpr
  rw [abs_of_nonneg (sub_nonneg.mpr (RealBarcode.finite_positive hD i).le)]
  linarith

/-- Adding epsilon back to the shifted target converts the proved double-shift
endpoint and unmatched-length bounds into a cost bound for the original diagrams.
Positivity is used for unmatched diagonal costs, including threshold equality. -/
theorem untranslateTarget_cost_le {D E : Diagram ℝ} (hD : D.IsPositive) (hE : E.IsPositive)
    (ε : ℝ≥0)
    (A : OccurrenceMatching D.finiteOccurrences (translateDiagram E (-(ε : ℝ))).finiteOccurrences
      D.essentialOccurrences (translateDiagram E (-(ε : ℝ))).essentialOccurrences)
    (h : RealMatchingBounds (ε + ε) (ε + ε) A) :
    (A.untranslateTarget (-(ε : ℝ))).cost (fun p => p.1) (fun p => p.1)
      (fun b => b.1) (fun b => b.1) ≤ (ε : ℝ≥0∞) := by
  apply OccurrenceMatching.cost_le_of
  · intro i
    cases hi : (A.untranslateTarget (-(ε : ℝ))).finite i with
    | none =>
      have hs := h.source_short i ((A.untranslateTarget_finite_eq_none_iff _ i).mp hi)
      exact diagonal_le hD ε i (by simpa only [NNReal.coe_add] using hs)
    | some j =>
      have hm := (A.untranslateTarget_finite_eq_some_iff _ i j).mp hi
      have hb := h.finite_bounds i _ hm
      simp only [RealEndpointBounds, finiteTranslationEquiv_value, NNReal.coe_add] at hb
      apply ENNReal.ofReal_le_coe.mpr
      apply max_le
      · exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2.1]⟩
      · exact abs_le.mpr ⟨by linarith [hb.2.2.2.1], by linarith [hb.2.2.2.2]⟩
  · intro j
    split_ifs with hj
    · exact zero_le
    · have hn : ∀ i, A.finite i ≠ some (finiteTranslationEquiv E (-(ε : ℝ)) j) := by
        intro i hi
        exact hj ⟨i, (A.untranslateTarget_finite_eq_some_iff _ i j).mpr hi⟩
      have hs := h.target_short _ hn
      rw [finiteTranslationEquiv_value] at hs
      apply diagonal_le hE ε j
      simpa only [NNReal.coe_add, Prod.fst, Prod.snd, add_sub_add_right_eq_sub] using hs
  · intro b
    have hb := h.essential_bounds b
    have hv := A.untranslateTarget_essential_value (-(ε : ℝ)) b
    simp only [RealEndpointBounds, NNReal.coe_add] at hb
    apply ENNReal.ofReal_le_coe.mpr
    rw [hv]
    exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2.1]⟩

end RealMatchingBounds

namespace FiniteConstructible

variable {k : Type u} [Field k] {n m : ℕ}
variable {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ} {M N : PModule.{u,0,u} k ℝ}
variable (hM : IsConstructible c M) (hN : IsConstructible d N)
variable (hfdM : ∀ j, FiniteDimensional k (M.obj (c j)))
variable (hfdN : ∀ j, FiniteDimensional k (N.obj (d j)))

include hM hN

/-- An actual interleaving constructs a matching of the original unshifted
diagrams. All common-grid, finiteness and defect data are derived. -/
noncomputable def interleavingMatching {ε : ℝ≥0} (i : RealInterleaving ε M N) :
    OccurrenceMatching (moduleDiagram c M hfdM).finiteOccurrences
      (moduleDiagram d N hfdN).finiteOccurrences
      (moduleDiagram c M hfdM).essentialOccurrences (moduleDiagram d N hfdN).essentialOccurrences :=
  (interleaving_shifted_induced_matching hM hN hfdM hfdN i).choose.untranslateTarget (-(ε : ℝ))

/-- The matching constructed from the actual interleaving has cost at most its
parameter, including zero; no supplied cost or optimality witness is needed. -/
theorem interleavingMatching_cost_le {ε : ℝ≥0} (i : RealInterleaving ε M N) :
    (interleavingMatching hM hN hfdM hfdN i).cost
      (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ (ε : ℝ≥0∞) :=
  RealMatchingBounds.untranslateTarget_cost_le (moduleDiagram_isPositive c M hfdM)
    (moduleDiagram_isPositive d N hfdN) ε _
    (interleaving_shifted_induced_matching hM hN hfdM hfdN i).choose_spec

/-- Every actual finite-parameter interleaving bounds the bottleneck of the two
original diagrams; the critical grids may have different sizes. -/
theorem bottleneck_le_of_interleaving {ε : ℝ≥0} (i : RealInterleaving ε M N) :
    bottleneck (moduleDiagram c M hfdM) (moduleDiagram d N hfdN) ≤ (ε : ℝ≥0∞) :=
  (bottleneck_le_matching _ _ (interleavingMatching hM hN hfdM hfdN i)).trans
    (interleavingMatching_cost_le hM hN hfdM hfdN i)

/-- Algebraic stability on the finite-constructible subdomain. The proof bounds
every admissible parameter before taking its extended infimum; none is selected
at the distance, and an empty parameter set needs no special assumption. -/
theorem bottleneck_le_distance :
    bottleneck (moduleDiagram c M hfdM) (moduleDiagram d N hfdN) ≤
      realInterleavingDistance M N :=
  le_realInterleavingDistance_iff.mpr fun _ ⟨i⟩ => bottleneck_le_of_interleaving hM hN hfdM hfdN i

/-- Isometry for zero-left, right-continuous finite-constructible modules over a
field, with finite-dimensional critical fibers. Essential tails, empty grids,
different grids and infinite distances are included. -/
theorem bottleneck_eq_distance :
    bottleneck (moduleDiagram c M hfdM) (moduleDiagram d N hfdN) =
      realInterleavingDistance M N :=
  le_antisymm (bottleneck_le_distance hM hN hfdM hfdN)
    (distance_le_bottleneck c d M N hM hN hfdM hfdN)

/-- At every finite parameter, actual interleavings and cost-bounded occurrence
matchings exist together, without infimum attainment as a hypothesis. -/
theorem interleaving_iff_matching (ε : ℝ≥0) :
    Nonempty (RealInterleaving ε M N) ↔
      ∃ A : OccurrenceMatching (moduleDiagram c M hfdM).finiteOccurrences
          (moduleDiagram d N hfdN).finiteOccurrences
          (moduleDiagram c M hfdM).essentialOccurrences (moduleDiagram d N hfdN).essentialOccurrences,
        A.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤ (ε : ℝ≥0∞) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨interleavingMatching hM hN hfdM hfdN i, interleavingMatching_cost_le hM hN hfdM hfdN i⟩
  · rintro ⟨A, hA⟩
    exact ⟨matchingInterleaving c d M N hM hN hfdM hfdN ε A hA⟩

/-- Infinity is exactly an essential-multiplicity mismatch. This includes the
empty matching and empty finite-interleaving-parameter cases. -/
theorem distance_eq_top_iff_essential_card_ne :
    realInterleavingDistance M N = ⊤ ↔
      (essentialPart (moduleDiagram c M hfdM).points).card ≠
        (essentialPart (moduleDiagram d N hfdN).points).card := by
  rw [← bottleneck_eq_distance hM hN hfdM hfdN]
  exact bottleneck_eq_top_iff _ _

end FiniteConstructible
end TDA.Persistence
