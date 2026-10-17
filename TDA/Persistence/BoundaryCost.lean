import TDA.Persistence.AdditiveFeatures

/-!
# Coefficient-dependent finite boundary matching costs

Pairing, deletion and insertion coefficients are independent inputs. This exposes
exactly the linear cost used by the boundary assignment argument, so changing the
matching exponent changes coefficients without changing occurrence multiplicity.
-/

noncomputable section
namespace TDA.Persistence.OccurrenceMatching
open scoped Classical
variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

/-- Sum of selected pair coefficients and both unmatched boundary charges. -/
def totalBoundaryCost (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ) : ℝ :=
  (∑ i, match M.finite i with | some j => c i j | none => u i) +
    ∑ j, if ∃ i, M.finite i = some j then 0 else v j

/-- Nonnegative coefficients give a nonnegative candidate cost. -/
theorem totalBoundaryCost_nonneg (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (c : I → J → ℝ) (u : I → ℝ) (v : J → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ M.totalBoundaryCost c u v := by
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    cases M.finite i with
    | some j => exact hc i j
    | none => exact hu i
  · apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact le_rfl
    · exact hv j

/-- Relabelling transports all three coefficient families and preserves the sum. -/
theorem totalBoundaryCost_relabel (u : I' ≃ I) (v : J' ≃ J)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (c : I → J → ℝ) (uCost : I → ℝ) (vCost : J → ℝ) :
    (M.relabel u v (Equiv.refl _) (Equiv.refl _)).totalBoundaryCost (fun i j => c (u i) (v j)) (uCost ∘ u) (vCost ∘ v) =
      M.totalBoundaryCost c uCost vCost := by
  classical
  unfold totalBoundaryCost
  congr 1
  · have hf (i : I') :
        (match (M.relabel u v (Equiv.refl _) (Equiv.refl _)).finite i with
          | some j => c (u i) (v j)
          | none => uCost (u i)) =
        (match M.finite (u i) with
          | some j => c (u i) j
          | none => uCost (u i)) := by
      cases h : M.finite (u i) <;> simp [relabel, h]
    calc
      _ = ∑ i : I', match M.finite (u i) with
          | some j => c (u i) j
          | none => uCost (u i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hf i
      _ = _ := u.sum_comp (fun i => match M.finite i with
          | some j => c i j
          | none => uCost i)
  · have hh (j : J') :
        (∃ i : I', (M.relabel u v (Equiv.refl _) (Equiv.refl _)).finite i = some j) ↔
          ∃ i : I, M.finite i = some (v j) := by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨u i, ?_⟩
        cases h : M.finite (u i) with
        | none => simp [relabel, h] at hi
        | some k =>
          simp [relabel, h] at hi
          have hk : k = v j := v.symm_apply_eq.mp hi
          exact congrArg some hk
      · rintro ⟨i, hi⟩
        exact ⟨u.symm i, by simp [relabel, hi]⟩
    simpa only [Function.comp_apply, hh] using v.sum_comp
      (fun j => if ∃ i, M.finite i = some j then 0 else vCost j)

end TDA.Persistence.OccurrenceMatching
