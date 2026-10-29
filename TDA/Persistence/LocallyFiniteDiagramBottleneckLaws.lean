import TDA.Persistence.LocallyFiniteDiagramBottleneck
import Mathlib.Topology.EMetricSpace.Defs

/-!
# Extended pseudometric laws for locally finite decorated diagrams

Composition and reversal of occurrence matchings give the bottleneck triangle
inequality and symmetry, including infinite costs and infinite occurrence sets.
The cost forgets endpoint decorations, so it defines an extended pseudometric.
-/

noncomputable section

namespace TDA.Persistence.LocallyFiniteDecoratedDiagram

open scoped ENNReal

variable {D E F : LocallyFiniteDecoratedDiagram}

local instance : DecidablePred (fun p : Prop => p) := fun _ => Classical.propDecidable _

private theorem source_le_matchingCost
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) (i : D.finiteOccurrences) :
    (match M.finite i with
      | some j => finitePairCost (D.finitePoint i) (E.finitePoint j)
      | none => diagonalCost (D.finitePoint i)) ≤ matchingCost M := by
  exact (le_iSup (fun i => match M.finite i with
    | some j => finitePairCost (D.finitePoint i) (E.finitePoint j)
    | none => diagonalCost (D.finitePoint i)) i).trans (le_max_left _ _)

private theorem target_le_matchingCost
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) (j : E.finiteOccurrences) :
    (if ∃ i, M.finite i = some j then 0 else diagonalCost (E.finitePoint j)) ≤
      matchingCost M := by
  classical
  exact (le_iSup (fun j => if ∃ i, M.finite i = some j then 0
    else diagonalCost (E.finitePoint j)) j).trans
      ((le_max_left _ _).trans (le_max_right _ _))

private theorem essential_le_matchingCost
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) (b : D.essentialOccurrences) :
    essentialPairCost (D.essentialBirth b) (E.essentialBirth (M.essential b)) ≤
      matchingCost M := by
  exact (le_iSup (fun b => essentialPairCost (D.essentialBirth b)
    (E.essentialBirth (M.essential b))) b).trans
      ((le_max_right _ _).trans (le_max_right _ _))

private theorem matchingCost_le_of
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) (r : ℝ≥0∞)
    (hs : ∀ i, (match M.finite i with
      | some j => finitePairCost (D.finitePoint i) (E.finitePoint j)
      | none => diagonalCost (D.finitePoint i)) ≤ r)
    (ht : ∀ j, (if ∃ i, M.finite i = some j then 0
      else diagonalCost (E.finitePoint j)) ≤ r)
    (he : ∀ b, essentialPairCost (D.essentialBirth b)
      (E.essentialBirth (M.essential b)) ≤ r) : matchingCost M ≤ r := by
  classical
  exact max_le (iSup_le hs) (max_le (iSup_le ht) (iSup_le he))

/-- Reverse a partial injection by taking the unique predecessor of each selected target. -/
def reverseMatching (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) :
    OccurrenceMatching E.finiteOccurrences D.finiteOccurrences
      E.essentialOccurrences D.essentialOccurrences where
  finite j := if h : ∃ i, M.finite i = some j then some h.choose else none
  finite_injective := by
    classical
    intro j j' i hj hj'
    change (if h : ∃ k, M.finite k = some j then some h.choose else none) = some i at hj
    change (if h : ∃ k, M.finite k = some j' then some h.choose else none) = some i at hj'
    split_ifs at hj hj' with h h'
    · have hi := h.choose_spec
      have hi' := h'.choose_spec
      have he : h.choose = h'.choose := Option.some.inj (hj.trans hj'.symm)
      exact Option.some.inj (hi.symm.trans (he ▸ hi'))
  essential := M.essential.symm

/-- A reversed finite match is exactly the original match with its endpoints exchanged. -/
@[simp] theorem reverseMatching_finite_some_iff
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences)
    (j : E.finiteOccurrences) (i : D.finiteOccurrences) :
    (reverseMatching M).finite j = some i ↔ M.finite i = some j := by
  classical
  constructor
  · intro h
    change (if he : ∃ k, M.finite k = some j then some he.choose else none) = some i at h
    split_ifs at h with he
    · have hi : he.choose = i := Option.some.inj h
      simpa [hi] using he.choose_spec
  · intro h
    have he : ∃ k, M.finite k = some j := ⟨i, h⟩
    have hi : he.choose = i := M.finite_injective _ _ _ he.choose_spec h
    change (if he : ∃ k, M.finite k = some j then some he.choose else none) = some i
    simp [he, hi]

/-- Reversing twice restores the original occurrence matching. -/
@[simp] theorem reverseMatching_reverseMatching
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) :
    reverseMatching (reverseMatching M) = M := by
  classical
  suffices hfinite : (reverseMatching (reverseMatching M)).finite = M.finite by
    have hessential : (reverseMatching (reverseMatching M)).essential = M.essential := rfl
    generalize reverseMatching (reverseMatching M) = N at hfinite hessential ⊢
    cases M
    cases N
    cases hfinite
    cases hessential
    rfl
  funext i
  cases h : M.finite i with
  | none =>
    have hh : (reverseMatching (reverseMatching M)).finite i = none := by
      cases h' : (reverseMatching (reverseMatching M)).finite i with
      | none => rfl
      | some j =>
        have hj := (reverseMatching_finite_some_iff (reverseMatching M) i j).mp h'
        have hi := (reverseMatching_finite_some_iff M j i).mp hj
        simp [h] at hi
    exact hh
  | some j =>
    exact (reverseMatching_finite_some_iff (reverseMatching M) i j).mpr
      ((reverseMatching_finite_some_iff M j i).mpr h)

private theorem matchingCost_reverse_le
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) :
    matchingCost (reverseMatching M) ≤ matchingCost M := by
  classical
  apply matchingCost_le_of
  · intro j
    cases hr : (reverseMatching M).finite j with
    | none =>
      have hn : ¬ ∃ i, M.finite i = some j := by
        intro ⟨i, hi⟩
        have hc := hr.symm.trans ((reverseMatching_finite_some_iff M j i).mpr hi)
        cases hc
      simpa [hr, hn] using target_le_matchingCost M j
    | some i =>
      have hi := (reverseMatching_finite_some_iff M j i).mp hr
      simpa [hr, hi, finitePairCost_comm] using source_le_matchingCost M i
  · intro i
    by_cases hi : ∃ j, (reverseMatching M).finite j = some i
    · rw [if_pos hi]
      exact bot_le
    · have hm : M.finite i = none := by
        cases h : M.finite i with
        | none => rfl
        | some j => exact (hi ⟨j, (reverseMatching_finite_some_iff M j i).mpr h⟩).elim
      simpa [hi, hm] using source_le_matchingCost M i
  · intro k
    simpa [reverseMatching, essentialPairCost_comm] using
      essential_le_matchingCost M (M.essential.symm k)

/-- Reversing an occurrence matching preserves its cost, including unmatched
finite occurrences and the essential boundary. -/
theorem matchingCost_reverse
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) :
    matchingCost (reverseMatching M) = matchingCost M := by
  apply le_antisymm (matchingCost_reverse_le M)
  simpa [reverseMatching_reverseMatching] using matchingCost_reverse_le (reverseMatching M)

/-- Composing occurrence matchings costs at most the sum of their costs. -/
theorem matchingCost_compose_le
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences)
    (N : OccurrenceMatching E.finiteOccurrences F.finiteOccurrences
      E.essentialOccurrences F.essentialOccurrences) :
    matchingCost (M.compose N) ≤ matchingCost M + matchingCost N := by
  classical
  apply matchingCost_le_of
  · intro i
    cases hm : M.finite i with
    | none =>
      have h := source_le_matchingCost M i
      simpa [OccurrenceMatching.compose, hm] using le_trans h (le_add_of_nonneg_right bot_le)
    | some j =>
      cases hn : N.finite j with
      | none =>
        have h₁ : finitePairCost (D.finitePoint i) (E.finitePoint j) ≤ matchingCost M := by
          simpa [hm] using source_le_matchingCost M i
        have h₂ : diagonalCost (E.finitePoint j) ≤ matchingCost N := by
          simpa [hn] using source_le_matchingCost N j
        have h := (diagonalCost_le_pair_add (D.finitePoint i) (E.finitePoint j)).trans (add_le_add h₁ h₂)
        simpa [OccurrenceMatching.compose, hm, hn] using h
      | some k =>
        have h₁ : finitePairCost (D.finitePoint i) (E.finitePoint j) ≤ matchingCost M := by
          simpa [hm] using source_le_matchingCost M i
        have h₂ : finitePairCost (E.finitePoint j) (F.finitePoint k) ≤ matchingCost N := by
          simpa [hn] using source_le_matchingCost N j
        have h := (finitePairCost_triangle (D.finitePoint i) (E.finitePoint j) (F.finitePoint k)).trans
          (add_le_add h₁ h₂)
        simpa [OccurrenceMatching.compose, hm, hn] using h
  · intro k
    by_cases hk : ∃ i, (M.compose N).finite i = some k
    · simp [hk]
    · by_cases hn : ∃ j, N.finite j = some k
      · obtain ⟨j, hj⟩ := hn
        have hm : ¬ ∃ i, M.finite i = some j := by
          rintro ⟨i, hi⟩
          apply hk
          exact ⟨i, by simp [OccurrenceMatching.compose, hi, hj]⟩
        have h₁ : diagonalCost (E.finitePoint j) ≤ matchingCost M := by
          simpa [hm] using target_le_matchingCost M j
        have h₂ : finitePairCost (E.finitePoint j) (F.finitePoint k) ≤ matchingCost N := by
          simpa [hj] using source_le_matchingCost N j
        have h := (diagonalCost_le_pair_add_rev (E.finitePoint j) (F.finitePoint k)).trans
          (add_le_add h₁ h₂)
        simpa [hk] using h
      · have h : diagonalCost (F.finitePoint k) ≤ matchingCost N := by
          simpa [hn] using target_le_matchingCost N k
        simpa [hk] using le_trans h (le_add_of_nonneg_left bot_le)
  · intro k
    have h₁ := essential_le_matchingCost M k
    have h₂ := essential_le_matchingCost N (M.essential k)
    exact (essentialPairCost_triangle (D.essentialBirth k) (E.essentialBirth (M.essential k))
      (F.essentialBirth (N.essential (M.essential k)))).trans (add_le_add h₁ h₂)

/-- A diagram has zero bottleneck distance to itself. -/
@[simp] theorem bottleneck_self (D : LocallyFiniteDecoratedDiagram) :
    D.bottleneck D = 0 := by
  classical
  let M : OccurrenceMatching D.finiteOccurrences D.finiteOccurrences
      D.essentialOccurrences D.essentialOccurrences :=
    ⟨some, by intro i i' j hi hi'; exact Option.some.inj (hi.trans hi'.symm), Equiv.refl _⟩
  have hc : matchingCost M = 0 := by
    simp [matchingCost, M, finitePairCost_self, essentialPairCost_self]
  exact le_antisymm ((iInf_le _ M).trans_eq hc) bot_le

/-- Bottleneck distance is symmetric on locally finite decorated diagrams. -/
theorem bottleneck_comm (D E : LocallyFiniteDecoratedDiagram) :
    D.bottleneck E = E.bottleneck D := by
  apply le_antisymm
  · apply le_iInf
    intro M
    exact (iInf_le _ (reverseMatching M)).trans_eq (matchingCost_reverse M)
  · apply le_iInf
    intro M
    exact (iInf_le _ (reverseMatching M)).trans_eq (matchingCost_reverse M)

/-- Bottleneck obeys the triangle inequality without assuming that the infimum
is attained or that any occurrence set is finite. -/
theorem bottleneck_triangle (D E F : LocallyFiniteDecoratedDiagram) :
    D.bottleneck F ≤ D.bottleneck E + E.bottleneck F := by
  apply ENNReal.le_iInf_add_iInf
  intro M N
  exact (iInf_le _ (M.compose N)).trans (matchingCost_compose_le M N)

/-- The bottleneck cost defines an extended pseudometric: endpoint decorations
are retained by diagrams but ignored by this distance. -/
instance instPseudoEMetricSpace : PseudoEMetricSpace LocallyFiniteDecoratedDiagram where
  edist := bottleneck
  edist_self := bottleneck_self
  edist_comm := bottleneck_comm
  edist_triangle := bottleneck_triangle

/-- The extended pseudometric uses exactly the occurrence-based bottleneck. -/
@[simp] theorem edist_eq_bottleneck (D E : LocallyFiniteDecoratedDiagram) :
    edist D E = D.bottleneck E := rfl

end TDA.Persistence.LocallyFiniteDecoratedDiagram
