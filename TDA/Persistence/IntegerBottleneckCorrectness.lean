import TDA.Persistence.IntegerBottleneck
import TDA.Persistence.DiagramBottleneck
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Algebra.Order.Ring.Int

/-! Correctness of the integer search with respect to the existing occurrence
matching cost and diagram bottleneck. All real-valued constructions in this file
belong to the semantic interpretation, not the executed search. -/

namespace TDA.Persistence.IntegerBottleneck

open scoped ENNReal

/-- Real finite coordinates of the original ordered presentation. -/
def realFinite (D : Presentation) (i : Fin D.finite.length) : ℝ × ℝ :=
  ((D.finite.get i).1, (D.finite.get i).2)

/-- Real essential coordinates of the original ordered presentation. -/
def realEssential (D : Presentation) (i : EssentialIndex D) : ℝ :=
  ((D.essential.get i : ℤ) : ℝ)

/-- Interpret an integer input through the existing diagonal-deleting `orderedQ`. -/
noncomputable def diagram (D : Presentation) : Diagram ℝ :=
  orderedQ D.finite.length D.essential.length (realFinite D, realEssential D)

/-- The proof-side interpretation of executable matching data. -/
noncomputable def Candidate.toMatching {D E : Presentation} (a : Candidate D E) :
    OccurrenceMatching (FiniteIndex D) (FiniteIndex E) (EssentialIndex D) (EssentialIndex E) where
  finite := a.1.1
  finite_injective := a.2.1
  essential := Equiv.ofBijective a.1.2 a.2.2

/-- Encode any existing occurrence matching as valid integer-index data. -/
def Candidate.ofMatching {D E : Presentation}
    (M : OccurrenceMatching (FiniteIndex D) (FiniteIndex E)
      (EssentialIndex D) (EssentialIndex E)) : Candidate D E :=
  ⟨(M.finite, M.essential), M.finite_injective, M.essential.bijective⟩

/-- Every mathematical occurrence matching is represented in the explicit search. -/
theorem matching_represented {D E : Presentation}
    (M : OccurrenceMatching (FiniteIndex D) (FiniteIndex E)
      (EssentialIndex D) (EssentialIndex E)) :
    Candidate.ofMatching M ∈ candidates D E ∧ (Candidate.ofMatching M).toMatching = M := by
  refine ⟨mem_candidates D E _, ?_⟩
  refine OccurrenceMatching.ext ?_ ?_
  · rfl
  · ext i; rfl

private theorem cast_natAbs_real (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

private theorem cast_natAbs_ennreal (z : ℤ) :
    (z.natAbs : ℝ≥0∞) = ENNReal.ofReal |(z : ℝ)| := by
  rw [← ENNReal.ofReal_natCast, cast_natAbs_real]

private theorem diagonalTwice_cast (p : ℤ × ℤ) :
    (diagonalTwice p : ℝ≥0∞) = 2 * diagonalCost ((p.1 : ℝ), (p.2 : ℝ)) := by
  rw [diagonalTwice, cast_natAbs_ennreal, diagonalCost]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [Int.cast_sub, ENNReal.ofReal_ofNat]
  rw [ENNReal.mul_div_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤)]

private theorem natCast_max (m n : ℕ) :
    ((max m n : ℕ) : ℝ≥0∞) = max (m : ℝ≥0∞) (n : ℝ≥0∞) :=
  (Nat.mono_cast : Monotone (fun n : ℕ => (n : ℝ≥0∞))).map_max

private theorem finiteTwice_cast (p q : ℤ × ℤ) :
    (finiteTwice p q : ℝ≥0∞) =
      2 * finitePairCost ((p.1 : ℝ), (p.2 : ℝ)) ((q.1 : ℝ), (q.2 : ℝ)) := by
  simp only [finiteTwice, Nat.cast_mul, Nat.cast_ofNat, natCast_max,
    cast_natAbs_ennreal, Int.cast_sub, finitePairCost, ENNReal.ofReal_max]

private theorem essentialTwice_cast (b c : ℤ) :
    (essentialTwice b c : ℝ≥0∞) = 2 * essentialPairCost (b : ℝ) (c : ℝ) := by
  simp only [essentialTwice, Nat.cast_mul, Nat.cast_ofNat,
    cast_natAbs_ennreal, Int.cast_sub, essentialPairCost]

private theorem natCast_sup {A : Type} (s : Finset A) (f : A → ℕ) :
    ((s.sup f : ℕ) : ℝ≥0∞) = s.sup (fun a => (f a : ℝ≥0∞)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sup_insert, ih, natCast_max]

private theorem two_mul_sup {A : Type} (s : Finset A) (f : A → ℝ≥0∞) :
    2 * s.sup f = s.sup (fun a => 2 * f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sup_insert, mul_max, ih]

/-- Executed integer costs are exactly twice the existing matching costs. -/
theorem twiceCost_eq {D E : Presentation} (a : Candidate D E) :
    (twiceCost a : ℝ≥0∞) = 2 * a.toMatching.cost
      (fun i => realFinite D i.1) (fun j => realFinite E j.1)
      (realEssential D) (realEssential E) := by
  classical
  simp only [twiceCost, natCast_max, natCast_sup, OccurrenceMatching.cost,
    mul_max, two_mul_sup]
  congr 1
  · apply Finset.sup_congr rfl
    intro i _
    cases h : a.1.1 i with
    | none => simpa [Candidate.toMatching, h, realFinite] using diagonalTwice_cast (D.finite.get i.1)
    | some j => simpa [Candidate.toMatching, h, realFinite] using
        finiteTwice_cast (D.finite.get i.1) (E.finite.get j.1)
  · congr 1
    · apply Finset.sup_congr rfl
      intro j _
      by_cases h : ∃ i, a.1.1 i = some j
      · simp [Candidate.toMatching, h]
      · simpa [Candidate.toMatching, h, realFinite] using diagonalTwice_cast (E.finite.get j.1)
    · apply Finset.sup_congr rfl
      intro i _
      exact essentialTwice_cast _ _

private noncomputable def realIndexEquiv (D : Presentation) :
    FiniteIndex D ≃ NonDiagonalIndices D.finite.length (realFinite D) where
  toFun i := ⟨i.1, by
    change (↑(D.finite.get i.1).1 : ℝ) ≠ ↑(D.finite.get i.1).2
    exact_mod_cast i.2⟩
  invFun i := ⟨i.1, by
    have h := i.2
    change (↑(D.finite.get i.1).1 : ℝ) ≠ ↑(D.finite.get i.1).2 at h
    exact_mod_cast h⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem finite_occurrences (D : Presentation) :
    (Finset.univ : Finset (FiniteIndex D)).val.map (fun i => realFinite D i.1) =
      finitePart (diagram D).points := by
  classical
  unfold diagram
  rw [← orderedQ_finite_occurrences D.finite.length D.essential.length
    (realFinite D, realEssential D)]
  have h := congrArg (Multiset.map (fun i => realFinite D i.1))
    (Multiset.map_univ_val_equiv (realIndexEquiv D))
  rw [Multiset.map_map] at h
  exact h

private theorem essential_occurrences (D : Presentation) :
    (Finset.univ : Finset (EssentialIndex D)).val.map (realEssential D) =
      essentialPart (diagram D).points :=
  orderedQ_essential_occurrences D.finite.length D.essential.length
    (realFinite D, realEssential D)

/-- The integer-index coordinates present precisely the existing real diagram. -/
theorem bottleneck_eq_integer_presentation (D E : Presentation) :
    bottleneck (diagram D) (diagram E) =
      presentationBottleneck (fun i : FiniteIndex D => realFinite D i.1)
        (fun j : FiniteIndex E => realFinite E j.1) (realEssential D) (realEssential E) := by
  exact bottleneck_eq_presentation _ _ _ _ _ _
    (finite_occurrences D) (finite_occurrences E)
    (essential_occurrences D) (essential_occurrences E)

/-- A returned occurrence matching attains the existing real bottleneck. -/
theorem solve_cost_eq (D E : Presentation) {a : Candidate D E}
    (h : solve D E = some a) :
    a.toMatching.cost (fun i => realFinite D i.1) (fun j => realFinite E j.1)
      (realEssential D) (realEssential E) = bottleneck (diagram D) (diagram E) := by
  rw [bottleneck_eq_integer_presentation]
  apply le_antisymm
  · apply le_iInf
    intro M
    have hm : (twiceCost a : ℝ≥0∞) ≤ (twiceCost (Candidate.ofMatching M) : ℝ≥0∞) :=
      Nat.cast_le.mpr (solve_minimal D E h (Candidate.ofMatching M))
    rw [twiceCost_eq, twiceCost_eq, (matching_represented M).2] at hm
    exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simp : (2 : ℝ≥0∞) ≠ ⊤)).mp hm
  · exact presentationBottleneck_le_cost _ _ _ _ a.toMatching

/-- Embed the exact doubled output in the extended nonnegative reals. -/
def embed (q : WithTop ℕ) : ℝ≥0∞ := q.recTopCoe ⊤ (fun n => (n : ℝ≥0∞))

@[simp] theorem embed_top : embed ⊤ = ⊤ := rfl

@[simp] theorem embed_coe (n : ℕ) : embed (n : WithTop ℕ) = (n : ℝ≥0∞) := rfl

/-- The executable value is twice the existing diagram bottleneck on every input. -/
theorem twiceDistance_correct (D E : Presentation) :
    embed (twiceDistance D E) = 2 * bottleneck (diagram D) (diagram E) := by
  cases h : solve D E with
  | none =>
    have hn := (solve_eq_none_iff D E).mp h
    have he : IsEmpty (OccurrenceMatching (FiniteIndex D) (FiniteIndex E)
        (EssentialIndex D) (EssentialIndex E)) :=
      ⟨fun M => hn ((candidate_nonempty_iff D E).mp ⟨Candidate.ofMatching M⟩)⟩
    rw [bottleneck_eq_integer_presentation]
    simp [twiceDistance, h, embed, presentationBottleneck]
  | some a =>
    simpa [twiceDistance, h] using
      (twiceCost_eq a).trans (congrArg (fun c : ℝ≥0∞ => 2 * c) (solve_cost_eq D E h))

/-- Read a computed finite doubled value as an exact real diagram distance. -/
theorem bottleneck_eq_of_twiceDistance (D E : Presentation) (q : ℕ)
    (h : twiceDistance D E = (q : WithTop ℕ)) :
    bottleneck (diagram D) (diagram E) = (q : ℝ≥0∞) / 2 := by
  apply (ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤)).mpr
  rw [← twiceDistance_correct, h, embed_coe]

/-- Read an even doubled output as an integer-valued real bottleneck distance. -/
theorem bottleneck_eq_nat_of_twiceDistance (D E : Presentation) (q : ℕ)
    (h : twiceDistance D E = ((2 * q : ℕ) : WithTop ℕ)) :
    bottleneck (diagram D) (diagram E) = (q : ℝ≥0∞) := by
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by simp)).mp
  rw [← twiceDistance_correct, h, embed_coe, Nat.cast_mul, Nat.cast_ofNat]

/-- Read an infinite computed output as infinity for the existing bottleneck. -/
theorem bottleneck_eq_top_of_twiceDistance (D E : Presentation)
    (h : twiceDistance D E = ⊤) : bottleneck (diagram D) (diagram E) = ⊤ := by
  have hc := (twiceDistance_correct D E).symm
  rw [h, embed_top] at hc
  simpa [ENNReal.mul_eq_top] using hc

/-- The public result's distance field has the same unconditional correctness contract. -/
theorem run_correct (D E : Presentation) :
    embed (run D E).twiceDistance = 2 * bottleneck (diagram D) (diagram E) :=
  twiceDistance_correct D E

/-- A returned result stores precisely its witness's doubled cost. -/
theorem run_finite_cost (D E : Presentation) {a : Candidate D E}
    (h : (run D E).matching = some a) :
    (run D E).twiceDistance = (twiceCost a : WithTop ℕ) := by
  change solve D E = some a at h
  change (match solve D E with
    | none => (⊤ : WithTop ℕ)
    | some b => (twiceCost b : WithTop ℕ)) = _
  rw [h]

/-- Every valid finite witness has the cost denoted by half its doubled integer cost. -/
theorem Candidate.cost_eq_half {D E : Presentation} (a : Candidate D E) :
    a.toMatching.cost (fun i => realFinite D i.1) (fun j => realFinite E j.1)
      (realEssential D) (realEssential E) = (twiceCost a : ℝ≥0∞) / 2 := by
  apply (ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤)).mpr
  exact (twiceCost_eq a).symm

/-- No mathematical occurrence matching has smaller cost than the returned witness. -/
theorem solve_optimal (D E : Presentation) {a : Candidate D E}
    (h : solve D E = some a)
    (M : OccurrenceMatching (FiniteIndex D) (FiniteIndex E)
      (EssentialIndex D) (EssentialIndex E)) :
    a.toMatching.cost (fun i => realFinite D i.1) (fun j => realFinite E j.1)
      (realEssential D) (realEssential E) ≤
      M.cost (fun i => realFinite D i.1) (fun j => realFinite E j.1)
        (realEssential D) (realEssential E) := by
  rw [solve_cost_eq D E h, bottleneck_eq_integer_presentation]
  exact presentationBottleneck_le_cost _ _ _ _ M

private theorem embed_injective : Function.Injective embed := by
  intro q r h
  induction q using WithTop.recTopCoe with
  | top =>
    induction r using WithTop.recTopCoe with
    | top => rfl
    | coe n => simp [embed] at h
  | coe m =>
    induction r using WithTop.recTopCoe with
    | top => simp [embed] at h
    | coe n =>
      change (m : ℝ≥0∞) = (n : ℝ≥0∞) at h
      have hmn : m = n := Nat.cast_injective h
      exact congrArg (fun n : ℕ => (n : WithTop ℕ)) hmn

/-- Changing ordered presentations without changing their diagrams preserves the
computed value. Occurrence labels and the chosen minimizer may still change. -/
theorem twiceDistance_eq_of_diagram_eq {D E D' E' : Presentation}
    (hD : diagram D = diagram D') (hE : diagram E = diagram E') :
    twiceDistance D E = twiceDistance D' E' := by
  apply embed_injective
  rw [twiceDistance_correct, twiceDistance_correct, hD, hE]

private theorem ofFn_realFinite (D : Presentation) :
    List.ofFn (realFinite D) = D.finite.map (fun p => ((p.1 : ℝ), (p.2 : ℝ))) := by
  change List.ofFn ((fun p : ℤ × ℤ => ((p.1 : ℝ), (p.2 : ℝ))) ∘ D.finite.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

private theorem ofFn_realEssential (D : Presentation) :
    List.ofFn (realEssential D) = D.essential.map (fun b : ℤ => (b : ℝ)) := by
  change List.ofFn ((fun b : ℤ => (b : ℝ)) ∘ D.essential.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- Reordering finite and essential lists preserves their interpreted diagram. -/
theorem diagram_eq_of_perm {D E : Presentation}
    (hf : D.finite.Perm E.finite) (he : D.essential.Perm E.essential) : diagram D = diagram E := by
  apply Diagram.ext
  simp only [diagram, orderedQ, ofFn_realFinite, ofFn_realEssential]
  rw [Multiset.coe_eq_coe.mpr (hf.map (fun p => ((p.1 : ℝ), (p.2 : ℝ)))),
    Multiset.coe_eq_coe.mpr (he.map (fun b : ℤ => (b : ℝ)))]

/-- The computed value is invariant under presentation permutations. -/
theorem twiceDistance_perm {D E D' E' : Presentation}
    (hDf : D.finite.Perm D'.finite) (hDe : D.essential.Perm D'.essential)
    (hEf : E.finite.Perm E'.finite) (hEe : E.essential.Perm E'.essential) :
    twiceDistance D E = twiceDistance D' E' :=
  twiceDistance_eq_of_diagram_eq (diagram_eq_of_perm hDf hDe) (diagram_eq_of_perm hEf hEe)

/-- Insert a diagonal pair at the beginning of the original finite list. -/
def Presentation.consDiagonal (D : Presentation) (b : ℤ) : Presentation :=
  ⟨(b, b) :: D.finite, D.essential⟩

@[simp] theorem diagram_consDiagonal (D : Presentation) (b : ℤ) :
    diagram (D.consDiagonal b) = diagram D := by
  apply Diagram.ext
  simp only [diagram, orderedQ, ofFn_realFinite, ofFn_realEssential]
  simp [Presentation.consDiagonal]

/-- Inserting or removing a diagonal pair on either side preserves the value. -/
theorem twiceDistance_consDiagonal (D E : Presentation) (b c : ℤ) :
    twiceDistance (D.consDiagonal b) (E.consDiagonal c) = twiceDistance D E :=
  twiceDistance_eq_of_diagram_eq (diagram_consDiagonal D b) (diagram_consDiagonal E c)

@[simp] theorem twiceDistance_consDiagonal_left (D E : Presentation) (b : ℤ) :
    twiceDistance (D.consDiagonal b) E = twiceDistance D E :=
  twiceDistance_eq_of_diagram_eq (diagram_consDiagonal D b) rfl

@[simp] theorem twiceDistance_consDiagonal_right (D E : Presentation) (b : ℤ) :
    twiceDistance D (E.consDiagonal b) = twiceDistance D E :=
  twiceDistance_eq_of_diagram_eq rfl (diagram_consDiagonal E b)

end TDA.Persistence.IntegerBottleneck
