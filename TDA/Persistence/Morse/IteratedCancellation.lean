import TDA.Persistence.Morse.FilteredContraction

/-!
# Iterated unit cancellation along a pivot schedule

A based complex `(ι, degree, grade, D)` is as in `TDA.Persistence.Morse.UnitCancellation`:
`D r c` is the coefficient of `r` in `d c`. A schedule is a list `l` of (lower, upper) pairs of
generators. `IsPivotSchedule grade D l` asks that

* the `2·|l|` endpoints (`scheduleEndpoints l`) are distinct;
* every pair `(a, b)` has `D a b = 1` and `grade a = grade b`;
* `l.Pairwise fun p q => D p.1 q.2 = 0`: the lower generator of a pair is never a face of the
  upper generator of a later pair.

`isPivotSchedule_iff_get` restates the last condition in indexed form: for pairs
`(a i, b i)` in schedule order, `D (a i) (b j) ≠ 0` with `i ≠ j` forces `j < i`, so the matched
block is unit lower triangular.

`cancelStep D a b r s = D r s - D r b * D a s` is the entry formula of `reducedDifferential`
on all of `ι`, and `scheduleMatrix l D` applies it along `l`, head first. Cancelling the head
`(a, b)` changes no column `s` with `D a s = 0` (`cancelStep_apply_of_eq_zero`); in a pivot
schedule this covers the upper generators of all later pairs
(`IsPivotSchedule.cancelStep_apply_snd`). So the tail is again a pivot schedule for
`cancelStep D a b` (`IsPivotSchedule.cancelStep`), and every later pair is a unit pair of
`reducedDifferential D a b` (`IsPivotSchedule.isUnitPair_reducedDifferential`).

The critical generators are `criticalSet l`, the generators that are not endpoints
(`mem_criticalSet`), with `card_critical`; `Critical l` is the subtype of original generators,
and `criticalDifferential D l` is `scheduleMatrix l D` restricted to it. For a filtered
differential `D`, `FilteredContraction.ofSchedule` composes the single cancellations of
`FilteredContraction.ofUnitPair` into a `FilteredContraction` of `(ι, degree, grade, D)` onto
`(Critical l, degree ∘ Subtype.val, grade ∘ Subtype.val, criticalDifferential D l)`. The
recursion `ofScheduleOn` runs on Finset-indexed carriers `{x // x ∈ S}`: each step is
`ofUnitPair`, transported by `reindex` along `survivorEquiv` and restated by `copy`
(`cancelOn`). `criticalDifferential_eq` gives `proj * D * incl`, and
`isFilteredDifferential_criticalDifferential` the filtered differential property.

All data are computable. The pivot invariant is sufficient for the head-first recursion, not
necessary: a schedule that violates it may still cancel. No explicit formula for the reduced
differential in terms of paths, no derivation of a schedule from an acyclic matching, and no
homology or persistence statement is provided here.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.Cancellation

section Schedule

variable {ι : Type*} {k : Type*} [CommRing k]

/-- All `2·|l|` endpoints of a list of (lower, upper) pairs, in order. -/
def scheduleEndpoints (l : List (ι × ι)) : List ι :=
  l.flatMap fun p => [p.1, p.2]

/-- The pivot invariant of a cancellation schedule `l` of (lower, upper) pairs for `D`:
the endpoints are distinct, every pair has coefficient `D a b = 1` and equal grades, and no
lower generator of a pair is a face of the upper generator of a later pair. -/
def IsPivotSchedule (grade : ι → ℤ) (D : Matrix ι ι k) (l : List (ι × ι)) : Prop :=
  (scheduleEndpoints l).Nodup ∧ (∀ p ∈ l, D p.1 p.2 = 1 ∧ grade p.1 = grade p.2) ∧
    l.Pairwise fun p q => D p.1 q.2 = 0

/-- The pivot invariant is a finite check over the schedule. -/
instance IsPivotSchedule.decidable [DecidableEq ι] [DecidableEq k] (grade : ι → ℤ)
    (D : Matrix ι ι k) (l : List (ι × ι)) : Decidable (IsPivotSchedule grade D l) := by
  unfold IsPivotSchedule
  infer_instance

/-- The pivot invariant in indexed form: distinct endpoints, unit equal-grade pairs, and
`D (a i) (b j) ≠ 0` with `i ≠ j` forces `j < i`, so the matched block is unit lower
triangular in schedule order. -/
theorem isPivotSchedule_iff_get {grade : ι → ℤ} {D : Matrix ι ι k} {l : List (ι × ι)} :
    IsPivotSchedule grade D l ↔
      (scheduleEndpoints l).Nodup ∧
      (∀ i : Fin l.length, D (l.get i).1 (l.get i).2 = 1 ∧
        grade (l.get i).1 = grade (l.get i).2) ∧
      ∀ i j : Fin l.length, i ≠ j → D (l.get i).1 (l.get j).2 ≠ 0 → j < i := by
  unfold IsPivotSchedule
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · exact fun h i => h _ (List.get_mem l i)
    · intro h p hp
      obtain ⟨i, rfl⟩ := List.get_of_mem hp
      exact h i
  · rw [List.pairwise_iff_get]
    constructor
    · intro h i j hij hne
      by_contra hlt
      exact hne (h i j (lt_of_le_of_ne (not_lt.mp hlt) hij))
    · intro h i j hij
      by_contra hne
      exact absurd (h i j (ne_of_lt hij) hne) (not_lt.mpr hij.le)

/-- `D r s - D r b * D a s` on all of `ι`: the entries of `reducedDifferential D a b`,
before restriction to the survivors. -/
def cancelStep (D : Matrix ι ι k) (a b : ι) : Matrix ι ι k :=
  fun r s => D r s - D r b * D a s

/-- Apply `cancelStep` along the schedule, head first. -/
def scheduleMatrix : List (ι × ι) → Matrix ι ι k → Matrix ι ι k
  | [], D => D
  | p :: l, D => scheduleMatrix l (cancelStep D p.1 p.2)

/-- A column whose `a`-entry vanishes is unchanged by `cancelStep D a b`. -/
theorem cancelStep_apply_of_eq_zero {D : Matrix ι ι k} {a b s : ι} (h : D a s = 0) (r : ι) :
    cancelStep D a b r s = D r s := by
  simp [cancelStep, h]

/-- Cancelling the head pair of a pivot schedule changes no column of a later upper
generator. -/
theorem IsPivotSchedule.cancelStep_apply_snd {grade : ι → ℤ} {D : Matrix ι ι k} {p : ι × ι}
    {l : List (ι × ι)} (h : IsPivotSchedule grade D (p :: l)) {q : ι × ι} (hq : q ∈ l)
    (r : ι) : cancelStep D p.1 p.2 r q.2 = D r q.2 :=
  cancelStep_apply_of_eq_zero ((List.pairwise_cons.mp h.2.2).1 q hq) r

/-- Cancelling the head pair of a pivot schedule leaves a pivot schedule for the tail. -/
theorem IsPivotSchedule.cancelStep {grade : ι → ℤ} {D : Matrix ι ι k} {p : ι × ι}
    {l : List (ι × ι)} (h : IsPivotSchedule grade D (p :: l)) :
    IsPivotSchedule grade (cancelStep D p.1 p.2) l := by
  have hcol := fun q (hq : q ∈ l) r => h.cancelStep_apply_snd hq r
  obtain ⟨hN, hC, hP⟩ := h
  rw [List.pairwise_cons] at hP
  refine ⟨?_, fun q hq => ?_, ?_⟩
  · simp only [scheduleEndpoints, List.flatMap_cons] at hN
    exact (List.nodup_append.mp hN).2.1
  · rw [hcol q hq]
    exact hC q (List.mem_cons_of_mem _ hq)
  · exact hP.2.imp_of_mem fun _ hb e => by rw [hcol _ hb]; exact e

/-- In a pivot schedule, the head pair is distinct from every endpoint of the tail. -/
theorem IsPivotSchedule.head_not_mem {grade : ι → ℤ} {D : Matrix ι ι k} {p : ι × ι}
    {l : List (ι × ι)} (h : IsPivotSchedule grade D (p :: l)) :
    p.1 ≠ p.2 ∧ p.1 ∉ scheduleEndpoints l ∧ p.2 ∉ scheduleEndpoints l := by
  have hN := h.1
  simp only [scheduleEndpoints, List.flatMap_cons] at hN
  obtain ⟨h1, -, h3⟩ := List.nodup_append.mp hN
  refine ⟨?_, fun hm => ?_, fun hm => ?_⟩
  · simpa using h1
  · exact h3 p.1 (by simp) p.1 hm rfl
  · exact h3 p.2 (by simp) p.2 hm rfl

/-- Every later pair of a pivot schedule is a unit pair of the reduced differential of the
head pair. -/
theorem IsPivotSchedule.isUnitPair_reducedDifferential
    {grade : ι → ℤ} {D : Matrix ι ι k} {a b : ι} {l : List (ι × ι)}
    (h : IsPivotSchedule grade D ((a, b) :: l)) {q : ι × ι} (hq : q ∈ l)
    (h₁ : q.1 ≠ a ∧ q.1 ≠ b) (h₂ : q.2 ≠ a ∧ q.2 ≠ b) :
    IsUnitPair (reducedDifferential D a b) ⟨q.1, h₁⟩ ⟨q.2, h₂⟩ := by
  have ht := h.cancelStep
  refine ⟨fun e => ?_, (ht.2.1 q hq).1⟩
  have hN := ht.1
  have hne : q.1 ≠ q.2 := by
    simp only [scheduleEndpoints] at hN
    simpa using (List.nodup_flatMap.mp hN).1 q hq
  exact hne (congrArg Subtype.val e)

/-- The generators of `S` that are not endpoints of the schedule, removed pair by pair. -/
def scheduleSurvivors [DecidableEq ι] : List (ι × ι) → Finset ι → Finset ι
  | [], S => S
  | p :: l, S => scheduleSurvivors l ((S.erase p.1).erase p.2)

/-- The survivors of `S` are its elements that are not endpoints of the schedule. -/
theorem mem_scheduleSurvivors [DecidableEq ι] {l : List (ι × ι)} {S : Finset ι} {x : ι} :
    x ∈ scheduleSurvivors l S ↔ x ∈ S ∧ x ∉ scheduleEndpoints l := by
  induction l generalizing S with
  | nil => simp [scheduleSurvivors, scheduleEndpoints]
  | cons p l ih =>
    simp only [scheduleSurvivors, ih, Finset.mem_erase, scheduleEndpoints, List.flatMap_cons,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
    tauto

variable [Fintype ι] [DecidableEq ι]

/-- The critical generators: those that are not endpoints of the schedule. -/
def criticalSet (l : List (ι × ι)) : Finset ι := scheduleSurvivors l Finset.univ

/-- A generator is critical exactly when it is not an endpoint of the schedule. -/
theorem mem_criticalSet {l : List (ι × ι)} {x : ι} :
    x ∈ criticalSet l ↔ x ∉ scheduleEndpoints l := by
  simp [criticalSet, mem_scheduleSurvivors]

/-- The critical generators as a subtype of the original generators. -/
abbrev Critical (l : List (ι × ι)) := {x : ι // x ∈ criticalSet l}

/-- A schedule with distinct endpoints leaves `card ι - 2·|l|` critical generators. -/
theorem card_critical {l : List (ι × ι)} (hN : (scheduleEndpoints l).Nodup) :
    Fintype.card (Critical l) = Fintype.card ι - 2 * l.length := by
  rw [Fintype.card_coe]
  have e : criticalSet l = Finset.univ \ (scheduleEndpoints l).toFinset := by
    ext x; simp [mem_criticalSet]
  have hl : (scheduleEndpoints l).length = 2 * l.length := by
    simp only [scheduleEndpoints, List.length_flatMap, List.length_cons, List.length_nil]
    simp [Nat.mul_comm]
  rw [e, Finset.card_univ_sdiff, List.toFinset_card_of_nodup hN, hl]

/-- The reduced differential on the critical generators. -/
def criticalDifferential (D : Matrix ι ι k) (l : List (ι × ι)) :
    Matrix (Critical l) (Critical l) k :=
  (scheduleMatrix l D).submatrix Subtype.val Subtype.val

end Schedule

namespace FilteredContraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [CommRing k]
  {degree : ι → ℕ} {grade : ι → ℤ}

/-- Forget the nesting of the survivors of a pair in a Finset-indexed carrier. -/
def survivorEquiv {S : Finset ι} {a b : ι} (ha : a ∈ S) (hb : b ∈ S) :
    PairSurvivor (⟨a, ha⟩ : S) ⟨b, hb⟩ ≃ (S.erase a).erase b where
  toFun u := ⟨u.val.val, Finset.mem_erase.mpr ⟨fun h => u.property.2 (Subtype.ext h),
    Finset.mem_erase.mpr ⟨fun h => u.property.1 (Subtype.ext h), u.val.property⟩⟩⟩
  invFun x := ⟨⟨x.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase x.property)⟩,
    fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp x.property).2).1
      (congrArg Subtype.val h),
    fun h => (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- One cancellation on a Finset-indexed carrier, restated on the flat carrier of the
remaining generators with the differential `cancelStep M a b`. -/
def cancelOn {M : Matrix ι ι k} {S : Finset ι} {a b : ι} (ha : a ∈ S) (hb : b ∈ S)
    (hM : IsFilteredDifferential (degree ∘ (Subtype.val : S → ι))
      (grade ∘ Subtype.val) (M.submatrix Subtype.val Subtype.val))
    (hab : a ≠ b) (h1 : M a b = 1) (hg : grade a = grade b) :
    FilteredContraction (degree ∘ (Subtype.val : S → ι)) (grade ∘ Subtype.val)
      (M.submatrix Subtype.val Subtype.val)
      (degree ∘ (Subtype.val : ↥((S.erase a).erase b) → ι)) (grade ∘ Subtype.val)
      ((cancelStep M a b).submatrix Subtype.val Subtype.val) :=
  ((ofUnitPair (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) hM
    ⟨fun h => hab (congrArg Subtype.val h), h1⟩ hg).reindex (survivorEquiv ha hb)).copy
      rfl rfl rfl

/-- Cancel a pivot schedule on a Finset-indexed carrier, head first. -/
def ofScheduleOn : (l : List (ι × ι)) → (S : Finset ι) → (M : Matrix ι ι k) →
    IsFilteredDifferential (degree ∘ (Subtype.val : S → ι)) (grade ∘ Subtype.val)
      (M.submatrix Subtype.val Subtype.val) →
    IsPivotSchedule grade M l → (∀ x ∈ scheduleEndpoints l, x ∈ S) →
    FilteredContraction (degree ∘ (Subtype.val : S → ι)) (grade ∘ Subtype.val)
      (M.submatrix Subtype.val Subtype.val)
      (degree ∘ (Subtype.val : scheduleSurvivors l S → ι)) (grade ∘ Subtype.val)
      ((scheduleMatrix l M).submatrix Subtype.val Subtype.val)
  | [], S, M, _, _, _ => refl _ _ _
  | p :: l, S, M, hM, hl, hS =>
    let c := cancelOn (degree := degree) (hS p.1 (by simp [scheduleEndpoints]))
      (hS p.2 (by simp [scheduleEndpoints])) hM hl.head_not_mem.1
      (hl.2.1 p (List.mem_cons_self ..)).1 (hl.2.1 p (List.mem_cons_self ..)).2
    c.trans (ofScheduleOn l ((S.erase p.1).erase p.2) (cancelStep M p.1 p.2)
      (c.isFilteredDifferential_target hM) hl.cancelStep fun x hx => by
        have hx' := hS x (by
          simp only [scheduleEndpoints, List.flatMap_cons, List.mem_append]
          exact Or.inr hx)
        obtain ⟨-, h1, h2⟩ := hl.head_not_mem
        refine Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hx), Finset.mem_erase.mpr
          ⟨fun e => h1 (e ▸ hx), hx'⟩⟩)

/-- The original complex, restated on the carrier `{x // x ∈ Finset.univ}`. -/
def toUniv (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k) :
    FilteredContraction degree grade D
      (degree ∘ (Subtype.val : ↥(Finset.univ : Finset ι) → ι)) (grade ∘ Subtype.val)
      (D.submatrix Subtype.val Subtype.val) :=
  ((refl degree grade D).reindex (Equiv.subtypeUnivEquiv Finset.mem_univ).symm).copy
    rfl rfl rfl

/-- Cancel all pairs of a pivot schedule, head first: a filtered contraction of the original
complex onto the critical generators with the reduced differential. -/
def ofSchedule {D : Matrix ι ι k} {l : List (ι × ι)}
    (hD : IsFilteredDifferential degree grade D) (hl : IsPivotSchedule grade D l) :
    FilteredContraction degree grade D (degree ∘ Subtype.val) (grade ∘ Subtype.val)
      (criticalDifferential D l) :=
  (toUniv degree grade D).trans
    (ofScheduleOn l Finset.univ D ((toUniv degree grade D).isFilteredDifferential_target hD)
      hl fun _ _ => Finset.mem_univ _)

/-- The reduced differential is `proj * D * incl` for the schedule contraction. -/
theorem criticalDifferential_eq {D : Matrix ι ι k} {l : List (ι × ι)}
    (hD : IsFilteredDifferential degree grade D) (hl : IsPivotSchedule grade D l) :
    criticalDifferential D l = (ofSchedule hD hl).proj * D * (ofSchedule hD hl).incl :=
  (ofSchedule hD hl).differential_eq

/-- The reduced differential is a filtered differential for the inherited degree and
grade. -/
theorem isFilteredDifferential_criticalDifferential {D : Matrix ι ι k} {l : List (ι × ι)}
    (hD : IsFilteredDifferential degree grade D) (hl : IsPivotSchedule grade D l) :
    IsFilteredDifferential (degree ∘ Subtype.val) (grade ∘ Subtype.val)
      (criticalDifferential D l) :=
  (ofSchedule hD hl).isFilteredDifferential_target hD

/-- The matrices of the schedule contraction depend on the differential only through its
value. -/
theorem ofSchedule_congr {D₁ D₂ : Matrix ι ι k} {l : List (ι × ι)} (e : D₁ = D₂)
    (h₁ : IsFilteredDifferential degree grade D₁) (hl₁ : IsPivotSchedule grade D₁ l)
    (h₂ : IsFilteredDifferential degree grade D₂) (hl₂ : IsPivotSchedule grade D₂ l) :
    (ofSchedule h₁ hl₁).proj = (ofSchedule h₂ hl₂).proj ∧
      (ofSchedule h₁ hl₁).incl = (ofSchedule h₂ hl₂).incl ∧
      (ofSchedule h₁ hl₁).htpy = (ofSchedule h₂ hl₂).htpy := by
  subst e
  exact ⟨rfl, rfl, rfl⟩

end FilteredContraction

end TDA.Persistence.Morse.Cancellation
