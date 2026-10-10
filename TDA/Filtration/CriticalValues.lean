import TDA.Filtration.FilterFunction
import Mathlib.Data.Finset.Sort

/-!
# Finite critical-value filtrations

For a filter function on the supplied finite type of actual faces, this module forms the finite
image of its values, enumerates the distinct values increasingly, and reindexes its existing
sublevel filtration. Tied face values share a grade, and no sentinel or default grade is added.

The construction reuses the existing FilterFunction API and Finset.orderEmbOfFin from mathlib
at the pinned revision. It is a direct library construction, not a translation of a separate
persistence, homology, or Reeb theorem.
-/

set_option autoImplicit false

universe u w

namespace TDA.Filtration.FilterFunction

variable {V : Type u} {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]

/-- The finite set of values attained on actual faces of `K`. -/
def criticalValues (f : FilterFunction K α) : Finset α :=
  Finset.univ.image f.value

/-- The increasing enumeration of `criticalValues` by `Fin` using `orderEmbOfFin`. -/
def criticalValue (f : FilterFunction K α) :
    Fin (f.criticalValues.card) ↪o α :=
  f.criticalValues.orderEmbOfFin rfl

/-- The sublevel filtration reindexed by its distinct critical values. -/
def gradeFiltration (f : FilterFunction K α) :
    TDA.Filtration.SimplicialFiltration (Fin (f.criticalValues.card)) V :=
  TDA.Filtration.reindex f.criticalValue.toOrderHom f.sublevelFiltration

/-- Membership in `criticalValues` is exactly attainment on an actual face. -/
theorem mem_criticalValues (f : FilterFunction K α) (a : α) :
    a ∈ f.criticalValues ↔ ∃ s : TDA.Simplicial.TotalFace K, f.value s = a := by
  simp [criticalValues]

/-- The critical-value set is empty exactly for the bottom complex. -/
theorem criticalValues_eq_empty_iff (f : FilterFunction K α) :
    f.criticalValues = ∅ ↔ K = ⊥ := by
  constructor
  · intro h
    apply le_antisymm _ bot_le
    intro s hs
    have hm : f.value ⟨s, hs⟩ ∈ f.criticalValues :=
      (f.mem_criticalValues _).2 ⟨⟨s, hs⟩, rfl⟩
    simp [h] at hm
  · intro h
    ext a
    constructor
    · intro ha
      obtain ⟨s, _⟩ := (f.mem_criticalValues a).1 ha
      rw [h] at s
      exact ((TDA.Filtration.mem_bot_iff s.val).1 s.property).elim
    · intro ha
      simp at ha

/-- Every enumerated value belongs to the critical-value set. -/
theorem criticalValue_mem (f : FilterFunction K α)
    (i : Fin (f.criticalValues.card)) :
    f.criticalValue i ∈ f.criticalValues :=
  Finset.orderEmbOfFin_mem _ rfl i

private theorem exists_criticalValue_of_mem (f : FilterFunction K α) {a : α}
    (ha : a ∈ f.criticalValues) :
    ∃ i : Fin (f.criticalValues.card), f.criticalValue i = a := by
  have hr : a ∈ Set.range f.criticalValue := by
    rw [criticalValue, Finset.range_orderEmbOfFin]
    exact ha
  exact hr

/-- Each actual face value occurs at an enumerated grade. -/
theorem exists_criticalValue_eq (f : FilterFunction K α)
    (s : TDA.Simplicial.TotalFace K) :
    ∃ i : Fin (f.criticalValues.card), f.criticalValue i = f.value s := by
  apply f.exists_criticalValue_of_mem
  exact (f.mem_criticalValues _).2 ⟨s, rfl⟩

/-- A grade is the sublevel at its enumerated critical value. -/
theorem gradeFiltration_apply (f : FilterFunction K α)
    (i : Fin (f.criticalValues.card)) :
    f.gradeFiltration i = f.sublevel (f.criticalValue i) := rfl

/-- A threshold below the first grade has bottom sublevel. -/
theorem sublevel_eq_bot_of_lt_first (f : FilterFunction K α)
    (hN : 0 < f.criticalValues.card) (r : α)
    (hr : r < f.criticalValue ⟨0, hN⟩) :
    f.sublevel r = ⊥ := by
  apply f.sublevel_eq_bot_of_forall_lt
  intro s
  obtain ⟨i, hi⟩ := f.exists_criticalValue_eq s
  have h0 : (⟨0, hN⟩ : Fin (f.criticalValues.card)) ≤ i :=
    Fin.le_def.mpr (Nat.zero_le _)
  exact lt_of_lt_of_le hr ((f.criticalValue.monotone h0).trans_eq hi)

/-- A threshold between one grade and every later grade gives that stage. -/
theorem sublevel_eq_grade_of_gap (f : FilterFunction K α)
    (i : Fin (f.criticalValues.card)) (r : α)
    (hlo : f.criticalValue i ≤ r)
    (hgap : ∀ j : Fin (f.criticalValues.card), i < j → r < f.criticalValue j) :
    f.sublevel r = f.gradeFiltration i := by
  rw [f.gradeFiltration_apply]
  apply le_antisymm
  · intro s hs
    obtain ⟨hsK, hsr⟩ := (f.mem_sublevel_iff r s).1 hs
    obtain ⟨j, hj⟩ := f.exists_criticalValue_eq ⟨s, hsK⟩
    have hji : j ≤ i := by
      by_contra h
      have hij : i < j := lt_of_not_ge h
      exact (not_lt_of_ge hsr) (by simpa [hj] using hgap j hij)
    have hle : f.value ⟨s, hsK⟩ ≤ f.criticalValue i :=
      hj ▸ f.criticalValue.monotone hji
    exact (f.mem_sublevel_iff _ s).2 ⟨hsK, hle⟩
  · exact f.sublevel_mono hlo

/-- A threshold in an adjacent grade gap gives the lower stage. -/
theorem sublevel_eq_grade_of_adjacent (f : FilterFunction K α)
    (i j : Fin (f.criticalValues.card)) (hij : i.val + 1 = j.val)
    (r : α) (hlo : f.criticalValue i ≤ r) (hhi : r < f.criticalValue j) :
    f.sublevel r = f.gradeFiltration i := by
  apply f.sublevel_eq_grade_of_gap i r hlo
  intro k hik
  have hjk : j ≤ k := by
    apply Fin.le_def.mpr
    have hk : i.val < k.val := hik
    omega
  exact lt_of_lt_of_le hhi (f.criticalValue.monotone hjk)

/-- At or above the last grade the sublevel is exactly `K`. -/
theorem sublevel_eq_self_of_last_le (f : FilterFunction K α)
    (hN : 0 < f.criticalValues.card) (r : α)
    (hr : f.criticalValue
      ⟨f.criticalValues.card - 1, Nat.sub_lt hN (by decide)⟩ ≤ r) :
    f.sublevel r = K := by
  apply f.sublevel_eq_self_of_forall_le
  intro s
  obtain ⟨i, hi⟩ := f.exists_criticalValue_eq s
  have hilast : i ≤ (⟨f.criticalValues.card - 1,
      Nat.sub_lt hN (by decide)⟩ : Fin (f.criticalValues.card)) := by
    apply Fin.le_def.mpr
    change i.val ≤ f.criticalValues.card - 1
    have := i.isLt
    omega
  exact (hi ▸ (f.criticalValue.monotone hilast)).trans hr

/-- Every threshold gives bottom or one of the finite grade stages. -/
theorem sublevel_eq_bot_or_grade (f : FilterFunction K α) (r : α) :
    f.sublevel r = ⊥ ∨
      ∃ i : Fin (f.criticalValues.card),
        f.criticalValue i ≤ r ∧ f.sublevel r = f.gradeFiltration i := by
  classical
  let S : Finset α := f.criticalValues.filter (· ≤ r)
  by_cases hS : S.Nonempty
  · let a : α := S.max' hS
    have haS : a ∈ S := S.max'_mem hS
    have haC : a ∈ f.criticalValues := (Finset.mem_filter.mp haS).1
    have har : a ≤ r := (Finset.mem_filter.mp haS).2
    obtain ⟨i, hi⟩ := f.exists_criticalValue_of_mem haC
    right
    refine ⟨i, hi.symm ▸ har, ?_⟩
    apply f.sublevel_eq_grade_of_gap i r (hi.symm ▸ har)
    intro j hij
    have hiaj : a < f.criticalValue j := hi ▸ f.criticalValue.strictMono hij
    by_contra h
    have hjr : f.criticalValue j ≤ r := le_of_not_gt h
    have hjS : f.criticalValue j ∈ S :=
      Finset.mem_filter.mpr ⟨f.criticalValue_mem j, hjr⟩
    exact (not_lt_of_ge (S.le_max' _ hjS)) hiaj
  · left
    apply f.sublevel_eq_bot_of_forall_lt
    intro s
    have hsC : f.value s ∈ f.criticalValues :=
      (f.mem_criticalValues _).2 ⟨s, rfl⟩
    have hsNot : f.value s ∉ S := fun hs => hS ⟨_, hs⟩
    exact lt_of_not_ge (fun hle => hsNot (Finset.mem_filter.mpr ⟨hsC, hle⟩))

end TDA.Filtration.FilterFunction
