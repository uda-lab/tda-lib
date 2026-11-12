import TDA.Persistence.Reduction.FiniteInputRepresentativeCorrectness

/-! Integer-grade queries of the existing executable representative output. -/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- Half-open value aliveness, with no upper endpoint for essential occurrences. -/
def Occurrence.AliveAt (o : Occurrence) (a : ℤ) : Prop :=
  o.birth ≤ a ∧ match o.death with
    | .finite d => a < d
    | .essential => True

instance (o : Occurrence) (a : ℤ) : Decidable (o.AliveAt a) := by
  unfold Occurrence.AliveAt
  cases o.death <;> infer_instance

/-- Filter the unchanged represented output at an integer threshold. -/
def runAtGrade (xs : Input) (a : ℤ) : Option (List (Representative xs.length)) :=
  (runWithRepresentatives xs).map (List.filter (fun r => decide (r.occurrence.AliveAt a)))

theorem runAtGrade_eq_some_iff (xs : Input) (a : ℤ)
    (out : List (Representative xs.length)) :
    runAtGrade xs a = some out ↔ Valid xs ∧
      out = (representedOccurrences xs).filter (fun r => decide (r.occurrence.AliveAt a)) := by
  unfold runAtGrade
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨rs, hrs, rfl⟩
    obtain ⟨hv, rfl⟩ := (runWithRepresentatives_eq_some_iff xs rs).mp hrs
    exact ⟨hv, rfl⟩
  · rintro ⟨hv, rfl⟩
    exact ⟨_, (runWithRepresentatives_eq_some_iff xs _).mpr ⟨hv, rfl⟩, rfl⟩

theorem runAtGrade_eq_none_iff (xs : Input) (a : ℤ) :
    runAtGrade xs a = none ↔ ¬ Valid xs := by
  simp [runAtGrade, runWithRepresentatives_eq_none_iff]

theorem mem_runAtGrade (xs : Input) (a : ℤ) (out : List (Representative xs.length))
    (hout : runAtGrade xs a = some out) (r : Representative xs.length) :
    r ∈ out ↔ r ∈ representedOccurrences xs ∧ r.occurrence.AliveAt a := by
  rw [(runAtGrade_eq_some_iff xs a out).mp hout |>.2]
  simp

theorem runAtGrade_sublist (xs : Input) (a : ℤ) :
    ((representedOccurrences xs).filter (fun r => decide (r.occurrence.AliveAt a))).Sublist
      (representedOccurrences xs) := List.filter_sublist

theorem runAtGrade_forget (xs : Input) (a : ℤ) :
    (runAtGrade xs a).map (List.map Representative.occurrence) =
      (run xs).map (List.filter (fun o => decide (o.AliveAt a))) := by
  unfold runAtGrade
  rw [Option.map_map]
  rw [← runWithRepresentatives_forget xs, Option.map_map]
  congr 1
  funext rs
  simpa only [Function.comp_def] using
    (List.filter_map (f := Representative.occurrence)
      (p := fun o => decide (o.AliveAt a)) (l := rs)).symm

/-- Executable number of list faces admitted at the given threshold. -/
def sublevelStage (xs : Input) (a : ℤ) : ℕ :=
  (Finset.univ.filter (fun i : Fin xs.length => (xs.get i).2 ≤ a)).card

theorem sublevelStage_le_length (xs : Input) (a : ℤ) : sublevelStage xs a ≤ xs.length :=
  (Finset.card_filter_le _ _).trans (Finset.card_fin _).le

theorem sublevelStage_mono (xs : Input) : Monotone (sublevelStage xs) := by
  intro a b hab
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans hab

private theorem count_reindex {m n : ℕ} (hn : m = n) (g : Fin n → ℤ) (a : ℤ) :
    (Finset.univ.filter (fun i : Fin m => g (Fin.cast hn i) ≤ a)).card =
      (Finset.univ.filter (fun i : Fin n => g i ≤ a)).card := by
  cases hn
  rfl

theorem sublevelStage_eq_count (xs : Input) (h : Valid xs) (a : ℤ) :
    letI := faceFintype xs h
    sublevelStage xs a = (compatibleOrder xs h).sublevelCount a := by
  let := faceFintype xs h
  have hg : (gradeFilter xs h).value ∘ (compatibleOrder xs h).enum =
      fun i => (xs.get (Fin.cast (faceCount_eq_length xs h) i)).2 := by
    funext i
    exact (grade_eq_semantic xs h i).symm
  change _ = (Finset.univ.filter (fun i =>
    ((gradeFilter xs h).value ∘ (compatibleOrder xs h).enum) i ≤ a)).card
  rw [hg]
  exact (count_reindex (faceCount_eq_length xs h) (fun i => (xs.get i).2) a).symm

theorem grade_le_iff_index_lt_stage (xs : Input) (h : Valid xs) (a : ℤ)
    (i : Fin xs.length) : (xs.get i).2 ≤ a ↔ i.val < sublevelStage xs a := by
  let := faceFintype xs h
  rw [sublevelStage_eq_count xs h a]
  have hi : ((finCongr (faceCount_eq_length xs h)).symm i).val = i.val := by
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast]
  simpa only [← grade_eq_semantic xs h, Equiv.apply_symm_apply, hi] using
    (compatibleOrder xs h).value_le_iff_index_lt_sublevelCount a
      ((finCongr (faceCount_eq_length xs h)).symm i)

theorem sublevel_eq_prefix (xs : Input) (h : Valid xs) (a : ℤ) :
    letI := faceFintype xs h
    (gradeFilter xs h).sublevel a =
      (compatibleOrder xs h).prefixComplex (sublevelStage xs a) := by
  let := faceFintype xs h
  rw [sublevelStage_eq_count xs h a]
  exact (compatibleOrder xs h).sublevel_eq_prefixComplex a

end TDA.Persistence.Reduction.FiniteInput
