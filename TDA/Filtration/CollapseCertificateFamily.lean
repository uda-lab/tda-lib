import TDA.Simplicial.CollapseCertificate
import TDA.Filtration.Basic
import Mathlib.Basic.Real.Basic

set_option autoImplicit false

/-!
# Collapse certificates across the critical grades of a filtered pair

A real-indexed filtration `K` has the rational grade table `g : Finset (Finset V × ℚ)` when a
face is in `K t` exactly when it has a row of grade at most `t` (`HasGradeTable`). The grades are
closed: a row of grade `c` is present from `t = c` on. `stageTable g c` is the face table of the
rows of grade at most `c`; at a rational grade it is the face table of the stage itself
(`HasGradeTable.mem_cast_iff`).

For a pair `F`, `G` with grade tables `gF`, `gG`, `criticalGrades gF gG` is the finite set of all
grades of both tables; either filtration changes only at these grades. The real line splits into
three kinds of regime:
- below the least critical grade, both stages have no faces (`stages_of_lt_criticalGrades`);
- on `[c, d)` for a critical grade `c` and the next critical grade `d`, both stages are those at
  `c` (`stages_eq_stageTable_of_mem_Ico`);
- on the unbounded tail `[c, ∞)` from the greatest critical grade `c`, both stages are those
  at `c` (`stages_eq_stageTable_of_le_of_forall_le`).
The last two are cases of `stages_eq_stageTable`, and on each of them the stages are those at `c`
(`stages_eq_of_regime`).

A certificate family assigns a list of steps to every rational grade. `checkCertificates` checks,
by `Simplicial.checkSteps`, that at every critical grade `c` the steps collapse the stage table of
`gG` at `c` exactly onto the stage table of `gF` at `c`; below the least critical grade nothing is
checked, since both stages are empty there. Acceptance gives `CollapsesTo (G t) (F t)` at every
real grade `t` (`collapsesTo_of_checkCertificates`), and conversely every such pair of
filtrations has an accepted family (`exists_checkCertificates_of_collapsesTo`). The persistence
consequence is in `TDA.Persistence.CollapseCertificatePersistence`.

The certificates are supplied: nothing here produces them, and no general-position hypothesis
is used.

`checkCertificates` and `Simplicial.checkSteps` do not verify that a table is the face set of a
complex: they accept tables that no complex has, for example one that contains `∅` or lacks a
vertex of a listed face. The face-set hypotheses are carried by the theorems about acceptance.
-/

namespace TDA.Filtration

open TDA.Simplicial

variable {V : Type*}

/-- The real-indexed filtration `K` has the rational grade table `g`: a face is in `K t` exactly
when it has a row of grade at most `t`. -/
def HasGradeTable (K : SimplicialFiltration ℝ V) (g : Finset (Finset V × ℚ)) : Prop :=
  ∀ s t, s ∈ K t ↔ ∃ q, (s, q) ∈ g ∧ (q : ℝ) ≤ t

/-- The critical grades of a pair of grade tables: every grade of either table. -/
def criticalGrades (gF gG : Finset (Finset V × ℚ)) : Finset ℚ :=
  gF.image Prod.snd ∪ gG.image Prod.snd

/-- A grade is critical exactly when it is the grade of a row of one of the two tables. -/
theorem mem_criticalGrades {gF gG : Finset (Finset V × ℚ)} {c : ℚ} :
    c ∈ criticalGrades gF gG ↔ (∃ s, (s, c) ∈ gF) ∨ ∃ s, (s, c) ∈ gG := by
  simp [criticalGrades]

private theorem grade_mem_left {gF gG : Finset (Finset V × ℚ)} {r : Finset V × ℚ}
    (hr : r ∈ gF) : r.2 ∈ criticalGrades gF gG :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr)

private theorem grade_mem_right {gF gG : Finset (Finset V × ℚ)} {r : Finset V × ℚ}
    (hr : r ∈ gG) : r.2 ∈ criticalGrades gF gG :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)

/-- If `C` contains every grade of `g` and `t` is below every element of `C`, the stage of `K`
at `t` has no faces. -/
theorem HasGradeTable.notMem_of_lt {K : SimplicialFiltration ℝ V} {g : Finset (Finset V × ℚ)}
    (hK : HasGradeTable K g) {C : Finset ℚ} (hC : ∀ r ∈ g, r.2 ∈ C) {t : ℝ}
    (ht : ∀ q ∈ C, t < q) (s : Finset V) : s ∉ K t := by
  rw [hK]
  rintro ⟨q, hq, h⟩
  exact absurd h (not_le.2 (ht q (hC _ hq)))

variable {F G : SimplicialFiltration ℝ V} {gF gG : Finset (Finset V × ℚ)}

/-- Below the least critical grade, neither stage has a face. -/
theorem stages_of_lt_criticalGrades (hF : HasGradeTable F gF) (hG : HasGradeTable G gG)
    {t : ℝ} (ht : ∀ q ∈ criticalGrades gF gG, t < q) (s : Finset V) : s ∉ F t ∧ s ∉ G t :=
  ⟨hF.notMem_of_lt (fun _ => grade_mem_left) ht s,
    hG.notMem_of_lt (fun _ => grade_mem_right) ht s⟩

variable [DecidableEq V]

/-- The face table of the rows of `g` of grade at most `c`. -/
def stageTable (g : Finset (Finset V × ℚ)) (c : ℚ) : Finset (Finset V) :=
  (g.filter fun r => r.2 ≤ c).image Prod.fst

/-- A face is in the stage table at `c` exactly when it has a row of grade at most `c`. -/
theorem mem_stageTable {g : Finset (Finset V × ℚ)} {c : ℚ} {s : Finset V} :
    s ∈ stageTable g c ↔ ∃ q, (s, q) ∈ g ∧ q ≤ c := by
  simp [stageTable]

/-- At a rational grade, the stage of `K` has the stage table as its face table. -/
theorem HasGradeTable.mem_cast_iff {K : SimplicialFiltration ℝ V} {g : Finset (Finset V × ℚ)}
    (hK : HasGradeTable K g) (c : ℚ) (s : Finset V) : s ∈ K c ↔ s ∈ stageTable g c := by
  rw [hK, mem_stageTable]
  exact exists_congr fun q => and_congr_right fun _ => Rat.cast_le

/-- If `C` contains every grade of `g`, `c ≤ t`, and no element of `C` lies in `(c, t]`, then the
stage of `K` at `t` has the stage table at `c` as its face table. -/
theorem HasGradeTable.mem_iff_mem_stageTable {K : SimplicialFiltration ℝ V}
    {g : Finset (Finset V × ℚ)} (hK : HasGradeTable K g) {C : Finset ℚ}
    (hC : ∀ r ∈ g, r.2 ∈ C) {c : ℚ} {t : ℝ} (hc : (c : ℝ) ≤ t)
    (hgap : ∀ q ∈ C, c < q → t < q) (s : Finset V) : s ∈ K t ↔ s ∈ stageTable g c := by
  rw [hK, mem_stageTable]
  refine exists_congr fun q => and_congr_right fun hq => ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hlt
    exact absurd h (not_le.2 (hgap q (hC _ hq) (lt_of_not_ge hlt)))
  · exact (Rat.cast_le.2 h).trans hc

/-- If `c ≤ t` and no critical grade lies in `(c, t]`, both stages at `t` have the stage tables
at `c` as their face tables. -/
theorem stages_eq_stageTable (hF : HasGradeTable F gF) (hG : HasGradeTable G gG) {c : ℚ}
    {t : ℝ} (hc : (c : ℝ) ≤ t) (hgap : ∀ q ∈ criticalGrades gF gG, c < q → t < q)
    (s : Finset V) : (s ∈ F t ↔ s ∈ stageTable gF c) ∧ (s ∈ G t ↔ s ∈ stageTable gG c) :=
  ⟨hF.mem_iff_mem_stageTable (fun _ => grade_mem_left) hc hgap s,
    hG.mem_iff_mem_stageTable (fun _ => grade_mem_right) hc hgap s⟩

/-- On `[c, d)`, where no critical grade lies in `(c, d)`, both stages are those at `c`. -/
theorem stages_eq_stageTable_of_mem_Ico (hF : HasGradeTable F gF) (hG : HasGradeTable G gG)
    {c d : ℚ} (hnext : ∀ q ∈ criticalGrades gF gG, c < q → d ≤ q) {t : ℝ}
    (ht : t ∈ Set.Ico (c : ℝ) d) (s : Finset V) :
    (s ∈ F t ↔ s ∈ stageTable gF c) ∧ (s ∈ G t ↔ s ∈ stageTable gG c) :=
  stages_eq_stageTable hF hG ht.1
    (fun q hq hcq => ht.2.trans_le (Rat.cast_le.2 (hnext q hq hcq))) s

/-- On the unbounded tail `[c, ∞)` from a grade `c` at least every critical grade, both stages
are those at `c`. -/
theorem stages_eq_stageTable_of_le_of_forall_le (hF : HasGradeTable F gF)
    (hG : HasGradeTable G gG) {c : ℚ} (hlast : ∀ q ∈ criticalGrades gF gG, q ≤ c) {t : ℝ}
    (ht : (c : ℝ) ≤ t) (s : Finset V) :
    (s ∈ F t ↔ s ∈ stageTable gF c) ∧ (s ∈ G t ↔ s ∈ stageTable gG c) :=
  stages_eq_stageTable hF hG ht (fun q hq hcq => absurd (hlast q hq) (not_le.2 hcq)) s

/-- The stages are constant on each regime: if `c ≤ t` and no critical grade lies in `(c, t]`,
the stages at `t` are the stages at `c`. -/
theorem stages_eq_of_regime (hF : HasGradeTable F gF) (hG : HasGradeTable G gG) {c : ℚ}
    {t : ℝ} (hc : (c : ℝ) ≤ t) (hgap : ∀ q ∈ criticalGrades gF gG, c < q → t < q) :
    F t = F c ∧ G t = G c := by
  have e := stages_eq_stageTable hF hG hc hgap
  exact ⟨SetLike.ext fun s => (e s).1.trans (hF.mem_cast_iff c s).symm,
    SetLike.ext fun s => (e s).2.trans (hG.mem_cast_iff c s).symm⟩

/-- Accept the certificate family `cert` for the pair of grade tables: at every critical grade
`c`, the steps `cert c` collapse the stage table of `gG` at `c` exactly onto the stage table of
`gF` at `c`. -/
def checkCertificates (gF gG : Finset (Finset V × ℚ)) (cert : ℚ → List (Finset V × Finset V)) :
    Bool :=
  decide (∀ c ∈ criticalGrades gF gG,
    checkSteps (stageTable gG c) (cert c) (stageTable gF c) = true)

/-- Acceptance means that every critical grade has an accepted certificate with the exact
endpoint. -/
theorem checkCertificates_eq_true_iff {cert : ℚ → List (Finset V × Finset V)} :
    checkCertificates gF gG cert = true ↔ ∀ c ∈ criticalGrades gF gG,
      checkSteps (stageTable gG c) (cert c) (stageTable gF c) = true :=
  decide_eq_true_iff

/-- Soundness: if the family is accepted, the stage of `G` collapses to the stage of `F` at every
real grade. -/
theorem collapsesTo_of_checkCertificates (hF : HasGradeTable F gF) (hG : HasGradeTable G gG)
    {cert : ℚ → List (Finset V × Finset V)} (h : checkCertificates gF gG cert = true) (t : ℝ) :
    CollapsesTo (G t) (F t) := by
  classical
  rw [checkCertificates_eq_true_iff] at h
  by_cases hS : ∃ c ∈ criticalGrades gF gG, (c : ℝ) ≤ t
  · set S := (criticalGrades gF gG).filter fun c : ℚ => (c : ℝ) ≤ t
    have hne : S.Nonempty := by
      obtain ⟨c, hc, hct⟩ := hS
      exact ⟨c, Finset.mem_filter.2 ⟨hc, hct⟩⟩
    obtain ⟨hcC, hct⟩ := Finset.mem_filter.1 (S.max'_mem hne)
    have hgap : ∀ q ∈ criticalGrades gF gG, S.max' hne < q → t < q := by
      intro q hq hlt
      by_contra hle
      exact absurd (S.le_max' q (Finset.mem_filter.2 ⟨hq, le_of_not_gt hle⟩)) (not_le.2 hlt)
    have e := stages_eq_stageTable hF hG hct hgap
    exact collapsesTo_of_checkSteps (fun s => (e s).2) (fun s => (e s).1) (h _ hcC)
  · push Not at hS
    have e := stages_of_lt_criticalGrades hF hG hS
    have hGF : G t = F t := SetLike.ext fun s => iff_of_false (e s).2 (e s).1
    rw [hGF]
    exact Relation.ReflTransGen.refl

/-- An accepted family gives the levelwise inclusion of the stages of `F` in those of `G`. -/
theorem le_of_checkCertificates (hF : HasGradeTable F gF) (hG : HasGradeTable G gG)
    {cert : ℚ → List (Finset V × Finset V)} (h : checkCertificates gF gG cert = true) (t : ℝ) :
    F t ≤ G t :=
  (collapsesTo_of_checkCertificates hF hG h t).le

/-- Completeness: if the stage of `G` collapses to the stage of `F` at every grade, some
certificate family is accepted. -/
theorem exists_checkCertificates_of_collapsesTo (hF : HasGradeTable F gF)
    (hG : HasGradeTable G gG) (h : ∀ t, CollapsesTo (G t) (F t)) :
    ∃ cert, checkCertificates gF gG cert = true := by
  have key : ∀ c : ℚ, ∃ steps, checkSteps (stageTable gG c) steps (stageTable gF c) = true :=
    fun c => exists_checkSteps_of_collapsesTo (hG.mem_cast_iff c) (hF.mem_cast_iff c) (h c)
  choose cert hcert using key
  exact ⟨cert, checkCertificates_eq_true_iff.2 fun c _ => hcert c⟩

/-- For filtrations with grade tables `gF` and `gG`, the stage of `G` collapses to the stage of
`F` at every grade exactly when some certificate family is accepted. -/
theorem collapsesTo_iff_exists_checkCertificates (hF : HasGradeTable F gF)
    (hG : HasGradeTable G gG) :
    (∀ t, CollapsesTo (G t) (F t)) ↔ ∃ cert, checkCertificates gF gG cert = true :=
  ⟨exists_checkCertificates_of_collapsesTo hF hG,
    fun ⟨_, h⟩ => collapsesTo_of_checkCertificates hF hG h⟩

end TDA.Filtration
