import TDA.Filtration.AlphaLabelled
import TDA.Filtration.RationalAlphaExamples
import TDA.Simplicial.Collapse

set_option autoImplicit false

/-!
# A Čech-to-α collapse on the obtuse triangle

The labels `0, 1, 2` of `RationalAlpha.Examples.obtuse` are the sites `(0,0)`, `(4,0)` and
`(1,1)`. Both stages are taken on squared grades: `cech t` is
`Alpha.squaredCechFiltration (realSites obtuse) t`, the closed Čech complex at radius `√t` for
`t ≥ 0`, and `alpha t` is `Alpha.labelledComplexFiltration (realSites obtuse) t`.

`cechGrades` lists the squared Čech grades and `mem_cech_iff` proves them; `mem_alpha_iff`
reads the α stage off `gradedFaces obtuse` (`obtuse_grades`). The two tables differ only at
the long edge `{0,1}` and the triangle `{0,1,2}`, at grade `4` for Čech and `5` for α
(`cechGrades_sdiff`). For `4 ≤ t` the long edge is a free face of the triangle in `cech t`
(`isFreePair_long_edge`). Below grade `5` the α stage is the Čech stage without these two faces
(`mem_alpha_iff_of_lt_five`), that is, the deletion of the long edge; this deletion gives the α
stage exactly for `t < 5` (`alpha_eq_deletion_iff`). Outside `[4, 5)` the two stages are equal
(`alpha_eq_cech`), and they differ exactly on `[4, 5)` (`alpha_eq_cech_iff`). So `cech t`
collapses to `alpha t` at every grade (`collapsesTo`): by one elementary collapse on `[4, 5)`
and by the empty sequence elsewhere, and a single elementary collapse gives the α stage
exactly on `[4, 5)` (`elementaryCollapsesTo_iff`). The labelled inclusion
`alpha t ≤ cech t` is `Alpha.labelledComplexFiltration_le_squaredCech`; `CollapsesTo.le`
gives the same inclusion.

At `t = 5` the pair is still free in `cech 5`, but both faces belong to `alpha 5`. No fixed set
of faces cuts every Čech stage down to the α stage at the same grade
(`not_exists_fixed_faces`): the collapses form a family indexed by the grade, not one
same-grade matching whose critical faces are fixed across the filtration.
-/

namespace TDA.Filtration.AlphaCollapseExamples

open TDA.Simplicial TDA.Filtration.RationalAlpha TDA.Filtration.RationalAlpha.Examples

/-- The squared-grade Čech filtration of the obtuse triangle. -/
local notation "cech" => Alpha.squaredCechFiltration (realSites obtuse)

/-- The squared-grade α filtration of the obtuse triangle. -/
local notation "alpha" => Alpha.labelledComplexFiltration (realSites obtuse)

/-- The squared Čech grades of the faces of the obtuse triangle. -/
def cechGrades : Finset (Finset (Fin 3) × ℚ) :=
  {({0}, 0), ({1}, 0), ({2}, 0), ({0,2}, 1/2), ({1,2}, 5/2), ({0,1}, 4), ({0,1,2}, 4)}

/-- The two grade tables differ exactly at the long edge and the triangle. -/
theorem cechGrades_sdiff :
    cechGrades \ gradedFaces obtuse = {({0,1}, 4), ({0,1,2}, 4)} ∧
      gradedFaces obtuse \ cechGrades = {({0,1}, 5), ({0,1,2}, 5)} := by
  rw [obtuse_grades]
  decide +kernel

private theorem univ_faces : (Finset.univ : Finset (Finset (Fin 3))) =
    {∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} := by
  decide

private theorem cases_face (s : Finset (Fin 3)) :
    s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {2} ∨ s = {0,1} ∨ s = {0,2} ∨ s = {1,2} ∨ s = {0,1,2} := by
  have h := Finset.mem_univ s
  rw [univ_faces] at h
  simpa using h

private theorem dist_sq_site (c : Point) (v : Fin 3) :
    dist (castPoint c) (realSites obtuse v) ^ 2 = (sqDist c (obtuse v) : ℝ) :=
  distSq_cast c (obtuse v)

/-- A rational center within squared distance `q ≤ t` of every site of `s` witnesses
`s ∈ cech t`. -/
private theorem mem_cech_of_center {s : Finset (Fin 3)} (hs : s.Nonempty) (c : Point) (q : ℚ)
    (hc : ∀ v ∈ s, sqDist c (obtuse v) ≤ q) {t : ℝ} (ht : (q : ℝ) ≤ t) : s ∈ cech t := by
  obtain ⟨v₀, hv₀⟩ := hs
  have hq : (0 : ℝ) ≤ q := by
    have h := dist_sq_site c v₀
    have h' : (sqDist c (obtuse v₀) : ℝ) ≤ q := by exact_mod_cast hc v₀ hv₀
    nlinarith [sq_nonneg (dist (castPoint c) (realSites obtuse v₀))]
  have t0 : 0 ≤ t := hq.trans ht
  rw [Alpha.squaredCechFiltration_apply_of_nonneg _ t0, Cech.mem_complex_iff]
  refine ⟨⟨v₀, hv₀⟩, castPoint c, fun v hv => ?_⟩
  apply Real.le_sqrt_of_sq_le
  rw [dist_sq_site]
  exact (by exact_mod_cast hc v hv : (sqDist c (obtuse v) : ℝ) ≤ q).trans ht

/-- Two sites of a face of `cech t` are at squared distance at most `4 t`. -/
private theorem sqDist_le_of_mem_cech {s : Finset (Fin 3)} {t : ℝ} (h : s ∈ cech t)
    {v w : Fin 3} (hv : v ∈ s) (hw : w ∈ s) :
    0 ≤ t ∧ (sqDist (obtuse v) (obtuse w) : ℝ) ≤ 4 * t := by
  by_cases ht : t < 0
  · rw [Alpha.squaredCechFiltration_apply_of_neg _ ht] at h
    exact h.elim
  have t0 : 0 ≤ t := le_of_not_gt ht
  rw [Alpha.squaredCechFiltration_apply_of_nonneg _ t0] at h
  have hd := Cech.dist_le_two_mul_of_mem_complex _ h hv hw
  have hsq : dist (realSites obtuse v) (realSites obtuse w) ^ 2 =
      (sqDist (obtuse v) (obtuse w) : ℝ) := distSq_cast (obtuse v) (obtuse w)
  have hr := Real.sq_sqrt t0
  refine ⟨t0, ?_⟩
  rw [← hsq]
  nlinarith [dist_nonneg (x := realSites obtuse v) (y := realSites obtuse w),
    Real.sqrt_nonneg t]

/-- Squared Čech grades: a face of the obtuse triangle is in `cech t` exactly when its
grade in `cechGrades` is at most `t`. -/
theorem mem_cech_iff (s : Finset (Fin 3)) (t : ℝ) :
    s ∈ cech t ↔ ∃ q, (s, q) ∈ cechGrades ∧ (q : ℝ) ≤ t := by
  constructor
  · intro h
    rcases cases_face s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd h (fun h => (Finset.not_nonempty_empty
        ((Alpha.squaredCechFiltration (realSites obtuse) t).isRelLowerSet_faces h).1))
    · exact ⟨0, by decide, by simpa using (sqDist_le_of_mem_cech h (v := 0) (w := 0)
        (by decide) (by decide)).1⟩
    · exact ⟨0, by decide, by simpa using (sqDist_le_of_mem_cech h (v := 1) (w := 1)
        (by decide) (by decide)).1⟩
    · exact ⟨0, by decide, by simpa using (sqDist_le_of_mem_cech h (v := 2) (w := 2)
        (by decide) (by decide)).1⟩
    · have h' := (sqDist_le_of_mem_cech h (v := 0) (w := 1) (by decide) (by decide)).2
      have e : sqDist (obtuse 0) (obtuse 1) = 16 := by decide +kernel
      rw [e] at h'
      push_cast at h'
      exact ⟨4, by decide +kernel, by push_cast; linarith⟩
    · have h' := (sqDist_le_of_mem_cech h (v := 0) (w := 2) (by decide) (by decide)).2
      have e : sqDist (obtuse 0) (obtuse 2) = 2 := by decide +kernel
      rw [e] at h'
      push_cast at h'
      exact ⟨1/2, by decide +kernel, by push_cast; linarith⟩
    · have h' := (sqDist_le_of_mem_cech h (v := 1) (w := 2) (by decide) (by decide)).2
      have e : sqDist (obtuse 1) (obtuse 2) = 10 := by decide +kernel
      rw [e] at h'
      push_cast at h'
      exact ⟨5/2, by decide +kernel, by push_cast; linarith⟩
    · have h' := (sqDist_le_of_mem_cech h (v := 0) (w := 1) (by decide) (by decide)).2
      have e : sqDist (obtuse 0) (obtuse 1) = 16 := by decide +kernel
      rw [e] at h'
      push_cast at h'
      exact ⟨4, by decide +kernel, by push_cast; linarith⟩
  · rintro ⟨q, hq, ht⟩
    simp only [cechGrades, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hq
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
    · exact mem_cech_of_center (by decide) (0, 0) 0 (by decide +kernel) ht
    · exact mem_cech_of_center (by decide) (4, 0) 0 (by decide +kernel) ht
    · exact mem_cech_of_center (by decide) (1, 1) 0 (by decide +kernel) ht
    · exact mem_cech_of_center (by decide) (1/2, 1/2) (1/2) (by decide +kernel) ht
    · exact mem_cech_of_center (by decide) (5/2, 1/2) (5/2) (by decide +kernel) ht
    · exact mem_cech_of_center (by decide) (2, 0) 4 (by decide +kernel) ht
    · exact mem_cech_of_center (by decide) (2, 0) 4 (by decide +kernel) ht

/-- The α stage of the obtuse triangle is read off its exact grade table. -/
theorem mem_alpha_iff (s : Finset (Fin 3)) (t : ℝ) :
    s ∈ alpha t ↔ ∃ q, (s, q) ∈ gradedFaces obtuse ∧ (q : ℝ) ≤ t := by
  change s ∈ Alpha.complex (realSites obtuse) t ↔ _
  rw [mem_complex_iff]
  constructor
  · rintro ⟨r, hr, ht⟩
    exact ⟨r.grade, (mem_gradedFaces_iff obtuse r.grade).2 ⟨r, hr, rfl⟩, ht⟩
  · rintro ⟨q, hq, ht⟩
    obtain ⟨r, hr, rfl⟩ := (mem_gradedFaces_iff obtuse q).1 hq
    exact ⟨r, hr, ht⟩

/-- Outside `[4, 5)` the α stage is the Čech stage. -/
theorem alpha_eq_cech {t : ℝ} (ht : t < 4 ∨ 5 ≤ t) : alpha t = cech t := by
  refine SetLike.ext fun s => ?_
  rw [mem_alpha_iff, mem_cech_iff, obtuse_grades]
  rcases cases_face s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [cechGrades] <;>
    constructor <;> intro h <;> rcases ht with ht | ht <;> linarith

/-- For `4 ≤ t`, the long edge `{0,1}` is a free face of the triangle `{0,1,2}` in `cech t`. -/
theorem isFreePair_long_edge {t : ℝ} (ht : 4 ≤ t) : IsFreePair (cech t) {0,1} {0,1,2} where
  lower_mem := (mem_cech_iff _ _).2 ⟨4, by decide +kernel, by simpa using ht⟩
  upper_mem := (mem_cech_iff _ _).2 ⟨4, by decide +kernel, by simpa using ht⟩
  covBy := by
    rw [show ({0,1,2} : Finset (Fin 3)) = insert 2 {0,1} by decide]
    exact Finset.covBy_insert (by decide)
  eq_upper := by
    intro ω _ hω
    have key : ∀ ω : Finset (Fin 3), ({0,1} : Finset (Fin 3)) ⊂ ω → ω = {0,1,2} := by decide
    exact key ω hω

/-- Below grade `5` the α stage is the Čech stage without the long edge and the triangle. -/
theorem mem_alpha_iff_of_lt_five {t : ℝ} (ht : t < 5) (s : Finset (Fin 3)) :
    s ∈ alpha t ↔ s ∈ cech t ∧ s ≠ {0,1} ∧ s ≠ {0,1,2} := by
  rw [mem_alpha_iff, mem_cech_iff, obtuse_grades]
  rcases cases_face s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [cechGrades] <;>
    linarith

/-- Below grade `5` the α stage is the deletion of the long edge from the Čech stage. -/
theorem alpha_eq_deletion {t : ℝ} (ht : t < 5) : alpha t = deletion (cech t) {0,1} := by
  refine SetLike.ext fun s => ?_
  rw [mem_deletion, mem_alpha_iff_of_lt_five ht]
  rcases cases_face s with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})

/-- The deletion of the long edge gives the α stage exactly below grade `5`. -/
theorem alpha_eq_deletion_iff (t : ℝ) : alpha t = deletion (cech t) {0,1} ↔ t < 5 := by
  refine ⟨fun e => ?_, alpha_eq_deletion⟩
  by_contra h
  have h5 : ({0,1} : Finset (Fin 3)) ∈ alpha t := (obtuse_alpha_long_edge t).2 (le_of_not_gt h)
  rw [e] at h5
  exact h5.2 subset_rfl

/-- The Čech stage collapses to the α stage in one elementary collapse exactly on `[4, 5)`. -/
theorem elementaryCollapsesTo_iff (t : ℝ) :
    ElementaryCollapsesTo (cech t) (alpha t) ↔ 4 ≤ t ∧ t < 5 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hne
    exact (h.lt).ne (alpha_eq_cech (by
      rcases lt_or_ge t 4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr (le_of_not_gt fun h5 => hne ⟨h4, h5⟩)))
  · rw [alpha_eq_deletion h.2]
    exact (isFreePair_long_edge h.1).elementaryCollapsesTo

/-- At every grade the Čech stage collapses to the α stage: by one elementary collapse on
`[4, 5)` and by the empty sequence elsewhere. -/
theorem collapsesTo (t : ℝ) : CollapsesTo (cech t) (alpha t) := by
  rcases lt_or_ge t 4 with h4 | h4
  · rw [alpha_eq_cech (Or.inl h4)]
    exact Relation.ReflTransGen.refl
  rcases lt_or_ge t 5 with h5 | h5
  · exact Relation.ReflTransGen.single ((elementaryCollapsesTo_iff t).2 ⟨h4, h5⟩)
  · rw [alpha_eq_cech (Or.inr h5)]
    exact Relation.ReflTransGen.refl

/-- The α stage differs from the Čech stage exactly on `[4, 5)`. -/
theorem alpha_eq_cech_iff (t : ℝ) : alpha t = cech t ↔ t < 4 ∨ 5 ≤ t := by
  refine ⟨fun e => ?_, alpha_eq_cech⟩
  rcases lt_or_ge t 4 with h4 | h4
  · exact Or.inl h4
  have hc : ({0,1} : Finset (Fin 3)) ∈ cech t := (isFreePair_long_edge h4).lower_mem
  rw [← e] at hc
  exact Or.inr ((obtuse_alpha_long_edge t).1 hc)

/-- No fixed set `C` of faces cuts every Čech stage down to the α stage at the same grade. -/
theorem not_exists_fixed_faces :
    ¬ ∃ C : Set (Finset (Fin 3)), ∀ t s, s ∈ alpha t ↔ s ∈ cech t ∧ s ∈ C := by
  rintro ⟨C, hC⟩
  have h5 := ((hC 5 {0,1}).1 ((obtuse_alpha_long_edge 5).2 le_rfl)).2
  have h4 := (hC 4 {0,1}).2 ⟨(isFreePair_long_edge le_rfl).lower_mem, h5⟩
  exact absurd ((obtuse_alpha_long_edge 4).1 h4) (by norm_num)

end TDA.Filtration.AlphaCollapseExamples
