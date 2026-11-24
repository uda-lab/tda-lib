import TDA.Filtration.CollapseCertificateFamily
import TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration

set_option autoImplicit false

/-!
# Actual Alpha stages from supplied rational grade rows

Filter the supplied rational rows at a real squared cutoff using the closed
comparison. Under the supplied certificate the surviving faces are exactly
the faces of the actual Alpha complex. A rational cutoff computes through
the existing rational stage table.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedStages

open Set
open scoped BigOperators
open TDA.Filtration TDA.Filtration.RationalAlpha TDA.Simplicial
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.SuppliedCarrier
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration

/-- A real closed cutoff on a finite rational grade table. -/
noncomputable def realStageTable {n : ℕ} (rows : Finset (Finset (Fin n) × ℚ)) (t : ℝ) :
    Finset (Finset (Fin n)) := by
  classical
  exact (rows.filter fun row => (row.2 : ℝ) ≤ t).image Prod.fst

/-- A face survives the real cutoff exactly when a row for it meets the cutoff. -/
theorem mem_realStageTable_iff {n : ℕ} {rows : Finset (Finset (Fin n) × ℚ)}
    {t : ℝ} {s : Finset (Fin n)} :
    s ∈ realStageTable rows t ↔ ∃ q, (s, q) ∈ rows ∧ (q : ℝ) ≤ t := by
  classical
  simp [realStageTable]

/-- At a rational threshold the real cutoff agrees with the executable rational stage table. -/
theorem realStageTable_cast {n : ℕ} (rows : Finset (Finset (Fin n) × ℚ)) (c : ℚ) :
    realStageTable rows (c : ℝ) = stageTable rows c := by
  ext s
  simp only [mem_realStageTable_iff, mem_stageTable, Rat.cast_le]

/-- The reference grade table describes the actual Alpha filtration at all real thresholds. -/
theorem reference_hasGradeTable {n : ℕ} (p : Fin n ↪ Point) :
    HasGradeTable (Alpha.complexFiltration (realSites p)) (gradedFaces p) := by
  intro s t
  change s ∈ Alpha.complex (realSites p) t ↔
    ∃ q : ℚ, (s, q) ∈ gradedFaces p ∧ (q : ℝ) ≤ t
  rw [RationalAlpha.mem_complex_iff p t]
  constructor
  · rintro ⟨r, hr, ht⟩
    exact ⟨r.grade, (mem_gradedFaces_iff p r.grade).2 ⟨r, hr, rfl⟩, ht⟩
  · rintro ⟨q, hq, ht⟩
    obtain ⟨r, hr, rfl⟩ := (mem_gradedFaces_iff p q).1 hq
    exact ⟨r, hr, ht⟩

section Certified

variable {m n k : ℕ} (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n)
    (hv : Function.Injective hull) (tri : Fin m → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i,j))) =
      ∑ j, signedEdge (cycleEdges hull j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p)

include hv hh hsite hccw hchain hpass hno in
/-- The certified supplied row set gives the exact actual Alpha grade table. -/
theorem supplied_hasGradeTable :
    HasGradeTable (Alpha.complexFiltration (realSites p)) (suppliedGrades p tri) := by
  rw [suppliedGrades_eq_reference p hull hv tri hh hsite hccw hchain hpass hno]
  exact reference_hasGradeTable p

include hv hh hsite hccw hchain hpass hno in
/-- At every real squared grade, the supplied cutoff gives actual Alpha membership. -/
theorem supplied_realStage_iff (s : Finset (Fin n)) (t : ℝ) :
    s ∈ realStageTable (suppliedGrades p tri) t ↔ s ∈ Alpha.complex (realSites p) t :=
  mem_realStageTable_iff.trans ((supplied_hasGradeTable p hull hv tri hh hsite hccw hchain
    hpass hno s t).symm)

include hv hh hsite hccw hchain hpass hno in
/-- The certified supplied cutoff gives the full set of actual Alpha faces. -/
theorem supplied_realStage_faces (t : ℝ) :
    (↑(realStageTable (suppliedGrades p tri) t) : Set (Finset (Fin n))) =
      (Alpha.complex (realSites p) t).faces := by
  ext s
  exact supplied_realStage_iff p hull hv tri hh hsite hccw hchain hpass hno s t

include hv hh hsite hccw hchain hpass hno in
/-- Below grade zero the certified supplied cutoff gives an empty stage. -/
theorem supplied_realStage_neg {t : ℝ} (ht : t < 0) :
    realStageTable (suppliedGrades p tri) t = ∅ := by
  ext s
  rw [supplied_realStage_iff p hull hv tri hh hsite hccw hchain hpass hno,
    Alpha.complex_eq_bot_of_neg (realSites p) ht]
  simp

end Certified

/-- An emitted face has a unique grade. It appears exactly at and above that grade. -/
theorem supplied_row_cutoff {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n)
    {s : Finset (Fin n)} {q : ℚ} (hq : (s, q) ∈ suppliedGrades p tri) (t : ℝ) :
    s ∈ realStageTable (suppliedGrades p tri) t ↔ (q : ℝ) ≤ t := by
  rw [mem_realStageTable_iff]
  constructor
  · rintro ⟨r, hr, ht⟩
    have he := ((mem_suppliedGrades p tri).1 hr).2
    have hq' := ((mem_suppliedGrades p tri).1 hq).2
    exact (Option.some.inj (he.symm.trans hq')) ▸ ht
  · exact fun ht => ⟨q, hq, ht⟩

/-- Both stage conventions exclude the empty label set at every grade. -/
theorem empty_never_emitted {m n : ℕ} (p : Fin n ↪ Point)
    (tri : Fin m → Fin 3 → Fin n) (t : ℝ) :
    (∅ : Finset (Fin n)) ∉ realStageTable (suppliedGrades p tri) t ∧
      (∅ : Finset (Fin n)) ∉ Alpha.complex (realSites p) t := by
  refine ⟨?_, ?_⟩
  · rw [mem_realStageTable_iff]
    rintro ⟨q, hq, _⟩
    exact (empty_excluded p tri).2 ((mem_suppliedGrades p tri).1 hq).1
  · intro h
    exact (empty_excluded p tri).1 ((Alpha.exists_mem_complex_iff (realSites p) ∅).1 ⟨t, h⟩)

end TDA.Filtration.RationalAlpha.SuppliedStages
