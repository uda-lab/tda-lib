import TDA.Filtration.RationalAlpha.SuppliedStages

set_option autoImplicit false

/-!
# Grades and stages for supplied triangulations with subdivided hull sides

`HullDual p tri a b` describes one directed edge: a unique incident occurrence, the closed
ray `edgeParameters = Iic upper`, the common cells as that ray, and the stage threshold
`D/4 + D·(min 0 upper)²`. None of its fields mentions the hull cycle. Only its coarse
constructor `supplied_hull_dual` reads the coarse cycle, through `rational_edge_counts`.
The refined boundary dual keeps the structure and adds a constructor for each refined side
`subdividedEdge (cycleEdges hull) cuts j`.

A subdivided hull side is treated as the chain of its pieces, each piece a triangle edge. Every
piece lies on the line of its coarse side, so its side form is a positive multiple of the coarse
one, and every site lies on its closed left side. Signed coverage of the subdivided chain gives
disjoint triangle interiors, so each directed triangle edge occurs at most once. The chain
coefficient shows that an edge occurring in one direction only is a refined side. The strict
coarse certificate excludes a refined side together with its reverse, so each refined side occurs
exactly once, forward. A supplied edge is then classified by its occurrences: an edge with both
directions gets an `InteriorDual`, an edge with one direction gets a `HullDual`, and there is no
third case. The coarse cycle is never consulted. With the carrier equality of
`carrier_eq_of_subdivided_boundary`, the supplied rows equal the reference rows, which gives all
real stages. The coarse theorems remain as stated; the refined ones need no injectivity of the
hull labels.
-/

namespace TDA.Filtration.RationalAlpha.SubdividedStages

open Set
open scoped BigOperators Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha TDA.Simplicial
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.SuppliedCarrier
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration
open TDA.Filtration.RationalAlpha.SuppliedStages

section Subdivided

variable {n k : ℕ} {I : Type*} [Fintype I] (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n)
    (cuts : Fin (k+3) → List (Fin n)) (tri : I → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hcuts : ∀ e, OrderedEdgeCuts p (cycleEdges hull e).2 (cycleEdges hull e).1 (cuts e))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) j)) =
      ∑ j, signedEdge (subdividedEdge (cycleEdges hull) cuts j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)

include hcuts in
/-- A refined hull side has the side form of its coarse side, scaled by a positive factor. -/
theorem subdivided_side_form (j : SubdivisionIndex (cycleEdges hull) cuts) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : Plane,
      edgeSide (realEdge p (subdividedEdge (cycleEdges hull) cuts j)) y =
        c * edgeSide (realEdge p (cycleEdges hull j.1)) y :=
  subdivisionEdges_side p _ _ _ (hcuts j.1) _ (List.get_mem _ j.2)

include hh hcuts hsite in
/-- Every site lies on the closed left side of every refined hull side. -/
theorem subdivided_supporting_side (j : SubdivisionIndex (cycleEdges hull) cuts) (x : Fin n) :
    0 ≤ orient (p (subdividedEdge (cycleEdges hull) cuts j).1)
      (p (subdividedEdge (cycleEdges hull) cuts j).2) (p x) := by
  obtain ⟨c, hc, hside⟩ := subdivided_side_form p hull cuts hcuts j
  have h : 0 ≤ edgeSide (realEdge p (cycleEdges hull j.1)) (castPoint (p x)) :=
    hh.left j.1 _ (hsite x)
  have hge : 0 ≤ edgeSide (realEdge p (subdividedEdge (cycleEdges hull) cuts j))
      (castPoint (p x)) := by
    rw [hside]
    exact mul_nonneg hc.le h
  change 0 ≤ edgeSide (castPoint (p _), castPoint (p _)) (castPoint (p x)) at hge
  rw [side_of_rational_sites] at hge
  exact_mod_cast hge

include hh hcuts in
/-- Some site lies strictly left of every refined hull side. -/
theorem subdivided_strict_site (j : SubdivisionIndex (cycleEdges hull) cuts) :
    ∃ x : Fin n, 0 < orient (p (subdividedEdge (cycleEdges hull) cuts j).1)
      (p (subdividedEdge (cycleEdges hull) cuts j).2) (p x) := by
  obtain ⟨c, hc, hside⟩ := subdivided_side_form p hull cuts hcuts j
  have hne : j.1 + 1 ≠ j.1 := by
    intro h
    have hz : (0 : Fin (k + 3)) = 1 := add_left_cancel (by simpa only [add_zero] using h.symm)
    have hv := congrArg Fin.val hz
    simp at hv
  have hpos (y : Fin n) (hy : 0 < edgeSide (realEdge p (cycleEdges hull j.1)) (castPoint (p y))) :
      0 < orient (p (subdividedEdge (cycleEdges hull) cuts j).1)
        (p (subdividedEdge (cycleEdges hull) cuts j).2) (p y) := by
    have h := hside (castPoint (p y))
    have hg : 0 < edgeSide (realEdge p (subdividedEdge (cycleEdges hull) cuts j))
        (castPoint (p y)) := by
      rw [h]
      exact mul_pos hc hy
    change 0 < edgeSide (castPoint (p _), castPoint (p _)) (castPoint (p y)) at hg
    rw [side_of_rational_sites] at hg
    exact_mod_cast hg
  rcases hh.strict_endpoint (j.1 + 1) j.1 hne with h | h
  · exact ⟨_, hpos _ h⟩
  · exact ⟨_, hpos _ h⟩

include hh hcuts hsite in
/-- No refined hull side is the reverse of another. -/
theorem subdivided_no_reverse (j l : SubdivisionIndex (cycleEdges hull) cuts) :
    subdividedEdge (cycleEdges hull) cuts l ≠ (subdividedEdge (cycleEdges hull) cuts j).swap := by
  intro he
  obtain ⟨x, hx⟩ := subdivided_strict_site p hull cuts hh hcuts j
  have hl := subdivided_supporting_side p hull cuts hh hcuts hsite l x
  rw [he] at hl
  change 0 ≤ orient (p (subdividedEdge (cycleEdges hull) cuts j).2)
    (p (subdividedEdge (cycleEdges hull) cuts j).1) (p x) at hl
  rw [(orient_swaps _ _ _).1] at hl
  linarith

include hh hcuts hsite hccw hchain in
/-- Each directed triangle edge occurs at most once under certified subdivided coverage. -/
theorem subdivided_occurrence_injective : Function.Injective (occurrenceEdge tri) := by
  have hc := (rational_cover_from_subdivided_signed_boundary p hull cuts tri hh hcuts
    (fun i j => hsite (tri i j)) hccw hchain).1
  apply occurrenceEdge_injective_of_disjoint_interiors p tri hccw
  intro i j hij
  apply disjoint_interiors_of_off_edge_bound (subdividedListedEdges p
    (fun i => triangleEdges (tri i 0) (tri i 1) (tri i 2)) (cycleEdges hull) cuts)
    (fun i => siteTriangle p (tri i)) _ hij
  intro x hx
  rw [hc x hx]
  unfold interiorIndicator
  split <;> omega

include hh hcuts hsite hccw hchain in
/-- Incidence counts of a subdivided boundary: each refined side occurs once forward and never
backward, and an edge that occurs forward but never backward is a refined side. -/
theorem subdivided_edge_counts :
    Function.Injective (occurrenceEdge tri) ∧
    (∀ j, directedMultiplicity (occurrenceEdge tri) (subdividedEdge (cycleEdges hull) cuts j) = 1 ∧
      directedMultiplicity (occurrenceEdge tri)
        (subdividedEdge (cycleEdges hull) cuts j).swap = 0) ∧
    (∀ e : Fin n × Fin n, (∃ i, occurrenceEdge tri i = e) →
      (∀ i, occurrenceEdge tri i ≠ e.swap) →
      ∃ j, subdividedEdge (cycleEdges hull) cuts j = e) := by
  have hinj := subdivided_occurrence_injective p hull cuts tri hh hcuts hsite hccw hchain
  have hflat : (∑ q : I × Fin 3, signedEdge (occurrenceEdge tri q)) =
      ∑ j, signedEdge (subdividedEdge (cycleEdges hull) cuts j) := by
    rw [Fintype.sum_prod_type]
    exact hchain
  have bal (e : Fin n × Fin n) := congrArg (fun c : (Fin n × Fin n) →₀ ℤ => c e) hflat
  simp only [chain_coefficient_eq_directed_counts] at bal
  have hnn (e : Fin n × Fin n) :
      0 ≤ directedMultiplicity (subdividedEdge (cycleEdges hull) cuts) e :=
    Finset.sum_nonneg (fun _ _ => by split <;> omega)
  refine ⟨hinj, fun j => ?_, fun e ⟨i, hi⟩ hnone => ?_⟩
  · have hr := multiplicity_absent (subdividedEdge (cycleEdges hull) cuts) _
      (fun l => subdivided_no_reverse p hull cuts hh hcuts hsite j l)
    have hf : 1 ≤ directedMultiplicity (subdividedEdge (cycleEdges hull) cuts)
        (subdividedEdge (cycleEdges hull) cuts j) := by
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun l => if subdividedEdge (cycleEdges hull) cuts l =
          subdividedEdge (cycleEdges hull) cuts j then (1 : ℤ) else 0)
        (fun _ _ => by split <;> omega) (Finset.mem_univ j)
      simpa [directedMultiplicity] using h
    have hb := bal (subdividedEdge (cycleEdges hull) cuts j)
    have h1 := multiplicity_at_most_one (occurrenceEdge tri) hinj
      (subdividedEdge (cycleEdges hull) cuts j)
    have h2 := multiplicity_at_most_one (occurrenceEdge tri) hinj
      (subdividedEdge (cycleEdges hull) cuts j).swap
    omega
  · have h1 : directedMultiplicity (occurrenceEdge tri) e = 1 :=
      hi ▸ multiplicity_listed _ hinj i
    have h0 := multiplicity_absent (occurrenceEdge tri) e.swap hnone
    by_contra hj
    push Not at hj
    have hb := bal e
    rw [h1, h0, multiplicity_absent _ e hj] at hb
    have := hnn e.swap
    omega

include hh hcuts hsite hccw hchain hpass in
/-- The refined boundary dual: every refined hull side, including each piece of a subdivided
coarse side, carries a `HullDual`. -/
theorem subdivided_hull_dual (j : SubdivisionIndex (cycleEdges hull) cuts) :
    Nonempty (HullDual p tri (subdividedEdge (cycleEdges hull) cuts j).1
      (subdividedEdge (cycleEdges hull) cuts j).2) := by
  obtain ⟨hinj, hcount, _⟩ := subdivided_edge_counts p hull cuts tri hh hcuts hsite hccw hchain
  have hex : ∃ i, occurrenceEdge tri i = subdividedEdge (cycleEdges hull) cuts j := by
    by_contra he
    push Not at he
    have h0 := multiplicity_absent (occurrenceEdge tri) _ he
    have h1 := (hcount j).1
    omega
  obtain ⟨i, hi⟩ := hex
  exact hull_dual_of_supporting_side p tri hi (fun l hl => hinj (hl.trans hi.symm))
    (hccw i.1) (hpass i.1) (subdivided_supporting_side p hull cuts hh hcuts hsite j)

end Subdivided

section SubdividedRows

variable {m n k : ℕ} (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n)
    (cuts : Fin (k+3) → List (Fin n)) (tri : Fin m → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hcuts : ∀ e, OrderedEdgeCuts p (cycleEdges hull e).2 (cycleEdges hull e).1 (cuts e))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (triangleEdges (tri i 0) (tri i 1) (tri i 2) j)) =
      ∑ j, signedEdge (subdividedEdge (cycleEdges hull) cuts j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p)

include hh hcuts hsite hccw hchain hpass in
/-- Under certified subdivided coverage, every supplied carrier edge has a correct rational
grade. Edges are classified by their directed occurrences, not by coarse hull sides. -/
theorem edge_grade_on_subdivided {a b : Fin n} (hab : a ≠ b)
    (hs : ({a, b} : Finset (Fin n)) ∈ (labelComplex tri).faces)
    (hf : ({a, b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p)) :
    ∃ q : ℚ, edgeGrade? p tri a b = some q ∧
      (q : ℝ) = (Alpha.filter (realSites p)).value ⟨{a, b}, hf⟩ := by
  obtain ⟨hinj, _, hside⟩ := subdivided_edge_counts p hull cuts tri hh hcuts hsite hccw hchain
  by_cases hF : ∃ i, occurrenceEdge tri i = (a, b)
  · by_cases hR : ∃ i, occurrenceEdge tri i = (b, a)
    · obtain ⟨f, hf'⟩ := hF
      obtain ⟨r, hr'⟩ := hR
      obtain ⟨D⟩ := interior_dual_of_opposite_occurrences p tri hccw hpass hf' hr'
      exact edge_interior_correct p tri hab D hinj
    · push Not at hR
      obtain ⟨j, hj⟩ := hside (a, b) hF hR
      obtain ⟨D⟩ := subdivided_hull_dual p hull cuts tri hh hcuts hsite hccw hchain hpass j
      rw [hj] at D
      obtain ⟨q, hq, _, hg⟩ := edge_hull_correct p tri hab D hR
      exact ⟨q, hq, hg⟩
  · push Not at hF
    obtain ⟨i, hi | hi⟩ := (pair_mem_iff_occurrence tri hab).1 hs
    · exact absurd hi (hF i)
    · obtain ⟨j, hj⟩ := hside (b, a) ⟨i, hi⟩ hF
      obtain ⟨D⟩ := subdivided_hull_dual p hull cuts tri hh hcuts hsite hccw hchain hpass j
      rw [hj] at D
      obtain ⟨q, _, hq, hg⟩ := edge_hull_correct p tri hab.symm D hF
      exact ⟨q, hq, hg.trans (congrArg (Alpha.filter (realSites p)).value
        (Subtype.ext (Finset.pair_comm b a)))⟩

include hh hcuts hsite hccw hchain hpass in
/-- Every supplied carrier face has a correct executable grade under subdivided coverage. -/
theorem grade_on_subdivided_face {s : Finset (Fin n)}
    (hs : s ∈ labelComplex tri) (hf : s ∈ Alpha.carrier (realSites p)) :
    ∃ q : ℚ, grade? p tri s = some q ∧
      (q : ℝ) = (Alpha.filter (realSites p)).value ⟨s, hf⟩ :=
  grade_on_face_of_edge_grades p tri hccw
    (fun hab hpair hpf => edge_grade_on_subdivided p hull cuts tri hh hcuts hsite hccw hchain
      hpass hab hpair hpf) hs hf

include hh hcuts hsite hccw hchain hpass hno in
/-- Analogue of `suppliedGrades_eq_reference` for a subdivided hull. -/
theorem suppliedGrades_eq_reference_of_subdivided_boundary :
    suppliedGrades p tri = gradedFaces p :=
  suppliedGrades_eq_reference_of_face_grades p tri
    (carrier_eq_of_subdivided_boundary p hull cuts tri hh hcuts hsite hccw hchain hpass hno)
    (fun hs hf => grade_on_subdivided_face p hull cuts tri hh hcuts hsite hccw hchain hpass hs hf)

include hh hcuts hsite hccw hchain hpass hno in
/-- Analogue of `supplied_hasGradeTable` for a subdivided hull. -/
theorem supplied_hasGradeTable_of_subdivided_boundary :
    HasGradeTable (Alpha.complexFiltration (realSites p)) (suppliedGrades p tri) := by
  rw [suppliedGrades_eq_reference_of_subdivided_boundary p hull cuts tri hh hcuts hsite hccw
    hchain hpass hno]
  exact reference_hasGradeTable p

include hh hcuts hsite hccw hchain hpass hno in
/-- Analogue of `supplied_realStage_iff` for a subdivided hull. -/
theorem supplied_realStage_iff_of_subdivided_boundary (s : Finset (Fin n)) (t : ℝ) :
    s ∈ realStageTable (suppliedGrades p tri) t ↔ s ∈ Alpha.complex (realSites p) t :=
  mem_realStageTable_iff.trans ((supplied_hasGradeTable_of_subdivided_boundary p hull cuts tri
    hh hcuts hsite hccw hchain hpass hno s t).symm)

include hh hcuts hsite hccw hchain hpass hno in
/-- Analogue of `supplied_realStage_faces` for a subdivided hull. -/
theorem supplied_realStage_faces_of_subdivided_boundary (t : ℝ) :
    (↑(realStageTable (suppliedGrades p tri) t) : Set (Finset (Fin n))) =
      (Alpha.complex (realSites p) t).faces := by
  ext s
  exact supplied_realStage_iff_of_subdivided_boundary p hull cuts tri hh hcuts hsite hccw hchain
    hpass hno s t

include hh hcuts hsite hccw hchain hpass hno in
/-- Analogue of `supplied_realStage_neg` for a subdivided hull. -/
theorem supplied_realStage_neg_of_subdivided_boundary {t : ℝ} (ht : t < 0) :
    realStageTable (suppliedGrades p tri) t = ∅ := by
  ext s
  rw [supplied_realStage_iff_of_subdivided_boundary p hull cuts tri hh hcuts hsite hccw hchain
    hpass hno,
    Alpha.complex_eq_bot_of_neg (realSites p) ht]
  simp

end SubdividedRows

end TDA.Filtration.RationalAlpha.SubdividedStages
