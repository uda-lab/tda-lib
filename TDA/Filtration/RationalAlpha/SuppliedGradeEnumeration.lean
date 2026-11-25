import TDA.Filtration.RationalAlpha.SuppliedCarrier

set_option autoImplicit false

/-!
# Executable grades of a supplied rational alpha triangulation

The enumeration uses the nonempty labelled faces of supplied triangles. It
assigns zero to vertices, squared circumradius to triangles, and the squared
distance at the nearest feasible bisector parameter to edges. Directed edge
occurrences identify the centers of one or two incident triangles. The output
is a finite set of face/grade pairs.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration

open Set
open scoped BigOperators Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha TDA.Simplicial
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.DirectedEdgeIncidence
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.EdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade
open TDA.Filtration.RationalAlpha.SuppliedCarrier

/-- Rational coordinate of a circumcenter in the directed midpoint/quarter-turn parameter. -/
def parameter (a b o : Point) : ℚ :=
  let m := RationalAlpha.midpoint a b
  let v := normal a b
  ((o.1-m.1)*(-v.2) + (o.2-m.2)*v.1) / sqDist b a

/-- Squared distance to the first site at a directed bisector parameter. -/
def squaredRadius (a b : Point) (s : ℚ) : ℚ :=
  sqDist b a / 4 + sqDist b a * s^2

/-- The closest parameter to zero on the outward ray ending at the incident center. -/
def hullParam (a b o : Point) : ℚ := min 0 (parameter a b o)

/-- The closest parameter to zero between the right and left incident centers. -/
def interiorParam (a b left right : Point) : ℚ :=
  max (parameter a b right) (min (parameter a b left) 0)

/-- All directed triangle edge occurrences, indexed by triangle and local edge. -/
def occurrenceList (m : ℕ) : List (Fin m × Fin 3) :=
  (List.finRange m).flatMap fun i => (List.finRange 3).map fun j => (i,j)

/-- Find an occurrence of the ordered edge by its labels. -/
def occurrence? {m n : ℕ} (tri : Fin m → Fin 3 → Fin n) (a b : Fin n) :
    Option (Fin m × Fin 3) :=
  (occurrenceList m).find? fun i => decide (occurrenceEdge tri i = (a,b))

/-- Compute the rational circumcenter using the supplied triangle order. -/
def centerAt? {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n) (i : Fin m) :
    Option Point :=
  circumcenter? (p (tri i 0)) (p (tri i 1)) (p (tri i 2))

/-- Look up the circumcenter for a directed edge occurrence. -/
def directedCenter? {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n) (a b : Fin n) :
    Option Point :=
  (occurrence? tri a b).bind fun i => centerAt? p tri i.1

/-- Compute the squared edge grade from one or two incident circumcenters. -/
def edgeGrade? {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n) (a b : Fin n) :
    Option ℚ :=
  match directedCenter? p tri a b, directedCenter? p tri b a with
  | some l, some r => some (squaredRadius (p a) (p b) (interiorParam (p a) (p b) l r))
  | some o, none => some (squaredRadius (p a) (p b) (hullParam (p a) (p b) o))
  | none, some o => some (squaredRadius (p b) (p a) (hullParam (p b) (p a) o))
  | none, none => none

/-- Find a supplied triangle by its unordered label set. -/
def facet? {m n : ℕ} (tri : Fin m → Fin 3 → Fin n) (s : Finset (Fin n)) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (labelVertices (tri i) = s)

/-- Compute the squared circumradius of a supplied triangle. -/
def triangleGrade? {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n) (i : Fin m) :
    Option ℚ :=
  (centerAt? p tri i).map fun o => sqDist o (p (tri i 0))

/-- Compute the grade for one face. The enumerator restricts queries to supplied faces.
`decide +kernel` does not reduce the `Finset.sort` in this lookup; `kernelGrade?` computes the
same value in the kernel (`kernelGrade?_eq_grade?`). -/
def grade? {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n) (s : Finset (Fin n)) :
    Option ℚ :=
  match s.sort with
  | [_] => some 0
  | [a,b] => edgeGrade? p tri a b
  | [_,_,_] => (facet? tri s).bind (triangleGrade? p tri)
  | _ => none

/-- Enumerate one rational row per successful lookup over the deduplicated set of
nonempty supplied faces. -/
def suppliedGrades {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n) :
    Finset (Finset (Fin n) × ℚ) :=
  (faceFinset tri).biUnion fun s => ((grade? p tri s).map fun q => (s,q)).toFinset

/-- A real bisector coordinate of a rational center equals the cast rational coordinate. -/
theorem cast_parameter_of_center {a b o : Point} (hab : a ≠ b) {t : ℝ}
    (h : bisectorPoint a b t = castPoint o) : (parameter a b o : ℝ) = t := by
  have hx := congrArg (fun x : Plane => x 0) h
  have hy := congrArg (fun x : Plane => x 1) h
  change (((a.1 : ℝ)+b.1)/2 - t*((b.2 : ℝ)-a.2)) = (o.1 : ℝ) at hx
  change (((a.2 : ℝ)+b.2)/2 + t*((b.1 : ℝ)-a.1)) = (o.2 : ℝ) at hy
  simp only [parameter, RationalAlpha.midpoint, normal, Rat.cast_div, Rat.cast_add,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_neg, Rat.cast_ofNat]
  rw [← directionSq_eq_sqDist, div_eq_iff (directionSq_pos hab).ne']
  unfold directionSq
  linear_combination ((b.2 : ℝ)-a.2)*hx - ((b.1 : ℝ)-a.1)*hy

/-- The rational squared radius agrees with the real bisector formula. -/
theorem cast_squaredRadius (a b : Point) (s : ℚ) :
    (squaredRadius a b s : ℝ) = directionSq a b / 4 + directionSq a b * (s : ℝ)^2 := by
  simp only [squaredRadius, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, directionSq_eq_sqDist]

private theorem occurrence_mem {m : ℕ} (i : Fin m × Fin 3) : i ∈ occurrenceList m := by
  obtain ⟨i,j⟩ := i
  simp [occurrenceList, List.mem_flatMap]

/-- A unique occurrence of an ordered edge is selected by the lookup. -/
theorem occurrence_found {m n : ℕ} (tri : Fin m → Fin 3 → Fin n) {a b : Fin n}
    {i : Fin m × Fin 3} (hi : occurrenceEdge tri i = (a,b))
    (hu : ∀ j, occurrenceEdge tri j = (a,b) → j = i) :
    occurrence? tri a b = some i := by
  unfold occurrence?
  cases h : (occurrenceList m).find? (fun j => decide (occurrenceEdge tri j = (a,b))) with
  | none =>
    have hn := List.find?_eq_none.mp h i (occurrence_mem i)
    simp [hi] at hn
  | some j =>
    have he : occurrenceEdge tri j = (a,b) := by simpa using List.find?_some h
    exact congrArg some (hu j he)

/-- Lookup returns no occurrence when the ordered edge never appears. -/
theorem occurrence_absent {m n : ℕ} (tri : Fin m → Fin 3 → Fin n) {a b : Fin n}
    (hn : ∀ j, occurrenceEdge tri j ≠ (a,b)) : occurrence? tri a b = none := by
  unfold occurrence?
  apply List.find?_eq_none.mpr
  intro j _
  simp [hn j]

private theorem directed_center_found {m n : ℕ} (p : Fin n ↪ Point)
    (tri : Fin m → Fin 3 → Fin n) {a b : Fin n} {i : Fin m × Fin 3}
    (D : IncidentCenter p tri i a b) (hu : ∀ j, occurrenceEdge tri j = (a,b) → j = i) :
    directedCenter? p tri a b = some D.center := by
  simp [directedCenter?, occurrence_found tri D.edge hu, centerAt?, D.computed]

/-- The edge calculation in either query order agrees with the hull witness. -/
theorem edge_hull_correct {m n : ℕ} (p : Fin n ↪ Point) (tri : Fin m → Fin 3 → Fin n)
    {a b : Fin n} (hab : a ≠ b) (D : HullDual p tri a b)
    (hn : ∀ j, occurrenceEdge tri j ≠ (b,a)) :
    ∃ q : ℚ, edgeGrade? p tri a b = some q ∧ edgeGrade? p tri b a = some q ∧
      (q : ℝ) = (Alpha.filter (realSites p)).value ⟨{a,b},D.carrier⟩ := by
  have hf := directed_center_found p tri D.incident D.unique
  have hr : directedCenter? p tri b a = none := by simp [directedCenter?, occurrence_absent tri hn]
  refine ⟨squaredRadius (p a) (p b) (hullParam (p a) (p b) D.incident.center),
    by simp [edgeGrade?,hf,hr], by simp [edgeGrade?,hf,hr], ?_⟩
  rw [D.grade, cast_squaredRadius]
  simp [hullParam, Rat.cast_min, cast_parameter_of_center (p.injective.ne hab) D.upper_center]

/-- The exact rational clamp uses the backward center for the lower bound and the forward one
for the upper bound in the same parameter. -/
theorem edge_interior_correct {m n : ℕ} (p : Fin n ↪ Point) (tri : Fin m → Fin 3 → Fin n)
    {a b : Fin n} (hab : a ≠ b) (D : InteriorDual p tri a b)
    (hinj : Function.Injective (occurrenceEdge tri)) :
    ∃ q : ℚ, edgeGrade? p tri a b = some q ∧
      (q : ℝ) = (Alpha.filter (realSites p)).value ⟨{a,b},D.carrier⟩ := by
  have hf := directed_center_found p tri D.left (fun _ h => hinj (h.trans D.left.edge.symm))
  have hr := directed_center_found p tri D.right (fun _ h => hinj (h.trans D.right.edge.symm))
  refine ⟨squaredRadius (p a) (p b) (interiorParam (p a) (p b) D.left.center D.right.center),
    by simp [edgeGrade?,hf,hr], ?_⟩
  rw [D.grade, cast_squaredRadius]
  simp [interiorParam, Rat.cast_min, Rat.cast_max,
    cast_parameter_of_center (p.injective.ne hab) D.lower_center,
    cast_parameter_of_center (p.injective.ne hab) D.upper_center]

private theorem labels_eq_triple {n : ℕ} (v : Fin 3 → Fin n) :
    labelVertices v = {v 0,v 1,v 2} := by
  ext j
  rw [mem_labelVertices]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

/-- The computed circumradius squared is the actual grade of a CCW triangle. -/
theorem triangle_grade_correct {m n : ℕ} (p : Fin n ↪ Point) (tri : Fin m → Fin 3 → Fin n)
    (i : Fin m) (hccw : 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hf : labelVertices (tri i) ∈ Alpha.carrier (realSites p)) :
    ∃ q : ℚ, triangleGrade? p tri i = some q ∧
      (q : ℝ) = (Alpha.filter (realSites p)).value ⟨labelVertices (tri i),hf⟩ := by
  obtain ⟨o,ho,_,_⟩ := circumcenter_exists_eq_sqDist _ _ _ hccw.ne'
  refine ⟨sqDist o (p (tri i 0)), by simp [triangleGrade?,centerAt?,ho], ?_⟩
  have hf' : ({tri i 0,tri i 1,tri i 2} : Finset (Fin n)) ∈ Alpha.carrier (castSites p) :=
    labels_eq_triple (tri i) ▸ hf
  have hg := triangle_actual_grade p (tri i 0) (tri i 1) (tri i 2) hccw ho hf'
  have he : (⟨labelVertices (tri i),hf⟩ : TotalFace (Alpha.carrier (realSites p))) =
      ⟨{tri i 0,tri i 1,tri i 2},hf'⟩ := Subtype.ext (labels_eq_triple (tri i))
  rw [he]
  exact hg.symm

/-- The actual alpha grade of a singleton is zero. -/
theorem singleton_grade_correct {n : ℕ} (p : Fin n ↪ Point) (a : Fin n)
    (hf : ({a} : Finset (Fin n)) ∈ Alpha.carrier (realSites p)) :
    (Alpha.filter (realSites p)).value ⟨{a},hf⟩ = 0 := by
  apply (Alpha.isLeast_grade (realSites p) ⟨{a},hf⟩).unique
  exact ⟨(Alpha.singleton_mem_complex_iff (realSites p) a 0).2 le_rfl,
    fun t ht => (Alpha.singleton_mem_complex_iff (realSites p) a t).1 ht⟩

private theorem no_occurrence_of_zero {m n : ℕ} (tri : Fin m → Fin 3 → Fin n)
    {a b : Fin n} (hz : directedMultiplicity (occurrenceEdge tri) (a,b) = 0) :
    ∀ i, occurrenceEdge tri i ≠ (a,b) := by
  intro i hi
  unfold directedMultiplicity at hz
  have hn (j : Fin m × Fin 3) (_ : j ∈ Finset.univ) :
      (0 : ℤ) ≤ if occurrenceEdge tri j = (a,b) then 1 else 0 := by split <;> omega
  have h := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hz i (Finset.mem_univ i)
  simp [hi] at h

private theorem grade_congr {n : ℕ} {p : Fin n ↪ Point} {s t : Finset (Fin n)}
    {hs : s ∈ Alpha.carrier (realSites p)} {ht : t ∈ Alpha.carrier (realSites p)} (he : s = t) :
    (Alpha.filter (realSites p)).value ⟨s,hs⟩ = (Alpha.filter (realSites p)).value ⟨t,ht⟩ :=
  congrArg (Alpha.filter (realSites p)).value (Subtype.ext he)

private theorem facet_found {m n : ℕ} (tri : Fin m → Fin 3 → Fin n) {s : Finset (Fin n)}
    (h : ∃ i, labelVertices (tri i) = s) :
    ∃ i, facet? tri s = some i ∧ labelVertices (tri i) = s := by
  obtain ⟨i, hi⟩ := h
  unfold facet?
  cases hfind : (List.finRange m).find? (fun j => decide (labelVertices (tri j) = s)) with
  | none =>
    have hn := List.find?_eq_none.mp hfind i (by simp)
    simp [hi] at hn
  | some j =>
    exact ⟨j, rfl, by simpa using List.find?_some hfind⟩

private theorem label_card_le_three {n : ℕ} (v : Fin 3 → Fin n) :
    (labelVertices v).card ≤ 3 :=
  Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin 3))

private theorem mem_faceFinset_iff {m n : ℕ} (tri : Fin m → Fin 3 → Fin n)
    (s : Finset (Fin n)) : s ∈ faceFinset tri ↔ s ∈ labelComplex tri := by
  change s ∈ faceFinset tri ↔ s ∈ (labelComplex tri).faces
  rw [faces_eq_finset]
  rfl

/-- A row occurs exactly when its face is supplied and its grade lookup returns the grade. -/
theorem mem_suppliedGrades {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n)
    {s : Finset (Fin n)} {q : ℚ} :
    (s,q) ∈ suppliedGrades p tri ↔ s ∈ labelComplex tri ∧ grade? p tri s = some q := by
  simp [suppliedGrades, Option.mem_def, Option.map_eq_some_iff, mem_faceFinset_iff]

/-- The labels of a face in increasing order, found by scanning every label. -/
def sortedLabels {n : ℕ} (s : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (· ∈ s)

/-- The label scan lists the same labels as `Finset.sort`, in the same order. -/
theorem sortedLabels_eq_sort {n : ℕ} (s : Finset (Fin n)) : sortedLabels s = s.sort :=
  List.SortedLT.eq_of_mem_iff
    (((List.sortedLT_finRange n).pairwise.filter _).sortedLT) (Finset.sortedLT_sort s)
    (fun a => by simp [sortedLabels])

/-- The grade lookup of `grade?` with the face labels read off by `sortedLabels`. It reduces
under `decide +kernel`. -/
def kernelGrade? {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n)
    (s : Finset (Fin n)) : Option ℚ :=
  match sortedLabels s with
  | [_] => some 0
  | [a,b] => edgeGrade? p tri a b
  | [_,_,_] => (facet? tri s).bind (triangleGrade? p tri)
  | _ => none

/-- The kernel-reducible lookup returns the grade of `grade?` on every face. -/
theorem kernelGrade?_eq_grade? {m n : ℕ} (p : Fin n → Point) (tri : Fin m → Fin 3 → Fin n)
    (s : Finset (Fin n)) : kernelGrade? p tri s = grade? p tri s := by
  rw [kernelGrade?, grade?, sortedLabels_eq_sort]

section Certified

variable {m n k : ℕ} (p : Fin n ↪ Point) (hull : Fin (k+3) → Fin n)
    (hv : Function.Injective hull) (tri : Fin m → Fin 3 → Fin n)
    (hh : PolygonCertificate (siteHull p hull) (fun j => realEdge p (cycleEdges hull j)))
    (hsite : ∀ i, castPoint (p i) ∈ siteHull p hull)
    (hccw : ∀ i, 0 < orient (p (tri i 0)) (p (tri i 1)) (p (tri i 2)))
    (hchain : (∑ i, ∑ j, signedEdge (occurrenceEdge tri (i,j))) =
      ∑ j, signedEdge (cycleEdges hull j))
    (hpass : ∀ i, checkIncircle p (tri i 0) (tri i 1) (tri i 2) = true)

include hv hh hsite hccw hchain hpass in
/-- The oriented incidence certificate determines the correct rational edge grade. -/
theorem edge_grade_on_supplied {a b : Fin n} (hab : a ≠ b)
    (hs : ({a,b} : Finset (Fin n)) ∈ (labelComplex tri).faces)
    (hf : ({a,b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p)) :
    ∃ q : ℚ, edgeGrade? p tri a b = some q ∧
      (q : ℝ) = (Alpha.filter (realSites p)).value ⟨{a,b},hf⟩ := by
  classical
  have hc := rational_edge_counts p p.injective hull hv tri hh hccw hchain
  by_cases h : ∃ j, cycleEdges hull j = (a,b) ∨ cycleEdges hull j = (b,a)
  · obtain ⟨j,hej | hej⟩ := h
    · obtain ⟨D⟩ := supplied_hull_dual p hull hv tri hh hccw hchain hpass hsite j
      rw [hej] at D
      have hz := (hc.2.1 j).2
      rw [hej] at hz
      obtain ⟨q,hq,_,hg⟩ := edge_hull_correct p tri hab D (no_occurrence_of_zero tri hz)
      exact ⟨q,hq,hg⟩
    · obtain ⟨D⟩ := supplied_hull_dual p hull hv tri hh hccw hchain hpass hsite j
      rw [hej] at D
      have hz := (hc.2.1 j).2
      rw [hej] at hz
      obtain ⟨q,_,hq,hg⟩ := edge_hull_correct p tri hab.symm D (no_occurrence_of_zero tri hz)
      exact ⟨q,hq,hg.trans (grade_congr (Finset.pair_comm b a))⟩
  · have hnh : ∀ j, cycleEdges hull j ≠ (a,b) ∧ cycleEdges hull j ≠ (b,a) :=
      fun j => ⟨fun h' => h ⟨j,Or.inl h'⟩,fun h' => h ⟨j,Or.inr h'⟩⟩
    obtain ⟨D⟩ := supplied_interior_dual p hull hv tri hh hccw hchain hpass hab hs hnh
    exact edge_interior_correct p tri hab D hc.1

include hv hh hsite hccw hchain hpass in
/-- Every supplied face in the actual carrier has a correct executable rational grade. -/
theorem grade_on_supplied_face {s : Finset (Fin n)}
    (hs : s ∈ labelComplex tri) (hf : s ∈ Alpha.carrier (realSites p)) :
    ∃ q : ℚ, grade? p tri s = some q ∧
      (q : ℝ) = (Alpha.filter (realSites p)).value ⟨s,hf⟩ := by
  have hFace := hs
  obtain ⟨hn,i,hsub⟩ := hs
  have hcard := (Finset.card_le_card hsub).trans (label_card_le_three (tri i))
  have hsort := Finset.sort_toFinset s (· ≤ ·)
  have hlen := Finset.length_sort (s := s) (· ≤ ·)
  have hnod := Finset.sort_nodup s (· ≤ ·)
  cases he : s.sort with
  | nil =>
    rw [he,List.toFinset_nil] at hsort
    exact False.elim (Finset.not_nonempty_empty (hsort.symm ▸ hn))
  | cons a ls =>
    cases ls with
    | nil =>
      have hEq : ({a} : Finset (Fin n)) = s := by simpa [he] using hsort
      have h1 : ({a} : Finset (Fin n)) ∈ Alpha.carrier (realSites p) := hEq ▸ hf
      refine ⟨0,by simp [grade?,he],?_⟩
      simpa using (singleton_grade_correct p a h1).symm.trans (grade_congr hEq)
    | cons b ls =>
      cases ls with
      | nil =>
        have hEq : ({a,b} : Finset (Fin n)) = s := by simpa [he] using hsort
        have hab : a ≠ b := by simpa [he] using hnod
        have hpair : ({a,b} : Finset (Fin n)) ∈ (labelComplex tri).faces := hEq ▸ hFace
        have hpairAlpha : ({a,b} : Finset (Fin n)) ∈ Alpha.carrier (realSites p) := hEq ▸ hf
        obtain ⟨q,hq,hg⟩ := edge_grade_on_supplied p hull hv tri hh hsite hccw hchain hpass
          hab hpair hpairAlpha
        exact ⟨q,by simp [grade?,he,hq],hg.trans (grade_congr hEq)⟩
      | cons c ls =>
        cases ls with
        | nil =>
          have h3 : s.card = 3 := by simpa [he] using hlen.symm
          have hEq : labelVertices (tri i) = s :=
            (Finset.eq_of_subset_of_card_le hsub ((label_card_le_three (tri i)).trans_eq h3.symm)).symm
          obtain ⟨j,hj,hEqj⟩ := facet_found tri ⟨i,hEq⟩
          have hjAlpha : labelVertices (tri j) ∈ Alpha.carrier (realSites p) := hEqj ▸ hf
          obtain ⟨q,hq,hg⟩ := triangle_grade_correct p tri j (hccw j) hjAlpha
          exact ⟨q,by simp [grade?,he,hj,hq],hg.trans (grade_congr hEqj)⟩
        | cons d ls =>
          rw [he] at hlen
          simp only [List.length_cons] at hlen
          omega

include hv hh hsite hccw hchain hpass in
/-- The executable rows equal the full rational reference rows under the supplied certificate.
The certificate gives site containment. The carrier equality also implies
`allSitesUsed` separately by `SuppliedCarrier.allSitesUsed_of_carrier_eq`. -/
theorem suppliedGrades_eq_reference
    (hno : GeometricNoFourCocircular p ∨ NoFourIncircleZeros p) :
    suppliedGrades p tri = gradedFaces p := by
  have he := carrier_eq_of_signed_boundary p hull hv tri hh hsite hccw hchain hpass hno
  ext row
  rcases row with ⟨s,q⟩
  rw [mem_suppliedGrades, mem_gradedFaces_iff]
  constructor
  · rintro ⟨hs,hq⟩
    have hf : s ∈ Alpha.carrier (realSites p) := he ▸ hs
    obtain ⟨r,hr⟩ := (exists_entry_iff p).2 hf
    obtain ⟨u,hu,hg⟩ := grade_on_supplied_face p hull hv tri hh hsite hccw hchain hpass hs hf
    have hqu := Option.some.inj (hq.symm.trans hu)
    have hg' := cast_grade p hf hr
    exact ⟨r,hr,Rat.cast_injective (hg'.trans (hqu ▸ hg).symm)⟩
  · rintro ⟨r,hr,rfl⟩
    have hf := (exists_entry_iff p).1 ⟨r,hr⟩
    have hs : s ∈ labelComplex tri := he ▸ hf
    obtain ⟨u,hu,hg⟩ := grade_on_supplied_face p hull hv tri hh hsite hccw hchain hpass hs hf
    have hue : u = r.grade := Rat.cast_injective (hg.trans (cast_grade p hf hr).symm)
    exact ⟨hs,hue ▸ hu⟩

end Certified

end TDA.Filtration.RationalAlpha.SuppliedGradeEnumeration
