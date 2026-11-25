import TDA.Filtration.RationalAlpha.SuppliedCarrier
import TDA.Filtration.RationalAlpha.EdgeGradeExamples

set_option autoImplicit false

/-!
# Exact fixtures for the supplied Alpha carrier

The certified trapezoid gives literal carrier equality. The cocircular
square has a four-label face in the actual carrier, while its supplied
triangles still give valid Alpha faces.
-/

namespace TDA.Filtration.RationalAlpha.SuppliedCarrierExamples

open Set
open scoped BigOperators Matrix
open TDA.Filtration TDA.Filtration.RationalAlpha
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.TriangulationAssembly
open TDA.Filtration.RationalAlpha.IncircleGrade
open TDA.Filtration.RationalAlpha.SuppliedEdgeGrade

noncomputable section

open TDA.Filtration.RationalAlpha.SuppliedCarrier

/-- A site supplies its singleton by the actual grade-zero theorem. -/
theorem singleton_carrier {n : ℕ} (p : Fin n ↪ Point) (j : Fin n) :
    ({j} : Finset (Fin n)) ∈ Alpha.carrier (realSites p) :=
  (Alpha.exists_mem_complex_iff (realSites p) {j}).1
    ⟨0, (Alpha.singleton_mem_complex_iff (realSites p) j 0).2 le_rfl⟩

/-- The existing two-site threshold yields the pair in the carrier even without a polygon. -/
theorem two_site_pair (p : Fin 2 ↪ Point) :
    ({0,1} : Finset (Fin 2)) ∈ Alpha.carrier (realSites p) :=
  (Alpha.exists_mem_complex_iff (realSites p) {0,1}).1
    ⟨_, (EdgeGradeExamples.two_site_exact_stage p _).2 le_rfl⟩

/-- The actual carrier on zero labels has no faces. -/
theorem no_zero_site_face (p : Fin 0 ↪ Point) (s : Finset (Fin 0)) :
    s ∉ Alpha.carrier (realSites p) := by
  intro h
  obtain ⟨j,_⟩ := ((TDA.Topology.mem_nerve_iff _ _).1 h).1
  exact Fin.elim0 j

open TDA.Filtration.RationalAlpha.SignedBoundaryExamples

/-- The trapezoid sites `quad` of `SignedBoundaryExamples` as a labelled embedding. -/
def quadSites : Fin 4 ↪ Point := ⟨quad, by
  change ∀ a b : Fin 4, quad a = quad b → a = b
  decide +kernel⟩

/-- The trapezoid checked in the earlier units has exactly the actual all-scales carrier. -/
theorem trapezoid_carrier :
    Alpha.carrier (realSites quadSites) = labelComplex good := by
  apply carrier_eq_of_signed_boundary (k := 1) quadSites cycle (fun _ _ h => h)
    good trapezoid_certificate
  · intro i
    exact subset_convexHull ℝ _ ⟨i,rfl⟩
  · decide +kernel
  · exact good_boundary
  · decide +kernel
  · right
    unfold NoFourIncircleZeros
    decide +kernel

/-- The exact certified diagonal is present and the other diagonal is absent at all stages. -/
theorem trapezoid_diagonals :
    ({0,2} : Finset (Fin 4)) ∈ Alpha.carrier (realSites quadSites) ∧
    ({1,3} : Finset (Fin 4)) ∉ Alpha.carrier (realSites quadSites) := by
  rw [trapezoid_carrier]
  constructor
  · exact (pair_mem_iff_occurrence good (show (0 : Fin 4) ≠ 2 by decide)).2
      ⟨(1,0),Or.inl rfl⟩
  · change ({1,3} : Finset (Fin 4)) ∉ (labelComplex good).faces
    rw [pair_mem_iff_occurrence good (show (1 : Fin 4) ≠ 3 by decide)]
    decide +kernel

/-- The split of the square into triangles `0 1 3` and `0 3 2`. -/
def squareSplit : Fin 2 → Fin 3 → Fin 4 := ![![0,1,3],![0,3,2]]

/-- The full four-label tied face cannot belong to any downward closure of triangle label sets. -/
theorem square_four_face_regression {I : Type*} (tri : I → Fin 3 → Fin 4) :
    (Finset.univ : Finset (Fin 4)) ∈ Alpha.carrier (realSites Examples.square) ∧
    (Finset.univ : Finset (Fin 4)) ∉ labelComplex tri := by
  constructor
  · rw [show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} by decide]
    exact (exists_entry_iff Examples.square).1 ⟨_,Examples.square_full_tie⟩
  · rintro ⟨_,i,hsub⟩
    have hle := Finset.card_le_card hsub
    have ht : (labelVertices (tri i)).card ≤ 3 :=
      Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin 3))
    rw [Finset.card_univ, Fintype.card_fin] at hle
    omega

/-- The cocircular square split is CCW, passes the all-site incircle tests, and uses every
label. Its triangle closure omits the four-label Alpha face. -/
theorem square_passing_split_carrier_mismatch :
    (∀ i, 0 < orient (Examples.square (squareSplit i 0)) (Examples.square (squareSplit i 1))
      (Examples.square (squareSplit i 2)) ∧
      checkIncircle Examples.square (squareSplit i 0) (squareSplit i 1) (squareSplit i 2) = true) ∧
    allSitesUsed squareSplit ∧
    labelComplex squareSplit ≤ Alpha.carrier (realSites Examples.square) ∧
    Alpha.carrier (realSites Examples.square) ≠ labelComplex squareSplit := by
  have hchecks : ∀ i, 0 < orient (Examples.square (squareSplit i 0)) (Examples.square (squareSplit i 1))
      (Examples.square (squareSplit i 2)) ∧
      checkIncircle Examples.square (squareSplit i 0) (squareSplit i 1) (squareSplit i 2) = true :=
    by decide +kernel
  refine ⟨hchecks, ?_, ?_, ?_⟩
  · unfold allSitesUsed
    decide +kernel
  · exact labelComplex_le_alphaCarrier Examples.square squareSplit
      (fun i => (hchecks i).1) (fun i => (hchecks i).2)
  · intro he
    obtain ⟨hmem,hmiss⟩ := square_four_face_regression squareSplit
    exact hmiss (he ▸ hmem)

end
end TDA.Filtration.RationalAlpha.SuppliedCarrierExamples
