import TDA.Filtration.RationalAlpha.SubdividedBoundaryCoverage

set_option autoImplicit false

/-!
# A split side of a triangular hull

The coarse triangle is certified by its orientation. Its bottom midpoint is a boundary label
of the pieces. The two pieces cancel the directed occurrences of their shared edge.
-/

namespace TDA.Filtration.RationalAlpha.SubdividedBoundaryExamples

open Set SignedBoundary
open scoped Matrix

/-- The sites are `A = (0, 0)`, `B = (2, 0)`, `C = (0, 2)` and `M = (1, 0)`. -/
def splitSites : Fin 4 → Point := ![(0, 0), (2, 0), (0, 2), (1, 0)]

/-- The coarse CCW triangle `ABC`. -/
def coarseCycle : Fin 3 → Fin 4 := ![0, 1, 2]

/-- The bottom side passes through `M`; the other two sides are unchanged. -/
def cuts : Fin 3 → List (Fin 4) := ![[3], [], []]

/-- The two CCW pieces `AMC` and `MBC`. -/
def splitTriangles : Fin 2 → Fin 3 → Fin 4 := ![![0, 3, 2], ![3, 1, 2]]

private abbrev pieceEdges (i : Fin 2) := triangleEdges
  (splitTriangles i 0) (splitTriangles i 1) (splitTriangles i 2)

private theorem coarse_hull_eq :
    siteHull splitSites coarseCycle = siteTriangle splitSites coarseCycle := by
  change convexHull ℝ (range fun i : Fin 3 => castPoint (splitSites (coarseCycle i))) =
    convexHull ℝ ({castPoint (splitSites 0), castPoint (splitSites 1),
      castPoint (splitSites 2)} : Set Plane)
  apply congrArg (convexHull ℝ)
  ext x
  simp only [mem_insert_iff, mem_singleton_iff, mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private theorem coarse_edge (i : Fin 3) :
    realEdge splitSites (cycleEdges coarseCycle i) =
      triangleEdges (castPoint (splitSites 0)) (castPoint (splitSites 1))
        (castPoint (splitSites 2)) i := by
  fin_cases i <;> rfl

private theorem coarse_certificate :
    PolygonCertificate (siteHull splitSites coarseCycle)
      (fun i => realEdge splitSites (cycleEdges coarseCycle i)) := by
  rw [coarse_hull_eq]
  simp only [siteTriangle, coarse_edge]
  exact rational_triangle_polygonCertificate _ _ _ (by decide +kernel)

private theorem midpoint_eq :
    castPoint (splitSites 3) = AffineMap.lineMap (castPoint (splitSites 0))
      (castPoint (splitSites 1)) (1 / 2 : ℝ) := by
  ext i
  simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  fin_cases i
  · change ((1 : ℚ) : ℝ) = 1 / 2 * (((2 : ℚ) : ℝ) - (0 : ℚ)) + (0 : ℚ)
    norm_num
  · change ((0 : ℚ) : ℝ) = 1 / 2 * (((0 : ℚ) : ℝ) - (0 : ℚ)) + (0 : ℚ)
    norm_num

private theorem ordered_cuts (i : Fin 3) :
    OrderedEdgeCuts splitSites (cycleEdges coarseCycle i).2 (cycleEdges coarseCycle i).1 (cuts i) := by
  fin_cases i
  · exact ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, midpoint_eq⟩, trivial⟩
  · trivial
  · trivial

private theorem sites_contained (j : Fin 4) : castPoint (splitSites j) ∈ siteHull splitSites coarseCycle := by
  fin_cases j
  · exact subset_convexHull ℝ _ ⟨0, rfl⟩
  · exact subset_convexHull ℝ _ ⟨1, rfl⟩
  · exact subset_convexHull ℝ _ ⟨2, rfl⟩
  · change castPoint (splitSites 3) ∈ siteHull splitSites coarseCycle
    rw [midpoint_eq]
    exact coarse_certificate.edge_subset 0
      (lineMap_mem_segment ℝ _ _ ⟨by norm_num, by norm_num⟩)

/-- Cancellation of the shared edge gives the refined cycle `A → M → B → C → A`. -/
theorem signed_boundary :
    (∑ i, ∑ e, signedEdge (pieceEdges i e)) =
      ∑ j, signedEdge (subdividedEdge (cycleEdges coarseCycle) cuts j) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_three,
    Fin.sum_univ_three]
  change (signedEdge (0, 3) + signedEdge (3, 2) + signedEdge ((2 : Fin 4), 0)) +
    (signedEdge (3, 1) + signedEdge (1, 2) + signedEdge (2, 3)) =
      (∑ j : Fin 2, signedEdge (subdividedEdge (cycleEdges coarseCycle) cuts ⟨0, j⟩)) +
      (∑ j : Fin 1, signedEdge (subdividedEdge (cycleEdges coarseCycle) cuts ⟨1, j⟩)) +
      ∑ j : Fin 1, signedEdge (subdividedEdge (cycleEdges coarseCycle) cuts ⟨2, j⟩)
  rw [Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_one]
  change (signedEdge (0, 3) + signedEdge (3, 2) + signedEdge ((2 : Fin 4), 0)) +
    (signedEdge (3, 1) + signedEdge (1, 2) + signedEdge (2, 3)) =
      signedEdge (0, 3) + signedEdge (3, 1) + signedEdge (1, 2) + signedEdge (2, 0)
  simp only [signedEdge, Prod.swap_prod_mk]
  abel

/-- The signed refined chain gives coverage of the original closed hull and off-edge multiplicity. -/
theorem coverage_and_multiplicity :
    (∀ x ∈ offEdges (subdividedListedEdges splitSites pieceEdges (cycleEdges coarseCycle) cuts),
      interiorMultiplicity (fun i => siteTriangle splitSites (splitTriangles i)) x =
        interiorIndicator (siteHull splitSites coarseCycle) x) ∧
    (⋃ i, siteTriangle splitSites (splitTriangles i)) = siteHull splitSites coarseCycle :=
  rational_cover_from_subdivided_signed_boundary splitSites coarseCycle cuts splitTriangles
    coarse_certificate ordered_cuts (fun i j => sites_contained (splitTriangles i j))
    (by decide +kernel) signed_boundary

private def sample : Point := (1 / 4, 1 / 2)

private theorem sample_off_edges :
    castPoint sample ∈ offEdges (subdividedListedEdges splitSites pieceEdges (cycleEdges coarseCycle) cuts) := by
  intro hx
  obtain ⟨j, hj⟩ := mem_iUnion.1 hx
  have hz := edgeSide_eq_zero_on_segment _ hj
  let labelEdge : Sum (Sum (Fin 2 × Fin 3) (Fin 3)) (SubdivisionIndex (cycleEdges coarseCycle) cuts) →
      Fin 4 × Fin 4 :=
    Sum.elim (Sum.elim (fun ie => pieceEdges ie.1 ie.2) (cycleEdges coarseCycle))
      (subdividedEdge (cycleEdges coarseCycle) cuts)
  have hreal : subdividedListedEdges splitSites pieceEdges (cycleEdges coarseCycle) cuts j =
      realEdge splitSites (labelEdge j) := by
    rcases j with (_ | _) | _ <;> rfl
  rw [hreal] at hz
  change edgeSide (castPoint (splitSites (labelEdge j).1), castPoint (splitSites (labelEdge j).2))
    (castPoint sample) = 0 at hz
  rw [side_of_rational_sites] at hz
  have horient : ∀ k, orient (splitSites (labelEdge k).1) (splitSites (labelEdge k).2) sample ≠ 0 := by
    decide +kernel
  exact horient j (by exact_mod_cast hz)

private theorem sample_interior : castPoint sample ∈ interior (siteHull splitSites coarseCycle) := by
  have hccw : 0 < edgeSide (castPoint (splitSites 0), castPoint (splitSites 1))
      (castPoint (splitSites 2)) := by
    rw [side_of_rational_sites]
    exact_mod_cast (by decide +kernel : 0 < orient (splitSites 0) (splitSites 1) (splitSites 2))
  have hmem : castPoint sample ∈ siteHull splitSites coarseCycle := by
    rw [coarse_hull_eq]
    apply (triangle_mem_iff _ _ _ _ hccw).2
    intro i
    rw [← coarse_edge]
    change 0 ≤ edgeSide (castPoint (splitSites (cycleEdges coarseCycle i).1),
      castPoint (splitSites (cycleEdges coarseCycle i).2)) (castPoint sample)
    rw [side_of_rational_sites]
    have hs : ∀ i, 0 ≤ orient (splitSites (cycleEdges coarseCycle i).1)
      (splitSites (cycleEdges coarseCycle i).2) sample := by decide +kernel
    exact_mod_cast hs i
  by_contra hi
  have hf : castPoint sample ∈ frontier (siteHull splitSites coarseCycle) := by
    rw [frontier, coarse_certificate.compact.isClosed.closure_eq]
    exact ⟨hmem, hi⟩
  rw [coarse_certificate.frontier_eq] at hf
  obtain ⟨e, he⟩ := mem_iUnion.1 hf
  exact sample_off_edges (mem_iUnion.2 ⟨Sum.inl (Sum.inr e), he⟩)

/-- The subdivision theorem gives multiplicity one at `(1/4, 1/2)`. Its generic ray avoids
all vertices of both hull presentations and both triangles. -/
theorem sample_multiplicity_one :
    interiorMultiplicity (fun i => siteTriangle splitSites (splitTriangles i)) (castPoint (1 / 4, 1 / 2)) = 1 := by
  change interiorMultiplicity (fun i => siteTriangle splitSites (splitTriangles i)) (castPoint sample) = 1
  rw [coverage_and_multiplicity.1 _ sample_off_edges]
  simp [interiorIndicator, sample_interior]

end TDA.Filtration.RationalAlpha.SubdividedBoundaryExamples
