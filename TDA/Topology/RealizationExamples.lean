import TDA.Topology.Realization
import TDA.Topology.NerveExamples

/-! # The boundary of a triangle inside the filled triangle -/

namespace TDA.Topology.RealizationExamples

open TDA.Simplicial Realization

/-- The three edges of the triangle, realized as the nerve of a pairwise-intersecting family. -/
abbrev triangleBoundary : PreAbstractSimplicialComplex (Fin 3) := nerve NerveExamples.pairwiseFamily
local notation "triangle" => (⊤ : PreAbstractSimplicialComplex (Fin 3))
local notation "boundaryIncl" => (le_top : triangleBoundary ≤ triangle)

private theorem triple_missing : (Finset.univ : Finset (Fin 3)) ∉ triangleBoundary := by
  simpa only [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide] using
    NerveExamples.pairwiseFamily_has_no_triangle

/-- Filling the triangle makes the three coordinate stars meet for the first time. -/
theorem triangle_star_intersections :
    triangleBoundary < triangle ∧
    ¬ (interMember (coordinateStar triangleBoundary) Finset.univ).Nonempty ∧
    (interMember (coordinateStar triangle) Finset.univ).Nonempty := by
  have hf : (Finset.univ : Finset (Fin 3)) ∈ triangle := Finset.univ_nonempty
  exact ⟨lt_of_le_not_ge boundaryIncl (fun h => triple_missing (h hf)),
    fun h => triple_missing ((interMember_nonempty_iff Finset.univ_nonempty).1 h),
    (interMember_nonempty_iff Finset.univ_nonempty).2 hf⟩

/-- The star-cover square for the boundary inclusion commutes on the original three labels. -/
theorem triangle_nerve_square :
    VertexMap.comp (starNerveInclusion boundaryIncl)
        (inclusionVertexMap (nerve_coordinateStar triangle).le) =
      VertexMap.comp (inclusionVertexMap (nerve_coordinateStar triangleBoundary).le)
        (inclusionVertexMap boundaryIncl) :=
  starNerveInclusion_naturality boundaryIncl

/-- The barycenter of the filled triangle lies outside the image of the boundary. -/
theorem triangle_incl_not_surjective : ¬ Function.Surjective (incl boundaryIncl) := by
  let J : Finset (Fin 3) := Finset.univ
  have hf : J ∈ triangle := Finset.univ_nonempty
  intro hs
  obtain ⟨x, hx⟩ := hs (faceBarycenter hf).val
  have hm : x ∈ (incl boundaryIncl) ⁻¹' interMember (coordinateStar triangle) J := by
    change incl boundaryIncl x ∈ interMember (coordinateStar triangle) J
    rw [hx]
    exact (faceBarycenter hf).property
  rw [preimage_interMember] at hm
  exact triangle_star_intersections.2.1 ⟨x, hm⟩

end TDA.Topology.RealizationExamples
