import TDA.Filtration.RationalAlpha.TriangleIncidence
import TDA.Filtration.RationalAlpha.SignedBoundaryExamples

set_option autoImplicit false

/-!
# Pairwise incidence for the exact rational trapezoid

The signed-boundary certificate for the split along AC gives the full closed edge
as the intersection of its two triangle carriers.
-/

namespace TDA.Filtration.RationalAlpha.TriangleIncidenceExamples

open TDA.Filtration.RationalAlpha (castPoint orient)
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.SignedBoundaryExamples
open TDA.Filtration.RationalAlpha.TriangleIncidence

/-- The two certified trapezoid triangles share the entire closed diagonal AC. -/
theorem trapezoid_pair_meets_along_AC :
    siteTriangle quad abc ∩ siteTriangle quad acd =
      segment ℝ (castPoint (quad 0)) (castPoint (quad 2)) := by
  classical
  have hinj : Function.Injective quad := by
    change ∀ a b : Fin 4, quad a = quad b → a = b
    decide +kernel
  have hgen : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      orient (quad a) (quad b) (quad c) ≠ 0 := by decide +kernel
  have hccw : ∀ i, 0 < orient (quad (good i 0)) (quad (good i 1)) (quad (good i 2)) := by
    decide +kernel
  have hsite (v : Label) : castPoint (quad v) ∈ siteHull quad cycle :=
    subset_convexHull ℝ _ ⟨v, rfl⟩
  have he := triangle_inter_eq_shared_labels_of_signed_boundary quad hinj cycle
    (fun _ _ h => h) good trapezoid_certificate hsite hccw hgen good_boundary
    (i := 0) (j := 1) (by decide)
  have hl : labelVertices abc ∩ labelVertices acd = ({0,2} : Finset (Fin 4)) := by
    decide +kernel
  change siteTriangle quad abc ∩ siteTriangle quad acd =
    convexHull ℝ (↑((labelVertices abc ∩ labelVertices acd).image (castPoint ∘ quad)) : Set Plane) at he
  rw [hl] at he
  simpa [Finset.image_insert, Finset.image_singleton, convexHull_pair] using he

end TDA.Filtration.RationalAlpha.TriangleIncidenceExamples
