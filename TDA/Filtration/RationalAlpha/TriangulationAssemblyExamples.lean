import TDA.Filtration.RationalAlpha.TriangulationAssembly
import TDA.Filtration.RationalAlpha.SignedBoundaryExamples

set_option autoImplicit false

/-!
# Certified triangulation assembly examples

The split along AC assembles to the full trapezoid. In the single-triangle fixture, a label
strictly inside the covered hull is absent from the supplied vertices.
-/

open Set
open TDA.Filtration.RationalAlpha (Plane castPoint orient)
open TDA.Filtration.RationalAlpha.SignedBoundary
open TDA.Filtration.RationalAlpha.TriangleIncidence
open TDA.Filtration.RationalAlpha.SignedBoundaryExamples
open TDA.Filtration.RationalAlpha.TriangulationAssembly

namespace TDA.Filtration.RationalAlpha.TriangulationAssemblyExamples

private theorem quad_inj : Function.Injective quad := by
  change ∀ a b : Fin 4, quad a = quad b → a = b
  decide +kernel

private theorem quad_mem (a : Fin 4) : castPoint (quad a) ∈ siteHull quad cycle :=
  subset_convexHull ℝ _ ⟨a, rfl⟩

private theorem quad_ccw : ∀ i, 0 < orient (quad (good i 0)) (quad (good i 1)) (quad (good i 2)) :=
  by decide +kernel

private theorem quad_noncollinear : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
    orient (quad a) (quad b) (quad c) ≠ 0 := by decide +kernel

/-- The real geometric complex formed by the certified split along AC. -/
noncomputable def trapezoidComplex : Geometry.SimplicialComplex ℝ Plane :=
  certifiedComplex quad quad_inj cycle (fun _ _ h => h) good trapezoid_certificate
    quad_mem quad_ccw quad_noncollinear good_boundary

/-- The assembled trapezoid has the full convex hull as its real space. -/
theorem trapezoid_space_eq_full_site_hull : trapezoidComplex.space = convexHull ℝ (range (embedSite quad)) :=
  certified_space_eq_full_site_hull quad quad_inj cycle (fun _ _ h => h) good trapezoid_certificate
    quad_mem quad_ccw quad_noncollinear good_boundary

/-- The closed edges AB and AD from different supplied triangles meet exactly at A. -/
theorem trapezoid_lower_faces_AB_AD :
    convexHull ℝ (pointVertices quad ({0, 1} : Finset (Fin 4)) : Set Plane) ∩
      convexHull ℝ (pointVertices quad ({0, 3} : Finset (Fin 4)) : Set Plane) =
      {castPoint (quad 0)} := by
  have hParent (i j : Fin 2) (hij : i ≠ j) :
      siteTriangle quad (good i) ∩ siteTriangle quad (good j) =
      convexHull ℝ (pointVertices quad (labelVertices (good i) ∩ labelVertices (good j)) : Set Plane) :=
    triangle_inter_eq_shared_labels_of_signed_boundary quad quad_inj cycle (fun _ _ h => h)
      good trapezoid_certificate quad_mem quad_ccw quad_noncollinear good_boundary hij
  have hAB : ({0, 1} : Finset (Fin 4)) ∈ (labelComplex good).faces := by
    exact ⟨by simp, 0, by decide +kernel⟩
  have hAD : ({0, 3} : Finset (Fin 4)) ∈ (labelComplex good).faces := by
    exact ⟨by simp, 1, by decide +kernel⟩
  have hEq : ({0, 1} : Finset (Fin 4)) ∩ {0, 3} = {0} := by decide +kernel
  simpa [hEq, pointVertices, embedSite] using
    label_face_hulls_inter quad quad_inj good quad_ccw hParent hAB hAD

private theorem inner_inj : Function.Injective inner := by
  change ∀ a b : Fin 4, inner a = inner b → a = b
  decide +kernel

private theorem incomplete_ccw :
    ∀ i, 0 < orient (inner (incomplete i 0)) (inner (incomplete i 1))
      (inner (incomplete i 2)) := by
  decide +kernel

/-- The one supplied triangle of the omitted-site fixture assembled as a geometric complex. -/
noncomputable def omittedComplex : Geometry.SimplicialComplex ℝ Plane :=
  geometricComplex inner inner_inj incomplete incomplete_ccw fun i j hij =>
    (hij (Subsingleton.elim i j)).elim

/-- The omitted label is strictly inside the covered hull and has no singleton face. -/
theorem omitted_interior_site_has_no_singleton :
    omittedComplex.space = siteHull inner innerCycle ∧
    castPoint (inner 3) ∈ interior (siteHull inner innerCycle) ∧
    ({3} : Finset (Fin 4)) ∉ (labelComplex incomplete).faces := by
  refine ⟨(geometric_space_eq_union inner inner_inj incomplete incomplete_ccw _).trans
    omitted_label_fixture.1, omitted_label_fixture.2.2.1, ?_⟩
  rw [singleton_mem_iff_used]
  decide +kernel

end TDA.Filtration.RationalAlpha.TriangulationAssemblyExamples
