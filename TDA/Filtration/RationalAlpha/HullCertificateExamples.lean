import TDA.Filtration.RationalAlpha.SignedBoundaryCoverage

set_option autoImplicit false

/-!
# Exact tests for supplied strict hull corners

The coarse trapezoid admits a site in the relative interior of a side. The finite checker
distinguishes that site from a collinear corner and from an exterior site.
-/

namespace TDA.Filtration.RationalAlpha.HullCertificateExamples

open Set SignedBoundary
open scoped Matrix

/-- The trapezoid sites and an additional midpoint of the bottom side. -/
def sampleSites : Fin 5 → Point := ![(0, 0), (4, 0), (3, 2), (0, 2), (2, 0)]
/-- The strict CCW corners of the trapezoid, in cycle order. -/
def sampleCorners : Fin 4 → Fin 5 := ![0, 1, 2, 3]
/-- The cycle that includes the bottom midpoint as a corner. -/
def splitCycle : Fin 5 → Fin 5 := ![0, 4, 1, 2, 3]
/-- The sites with the additional point moved below the bottom side. -/
def outsideSites : Fin 5 → Point := ![(0, 0), (4, 0), (3, 2), (0, 2), (2, -1)]

/-- The exact checker accepts a side-interior site with the strict coarse cycle. -/
theorem midpoint_accepted : cornerHullCheck sampleSites sampleCorners = true := by decide +kernel

/-- The extra site has zero bottom-side orientation and belongs to the hull. -/
theorem midpoint_active :
    orient (sampleSites 0) (sampleSites 1) (sampleSites 4) = 0 ∧
      castPoint (sampleSites 4) ∈ siteHull sampleSites sampleCorners :=
  ⟨by decide +kernel, ((cornerHullCheck_true_iff _ _).1 midpoint_accepted).2 4⟩

/-- The extra site belongs to the open bottom side. -/
theorem midpoint_in_open_side :
    castPoint (sampleSites 4) ∈ openSegment ℝ (castPoint (sampleSites 0)) (castPoint (sampleSites 1)) := by
  rw [openSegment_eq_image_lineMap]
  refine ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩
  ext i
  simp only [AffineMap.lineMap_apply_module', PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  fin_cases i
  · change 1 / 2 * (((4 : ℚ) : ℝ) - (0 : ℚ)) + (0 : ℚ) = ((2 : ℚ) : ℝ)
    norm_num
  · change 1 / 2 * (((0 : ℚ) : ℝ) - (0 : ℚ)) + (0 : ℚ) = ((0 : ℚ) : ℝ)
    norm_num

/-- The successful check supplies the polygon certificate and identifies the full site hull. -/
theorem sample_certificate :
    PolygonCertificate (siteHull sampleSites sampleCorners)
      (fun e => realEdge sampleSites (cycleEdges sampleCorners e)) ∧
        siteHull sampleSites sampleCorners = convexHull ℝ (range fun l => castPoint (sampleSites l)) :=
  cornerHullCheck_sound _ _ midpoint_accepted

/-- Inserting the collinear midpoint in the corner cycle passes the weak tests and fails strictness. -/
theorem subdivided_cycle_rejected :
    HullSitesLeft sampleSites splitCycle ∧
      ¬ StrictCornerCycle sampleSites splitCycle ∧
      cornerHullCheck sampleSites splitCycle = false := by
  decide +kernel

/-- The same strict corners fail the all-site check when one site is below the bottom side. -/
theorem outside_site_rejected :
    StrictCornerCycle outsideSites sampleCorners ∧
      cornerHullCheck outsideSites sampleCorners = false ∧
      orient (outsideSites 0) (outsideSites 1) (outsideSites 4) < 0 := by
  decide +kernel

end TDA.Filtration.RationalAlpha.HullCertificateExamples
