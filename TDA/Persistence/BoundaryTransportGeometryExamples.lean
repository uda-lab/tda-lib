import TDA.Persistence.BoundaryTransportGeometryCore

/-!
# Far-atom examples for collapsed-boundary geometry

Fixed points exhibit the strict shortcut and squared-leg comparison.
-/

noncomputable section

namespace TDA.Persistence.BoundaryTransport

open Set Filter Topology TopologicalSpace

/-- Direct transport between distant bars can be strictly more expensive than the shortcut. -/
theorem far_points_shortcut :
    dist (Space.point ⟨(0, 2), by norm_num⟩)
      (Space.point ⟨(10, 12), by norm_num⟩) = 2 := by
  rw [dist_point_point]
  norm_num [depth_eq, Subtype.dist_eq, Prod.dist_eq, Real.dist_eq]

/-- Squaring a shortcut length differs from summing the squared boundary legs. -/
theorem far_points_squared_shortcut_and_boundary_legs :
    dist (Space.point ⟨(0, 2), by norm_num⟩)
        (Space.point ⟨(10, 12), by norm_num⟩) ^ 2 = 4 ∧
      depth ⟨(0, 2), by norm_num⟩ ^ 2 + depth ⟨(10, 12), by norm_num⟩ ^ 2 = 2 := by
  constructor
  · rw [far_points_shortcut]
    norm_num
  · norm_num [depth_eq]

end TDA.Persistence.BoundaryTransport
