import TDA.Persistence.RankResolutionDegreeTwoSimplicialFinite
import TDA.Persistence.FiniteSimplicialPresentation
import Mathlib.Tactic

/-!
# Real-coordinate simplicial realization of the degree-two witness

The actual degree-one homology of the literal boundary-tetrahedron filtration
is naturally isomorphic on its finite grade grid to the existing finite
degree-two witness. The canonical finite-simplicial left Kan comparison
extends this isomorphism to every real coordinate grade. Its original finite
presentation follows independently from the finite-input homology theorem.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory TDA.Persistence TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence

variable {k : Type u} [Field k]

private noncomputable def globalizationOnGrid {C : FiniteComplex 4}
    (g : FiniteGraded C 2) (G : CoordinateGrid 2)
    (hgrid : G = g.gridCoordinates) (M : PModule.{u,0,u} k G.Point)
    (e : G.embedding.monotone.functor ⋙ finiteSimplicialHomology k g 1 ≅ M) :
    finiteSimplicialHomology k g 1 ≅ G.lan.obj M := by
  subst G
  exact (finiteSimplicialHomology_gridKanIso k g 1).symm.trans
    (g.gridCoordinates.lan.mapIso e)

/-- The actual degree-one homology module on all real coordinate grades is the
left Kan extension of the independently defined finite degree-two witness. -/
noncomputable def realIso (k : Type u) [Field k] :
    finiteSimplicialHomology k boundaryTetrahedronGrading 1 ≅
      RankResolutionDegreeTwo.realModule (k := k) :=
  globalizationOnGrid (k := k) boundaryTetrahedronGrading grid
    boundaryTetrahedronGrading_gridCoordinates.symm
    (finiteModule (k := k)) (finiteIso k)

/-- The actual real-coordinate degree-one homology has its original finite
graded-free presentation, by the finite-input simplicial homology theorem. -/
theorem homology_finitelyPresented (k : Type u) [Field k] :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (finiteSimplicialHomology k boundaryTetrahedronGrading 1) :=
  finiteSimplicialHomology_finitelyPresented k boundaryTetrahedronGrading 1

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
