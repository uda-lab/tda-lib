import TDA.Filtration.RipsRelation
import TDA.Persistence.SimplicialMultivaluedInterleaving
import TDA.Persistence.SublevelConstructible

/-!
# Canonical Rips interleavings across different metric label types

A native relation total on both ambient types, with a pairwise distance-distortion
bound, supplies both shifted Rips geometries. Its canonical homology maps form an
actual interleaving over every ring. For finite label types and field coefficients,
the existing different-grid constructible theorem bounds the full actual diagrams.

This is the supplied-relation mechanism of CDSO Lemma 4.3 at nonnegative scales,
with ring coefficients and finite-diagram consequences as library extensions.
The library's empty negative tail differs from the source's vertex convention;
no whole-real H₀ identification or Gromov–Hausdorff selection is asserted.
-/

universe u v

namespace TDA.Persistence.Rips

open CategoryTheory TDA.Filtration
open scoped NNReal ENNReal

noncomputable section

variable {X Y : Type u} [LinearOrder X] [LinearOrder Y]
variable (R : Type v) [Ring R] (dX : MetricSpace X) (dY : MetricSpace Y)
variable {C : SetRel X Y} {ε : ℝ≥0}
variable (hCT : Relator.LeftTotal (fun x y => (x,y) ∈ C))
variable (hIT : Relator.LeftTotal (fun y x => (y,x) ∈ C.inv))
variable (h : ∀ x x' y y', (x,y) ∈ C → (x',y') ∈ C →
  |dX.dist x x' - dY.dist y y'| ≤ (ε : ℝ))

omit [LinearOrder X] [LinearOrder Y] in
include h in
private theorem inverse_distortion :
    ∀ y y' x x', (y,x) ∈ C.inv → (y',x') ∈ C.inv →
      |dY.dist y y' - dX.dist x x'| ≤ (ε : ℝ) := by
  intro y y' x x' hy hy'
  simpa only [abs_sub_comm] using h x x' y y' hy hy'

/-- The actual canonical maps of a total bounded-distortion relation and its
native transpose give the Rips homology interleaving, in every degree. -/
def relationInterleaving (n : ℕ) :
    RealInterleaving ε (sublevelModule R (Rips.filter dX) n)
      (sublevelModule R (Rips.filter dY) n) :=
  multivaluedSimplicialHomologyConverseInterleaving R hCT hIT
    (Rips.isShiftedSimplicialRelation_of_distortion dX dY h)
    (Rips.isShiftedSimplicialRelation_of_distortion dY dX (inverse_distortion dX dY h)) n

/-- The forward field is the entire existing canonical map of the supplied relation. -/
@[simp] theorem relationInterleaving_φ (n : ℕ) :
    (relationInterleaving R dX dY hCT hIT h n).φ =
      multivaluedSimplicialHomologyMapNNReal R hCT
        (Rips.isShiftedSimplicialRelation_of_distortion dX dY h) n := rfl

/-- The backward field is the entire existing canonical map of the native transpose. -/
@[simp] theorem relationInterleaving_ψ (n : ℕ) :
    (relationInterleaving R dX dY hCT hIT h n).ψ =
      multivaluedSimplicialHomologyMapNNReal R hIT
        (Rips.isShiftedSimplicialRelation_of_distortion dY dX (by
          intro y y' x x' hy hy'
          simpa only [abs_sub_comm] using h x x' y y' hy hy')) n := rfl

include hCT hIT h in
/-- The constructed actual interleaving bounds the extended interleaving distance. -/
theorem realInterleavingDistance_le_of_relation (n : ℕ) :
    realInterleavingDistance (sublevelModule R (Rips.filter dX) n)
      (sublevelModule R (Rips.filter dY) n) ≤ (ε : ℝ≥0∞) :=
  (relationInterleaving R dX dY hCT hIT h n).distance_le

include hCT hIT h in
/-- Finite metric label types give stability of their full actual Rips diagrams.
Each filter supplies its own critical grid and finite-dimensional fibers. -/
theorem bottleneck_dgm_le_of_relation [Fintype X] [Fintype Y] (k : Type u) [Field k]
    (n : ℕ) :
    bottleneck (dgm k (Rips.filter dX) n) (dgm k (Rips.filter dY) n) ≤ (ε : ℝ≥0∞) := by
  rw [← moduleDiagram_sublevelModule k n (Rips.filter dX),
    ← moduleDiagram_sublevelModule k n (Rips.filter dY)]
  exact FiniteConstructible.bottleneck_le_of_interleaving
    (sublevelModule_isConstructible k n (Rips.filter dX))
    (sublevelModule_isConstructible k n (Rips.filter dY))
    (sublevelModule_finiteDimensional k n (Rips.filter dX))
    (sublevelModule_finiteDimensional k n (Rips.filter dY))
    (relationInterleaving k dX dY hCT hIT h n)

end
end TDA.Persistence.Rips
