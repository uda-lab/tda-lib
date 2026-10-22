import TDA.Persistence.MatchingInterleaving
import TDA.Persistence.RealInterleavingDistance
import TDA.Persistence.ConstructibleBarcode

/-!
# Interleaving distance bounded by finite barcode bottleneck

Each occurrence matching has finite cost and supplies an interleaving at that cost.
Taking the infimum proves the bound without selecting an optimal matching. The finite-constructible barcode isomorphisms then transport both witnesses and distances.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory
open scoped NNReal ENNReal

variable {k : Type u} [Field k]

namespace RealBarcode

/-- Every occurrence matching bounds the interleaving distance by its finite cost. -/
theorem distance_le_matching_cost (D E : Diagram ℝ) (hD : D.IsPositive) (hE : E.IsPositive)
    (M : OccurrenceMatching D.finiteOccurrences E.finiteOccurrences
      D.essentialOccurrences E.essentialOccurrences) :
    realInterleavingDistance (realize (k := k) D) (realize E) ≤
      M.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) := by
  let C := M.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1)
  have hC : C ≠ ⊤ := ne_of_lt (occurrenceMatching_cost_lt_top _ _ _ _ M)
  have hc : C ≤ (C.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hC).symm.le
  have i := matchingInterleaving (k := k) D E hD hE C.toNNReal M hc
  simpa only [ENNReal.coe_toNNReal hC] using i.distance_le

/-- The finite positive half-open matching-to-interleaving distance inequality.
The matching type may be empty, in which case the right side is infinity. -/
theorem distance_le_bottleneck (D E : Diagram ℝ) (hD : D.IsPositive) (hE : E.IsPositive) :
    realInterleavingDistance (realize (k := k) D) (realize E) ≤ bottleneck D E := by
  exact le_iInf fun M => distance_le_matching_cost D E hD hE M

end RealBarcode

namespace FiniteConstructible

variable {n m : ℕ}

/-- Transport a matching-induced witness to the original finite-constructible modules.
Only constructibility and critical-fiber finiteness are supplied for decomposition. -/
noncomputable def matchingInterleaving (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ)
    (M N : PModule.{u,0,u} k ℝ) (hM : IsConstructible c M) (hN : IsConstructible d N)
    (hfdM : ∀ i, FiniteDimensional k (M.obj (c i)))
    (hfdN : ∀ j, FiniteDimensional k (N.obj (d j))) (ε : ℝ≥0)
    (matching : OccurrenceMatching (moduleDiagram c M hfdM).finiteOccurrences
      (moduleDiagram d N hfdN).finiteOccurrences (moduleDiagram c M hfdM).essentialOccurrences
      (moduleDiagram d N hfdN).essentialOccurrences)
    (hc : matching.cost (fun p => p.1) (fun p => p.1) (fun b => b.1) (fun b => b.1) ≤
      (ε : ℝ≥0∞)) : RealInterleaving ε M N :=
  (RealBarcode.matchingInterleaving _ _ (moduleDiagram_isPositive c M hfdM)
    (moduleDiagram_isPositive d N hfdN) ε matching hc).congr
      (barcodeRealizationIso c M hM hfdM).symm (barcodeRealizationIso d N hN hfdN).symm

/-- Interleaving distance is bounded by the bottleneck of the two grid-based diagrams.
The critical grids may have different sizes; essential tails and empty grids are allowed. -/
theorem distance_le_bottleneck (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ)
    (M N : PModule.{u,0,u} k ℝ) (hM : IsConstructible c M) (hN : IsConstructible d N)
    (hfdM : ∀ i, FiniteDimensional k (M.obj (c i)))
    (hfdN : ∀ j, FiniteDimensional k (N.obj (d j))) :
    realInterleavingDistance M N ≤
      bottleneck (moduleDiagram c M hfdM) (moduleDiagram d N hfdN) := by
  rw [realInterleavingDistance_congr (barcodeRealizationIso c M hM hfdM)
    (barcodeRealizationIso d N hN hfdN)]
  exact RealBarcode.distance_le_bottleneck _ _ (moduleDiagram_isPositive c M hfdM)
    (moduleDiagram_isPositive d N hfdN)

end FiniteConstructible
end TDA.Persistence
