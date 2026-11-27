import TDA.Persistence.Reduction.SimplicialAdapterOrderFree
import TDA.Filtration.Rips
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

/-!
# Client statements of the order-free pivot barcode

Regression fixtures for #1308, family 17 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it. The inputs are a finite subset `S` of the Euclidean
plane as vertex type `↥S` with the instances found for a subtype of a `Finset`, the field
`ZMod 2`, and a compatible order of the faces of the Rips filtration. The first two statements
choose the vertex order internally; the third takes one supplied linear order on `↥S` and the
fourth two supplied linear orders on `↥S` as explicit arguments.

* The isomorphism of the prefix homology module with the interval module of the pivot barcode.
* The fibres of the prefix homology module as order-free homology of the prefix complexes.
* The equality of the order-free pivot barcode with the pivot barcode of a supplied order, and
  the invariance of the pivot barcode under two supplied orders.
-/

namespace TDA.Persistence.SimplicialAdapterOrderFreeClientExamples

open TDA.Persistence.Reduction TDA.Simplicial TDA.Filtration

/-- The prefix homology of the Rips filtration of a finite subset of the plane is isomorphic to
the interval module of the pivot barcode. -/
theorem plane_prefix_iso_pivot (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (e : CompatibleOrder (Rips.filter (inferInstance : MetricSpace S))) (p : ℕ) :
    Nonempty (facePrefixModuleOrderFree (ZMod 2) e p ≅
      barcodeModule (k := ZMod 2) (facePivotBarcodeOrderFree (ZMod 2) e p)) :=
  nonempty_facePrefixModuleOrderFreeIsoPivotBarcodeOrderFree (ZMod 2) e p

/-- The fibres of the prefix homology module are order-free homology of the prefix complexes. -/
theorem plane_prefix_obj (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (e : CompatibleOrder (Rips.filter (inferInstance : MetricSpace S))) (p : ℕ)
    (i : Fin (faceCount (Rips.fullComplex S) + 1)) :
    (facePrefixModuleOrderFree (ZMod 2) e p).obj i =
      simplicialHomologyOrderFree (e.prefixComplex i.val) (ZMod 2) p :=
  facePrefixModuleOrderFree_obj (ZMod 2) e p i

/-- The order-free pivot barcode equals the pivot barcode of a supplied order on a finite
subset of the plane. -/
theorem plane_pivot_eq (S : Finset (EuclideanSpace ℝ (Fin 2))) [LinearOrder S]
    (e : CompatibleOrder (Rips.filter (inferInstance : MetricSpace S))) (p : ℕ) :
    facePivotBarcodeOrderFree (ZMod 2) e p = facePivotBarcode (ZMod 2) e p :=
  facePivotBarcodeOrderFree_eq_facePivotBarcode (ZMod 2) e p

/-- The pivot barcode of two supplied orders on a finite subset of the plane agree. -/
theorem plane_pivot_congr (S : Finset (EuclideanSpace ℝ (Fin 2))) (o₁ o₂ : LinearOrder S)
    (e : CompatibleOrder (Rips.filter (inferInstance : MetricSpace S))) (p : ℕ) :
    @facePivotBarcode S o₁ ℝ _ _ _ _ (ZMod 2) _ _ e p =
      @facePivotBarcode S o₂ ℝ _ _ _ _ (ZMod 2) _ _ e p :=
  facePivotBarcode_congr_linearOrder (ZMod 2) o₁ o₂ e p

end TDA.Persistence.SimplicialAdapterOrderFreeClientExamples
