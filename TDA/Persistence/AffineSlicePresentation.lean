import TDA.Persistence.PositiveAffineSlice
import TDA.Persistence.FinitePresentationReindex
import TDA.Persistence.CoordinateRealBridge

/-!
# Finite presentations of positive affine restrictions

The entrance-time adjunction regrades every generator and relation of an
original finite presentation. Thus the actual restriction to a positive
affine line remains finitely presented, both over the real line and under
the one-coordinate identification used by the ordinary barcode API.
No slice presentation or reconstruction is assumed, and coefficients may
be any ring.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.PositiveAffineLine

variable {n : ℕ} [NeZero n] (L : PositiveAffineLine n)
    {R : Type u} [Ring R]

/-- The actual restriction to a positive affine line has an original finite
graded-free presentation obtained by regrading the original occurrences. -/
theorem finitelyPresented_slice
    {M : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (hM : GradedFree.FinitelyPresented.{u,0,w} M) :
    GradedFree.FinitelyPresented.{u,0,w} (reindex L.orderHom M) :=
  GradedFree.finitelyPresented_reindex_of_galoisConnection
    L.orderHom L.entrance L.galoisConnection hM

/-- The same actual slice has an original finite presentation in one real
coordinate, as required by the existing ordinary-barcode construction. -/
theorem finitelyPresented_fromReal_slice
    {M : PModule.{u,0,max u w} R (Fin n → ℝ)}
    (hM : GradedFree.FinitelyPresented.{u,0,w} M) :
    GradedFree.FinitelyPresented.{u,0,w}
      (CoordinateRealBridge.fromReal (reindex L.orderHom M)) := by
  apply GradedFree.finitelyPresented_reindex_of_galoisConnection
    CoordinateRealBridge.evaluate CoordinateRealBridge.diagonal
    (fun p q => ?_) (L.finitelyPresented_slice hM)
  change (∀ i : Fin 1, p ≤ q i) ↔ p ≤ q 0
  simp only [Fin.forall_fin_one]

end TDA.Persistence.PositiveAffineLine
