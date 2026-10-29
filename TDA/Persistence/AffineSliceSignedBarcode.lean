import TDA.Persistence.AffineSliceRank
import TDA.Persistence.AffineSlicePresentation
import TDA.Persistence.RankExactBarcodeCancellation

/-!
# Ordinary slice barcodes from signed hook barcodes

Rank exactness of the ambient resolution survives restriction to a positive
affine line. Telescoping its ranks and using uniqueness of finite positive
real endpoint multisets gives the ordinary slice barcode plus the sliced
odd hooks equal to the sliced even hooks. The ordinary barcode and its actual
realization are obtained from the derived original slice presentation.

These are identities and domination statements about endpoint multisets;
they do not identify bottleneck distances after cancellation.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.PositiveAffineLine

open CategoryTheory
open scoped TDA.Persistence Classical

variable {k : Type u} [Field k] {n : ℕ} [NeZero n]
variable (L : PositiveAffineLine n)

/-- The ordinary barcode of the actual slice cancels the odd hooks of any
certified minimal ambient resolution against its even hooks. No minimality
or projectivity of the restricted resolution is asserted or required. -/
theorem finitelyPresented_sliceSignedHookBarcode_cancel_of_resolution
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    (finitelyPresentedOneDimensionalBarcodeDiagram (reindex L.orderHom M)
        (L.finitelyPresented_fromReal_slice hM)).points +
        L.sliceHookMultiset
          (R.signedHookBarcode (NeZero.pos n) M
            (GradedFree.finitelyPresented_liftIndexUniverse M hM)).negative =
      L.sliceHookMultiset
        (R.signedHookBarcode (NeZero.pos n) M
          (GradedFree.finitelyPresented_liftIndexUniverse M hM)).positive := by
  let hM' := GradedFree.finitelyPresented_liftIndexUniverse M hM
  let B := finitelyPresentedOneDimensionalBarcodeDiagram (reindex L.orderHom M)
    (L.finitelyPresented_fromReal_slice hM)
  let D := fun j : Fin R.resolution.length =>
    L.sliceHookMultiset (R.hookBettiMultiset (NeZero.pos n) M hM' j.val)
  have hB : B.IsPositive :=
    finitelyPresentedOneDimensionalBarcodeDiagram_isPositive _ _
  have eB : reindex L.orderHom M ≅ RealBarcode.realize (k := k) B :=
    finitelyPresentedOneDimensionalBarcodeRealizationIso _ _
  have hcancel := R.resolution.toFiniteRankExactResolution.barcode_points_add_odd_eq_even
    L.orderHom B hB eB D
    (fun j => L.sliceHookDiagram_isPositive
      (R.hookBettiMultiset (NeZero.pos n) M hM' j.val))
    (fun j s t hst => L.resolution_term_rank_eq_sliceHookMultiset_countP M hM' R j s t hst)
  change B.points + L.sliceHookMultiset (R.oddHookBetti (NeZero.pos n) M hM') =
    L.sliceHookMultiset (R.evenHookBetti (NeZero.pos n) M hM')
  rw [L.sliceHookMultiset_oddHookBetti, L.sliceHookMultiset_evenHookBetti]
  exact hcancel

/-- The canonical ordinary slice barcode plus the sliced negative hook
occurrences equals the sliced positive hook occurrences. All presentations,
the ambient resolution, and the ordinary barcode realization are derived
from the original finite presentation inside the proof. -/
theorem finitelyPresented_sliceSignedHookBarcode_cancel
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M) :
    (finitelyPresentedOneDimensionalBarcodeDiagram (reindex L.orderHom M)
        (L.finitelyPresented_fromReal_slice hM)).points +
        L.sliceHookMultiset
          (finitelyPresentedSignedHookBarcode (NeZero.pos n) M hM).negative =
      L.sliceHookMultiset
        (finitelyPresentedSignedHookBarcode (NeZero.pos n) M hM).positive := by
  obtain ⟨R⟩ :=
    FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      (NeZero.pos n) M hM
  simpa only [finitelyPresentedSignedHookBarcode_eq (NeZero.pos n) M hM R] using
    L.finitelyPresented_sliceSignedHookBarcode_cancel_of_resolution M hM R

/-- The sliced negative hook multiset is dominated by the sliced positive
hook multiset, with all multiplicities retained. -/
theorem finitelyPresented_sliceSignedHookBarcode_negative_le_positive
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M) :
    L.sliceHookMultiset
        (finitelyPresentedSignedHookBarcode (NeZero.pos n) M hM).negative ≤
      L.sliceHookMultiset
        (finitelyPresentedSignedHookBarcode (NeZero.pos n) M hM).positive := by
  rw [← L.finitelyPresented_sliceSignedHookBarcode_cancel M hM]
  exact Multiset.le_add_left _ _

/-- After proving domination, multiset subtraction recovers precisely the
ordinary barcode of the actual slice. -/
theorem finitelyPresented_sliceSignedHookBarcode_eq_sub
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M) :
    (finitelyPresentedOneDimensionalBarcodeDiagram (reindex L.orderHom M)
        (L.finitelyPresented_fromReal_slice hM)).points =
      L.sliceHookMultiset
          (finitelyPresentedSignedHookBarcode (NeZero.pos n) M hM).positive -
        L.sliceHookMultiset
          (finitelyPresentedSignedHookBarcode (NeZero.pos n) M hM).negative := by
  have hdom := L.finitelyPresented_sliceSignedHookBarcode_negative_le_positive M hM
  exact add_right_cancel
    ((L.finitelyPresented_sliceSignedHookBarcode_cancel M hM).trans
      (Multiset.sub_add_cancel hdom).symm)

end TDA.Persistence.PositiveAffineLine
