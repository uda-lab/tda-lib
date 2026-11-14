import TDA.Persistence.AffineSliceInterleaving
import TDA.Persistence.AffineSlicePresentation
import TDA.Persistence.RankSignedBarcodeOneDimensional

set_option autoImplicit false

/-!
# Matching distance from ordinary positive affine slice barcodes

Each originally finitely presented coordinate module has an ordinary barcode
on every positive affine line. The minimum slope times the ordinary bottleneck
distance is bounded by coordinate interleaving distance.

The matching distance takes the supremum over the normalized lines with maximum
slope `1` and sum of offsets `0`, as in Landi, arXiv:1412.3374v1, Theorem 1.
Its self-distance, symmetry, triangle inequality, and natural-isomorphism
invariance are extended pseudometric laws. Its value may be infinite.
-/

universe u

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal BigOperators

namespace PositiveAffineLine

/-- The diagonal affine line with zero offset and unit slope. -/
def diagonal (n : ℕ) : PositiveAffineLine n where
  offset _ := 0
  slope _ := 1
  slope_pos _ := zero_lt_one

@[simp]
theorem diagonal_offset (n : ℕ) (i : Fin n) : (diagonal n).offset i = 0 := rfl

@[simp]
theorem diagonal_slope (n : ℕ) (i : Fin n) : (diagonal n).slope i = 1 := rfl

/-- At parameter `t`, every coordinate of the diagonal line is `t`. -/
@[simp]
theorem diagonal_orderHom (n : ℕ) (t : ℝ) (i : Fin n) :
    (diagonal n).orderHom t i = t := by
  simp only [orderHom_apply, diagonal_offset, diagonal_slope, mul_one, zero_add]

variable {n : ℕ} [NeZero n]

/-- The source normalization for the matching-distance family of affine lines. -/
noncomputable def IsNormalized (L : PositiveAffineLine n) : Prop :=
  Finset.univ.sup' Finset.univ_nonempty L.slope = 1 ∧ ∑ i, L.offset i = 0

/-- The diagonal line satisfies the matching-distance normalization. -/
theorem diagonal_isNormalized : (diagonal n).IsNormalized := by
  change Finset.univ.sup' Finset.univ_nonempty (fun _ : Fin n => (1 : ℝ)) = 1 ∧
    (∑ _i : Fin n, (0 : ℝ)) = 0
  constructor
  · apply le_antisymm
    · exact (Finset.sup'_le_iff _ _).mpr (fun _ _ => le_rfl)
    · obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
      exact Finset.le_sup' (fun _ : Fin n => (1 : ℝ)) (Finset.mem_univ i)
  · simp

end PositiveAffineLine

/-- Positive affine lines with maximum coordinate slope `1` and zero sum of offsets. -/
abbrev NormalizedAffineLine (n : ℕ) [NeZero n] :=
  {L : PositiveAffineLine n // L.IsNormalized}

namespace NormalizedAffineLine

/-- The normalized diagonal line gives a concrete member of the slice family. -/
def diagonal (n : ℕ) [NeZero n] : NormalizedAffineLine n :=
  ⟨PositiveAffineLine.diagonal n, PositiveAffineLine.diagonal_isNormalized⟩

/-- The family used in the matching-distance supremum is nonempty. -/
instance nonempty (n : ℕ) [NeZero n] : Nonempty (NormalizedAffineLine n) :=
  ⟨diagonal n⟩

end NormalizedAffineLine

namespace PositiveAffineLine

variable {n : ℕ} [NeZero n] {k : Type u} [Field k]
    (L : PositiveAffineLine n)
    (M N P M' N' : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} N)
    (hP : GradedFree.FinitelyPresented.{u,0,0} P)
    (hM' : GradedFree.FinitelyPresented.{u,0,0} M')
    (hN' : GradedFree.FinitelyPresented.{u,0,0} N')

/-- The actual slice's ordinary barcode, derived from the original presentation
of the coordinate module. -/
noncomputable def ordinarySliceBarcode : Diagram ℝ :=
  finitelyPresentedOneDimensionalBarcodeDiagram (reindex L.orderHom M)
    (L.finitelyPresented_fromReal_slice hM)

/-- Every ordinary slice-barcode occurrence is a positive half-open interval. -/
theorem ordinarySliceBarcode_isPositive : (L.ordinarySliceBarcode M hM).IsPositive :=
  finitelyPresentedOneDimensionalBarcodeDiagram_isPositive _ _

/-- The ordinary slice barcode realizes the actual restricted module. -/
noncomputable def ordinarySliceBarcode_realizationIso :
    reindex L.orderHom M ≅ RealBarcode.realize (k := k) (L.ordinarySliceBarcode M hM) :=
  finitelyPresentedOneDimensionalBarcodeRealizationIso _ _

/-- An actual realization by a positive ordinary diagram determines the slice
barcode, including multiplicities and essential intervals. -/
theorem ordinarySliceBarcode_eq_of_realizationIso (D : Diagram ℝ) (hD : D.IsPositive)
    (e : reindex L.orderHom M ≅ RealBarcode.realize (k := k) D) :
    L.ordinarySliceBarcode M hM = D := by
  let B := L.ordinarySliceBarcode M hM
  have hB : B.IsPositive := L.ordinarySliceBarcode_isPositive M hM
  let PB := positiveDiagram_hookPresentation (k := k) B hB
  let PD := positiveDiagram_hookPresentation (k := k) D hD
  have eB : RealBarcode.realize (k := k) B ≅ RealBarcode.realize (k := k) D :=
    (L.ordinarySliceBarcode_realizationIso M hM).symm ≪≫ e
  have e' : CoordinateRealBridge.fromReal (RealBarcode.realize (k := k) B) ≅
      CoordinateRealBridge.fromReal (RealBarcode.realize (k := k) D) :=
    Functor.isoWhiskerLeft CoordinateRealBridge.evaluate.toFunctor eB
  have htags := PB.tagMultiset_eq_of_iso PD e'
  have hdiagrams : oneDimensionalHookDiagram PB.tag = oneDimensionalHookDiagram PD.tag := by
    apply Diagram.ext
    rw [oneDimensionalHookDiagram_points, oneDimensionalHookDiagram_points, htags]
  exact (positiveDiagram_hookPresentation_diagram (k := k) B hB).symm.trans
    (hdiagrams.trans (positiveDiagram_hookPresentation_diagram (k := k) D hD))

/-- Minimum-slope-weighted bottleneck distance between the actual ordinary slice barcodes. -/
noncomputable def weightedSliceBottleneck : ℝ≥0∞ :=
  (L.minSlope : ℝ≥0∞) *
    bottleneck (L.ordinarySliceBarcode M hM) (L.ordinarySliceBarcode N hN)

/-- Ordinary barcode isometry identifies the weighted bottleneck with the
minimum slope times the real interleaving distance of the actual slices. -/
theorem weightedSliceBottleneck_eq_realInterleavingDistance :
    L.weightedSliceBottleneck M N hM hN = (L.minSlope : ℝ≥0∞) *
      realInterleavingDistance (reindex L.orderHom M) (reindex L.orderHom N) := by
  unfold weightedSliceBottleneck ordinarySliceBarcode
  rw [finitelyPresentedOneDimensionalBarcode_bottleneck_eq_distance]

@[simp]
theorem weightedSliceBottleneck_self : L.weightedSliceBottleneck M M hM hM = 0 := by
  simp only [weightedSliceBottleneck, bottleneck_self, mul_zero]

/-- The weighted ordinary slice bottleneck is symmetric. -/
theorem weightedSliceBottleneck_comm :
    L.weightedSliceBottleneck M N hM hN = L.weightedSliceBottleneck N M hN hM := by
  unfold weightedSliceBottleneck
  rw [bottleneck_comm]

/-- The weighted ordinary slice bottleneck satisfies the extended triangle inequality. -/
theorem weightedSliceBottleneck_triangle :
    L.weightedSliceBottleneck M P hM hP ≤
      L.weightedSliceBottleneck M N hM hN + L.weightedSliceBottleneck N P hN hP := by
  unfold weightedSliceBottleneck
  rw [← mul_add]
  exact mul_le_mul' le_rfl (bottleneck_triangle _ _ _)

/-- Natural isomorphisms of the coordinate modules preserve each weighted slice value. -/
theorem weightedSliceBottleneck_congr (e : M ≅ M') (d : N ≅ N') :
    L.weightedSliceBottleneck M N hM hN = L.weightedSliceBottleneck M' N' hM' hN' := by
  rw [weightedSliceBottleneck_eq_realInterleavingDistance,
    weightedSliceBottleneck_eq_realInterleavingDistance]
  congr 1
  exact realInterleavingDistance_congr
    (Functor.isoWhiskerLeft L.orderHom.toFunctor e)
    (Functor.isoWhiskerLeft L.orderHom.toFunctor d)

/-- Every positive line's weighted ordinary bottleneck is bounded by the
coordinate interleaving distance, including infinite distances. -/
theorem weightedSliceBottleneck_le_coordinateInterleavingDistance :
    L.weightedSliceBottleneck M N hM hN ≤ coordinateInterleavingDistance M N := by
  rw [weightedSliceBottleneck_eq_realInterleavingDistance]
  exact L.weighted_slice_distance_le M N

end PositiveAffineLine

variable {n : ℕ} [NeZero n] {k : Type u} [Field k]
    (M N P M' N' : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} N)
    (hP : GradedFree.FinitelyPresented.{u,0,0} P)
    (hM' : GradedFree.FinitelyPresented.{u,0,0} M')
    (hN' : GradedFree.FinitelyPresented.{u,0,0} N')

/-- Matching distance is the supremum of the weighted ordinary bottleneck
values over the source-normalized positive affine lines. -/
noncomputable def sliceMatchingDistance : ℝ≥0∞ :=
  ⨆ L : NormalizedAffineLine n, L.val.weightedSliceBottleneck M N hM hN

/-- Each normalized line contributes a lower bound to matching distance. -/
theorem weightedSliceBottleneck_le_sliceMatchingDistance (L : NormalizedAffineLine n) :
    L.val.weightedSliceBottleneck M N hM hN ≤ sliceMatchingDistance M N hM hN :=
  le_iSup (fun K : NormalizedAffineLine n => K.val.weightedSliceBottleneck M N hM hN) L

@[simp]
theorem sliceMatchingDistance_self : sliceMatchingDistance M M hM hM = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro L
    exact (L.val.weightedSliceBottleneck_self M hM).le
  · exact bot_le

/-- Matching distance is symmetric. -/
theorem sliceMatchingDistance_comm :
    sliceMatchingDistance M N hM hN = sliceMatchingDistance N M hN hM := by
  exact iSup_congr (fun L => L.val.weightedSliceBottleneck_comm M N hM hN)

/-- Matching distance satisfies the extended triangle inequality. -/
theorem sliceMatchingDistance_triangle :
    sliceMatchingDistance M P hM hP ≤
      sliceMatchingDistance M N hM hN + sliceMatchingDistance N P hN hP := by
  apply iSup_le
  intro L
  exact (L.val.weightedSliceBottleneck_triangle M N P hM hN hP).trans
    (add_le_add (weightedSliceBottleneck_le_sliceMatchingDistance M N hM hN L)
      (weightedSliceBottleneck_le_sliceMatchingDistance N P hN hP L))

/-- Natural isomorphisms preserve matching distance in both arguments. -/
theorem sliceMatchingDistance_congr (e : M ≅ M') (d : N ≅ N') :
    sliceMatchingDistance M N hM hN = sliceMatchingDistance M' N' hM' hN' := by
  exact iSup_congr
    (fun L => L.val.weightedSliceBottleneck_congr M N M' N' hM hN hM' hN' e d)

/-- The normalized matching distance is bounded by coordinate interleaving distance. -/
theorem sliceMatchingDistance_le_coordinateInterleavingDistance :
    sliceMatchingDistance M N hM hN ≤ coordinateInterleavingDistance M N := by
  apply iSup_le
  intro L
  exact L.val.weightedSliceBottleneck_le_coordinateInterleavingDistance M N hM hN

end TDA.Persistence
