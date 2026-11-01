import TDA.Persistence.PositiveAffineSlice
import TDA.Persistence.CoordinateInterleavingDistance
import TDA.Persistence.RealInterleavingDistance
import Mathlib.Data.ENNReal.Inv

/-!
# Interleavings of positive affine restrictions

A coordinate interleaving restricts to a positive affine line after padding
its components with the original module's structure maps. Dividing by the
minimum slope gives the real interleaving parameter. The resulting weighted
and quotient distance bounds allow infinite distances and zero parameters.

This is the construction of Landi, arXiv:1412.3374v1, Lemma 1, expressed with
padding after both components; naturality identifies the forward component
with the source's equivalent placement of padding before that component.
The core works over arbitrary rings and independent module-carrier universes.
-/

set_option autoImplicit false

universe u w
namespace TDA.Persistence
open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

variable {R : Type u} [Ring R] {n : ℕ}
variable {M N : PModule.{u,0,w} R (Fin n → ℝ)} {ε δ : ℝ≥0}

private def sliceIndexPadding (L : ℝ →o (Fin n → ℝ))
    (hp : ∀ t, CoordinateShift.translation ε (L t) ≤ L (t + (δ : ℝ)))
    (N : PModule.{u,0,w} R (Fin n → ℝ)) :
    reindex L ((CoordinateShift.shift ε).obj N) ⟶
      (RealShift.shift δ).obj (reindex L N) :=
  Functor.whiskerRight ((OrderHom.equivalenceFunctor (X := ℝ) (Y := Fin n → ℝ)).functor.map
    (homOfLE (show (CoordinateShift.translation ε).comp L ≤
      L.comp (RealShift.translation δ) from hp))) N

private def sliceRestrictionMap (L : ℝ →o (Fin n → ℝ))
    (hp : ∀ t, CoordinateShift.translation ε (L t) ≤ L (t + (δ : ℝ)))
    (f : M ⟶ (CoordinateShift.shift ε).obj N) :
    reindex L M ⟶ (RealShift.shift δ).obj (reindex L N) :=
  reindexNatTrans L f ≫ sliceIndexPadding L hp N

private theorem sliceRestriction_equation (L : ℝ →o (Fin n → ℝ))
    (hp : ∀ t, CoordinateShift.translation ε (L t) ≤ L (t + (δ : ℝ)))
    (i : CoordinateInterleaving ε M N) (t : ℝ) :
    (sliceRestrictionMap L hp i.φ).app t ≫
        (sliceRestrictionMap L hp i.ψ).app (t + (δ : ℝ)) ≫
          (RealShift.compIso δ δ (reindex L M)).hom.app t =
      (RealShift.transition (δ + δ) (reindex L M)).app t := by
  change (i.φ.app (L t) ≫ structureMap N (hp t)) ≫
    (i.ψ.app (L (t + (δ : ℝ))) ≫ structureMap M (hp (t + (δ : ℝ)))) ≫ _ = _
  repeat' erw [Category.assoc]
  erw [i.ψ.naturality_assoc]
  erw [← Category.assoc, i.φ_ψ_structureMap]
  change M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  repeat' erw [← M.map_comp]
  congr 1

namespace CoordinateInterleaving

/-- Actual restriction with structure-map padding for a shift comparison. -/
def reindexToReal (i : CoordinateInterleaving ε M N) (L : ℝ →o (Fin n → ℝ))
    (hp : ∀ t, CoordinateShift.translation ε (L t) ≤ L (t + (δ : ℝ))) :
    RealInterleaving δ (reindex L M) (reindex L N) :=
  RealInterleaving.ofApp (sliceRestrictionMap L hp i.φ) (sliceRestrictionMap L hp i.ψ)
    (sliceRestriction_equation L hp i) (sliceRestriction_equation L hp i.symm)

/-- Forward components are the supplied maps followed by padding. -/
@[simp] theorem reindexToReal_φ_app (i : CoordinateInterleaving ε M N)
    (L : ℝ →o (Fin n → ℝ))
    (hp : ∀ t, CoordinateShift.translation ε (L t) ≤ L (t + (δ : ℝ))) (t : ℝ) :
    (i.reindexToReal L hp).φ.app t = i.φ.app (L t) ≫ structureMap N (hp t) := rfl

/-- Reverse components are the supplied maps followed by padding. -/
@[simp] theorem reindexToReal_ψ_app (i : CoordinateInterleaving ε M N)
    (L : ℝ →o (Fin n → ℝ))
    (hp : ∀ t, CoordinateShift.translation ε (L t) ≤ L (t + (δ : ℝ))) (t : ℝ) :
    (i.reindexToReal L hp).ψ.app t = i.ψ.app (L t) ≫ structureMap M (hp t) := rfl

/-- Restrict a coordinate interleaving to any positive affine line. -/
noncomputable def restrictPositiveAffineLine [NeZero n] (i : CoordinateInterleaving ε M N)
    (L : PositiveAffineLine n) :
    RealInterleaving (ε / L.minSlope) (reindex L.orderHom M) (reindex L.orderHom N) :=
  i.reindexToReal L.orderHom (L.coordinateShift_le ε)

/-- The forward affine restriction uses the actual shifted structure map. -/
@[simp] theorem restrictPositiveAffineLine_φ_app [NeZero n]
    (i : CoordinateInterleaving ε M N) (L : PositiveAffineLine n) (t : ℝ) :
    (i.restrictPositiveAffineLine L).φ.app t =
      i.φ.app (L.orderHom t) ≫ structureMap N (L.coordinateShift_le ε t) := rfl

/-- The reverse affine restriction uses the actual shifted structure map. -/
@[simp] theorem restrictPositiveAffineLine_ψ_app [NeZero n]
    (i : CoordinateInterleaving ε M N) (L : PositiveAffineLine n) (t : ℝ) :
    (i.restrictPositiveAffineLine L).ψ.app t =
      i.ψ.app (L.orderHom t) ≫ structureMap M (L.coordinateShift_le ε t) := rfl

/-- A zero coordinate interleaving restricts to an actual zero real interleaving. -/
noncomputable def restrictPositiveAffineLineZero [NeZero n]
    (i : CoordinateInterleaving 0 M N) (L : PositiveAffineLine n) :
    RealInterleaving 0 (reindex L.orderHom M) (reindex L.orderHom N) := by
  simpa only [zero_div] using i.restrictPositiveAffineLine L

end CoordinateInterleaving

namespace PositiveAffineLine

variable [NeZero n] (L : PositiveAffineLine n)

/-- No finite-distance or attainment hypothesis is used. -/
theorem weighted_slice_distance_le (M N : PModule.{u,0,w} R (Fin n → ℝ)) :
    (L.minSlope : ℝ≥0∞) * realInterleavingDistance (reindex L.orderHom M)
      (reindex L.orderHom N) ≤ coordinateInterleavingDistance M N := by
  apply (le_coordinateInterleavingDistance_iff).mpr
  intro ε ⟨i⟩
  have h := (i.restrictPositiveAffineLine L).distance_le
  calc
    _ ≤ (L.minSlope : ℝ≥0∞) * (↑(ε / L.minSlope) : ℝ≥0∞) := mul_le_mul' le_rfl h
    _ = (ε : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul]
      congr 1
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt L.minSlope_pos)]

/-- Restriction increases interleaving distance by at most the inverse minimum slope. -/
theorem slice_distance_le_div (M N : PModule.{u,0,w} R (Fin n → ℝ)) :
    realInterleavingDistance (reindex L.orderHom M) (reindex L.orderHom N) ≤
      coordinateInterleavingDistance M N / (L.minSlope : ℝ≥0∞) := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.mpr
    (ne_of_gt L.minSlope_pos))) (Or.inl ENNReal.coe_ne_top)).mpr
  simpa only [mul_comm] using L.weighted_slice_distance_le M N

/-- Zero coordinate distance gives zero real slice distance without requiring attainment. -/
theorem slice_distance_eq_zero_of_coordinate_zero
    (M N : PModule.{u,0,w} R (Fin n → ℝ))
    (h : coordinateInterleavingDistance M N = 0) :
    realInterleavingDistance (reindex L.orderHom M) (reindex L.orderHom N) = 0 := by
  apply le_antisymm
  · simpa only [h, ENNReal.zero_div] using L.slice_distance_le_div M N
  · exact bot_le

end PositiveAffineLine

end TDA.Persistence
