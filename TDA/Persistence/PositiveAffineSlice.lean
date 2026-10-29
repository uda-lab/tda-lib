import TDA.Persistence.CoordinateShift
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.GaloisConnection.Basic

set_option autoImplicit false

/-!
# Positive affine lines in coordinate grade space

A positive affine line has coordinates `offset i + t * slope i`, with every
slope strictly positive. For a nonempty coordinate set, the maximum normalized
coordinate difference is its entrance time: a grade lies below the line at `t`
exactly when its entrance time is at most `t`.

The minimum slope is strictly positive and bounds the extra time needed to
absorb a diagonal coordinate shift. No entrance time or minimum is chosen for
the empty coordinate set.
-/

namespace TDA.Persistence

open scoped NNReal

/-- An affine line whose slope is strictly positive in every coordinate. -/
structure PositiveAffineLine (n : ℕ) where
  offset : Fin n → ℝ
  slope : Fin n → ℝ
  slope_pos : ∀ i, 0 < slope i

namespace PositiveAffineLine

variable {n : ℕ}

/-- The coordinate offset and slope determine the line. -/
@[ext]
theorem ext {L K : PositiveAffineLine n}
    (hb : ∀ i, L.offset i = K.offset i) (ha : ∀ i, L.slope i = K.slope i) : L = K := by
  cases L with
  | mk b a h =>
    cases K with
    | mk c d k =>
      have hbc : b = c := funext hb
      have had : a = d := funext ha
      cases hbc
      cases had
      rfl

variable (L : PositiveAffineLine n)

/-- Parameterize the line as a monotone map into coordinate grade space. -/
def orderHom : ℝ →o (Fin n → ℝ) where
  toFun t i := L.offset i + t * L.slope i
  monotone' _ _ h i :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right h (L.slope_pos i).le)

/-- The value of the line in one coordinate. -/
@[simp]
theorem orderHom_apply (t : ℝ) (i : Fin n) :
    L.orderHom t i = L.offset i + t * L.slope i := rfl

variable [NeZero n]

/-- The first line parameter at which the grade lies below the line. -/
noncomputable def entrance (p : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (p i - L.offset i) / L.slope i)

/-- A coordinate grade lies below the line exactly after its entrance time. -/
theorem entrance_le_iff (p : Fin n → ℝ) (t : ℝ) :
    L.entrance p ≤ t ↔ p ≤ L.orderHom t := by
  simp only [entrance, Finset.sup'_le_iff, Finset.mem_univ, forall_const]
  change (∀ i, (p i - L.offset i) / L.slope i ≤ t) ↔
    ∀ i, p i ≤ L.offset i + t * L.slope i
  constructor
  · intro h i
    have hi := (div_le_iff₀ (L.slope_pos i)).mp (h i)
    linarith
  · intro h i
    apply (div_le_iff₀ (L.slope_pos i)).mpr
    linarith [h i]

/-- Entrance time is left adjoint to the affine line parameterization. -/
theorem galoisConnection : GaloisConnection L.entrance L.orderHom :=
  L.entrance_le_iff

/-- Increasing the coordinate grade can only increase its entrance time. -/
theorem entrance_monotone : Monotone L.entrance :=
  L.galoisConnection.monotone_l

/-- Each normalized coordinate difference is bounded by the entrance time. -/
theorem normalizedDifference_le_entrance (p : Fin n → ℝ) (i : Fin n) :
    (p i - L.offset i) / L.slope i ≤ L.entrance p := by
  exact Finset.le_sup' (fun j => (p j - L.offset j) / L.slope j) (Finset.mem_univ i)

/-- A point on the line enters at its own parameter. -/
@[simp]
theorem entrance_orderHom (t : ℝ) : L.entrance (L.orderHom t) = t := by
  apply le_antisymm ((L.entrance_le_iff _ t).mpr le_rfl)
  obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
  have hi := (L.entrance_le_iff (L.orderHom t) _).mp le_rfl i
  change L.offset i + t * L.slope i ≤
    L.offset i + L.entrance (L.orderHom t) * L.slope i at hi
  nlinarith [L.slope_pos i]

/-- The minimum coordinate slope, regarded as a nonnegative real. -/
noncomputable def minSlope : ℝ≥0 :=
  ⟨Finset.univ.inf' Finset.univ_nonempty L.slope,
    (Finset.le_inf'_iff _ _).mpr (fun i _ => (L.slope_pos i).le)⟩

/-- The minimum slope is strictly positive. -/
theorem minSlope_pos : 0 < L.minSlope := by
  change 0 < Finset.univ.inf' Finset.univ_nonempty L.slope
  exact (Finset.lt_inf'_iff _).mpr (fun i _ => L.slope_pos i)

/-- The minimum slope is at most every coordinate slope. -/
theorem minSlope_le_slope (i : Fin n) : (L.minSlope : ℝ) ≤ L.slope i :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- A lower bound for the minimum slope is a lower bound for each coordinate. -/
theorem le_minSlope_iff (r : ℝ) :
    r ≤ (L.minSlope : ℝ) ↔ ∀ i, r ≤ L.slope i := by
  change r ≤ Finset.univ.inf' Finset.univ_nonempty L.slope ↔ ∀ i, r ≤ L.slope i
  simp only [Finset.le_inf'_iff, Finset.mem_univ, forall_const]

/-- Advancing the line by `ε / minSlope` absorbs a coordinate shift by `ε`. -/
theorem coordinateShift_le (ε : ℝ≥0) (t : ℝ) :
    CoordinateShift.translation ε (L.orderHom t) ≤
      L.orderHom (t + ((ε / L.minSlope : ℝ≥0) : ℝ)) := by
  intro i
  change L.offset i + t * L.slope i + (ε : ℝ) ≤
    L.offset i + (t + ((ε / L.minSlope : ℝ≥0) : ℝ)) * L.slope i
  have hμ : (0 : ℝ) < (L.minSlope : ℝ) := L.minSlope_pos
  have hb := mul_le_mul_of_nonneg_left (L.minSlope_le_slope i)
    (div_nonneg ε.coe_nonneg hμ.le)
  rw [div_mul_cancel₀ _ (ne_of_gt hμ)] at hb
  push_cast
  nlinarith

end PositiveAffineLine
end TDA.Persistence
