import TDA.Reeb.InterleavingDistance
import TDA.Reeb.SmoothingExamples

/-!
# Interleaving distance fixtures

Regression fixtures for `TDA.Reeb.interleavingDistance`, all at `C := Type`:

* the point precosheaf at `0` and the closure precosheaf at `0` are at distance `0`, but are
  neither `0`-interleaved nor isomorphic: zero distance does not imply isomorphism;
* the constant empty and constant one-point precosheaves admit no interleaving, so their
  distance is `⊤`;
* the point precosheaves at `0` and `1` are at distance exactly `1`;
* isomorphism invariance, and the triangle inequality with an infinite summand.

The point and closure precosheaves and their interleavings are reused from the smoothing
fixtures.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb.Examples

open OpenInterval Interleaving

/-- Zero distance does not give a `0`-interleaving: the point/closure pair has distance `0`
but no `0`-witness, so the infimum is not attained and `d = 0` does not give an isomorphism. -/
theorem point_closure_distance :
    interleavingDistance (pointPrecosheaf 0) (closurePrecosheaf 0) = 0 ∧
      IsEmpty (Interleaving 0 (pointPrecosheaf 0) (closurePrecosheaf 0)) ∧
      IsEmpty (pointPrecosheaf 0 ≅ closurePrecosheaf 0) :=
  ⟨interleavingDistance_eq_zero_iff.2 point_closure_interleaving.1,
    point_closure_interleaving.2,
    ⟨fun e => point_closure_interleaving.2.false (Interleaving.ofIso e)⟩⟩

/-- Empty witness set: the constant empty and constant point precosheaves are at `⊤`. -/
theorem const_empty_const_unit_distance :
    interleavingDistance ((Functor.const OpenInterval).obj PEmpty.{1})
      ((Functor.const OpenInterval).obj PUnit.{1}) = ⊤ :=
  interleavingDistance_eq_top_iff.2 fun _ =>
    ⟨fun i => (i.ψ.app ⊤ PUnit.unit : PEmpty.{1}).elim⟩

/-- A finite witness gives its bound, and here the bound is exact: `d(F_0, F_1) = 1`. -/
theorem point_distance_eq_one :
    interleavingDistance (pointPrecosheaf 0) (pointPrecosheaf 1) = 1 := by
  refine le_antisymm (by simpa using pointInterleaving.interleavingDistance_le)
    (le_interleavingDistance_iff.2 fun ε ⟨i⟩ => ?_)
  by_contra hlt
  have hε : (ε : ℝ) < 1 := by
    have : ε < 1 := by simpa using not_le.1 hlt
    exact_mod_cast this
  set r : ℝ := (1 - ε) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have x : (pointPrecosheaf 0).obj (ioo (-r) r) :=
    PLift.up (by change (0 : ℝ) ∈ Set.Ioo (-r) r; constructor <;> linarith)
  have h := (i.φ.app (ioo (-r) r) x).down
  rw [thicken_ioo (by linarith)] at h
  change (1 : ℝ) ∈ Set.Ioo _ _ at h
  linarith [h.2]

/-- Isomorphic precosheaves are at distance `0` and distances are iso-invariant. -/
example (F G F' : OpenInterval ⥤ Type) (e : F ≅ F') :
    interleavingDistance F G = interleavingDistance F' G ∧ interleavingDistance F F' = 0 :=
  ⟨interleavingDistance_congr e (Iso.refl G), interleavingDistance_eq_zero_of_iso e⟩

/-- Triangle with an infinite summand is immediate. -/
example (F G H : OpenInterval ⥤ Type) (h : interleavingDistance F G = ⊤) :
    interleavingDistance F H ≤ interleavingDistance F G + interleavingDistance G H := by
  rw [h, top_add]; exact le_top

end TDA.Reeb.Examples
