import TDA.Persistence.CoordinateInterleaving
import Mathlib.Data.ENNReal.Operations

/-!
# Extended coordinatewise interleaving distance

The distance is the infimum of finite parameters with coordinatewise
interleaving witnesses. Empty infima are infinite; no attainment or separation
assumption is imposed.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

variable {R : Type u} [Ring R] {n : ℕ}
variable {M N P M' N' : PModule.{u,0,w} R (Fin n → ℝ)}

/-- The infimum of finite parameters admitting a coordinatewise interleaving. -/
noncomputable def coordinateInterleavingDistance (M N : PModule.{u,0,w} R (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (CoordinateInterleaving ε M N)), (ε : ℝ≥0∞)

/-- Any coordinatewise witness gives an upper bound on the infimum. -/
theorem coordinateInterleavingDistance_le_of_nonempty {ε : ℝ≥0}
    (h : Nonempty (CoordinateInterleaving ε M N)) :
    coordinateInterleavingDistance M N ≤ ε :=
  iInf₂_le ε h

/-- An explicit coordinatewise interleaving bounds the distance. -/
theorem CoordinateInterleaving.distance_le {ε : ℝ≥0}
    (i : CoordinateInterleaving ε M N) :
    coordinateInterleavingDistance M N ≤ ε :=
  coordinateInterleavingDistance_le_of_nonempty ⟨i⟩

/-- A lower bound on every admissible parameter is a lower bound on the distance. -/
theorem le_coordinateInterleavingDistance_iff {r : ℝ≥0∞} :
    r ≤ coordinateInterleavingDistance M N ↔
      ∀ ε : ℝ≥0, Nonempty (CoordinateInterleaving ε M N) → r ≤ ε := le_iInf₂_iff

/-- Approximate from above at any extended bound, including zero and infinity. -/
theorem coordinateInterleavingDistance_lt_iff {r : ℝ≥0∞} :
    coordinateInterleavingDistance M N < r ↔
      ∃ ε : ℝ≥0, (ε : ℝ≥0∞) < r ∧ Nonempty (CoordinateInterleaving ε M N) := by
  simp only [coordinateInterleavingDistance, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- Infinity occurs exactly when every finite-parameter witness type is empty. -/
theorem coordinateInterleavingDistance_eq_top_iff :
    coordinateInterleavingDistance M N = ⊤ ↔
      ∀ ε : ℝ≥0, IsEmpty (CoordinateInterleaving ε M N) := by
  simp only [coordinateInterleavingDistance, iInf_eq_top, ENNReal.coe_ne_top, imp_false,
    not_nonempty_iff]

/-- A zero interleaving gives zero distance; this implication need not reverse. -/
theorem CoordinateInterleaving.distance_eq_zero (i : CoordinateInterleaving 0 M N) :
    coordinateInterleavingDistance M N = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using i.distance_le)

theorem coordinateInterleavingDistance_self
    (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    coordinateInterleavingDistance M M = 0 :=
  (CoordinateInterleaving.refl 0 M).distance_eq_zero

theorem coordinateInterleavingDistance_eq_zero_of_iso (e : M ≅ N) :
    coordinateInterleavingDistance M N = 0 :=
  (CoordinateInterleaving.ofIso e).distance_eq_zero

theorem coordinateInterleavingDistance_comm
    (M N : PModule.{u,0,w} R (Fin n → ℝ)) :
    coordinateInterleavingDistance M N = coordinateInterleavingDistance N M :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => i.symm.distance_le)
    (le_iInf₂ fun _ ⟨i⟩ => i.symm.distance_le)

/-- Triangle holds also for empty witness sets and infinite summands. -/
theorem coordinateInterleavingDistance_triangle
    (M N P : PModule.{u,0,w} R (Fin n → ℝ)) :
    coordinateInterleavingDistance M P ≤ coordinateInterleavingDistance M N +
      coordinateInterleavingDistance N P := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro ε hi δ hj
  obtain ⟨i⟩ := hi
  obtain ⟨j⟩ := hj
  simpa only [ENNReal.coe_add] using (i.trans j).distance_le

/-- Natural isomorphisms preserve the distance in both arguments. -/
theorem coordinateInterleavingDistance_congr (e : M ≅ M') (d : N ≅ N') :
    coordinateInterleavingDistance M N = coordinateInterleavingDistance M' N' :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => (i.congr e.symm d.symm).distance_le)
    (le_iInf₂ fun _ ⟨i⟩ => (i.congr e d).distance_le)

/-- Zero distance means witnesses at every positive parameter, without attainment. -/
theorem coordinateInterleavingDistance_eq_zero_iff :
    coordinateInterleavingDistance M N = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε → Nonempty (CoordinateInterleaving ε M N) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, ⟨i⟩⟩ :=
      coordinateInterleavingDistance_lt_iff.1 (h.trans_lt (ENNReal.coe_pos.2 hε))
    exact ⟨i.mono (ENNReal.coe_lt_coe.1 hδ).le⟩
  · intro h
    refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    simpa using coordinateInterleavingDistance_le_of_nonempty (h ε hε)

end TDA.Persistence
