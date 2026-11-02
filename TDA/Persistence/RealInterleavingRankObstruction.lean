import TDA.Persistence.RealInterleavingDistance
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Rank obstructions for real interleavings

In a real interleaving, either double-shift structure map factors through the other module's
single middle fiber. Over a field, this bounds its rank when that one fiber is finite-dimensional
and forces the map to vanish when the fiber is zero. The same obstructions give lower bounds on
the extended real interleaving distance. Over any ring, vanishing of both double-shift maps gives
an interleaving whose comparison maps are zero.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory RealShift
open scoped NNReal ENNReal

noncomputable section

namespace RealInterleaving

section Rank

variable {k : Type u} [Field k] {M N : PModule.{u,0,w} k ℝ} {ε : ℝ≥0}

/-- The second factor of the double-shift structure map of an `ε`-interleaving: `i.ψ` at
`t + ε` followed by the shift transport, as a linear map out of `N (t + ε)`. -/
private def backMap (i : RealInterleaving ε M N) (t : ℝ) :
    N.obj (t + ε) →ₗ[k] M.obj (t + ((ε + ε : ℝ≥0) : ℝ)) :=
  (i.ψ.app (t + (ε : ℝ)) ≫ (compIso ε ε M).hom.app t).hom

/-- In an `ε`-interleaving, the structure map of `M` across `2ε` factors through
`N (t + ε)`. -/
private theorem structureMapLinear_eq_comp (i : RealInterleaving ε M N) (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) :
    structureMapLinear M h = (backMap i t).comp (i.φ.app t).hom := by
  have e := i.φ_ψ_app t
  rw [transition_app] at e
  change (structureMap M h).hom = _
  rw [show structureMap M h = structureMap M (le_add_of_nonneg_right
    (ε + ε).coe_nonneg) from rfl, ← e]
  rfl

/-- **Rank bound.** In an `ε`-interleaving of `M` and `N`, the rank of the structure map of `M`
from `t` to `t + 2ε` is at most the dimension of `N (t + ε)`, provided only that this one value
of `N` is finite-dimensional. -/
theorem finrank_range_structureMapLinear_le_of_realInterleaving (i : RealInterleaving ε M N)
    (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [FiniteDimensional k (N.obj (t + ε))] :
    Module.finrank k (LinearMap.range (structureMapLinear M h)) ≤
      Module.finrank k (N.obj (t + ε)) := by
  rw [structureMapLinear_eq_comp i t h]
  exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
    (LinearMap.finrank_range_le (backMap i t))

/-- **Rank bound, symmetric form.** In an `ε`-interleaving of `M` and `N`, the rank of the
structure map of `N` from `t` to `t + 2ε` is at most the dimension of `M (t + ε)`. -/
theorem finrank_range_structureMapLinear_le_of_realInterleaving' (i : RealInterleaving ε M N)
    (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [FiniteDimensional k (M.obj (t + ε))] :
    Module.finrank k (LinearMap.range (structureMapLinear N h)) ≤
      Module.finrank k (M.obj (t + ε)) :=
  finrank_range_structureMapLinear_le_of_realInterleaving i.symm t h

/-- **Zero fibre.** In an `ε`-interleaving of `M` and `N`, if `N (t + ε)` is zero then the
structure map of `M` from `t` to `t + 2ε` is zero. -/
theorem structureMap_eq_zero_of_realInterleaving (i : RealInterleaving ε M N) (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [Subsingleton (N.obj (t + ε))] :
    structureMap M h = 0 := by
  apply ModuleCat.hom_ext
  rw [← structureMapLinear, structureMapLinear_eq_comp i t h]
  ext x
  change backMap i t ((i.φ.app t).hom x) = 0
  rw [Subsingleton.elim (α := N.obj (t + ε)) ((i.φ.app t).hom x) 0]
  exact (backMap i t).map_zero

/-- If the structure map of `M` from `t` to `t + 2ε` has rank larger than the dimension of a
finite-dimensional `N (t + ε)`, then `M` and `N` are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_of_finrank_lt (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ))
    [FiniteDimensional k (N.obj (t + ε))]
    (hlt : Module.finrank k (N.obj (t + ε)) <
      Module.finrank k (LinearMap.range (structureMapLinear M h))) :
    IsEmpty (RealInterleaving ε M N) :=
  ⟨fun i => (finrank_range_structureMapLinear_le_of_realInterleaving i t h).not_gt hlt⟩

/-- If the structure map of `M` from `t` to `t + 2ε` is nonzero and `N (t + ε)` is zero, then
`M` and `N` are not `ε`-interleaved. -/
theorem isEmpty_realInterleaving_of_structureMap_ne_zero (t : ℝ)
    (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)) [Subsingleton (N.obj (t + ε))]
    (hne : structureMap M h ≠ 0) : IsEmpty (RealInterleaving ε M N) :=
  ⟨fun i => hne (structureMap_eq_zero_of_realInterleaving i t h)⟩

/-- **Distance lower bound.** If for every finite parameter `ε < r` some structure map of `M`
from `t` to `t + 2ε` has rank larger than the dimension of a finite-dimensional `N (t + ε)`,
then the real interleaving distance of `M` and `N` is at least `r`. -/
theorem le_realInterleavingDistance_of_finrank_lt {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      FiniteDimensional k (N.obj (t + ε)) ∧
        Module.finrank k (N.obj (t + ε)) <
          Module.finrank k (LinearMap.range (structureMapLinear M h))) :
    r ≤ realInterleavingDistance M N := by
  rw [le_realInterleavingDistance_iff]
  intro ε ⟨i⟩
  by_contra hεr
  obtain ⟨t, h, _, hlt⟩ := hr ε (not_le.1 hεr)
  exact (isEmpty_realInterleaving_of_finrank_lt t h hlt).false i

/-- **Distance lower bound, zero-fibre form.** If for every finite parameter `ε < r` some
structure map of `M` from `t` to `t + 2ε` is nonzero while `N (t + ε)` is zero, then the real
interleaving distance of `M` and `N` is at least `r`. -/
theorem le_realInterleavingDistance_of_structureMap_ne_zero {r : ℝ≥0∞}
    (hr : ∀ ε : ℝ≥0, (ε : ℝ≥0∞) < r → ∃ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)),
      Subsingleton (N.obj (t + ε)) ∧ structureMap M h ≠ 0) :
    r ≤ realInterleavingDistance M N := by
  rw [le_realInterleavingDistance_iff]
  intro ε ⟨i⟩
  by_contra hεr
  obtain ⟨t, h, _, hne⟩ := hr ε (not_le.1 hεr)
  exact (isEmpty_realInterleaving_of_structureMap_ne_zero t h hne).false i

end Rank

section ZeroMaps

variable {R : Type u} [Ring R] {M N : PModule.{u,0,w} R ℝ}

/-- **Zero maps.** If every double-shift structure map of two real modules at the parameter `ε`
is zero, the zero maps form an `ε`-interleaving. This is a converse companion of
`isEmpty_realInterleaving_of_structureMap_ne_zero`. -/
theorem nonempty_realInterleaving_of_structureMap_eq_zero (ε : ℝ≥0)
    (hM : ∀ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)), structureMap M h = 0)
    (hN : ∀ (t : ℝ) (h : t ≤ t + ((ε + ε : ℝ≥0) : ℝ)), structureMap N h = 0) :
    Nonempty (RealInterleaving ε M N) :=
  ⟨RealInterleaving.ofApp 0 0
    (fun t => by
      rw [NatTrans.app_zero, Limits.zero_comp, transition_app]
      exact (hM t _).symm)
    (fun t => by
      rw [NatTrans.app_zero, Limits.zero_comp, transition_app]
      exact (hN t _).symm)⟩

end ZeroMaps

end RealInterleaving

end

end TDA.Persistence
