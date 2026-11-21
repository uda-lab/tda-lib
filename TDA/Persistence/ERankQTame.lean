import TDA.Persistence.ERankErosion
import TDA.Persistence.QTame
import TDA.Persistence.CoordinateRealBridge

/-!
# Extended ranks of q-tame modules and real interleavings

A real persistence module is q-tame exactly when every structure map across a strict
inequality has finite extended rank, and the same holds for its one-coordinate module
`CoordinateRealBridge.fromReal M`. A real `ε`-interleaving bounds the extended rank of the
doubled-shift structure map by the extended dimension of the middle fibre of the other
module, so that rank is finite when the middle fibre is finite-dimensional. Through the
coordinate bridge a real interleaving gives extended-rank erosion of the one-coordinate
modules, and the extended erosion distance is at most the real interleaving distance.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory CoordinateRealBridge
open scoped TDA.Persistence NNReal ENNReal

variable {k : Type u} [Field k]

namespace PModule

/-- A real module is q-tame exactly when every strict structure map has finite extended
rank. -/
theorem qTame_iff_eRankOfStructureMap_ne_top (M : PModule.{u,0,w} k ℝ) :
    M.QTame ↔ ∀ (a b : ℝ) (hab : a < b), eRankOfStructureMap M hab.le ≠ ⊤ := by
  simp only [QTame, eRankOfStructureMap_ne_top_iff]

/-- Every strict structure map of a q-tame module has finite extended rank. -/
theorem QTame.eRankOfStructureMap_ne_top {M : PModule.{u,0,w} k ℝ} (hM : M.QTame)
    {a b : ℝ} (hab : a < b) : eRankOfStructureMap M hab.le ≠ ⊤ :=
  (qTame_iff_eRankOfStructureMap_ne_top M).mp hM a b hab

/-- A real module is q-tame exactly when its one-coordinate module has finite extended rank
on every strict pair of the product order on `Fin 1 → ℝ`. -/
theorem qTame_iff_eRankOfStructureMap_fromReal_ne_top (M : PModule.{u,0,w} k ℝ) :
    M.QTame ↔ ∀ (a b : Fin 1 → ℝ) (hab : a < b),
      eRankOfStructureMap (fromReal M) hab.le ≠ ⊤ := by
  rw [qTame_iff_eRankOfStructureMap_ne_top]
  constructor
  · intro h a b hab
    have hlt : a 0 < b 0 := by
      obtain ⟨-, i, hi⟩ := Pi.lt_def.mp hab
      fin_cases i
      exact hi
    exact h (a 0) (b 0) hlt
  · intro h a b hab
    have hlt : diagonal a < diagonal b := Pi.lt_def.mpr ⟨fun _ => hab.le, ⟨0, hab⟩⟩
    exact h (diagonal a) (diagonal b) hlt

/-- Every strict structure map of the one-coordinate module of a q-tame module has finite
extended rank. -/
theorem QTame.eRankOfStructureMap_fromReal_ne_top {M : PModule.{u,0,w} k ℝ} (hM : M.QTame)
    {a b : Fin 1 → ℝ} (hab : a < b) : eRankOfStructureMap (fromReal M) hab.le ≠ ⊤ :=
  (qTame_iff_eRankOfStructureMap_fromReal_ne_top M).mp hM a b hab

end PModule

namespace RealInterleaving

variable {ε : ℝ≥0}

/-- The doubled-shift structure map of `M` factors through the middle fibre of `N`, so its
extended rank is at most the extended dimension of that fibre. -/
theorem eRankOfStructureMap_le_toENat_rank {M N : PModule.{u,0,w} k ℝ}
    (i : RealInterleaving ε M N) (a : ℝ) :
    eRankOfStructureMap M
        (show a ≤ (a + (ε : ℝ)) + (ε : ℝ) from
          (le_add_of_nonneg_right ε.coe_nonneg).trans
            (le_add_of_nonneg_right ε.coe_nonneg)) ≤
      (Module.rank k (N.obj (a + (ε : ℝ)))).toENat := by
  let f : M.obj a →ₗ[k] N.obj (a + (ε : ℝ)) := (i.φ.app a).hom
  let g : N.obj (a + (ε : ℝ)) →ₗ[k] M.obj ((a + (ε : ℝ)) + (ε : ℝ)) :=
    (i.ψ.app (a + (ε : ℝ))).hom
  have hfactor := congrArg (fun φ => (LinearMap.rank φ).toENat)
    (congrArg ModuleCat.Hom.hom (i.φ_ψ_structureMap a)).symm
  refine (le_of_eq hfactor).trans ?_
  change (g.comp f).rank.toENat ≤ _
  exact Cardinal.toENat.monotone'
    ((LinearMap.rank_comp_le_left f g).trans (LinearMap.rank_le_domain g))

/-- The local finite-image bound: with a finite-dimensional middle fibre the doubled-shift
structure map has finite extended rank. -/
theorem eRankOfStructureMap_ne_top {M N : PModule.{u,0,w} k ℝ}
    (i : RealInterleaving ε M N) (a : ℝ) [FiniteDimensional k (N.obj (a + (ε : ℝ)))] :
    eRankOfStructureMap M
        (show a ≤ (a + (ε : ℝ)) + (ε : ℝ) from
          (le_add_of_nonneg_right ε.coe_nonneg).trans
            (le_add_of_nonneg_right ε.coe_nonneg)) ≠ ⊤ :=
  (eRankOfStructureMap_ne_top_iff M _).mpr (i.finiteDimensional_range_structureMap a)

/-- A real interleaving gives extended-rank erosion of the one-coordinate modules. -/
theorem eRankErosion {M N : PModule.{u,0,u} k ℝ} (i : RealInterleaving ε M N) :
    ERankErosion ε (fromReal M) (fromReal N) :=
  (toCoordinate i).eRankErosion

end RealInterleaving

/-- The extended erosion distance of the one-coordinate modules is at most the real
interleaving distance. -/
theorem eRankErosionDistance_fromReal_le_realInterleavingDistance
    (M N : PModule.{u,0,u} k ℝ) :
    eRankErosionDistance (fromReal M) (fromReal N) ≤ realInterleavingDistance M N := by
  rw [← distance_eq]
  exact eRankErosionDistance_le_coordinateInterleavingDistance _ _

end TDA.Persistence
