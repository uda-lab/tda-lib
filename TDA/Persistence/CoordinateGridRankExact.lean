import TDA.Persistence.CoordinateGridKan
import TDA.Persistence.RankExact
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Rank-exact preservation by finite-grid Kan extension

Canonical fiber comparisons transport ordinary exactness and all dying
vectors to the greatest lower grid points. Their map and transition laws
then transport lifts back to the actual Kan extension. The kernel
criterion derives rank additivity, while the same fiber comparisons
give pointwise finite dimensionality.

This proves the finite-product-grid case of BOO,
arXiv:2107.06800v3, Section 4.3 Lemma 4.15.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.CoordinateGrid

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence

variable {k : Type u} [Field k] {n : ℕ} (G : CoordinateGrid n)

/-- Actual finite-grid Kan extension preserves pointwise finite dimensionality. -/
theorem lan_finiteDimensional (M : PModule.{u,0,w} k G.Point)
    [∀ p, FiniteDimensional k (M.obj p)] (a : Fin n → ℝ) :
    FiniteDimensional k ((G.lan.obj M).obj a) := by
  classical
  by_cases ha : G.HasLowerPoint a
  · exact (G.appIso M a ha).symm.toLinearEquiv.finiteDimensional
  · let := ModuleCat.subsingleton_of_isZero (G.isZero_obj_of_not_hasLowerPoint M a ha)
    infer_instance

variable {L M N : PModule.{u,0,w} k G.Point} {ι : L ⟶ M} {π : M ⟶ N}

/-- The actual Lan maps preserve ordinary pointwise short exactness. -/
theorem lan_isPointwiseShortExact (hs : IsPointwiseShortExact ι π) :
    IsPointwiseShortExact (G.lan.map ι) (G.lan.map π) where
  injective a := by
    classical
    intro x y hxy
    by_cases ha : G.HasLowerPoint a
    · let eL := (G.appIso L a ha).toLinearEquiv
      let eM := (G.appIso M a ha).toLinearEquiv
      apply eL.injective
      apply hs.injective (G.floor a ha)
      exact (G.appIso_map_apply ι a ha x).symm.trans
        ((congrArg eM hxy).trans (G.appIso_map_apply ι a ha y))
    · exact (G.eq_zero_of_not_hasLowerPoint L a ha x).trans
        (G.eq_zero_of_not_hasLowerPoint L a ha y).symm
  surjective a := by
    classical
    intro z
    by_cases ha : G.HasLowerPoint a
    · let eM := (G.appIso M a ha).toLinearEquiv
      let eN := (G.appIso N a ha).toLinearEquiv
      obtain ⟨m, hm⟩ := hs.surjective (G.floor a ha) (eN z)
      refine ⟨eM.symm m, ?_⟩
      apply eN.injective
      exact (G.appIso_map_apply π a ha (eM.symm m)).trans
        ((congrArg (π.app (G.floor a ha)).hom (eM.apply_symm_apply m)).trans hm)
    · refine ⟨0, ?_⟩
      exact (map_zero _).trans (G.eq_zero_of_not_hasLowerPoint N a ha z).symm
  range_eq_ker a := by
    classical
    ext z
    change (∃ x, ((G.lan.map ι).app a).hom x = z) ↔ ((G.lan.map π).app a).hom z = 0
    by_cases ha : G.HasLowerPoint a
    · let eL := (G.appIso L a ha).toLinearEquiv
      let eM := (G.appIso M a ha).toLinearEquiv
      let eN := (G.appIso N a ha).toLinearEquiv
      constructor
      · rintro ⟨x, rfl⟩
        apply eN.injective
        have hx : (ι.app (G.floor a ha)).hom (eL x) ∈
            LinearMap.range (ι.app (G.floor a ha)).hom := ⟨eL x, rfl⟩
        rw [hs.range_eq_ker] at hx
        exact (G.appIso_map_apply π a ha (((G.lan.map ι).app a).hom x)).trans
          ((congrArg (π.app (G.floor a ha)).hom (G.appIso_map_apply ι a ha x)).trans
            (hx.trans (map_zero eN).symm))
      · intro hz
        have hz₀ : (π.app (G.floor a ha)).hom (eM z) = 0 :=
          (G.appIso_map_apply π a ha z).symm.trans ((congrArg eN hz).trans (map_zero eN))
        have hr : eM z ∈ LinearMap.range (ι.app (G.floor a ha)).hom := by
          rw [hs.range_eq_ker]
          exact hz₀
        obtain ⟨x, hx⟩ := hr
        refine ⟨eL.symm x, ?_⟩
        apply eM.injective
        exact (G.appIso_map_apply ι a ha (eL.symm x)).trans
          ((congrArg (ι.app (G.floor a ha)).hom (eL.apply_symm_apply x)).trans hx)
    · constructor
      · intro _
        exact G.eq_zero_of_not_hasLowerPoint N a ha _
      · intro _
        exact ⟨0, (map_zero _).trans (G.eq_zero_of_not_hasLowerPoint M a ha z).symm⟩

/-- Dying vectors lift through the actual Lan quotient without changing their death grade. -/
theorem lan_lift_kernel (hs : IsRankExact ι π) {a b : Fin n → ℝ} (hab : a ≤ b)
    (z : (G.lan.obj N).obj a) (hz : structureMapLinear (G.lan.obj N) hab z = 0) :
    ∃ m : (G.lan.obj M).obj a,
      ((G.lan.map π).app a).hom m = z ∧ structureMapLinear (G.lan.obj M) hab m = 0 := by
  classical
  by_cases ha : G.HasLowerPoint a
  · have hb := G.hasLowerPoint_mono hab ha
    let eMa := (G.appIso M a ha).toLinearEquiv
    let eMb := (G.appIso M b hb).toLinearEquiv
    let eNa := (G.appIso N a ha).toLinearEquiv
    let eNb := (G.appIso N b hb).toLinearEquiv
    have hz₀ : structureMapLinear N (G.floor_mono hab ha hb) (eNa z) = 0 :=
      (G.appIso_structureMap_apply N hab ha hb z).symm.trans
        ((congrArg eNb hz).trans (map_zero eNb))
    obtain ⟨m, hm, hdie⟩ := hs.lift_kernel (G.floor_mono hab ha hb) (eNa z) hz₀
    refine ⟨eMa.symm m, ?_, ?_⟩
    · apply eNa.injective
      exact (G.appIso_map_apply π a ha (eMa.symm m)).trans
        ((congrArg (π.app (G.floor a ha)).hom (eMa.apply_symm_apply m)).trans hm)
    · apply eMb.injective
      exact (G.appIso_structureMap_apply M hab ha hb (eMa.symm m)).trans
        ((congrArg (structureMapLinear M (G.floor_mono hab ha hb))
          (eMa.apply_symm_apply m)).trans (hdie.trans (map_zero eMb).symm))
  · exact ⟨0, (map_zero _).trans (G.eq_zero_of_not_hasLowerPoint N a ha z).symm, map_zero _⟩

/-- Finite-product-grid Kan extension preserves actual rank-exact sequences.
Ordinary exactness, pfd fibers and rank additivity are all derived. -/
theorem lan_isRankExact (hs : IsRankExact ι π) : IsRankExact (G.lan.map ι) (G.lan.map π) := by
  let : ∀ p, FiniteDimensional k (M.obj p) := hs.finiteDimensional
  refine
    { toIsPointwiseShortExact := G.lan_isPointwiseShortExact hs.toIsPointwiseShortExact
      finiteDimensional := fun a => G.lan_finiteDimensional M a
      rank_add := ?_ }
  intro a b hab
  let : FiniteDimensional k ((G.lan.obj M).obj a) := G.lan_finiteDimensional M a
  exact ((G.lan_isPointwiseShortExact hs.toIsPointwiseShortExact).rank_add_iff_lift_kernel hab).mpr
    (G.lan_lift_kernel hs hab)

end TDA.Persistence.CoordinateGrid
