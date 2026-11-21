import TDA.Persistence.FiniteRankProjectiveResolution
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Extended-natural image rank of a structure map

`eRankOfStructureMap M hab` is the rank of the structure map of `M` at `a ≤ b`, valued in
`ℕ∞`: the dimension of its image when that is finite, and `⊤` when the image is
infinite-dimensional. Every infinite cardinal is collapsed to `⊤`. It is
`Cardinal.toENat` of Mathlib's cardinal-valued `LinearMap.rank`, as Mathlib's
`Matrix.eRank` is `Cardinal.toENat` of `Matrix.cRank`.

Unlike the `ℕ`-valued `rankOfStructureMap`, which is a `Module.finrank` and so is `0` on an
infinite-dimensional image, the composition and four-point inequalities hold for every
module, without finite dimensionality. On a finite-dimensional image the two ranks agree.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence

open CategoryTheory
open scoped ZeroObject

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- The rank of the structure map of `M` at `a ≤ b`, in `ℕ∞`: the dimension of its image
when finite, and `⊤` when the image is infinite-dimensional. -/
noncomputable def eRankOfStructureMap (M : PModule.{u,v,w} k P) {a b : P} (hab : a ≤ b) :
    ℕ∞ :=
  (structureMapLinear M hab).rank.toENat

/-- The extended rank is `Cardinal.toENat` of the dimension of the image of the structure
map. -/
theorem eRankOfStructureMap_eq_toENat_rank (M : PModule.{u,v,w} k P) {a b : P}
    (hab : a ≤ b) :
    eRankOfStructureMap M hab =
      (Module.rank k (LinearMap.range (structureMapLinear M hab))).toENat :=
  rfl

/-- On the diagonal the rank is the dimension of the fiber. -/
theorem eRankOfStructureMap_self (M : PModule.{u,v,w} k P) (a : P) :
    eRankOfStructureMap M (le_refl a) = (Module.rank k (M.obj a)).toENat := by
  rw [eRankOfStructureMap_eq_toENat_rank, structureMapLinear_self, LinearMap.range_id,
    rank_top]

/-- The rank of a composite structure map is at most the rank of its later factor. -/
theorem eRankOfStructureMap_trans_le_left (M : PModule.{u,v,w} k P) {a b c : P}
    (hab : a ≤ b) (hbc : b ≤ c) :
    eRankOfStructureMap M (hab.trans hbc) ≤ eRankOfStructureMap M hbc := by
  unfold eRankOfStructureMap
  rw [structureMapLinear_comp M hab hbc]
  exact Cardinal.toENat.monotone'
    (LinearMap.rank_comp_le_left (structureMapLinear M hab) (structureMapLinear M hbc))

/-- The rank of a composite structure map is at most the rank of its earlier factor. -/
theorem eRankOfStructureMap_trans_le_right (M : PModule.{u,v,w} k P) {a b c : P}
    (hab : a ≤ b) (hbc : b ≤ c) :
    eRankOfStructureMap M (hab.trans hbc) ≤ eRankOfStructureMap M hab := by
  unfold eRankOfStructureMap
  rw [structureMapLinear_comp M hab hbc]
  have h := LinearMap.rank_comp_le_right (structureMapLinear M hab)
    (structureMapLinear M hbc)
  exact Cardinal.toENat.monotone' h

/-- Ranks decrease when a structure-map interval is widened at both ends, for every module. -/
theorem eRankOfStructureMap_four_point (M : PModule.{u,v,w} k P)
    {a₀ a₁ b₁ b₀ : P} (ha : a₀ ≤ a₁) (hab : a₁ ≤ b₁) (hb : b₁ ≤ b₀) :
    eRankOfStructureMap M (ha.trans (hab.trans hb)) ≤ eRankOfStructureMap M hab :=
  (eRankOfStructureMap_trans_le_left M ha (hab.trans hb)).trans
    (eRankOfStructureMap_trans_le_right M hab hb)

/-- Every structure map of the zero module has extended rank `0`. -/
@[simp] theorem eRankOfStructureMap_zero {a b : P} (hab : a ≤ b) :
    eRankOfStructureMap (0 : PModule.{u,v,w} k P) hab = 0 := by
  have htarget : Subsingleton ((0 : PModule.{u,v,w} k P).obj b) :=
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj b)
  have hrange : Subsingleton
      (LinearMap.range (structureMapLinear (0 : PModule.{u,v,w} k P) hab)) :=
    ⟨fun x y => Subtype.ext (htarget.elim x.val y.val)⟩
  rw [eRankOfStructureMap_eq_toENat_rank, Cardinal.toENat_eq_zero]
  exact rank_subsingleton' k _

/-- The rank is `⊤` exactly when the image of the structure map is infinite-dimensional. -/
theorem eRankOfStructureMap_eq_top_iff (M : PModule.{u,v,w} k P) {a b : P}
    (hab : a ≤ b) :
    eRankOfStructureMap M hab = ⊤ ↔
      ¬ FiniteDimensional k (LinearMap.range (structureMapLinear M hab)) := by
  rw [eRankOfStructureMap_eq_toENat_rank, Cardinal.toENat_eq_top,
    FiniteDimensional, ← Module.rank_lt_aleph0_iff, not_lt]

/-- The extended rank is finite exactly when the image of the structure map is
finite-dimensional. -/
theorem eRankOfStructureMap_ne_top_iff (M : PModule.{u,v,w} k P) {a b : P} (hab : a ≤ b) :
    eRankOfStructureMap M hab ≠ ⊤ ↔
      FiniteDimensional k (LinearMap.range (structureMapLinear M hab)) := by
  rw [ne_eq, eRankOfStructureMap_eq_top_iff, not_not]

/-- The `ℕ`-valued rank is the truncation of the extended rank, with `⊤` sent to `0`; this
holds for every module. -/
theorem rankOfStructureMap_eq_toNat_eRankOfStructureMap
    (M : PModule.{u,v,u} k P) {a b : P} (hab : a ≤ b) :
    rankOfStructureMap M hab = (eRankOfStructureMap M hab).toNat := by
  rw [eRankOfStructureMap_eq_toENat_rank, Cardinal.toNat_toENat]
  rfl

/-- On a finite-dimensional image the extended rank is the `ℕ`-valued rank. -/
theorem eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional
    (M : PModule.{u,v,u} k P) {a b : P} (hab : a ≤ b)
    [FiniteDimensional k (LinearMap.range (structureMapLinear M hab))] :
    eRankOfStructureMap M hab = rankOfStructureMap M hab := by
  rw [eRankOfStructureMap_eq_toENat_rank, rankOfStructureMap,
    ← Module.finrank_eq_rank, Cardinal.toENat_nat]

/-- If the source fiber `M.obj a` is finite-dimensional, the extended rank is the
`ℕ`-valued rank. -/
theorem eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional_source
    (M : PModule.{u,v,u} k P) {a b : P} (hab : a ≤ b) [FiniteDimensional k (M.obj a)] :
    eRankOfStructureMap M hab = rankOfStructureMap M hab :=
  eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional M hab

/-- Comparisons of extended ranks are comparisons of `ℕ`-valued ranks when the two source
fibers `M.obj a` and `N.obj c` are finite-dimensional; in particular on pointwise
finite-dimensional modules. -/
theorem eRankOfStructureMap_le_eRankOfStructureMap_iff
    {M N : PModule.{u,v,u} k P} {a b c d : P} (hab : a ≤ b) (hcd : c ≤ d)
    [FiniteDimensional k (M.obj a)] [FiniteDimensional k (N.obj c)] :
    eRankOfStructureMap M hab ≤ eRankOfStructureMap N hcd ↔
      rankOfStructureMap M hab ≤ rankOfStructureMap N hcd := by
  rw [eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional_source,
    eRankOfStructureMap_eq_rankOfStructureMap_of_finiteDimensional_source, Nat.cast_le]

/-- Natural isomorphisms preserve extended ranks. -/
theorem eRankOfStructureMap_iso {M N : PModule.{u,v,w} k P} {a b : P}
    (hab : a ≤ b) (e : M ≅ N) :
    eRankOfStructureMap M hab = eRankOfStructureMap N hab := by
  let ea : M.obj a ≃ₗ[k] N.obj a := (e.app a).toLinearEquiv
  let eb : M.obj b ≃ₗ[k] N.obj b := (e.app b).toLinearEquiv
  have hnat : (structureMapLinear N hab).comp ea.toLinearMap =
      eb.toLinearMap.comp (structureMapLinear M hab) := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun f : M.obj a ⟶ N.obj b => f.hom x)
      (e.hom.naturality (homOfLE hab))
    change (e.app b).toLinearEquiv (structureMapLinear M hab x) =
      structureMapLinear N hab ((e.app a).toLinearEquiv x) at h
    exact h.symm
  have hrange := congrArg LinearMap.range hnat
  have hleft : LinearMap.range (eb.toLinearMap.comp (structureMapLinear M hab)) =
      Submodule.map eb.toLinearMap (LinearMap.range (structureMapLinear M hab)) :=
    LinearMap.range_comp _ _
  have hsurj : LinearMap.range ea.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr ea.surjective
  rw [LinearMap.range_comp_of_range_eq_top _ hsurj, hleft] at hrange
  rw [eRankOfStructureMap_eq_toENat_rank, eRankOfStructureMap_eq_toENat_rank, hrange,
    LinearEquiv.rank_map_eq]

end TDA.Persistence
