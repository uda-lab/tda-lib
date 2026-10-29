import TDA.Persistence.RankProjective
import Mathlib.Tactic

/-!
# Euler formula for finite rank-exact resolutions

For a supplied finite family of rank-exact short exact rows, the rank of each
structure map is the alternating sum of the corresponding ranks of the middle
terms. The proof uses the rank-additivity equation in every row and cancels the
successive kernel terms. Finite rank-exact projective resolutions are an
additional structured input for this row-only identity.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory
open scoped ZeroObject

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- The finrank of the image of a persistence-module structure map. On pointwise
finite-dimensional modules this is its usual rank. For an infinite-dimensional image,
Mathlib's `Module.finrank` convention gives zero, so the rank invariant interpretation
used below is in the finite-dimensional scope guaranteed by the rank-exact rows and
endpoint isomorphisms. -/
noncomputable def rankOfStructureMap (M : PModule.{u,v,u} k P) {a b : P}
    (hab : a ≤ b) : ℕ :=
  Module.finrank k (LinearMap.range (structureMapLinear M hab))

@[simp] theorem rankOfStructureMap_zero {a b : P} (hab : a ≤ b) :
    rankOfStructureMap (0 : PModule.{u,v,u} k P) hab = 0 := by
  unfold rankOfStructureMap
  have htarget : Subsingleton ((0 : PModule.{u,v,u} k P).obj b) :=
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj b)
  have hrange : Subsingleton
      (LinearMap.range (structureMapLinear (0 : PModule.{u,v,u} k P) hab)) :=
    ⟨fun x y => Subtype.ext (htarget.elim x.val y.val)⟩
  exact @Module.finrank_zero_of_subsingleton k _ _ _ _ _ hrange

/-- Natural isomorphisms preserve the ranks of corresponding structure maps. -/
theorem rankOfStructureMap_iso {M N : PModule.{u,v,u} k P} {a b : P}
    (hab : a ≤ b) (e : M ≅ N) :
    rankOfStructureMap M hab = rankOfStructureMap N hab := by
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
  calc
    rankOfStructureMap M hab =
        Module.finrank k (Submodule.map eb.toLinearMap
          (LinearMap.range (structureMapLinear M hab))) := by
      unfold rankOfStructureMap
      exact (LinearEquiv.finrank_map_eq eb _).symm
    _ = rankOfStructureMap N hab := by
      unfold rankOfStructureMap
      rw [← hrange]

/-- A finite family of actual rank-exact rows, retaining each indexed term as an occurrence.

For `i : Fin length`, the actual row is
`0 → kernel (i.succ) → term i → kernel (i.castSucc) → 0`.
The endpoint isomorphisms identify `kernel 0` with the resolved module and the
last kernel with zero. -/
structure FiniteRankExactResolution (M : PModule.{u,v,u} k P) where
  length : ℕ
  kernel : Fin (length + 1) → PModule.{u,v,u} k P
  term : Fin length → PModule.{u,v,u} k P
  inclusion : ∀ i, kernel i.succ ⟶ term i
  quotient : ∀ i, term i ⟶ kernel i.castSucc
  row_rank_exact : ∀ i, IsRankExact (inclusion i) (quotient i)
  initial_iso : kernel 0 ≅ M
  terminal_iso : kernel (Fin.last length) ≅ 0

/-! A projective resolution adds projectivity of each indexed middle term. The existing
`IsRankProjective` API is formulated for partial orders on a universe-zero index type. -/
structure FiniteRankProjectiveResolution {P : Type} [PartialOrder P]
    (M : PModule.{u,0,u} k P) extends FiniteRankExactResolution M where
  term_rank_projective : ∀ i, IsRankProjective (term i)

namespace FiniteRankExactResolution

variable {M : PModule.{u,v,u} k P}

private theorem alternatingRowSum :
    ∀ (m : ℕ) (r : Fin (m + 1) → ℤ) (q : Fin m → ℤ),
      (∀ i, q i = r i.succ + r i.castSucc) →
      (∑ i : Fin m, (-1 : ℤ) ^ i.val * q i) =
        r 0 - (-1 : ℤ) ^ m * r (Fin.last m) := by
  intro m
  induction m with
  | zero =>
      intro r q _
      simp
  | succ m ih =>
      intro r q hrow
      let r' : Fin (m + 1) → ℤ := fun i => r i.succ
      let q' : Fin m → ℤ := fun i => q i.succ
      have hrow' : ∀ i, q' i = r' i.succ + r' i.castSucc := by
        intro i
        dsimp [q', r']
        simpa using hrow i.succ
      have htail := ih r' q' hrow'
      have hsign :
          (∑ i : Fin m, (-1 : ℤ) ^ i.succ.val * q i.succ) =
            -(∑ i : Fin m, (-1 : ℤ) ^ i.val * q' i) := by
        calc
          _ = ∑ i : Fin m, -((-1 : ℤ) ^ i.val * q' i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [q', Fin.val_succ, pow_succ, mul_comm]
          _ = _ := by rw [Finset.sum_neg_distrib]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul]
      rw [hrow 0, hsign, htail]
      simp [r', Fin.castSucc_zero, Fin.succ_last, pow_succ, mul_comm]
      ring

/-- For every `a ≤ b`, the module rank is the integer alternating sum of the indexed
middle-term ranks. The equality follows by applying `IsRankExact.rank_add` to every actual
row and telescoping the kernel ranks. -/
theorem rank_eq_alternating_sum (R : FiniteRankExactResolution M)
    {a b : P} (hab : a ≤ b) :
    (rankOfStructureMap M hab : ℤ) =
      ∑ i : Fin R.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (R.term i) hab : ℤ) := by
  let r : Fin (R.length + 1) → ℤ := fun i =>
    (rankOfStructureMap (R.kernel i) hab : ℤ)
  let q : Fin R.length → ℤ := fun i =>
    (rankOfStructureMap (R.term i) hab : ℤ)
  have hrow : ∀ i, q i = r i.succ + r i.castSucc := by
    intro i
    dsimp [q, r, rankOfStructureMap]
    exact_mod_cast (R.row_rank_exact i).rank_add hab
  have hsum := alternatingRowSum R.length r q hrow
  have hstart : r 0 = (rankOfStructureMap M hab : ℤ) := by
    dsimp [r]
    exact_mod_cast rankOfStructureMap_iso hab R.initial_iso
  have hfinish : r (Fin.last R.length) = 0 := by
    dsimp [r]
    rw [rankOfStructureMap_iso hab R.terminal_iso]
    simp
  rw [hstart, hfinish] at hsum
  simp only [mul_zero, sub_zero] at hsum
  exact hsum.symm

end FiniteRankExactResolution

namespace FiniteRankProjectiveResolution

variable {P : Type} [PartialOrder P] {M : PModule.{u,0,u} k P}

/-- The Euler formula for a finite rank-exact projective resolution. -/
theorem rank_eq_alternating_sum (R : FiniteRankProjectiveResolution M)
    {a b : P} (hab : a ≤ b) :
    (rankOfStructureMap M hab : ℤ) =
      ∑ i : Fin R.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (R.term i) hab : ℤ) :=
  FiniteRankExactResolution.rank_eq_alternating_sum
    R.toFiniteRankExactResolution hab

end FiniteRankProjectiveResolution

end TDA.Persistence
