import TDA.Persistence.AlgebraicFamilyProjection
import TDA.Persistence.IntervalEndomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Uniqueness of interval decompositions of real persistence modules

For an isomorphism `e` between algebraic sums of nonempty interval modules over `ℝ`, with
arbitrary index types, and every `S : Set ℝ`, the types `{j // I j = S}` and `{j' // I' j' = S}`
of summands with support `S` have the same cardinality (`mk_support_fiber_eq_of_iso`). Hence the
index types are matched by a bijection that preserves supports (`exists_equiv_support_of_iso`),
and two decompositions of one module are matched in the same way
(`exists_equiv_support_of_iso_of_iso`). No pointwise finite-dimensionality is assumed.

The argument is the external form of Lemma 3.3 and Theorem 3.4 of W. L. Gan and
N. Upegui Keagy, *On interval decomposition of persistence modules*, arXiv:2507.01303 v1. At a
point `x ∈ S`, the block of coordinates with support `S` in the fibre of the first sum maps
linearly into the block of the second sum (include, apply `e`, project to the coordinates with
support `S`). The map is injective: a vector in its kernel is carried by `e` to coordinates with
supports different from `S`, and its image under `e.inv` is a sum of composites
`module S ⟶ module T ⟶ module S` with `T ≠ S`, which vanish by `comp_eq_zero_of_ne` (Lemma 3.1).
Each fibre at `x` is one-dimensional, so the dimension of a block is the cardinality of its index
type, and the cardinality of one fibre of supports is at most that of the other.

The uniqueness part of Theorem 3.4 of M. B. Botnan and M. Lesnick, *An Introduction to
Multiparameter Persistence*, arXiv:2203.14289 v2 (a pointwise finite-dimensional module over a
totally ordered set has a unique multiset of intervals) corresponds to
`exists_equiv_support_of_iso_of_iso`, here for `ℝ` and arbitrary index types.

`blockMap` and `blockMap_injective` give the injection for two families of real persistence
modules and two predicates on their index types, under a vanishing condition on composites
through coordinates outside the target block.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.AlgebraicFamily

open CategoryTheory
open scoped Classical

section Block

variable {k : Type u} [Field k]

/-- The sub-sum over a predicate, included in the full direct sum. -/
noncomputable def blockInclude {ι : Type} (X : ι → Type u) [∀ i, AddCommGroup (X i)]
    [∀ i, Module k (X i)] (p : ι → Prop) :
    (DirectSum {j // p j} (fun a => X a.1)) →ₗ[k] DirectSum ι X :=
  DirectSum.toModule k _ _ (fun a => DirectSum.lof k ι X a.1)

/-- The coordinates of a direct sum over a predicate. -/
noncomputable def blockRestrict {ι : Type} (X : ι → Type u) [∀ i, AddCommGroup (X i)]
    [∀ i, Module k (X i)] (p : ι → Prop) :
    DirectSum ι X →ₗ[k] (DirectSum {j // p j} (fun a => X a.1)) :=
  DirectSum.toModule k ι _ (fun j =>
    if h : p j then DirectSum.lof k {j // p j} (fun a => X a.1) ⟨j, h⟩ else 0)

/-- The coordinates outside a predicate, kept in the full direct sum. -/
noncomputable def blockCompl {ι : Type} (X : ι → Type u) [∀ i, AddCommGroup (X i)]
    [∀ i, Module k (X i)] (p : ι → Prop) : DirectSum ι X →ₗ[k] DirectSum ι X :=
  DirectSum.toModule k ι _ (fun j => if p j then 0 else DirectSum.lof k ι X j)

variable {ι : Type} (X : ι → Type u) [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)]
  (p : ι → Prop)

theorem blockInclude_of (a : {j // p j}) (y : X a.1) :
    blockInclude (k := k) X p (DirectSum.of (fun a : {j // p j} => X a.1) a y) =
      DirectSum.of X a.1 y := by
  change blockInclude (k := k) X p (DirectSum.lof k _ (fun a : {j // p j} => X a.1) a y) =
    DirectSum.lof k ι X a.1 y
  simp [blockInclude]

theorem blockRestrict_of_pos {j : ι} (h : p j) (y : X j) :
    blockRestrict (k := k) X p (DirectSum.of X j y) =
      DirectSum.of (fun a : {j // p j} => X a.1) ⟨j, h⟩ y := by
  change blockRestrict (k := k) X p (DirectSum.lof k ι X j y) =
    DirectSum.lof k _ (fun a : {j // p j} => X a.1) ⟨j, h⟩ y
  simp [blockRestrict, h]

theorem blockRestrict_of_neg {j : ι} (h : ¬ p j) (y : X j) :
    blockRestrict (k := k) X p (DirectSum.of X j y) = 0 := by
  change blockRestrict (k := k) X p (DirectSum.lof k ι X j y) = 0
  simp [blockRestrict, h]

theorem blockCompl_of_pos {j : ι} (h : p j) (y : X j) :
    blockCompl (k := k) X p (DirectSum.of X j y) = 0 := by
  change blockCompl (k := k) X p (DirectSum.lof k ι X j y) = 0
  simp [blockCompl, h]

theorem blockCompl_of_neg {j : ι} (h : ¬ p j) (y : X j) :
    blockCompl (k := k) X p (DirectSum.of X j y) = DirectSum.of X j y := by
  change blockCompl (k := k) X p (DirectSum.lof k ι X j y) = DirectSum.lof k ι X j y
  simp [blockCompl, h]

theorem blockRestrict_blockInclude (v : DirectSum {j // p j} (fun a => X a.1)) :
    blockRestrict (k := k) X p (blockInclude (k := k) X p v) = v := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of a y =>
    rw [blockInclude_of, blockRestrict_of_pos X p a.2]
  | add u w hu hw => simp [hu, hw]

theorem blockInclude_blockRestrict_add_compl (v : DirectSum ι X) :
    blockInclude (k := k) X p (blockRestrict (k := k) X p v) + blockCompl (k := k) X p v = v := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    by_cases h : p j
    · rw [blockRestrict_of_pos X p h, blockInclude_of, blockCompl_of_pos X p h, add_zero]
    · rw [blockRestrict_of_neg X p h, blockCompl_of_neg X p h, map_zero, zero_add]
  | add u w hu hw =>
    simp only [map_add]
    rw [add_add_add_comm, hu, hw]

theorem component_blockRestrict (a : {j // p j}) (v : DirectSum ι X) :
    DirectSum.component k {j // p j} (fun a => X a.1) a (blockRestrict (k := k) X p v) =
      DirectSum.component k ι X a.1 v := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    by_cases h : p j
    · rw [blockRestrict_of_pos X p h]
      simp only [← DirectSum.lof_eq_of k]
      rw [DirectSum.component.of, DirectSum.component.of]
      by_cases hja : j = a.1
      · have : (⟨j, h⟩ : {j // p j}) = a := Subtype.ext hja
        subst this
        simp
      · have : (⟨j, h⟩ : {j // p j}) ≠ a := fun e => hja (congrArg Subtype.val e)
        simp [this, hja]
    · rw [blockRestrict_of_neg X p h]
      simp only [← DirectSum.lof_eq_of k]
      rw [DirectSum.component.of, map_zero]
      by_cases hja : j = a.1
      · exact absurd (hja ▸ a.2) h
      · simp [hja]
  | add u w hu hw => simp [hu, hw]

end Block

section Injective

variable {k : Type u} [Field k] {ι ι' : Type}
  (F : ι → PModule.{u,0,u} k ℝ) (G : ι' → PModule.{u,0,u} k ℝ)
  (e : familyModule F ≅ familyModule G) (x : ℝ) (p : ι → Prop) (q : ι' → Prop)

/-- Include the `p`-block of the fibre at `x`, apply the isomorphism, and keep the `q`-block. -/
noncomputable def blockMap :
    DirectSum {j // p j} (fun a => (F a.1).obj x) →ₗ[k]
      DirectSum {j // q j} (fun a => (G a.1).obj x) :=
  blockRestrict (k := k) (fun j => (G j).obj x) q ∘ₗ (e.hom.app x).hom ∘ₗ
    blockInclude (k := k) (fun j => (F j).obj x) p

/-- The block map is injective when every composite through a coordinate outside the target
block vanishes between coordinates of the source block. -/
theorem blockMap_injective
    (hvan : ∀ i j j', p i → p j → ¬ q j' →
      (inclusion F i ≫ e.hom ≫ projection G j') ≫
        (inclusion G j' ≫ e.inv ≫ projection F j) = 0) :
    Function.Injective (blockMap F G e x p q) := by
  let eps : DirectSum ι (fun j => (F j).obj x) →ₗ[k] DirectSum ι' (fun j => (G j).obj x) :=
    (e.hom.app x).hom
  let del : DirectSum ι' (fun j => (G j).obj x) →ₗ[k] DirectSum ι (fun j => (F j).obj x) :=
    (e.inv.app x).hom
  have hde : ∀ v, del (eps v) = v := fun v => by
    have := congrArg (fun f => f.hom v) (e.hom_inv_id_app x)
    exact this
  have hvan' : ∀ i j j', p i → p j → ¬ q j' → ∀ y : (F i).obj x,
      DirectSum.component k ι (fun j => (F j).obj x) j
        (del (DirectSum.of (fun j => (G j).obj x) j'
          (DirectSum.component k ι' (fun j => (G j).obj x) j'
            (eps (DirectSum.of (fun j => (F j).obj x) i y))))) = 0 := by
    intro i j j' hi hj hj' y
    have := congrArg (fun f => (f.app x).hom y) (hvan i j j' hi hj hj')
    exact this
  let R : DirectSum {j // q j} (fun a => (G a.1).obj x) →ₗ[k]
      DirectSum {j // p j} (fun a => (F a.1).obj x) :=
    blockRestrict (k := k) (fun j => (F j).obj x) p ∘ₗ del ∘ₗ
      blockInclude (k := k) (fun j => (G j).obj x) q
  have hR : ∀ v, R (blockMap F G e x p q v) = v := by
    intro v
    induction v using DirectSum.induction_on with
    | zero => simp
    | add u w hu hw => simp only [map_add, hu, hw]
    | of a y =>
      have h1 : blockMap F G e x p q (DirectSum.of (fun a : {j // p j} => (F a.1).obj x) a y) =
          blockRestrict (k := k) (fun j => (G j).obj x) q
            (eps (DirectSum.of (fun j => (F j).obj x) a.1 y)) := by
        change blockRestrict (k := k) (fun j => (G j).obj x) q
          (eps (blockInclude (k := k) (fun j => (F j).obj x) p _)) = _
        rw [blockInclude_of]
      set w := eps (DirectSum.of (fun j => (F j).obj x) a.1 y) with hw
      have h2 : blockInclude (k := k) (fun j => (G j).obj x) q
          (blockRestrict (k := k) (fun j => (G j).obj x) q w) =
          w - blockCompl (k := k) (fun j => (G j).obj x) q w :=
        eq_sub_of_add_eq (blockInclude_blockRestrict_add_compl _ q w)
      have h3 : R (blockRestrict (k := k) (fun j => (G j).obj x) q w) =
          blockRestrict (k := k) (fun j => (F j).obj x) p
            (DirectSum.of (fun j => (F j).obj x) a.1 y) -
          blockRestrict (k := k) (fun j => (F j).obj x) p
            (del (blockCompl (k := k) (fun j => (G j).obj x) q w)) := by
        change blockRestrict (k := k) (fun j => (F j).obj x) p
          (del (blockInclude (k := k) (fun j => (G j).obj x) q _)) = _
        rw [h2, map_sub, map_sub, hw, hde]
      have h4 : blockRestrict (k := k) (fun j => (F j).obj x) p
          (del (blockCompl (k := k) (fun j => (G j).obj x) q w)) = 0 := by
        apply DirectSum.ext
        intro a₀
        change DirectSum.component k _ (fun a : {j // p j} => (F a.1).obj x) a₀ _ = 0
        rw [component_blockRestrict (k := k) (fun j => (F j).obj x) p a₀]
        have hsum : w = ∑ j' ∈ w.support, DirectSum.of (fun j => (G j).obj x) j' (w j') :=
          (DirectSum.sum_support_of w).symm
        rw [hsum]
        simp only [map_sum]
        apply Finset.sum_eq_zero
        intro j' _
        by_cases hq : q j'
        · rw [blockCompl_of_pos _ q hq, map_zero, map_zero]
        · rw [blockCompl_of_neg _ q hq]
          exact hvan' a.1 a₀.1 j' a.2 a₀.2 hq y
      rw [h1, h3, h4, sub_zero, blockRestrict_of_pos _ p a.2]
  exact Function.LeftInverse.injective (g := R) hR

end Injective

section Intervals

open SupportInterval

variable {k : Type u} [Field k] {J J' : Type}

private theorem rank_fiber (T : Set ℝ) {x : ℝ} (hx : x ∈ T) :
    Module.rank k (fiber (k := k) T x) = 1 := by
  have h : fiber (k := k) T x = ⊤ := by simp [fiber, hx]
  rw [(LinearEquiv.ofEq _ _ h |>.trans Submodule.topEquiv).rank_eq, Module.rank_self]

private theorem rank_block (I : J → Set ℝ) (hI : ∀ j, (I j).OrdConnected) {S : Set ℝ}
    {x : ℝ} (hx : x ∈ S) :
    Module.rank k (DirectSum {j // I j = S}
      (fun a => ((module (k := k) (I a.1) (hI a.1)).obj x))) =
      Cardinal.lift.{u} (Cardinal.mk {j // I j = S}) := by
  have h : ∀ a : {j // I j = S},
      Module.rank k ((module (k := k) (I a.1) (hI a.1)).obj x) = 1 := fun a =>
    rank_fiber (I a.1) (by rw [a.2]; exact hx)
  rw [rank_directSum]
  simp [h]

/-- For each support `S` with a point `x`, the number of summands with support `S` in a
decomposition is at most the number in any other decomposition of an isomorphic sum. -/
theorem mk_support_fiber_le_of_iso (I : J → Set ℝ) (hI : ∀ j, (I j).OrdConnected)
    (hne : ∀ j, (I j).Nonempty) (I' : J' → Set ℝ) (hI' : ∀ j, (I' j).OrdConnected)
    (e : familyModule (fun j => module (k := k) (I j) (hI j)) ≅
      familyModule (fun j => module (k := k) (I' j) (hI' j))) (S : Set ℝ) :
    Cardinal.mk {j // I j = S} ≤ Cardinal.mk {j' // I' j' = S} := by
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hinj := blockMap_injective (k := k) (fun j => module (k := k) (I j) (hI j))
      (fun j => module (k := k) (I' j) (hI' j)) e x (fun j => I j = S) (fun j => I' j = S)
      (by
        intro i j j' hi hj hj'
        exact comp_eq_zero_of_ne (hI i) (hI' j') (hI j) (hj.trans hi.symm)
          (fun h => hj' (h.symm.trans hi)) _ _)
    have h := LinearMap.lift_rank_le_of_injective _ hinj
    rw [rank_block I hI hx, rank_block I' hI' hx] at h
    simpa using h
  · have : IsEmpty {j // I j = S} := ⟨fun a => hS (a.2 ▸ hne a.1)⟩
    simp

/-- The number of summands with a given support agrees in any two decompositions of
isomorphic algebraic sums of nonempty interval modules; the index types are arbitrary. -/
theorem mk_support_fiber_eq_of_iso (I : J → Set ℝ) (hI : ∀ j, (I j).OrdConnected)
    (hne : ∀ j, (I j).Nonempty) (I' : J' → Set ℝ) (hI' : ∀ j, (I' j).OrdConnected)
    (hne' : ∀ j, (I' j).Nonempty)
    (e : familyModule (fun j => module (k := k) (I j) (hI j)) ≅
      familyModule (fun j => module (k := k) (I' j) (hI' j))) (S : Set ℝ) :
    Cardinal.mk {j // I j = S} = Cardinal.mk {j' // I' j' = S} :=
  le_antisymm (mk_support_fiber_le_of_iso I hI hne I' hI' e S)
    (mk_support_fiber_le_of_iso I' hI' hne' I hI e.symm S)

/-- An isomorphism of algebraic sums of nonempty interval modules gives a bijection of the
index types that preserves supports. -/
theorem exists_equiv_support_of_iso (I : J → Set ℝ) (hI : ∀ j, (I j).OrdConnected)
    (hne : ∀ j, (I j).Nonempty) (I' : J' → Set ℝ) (hI' : ∀ j, (I' j).OrdConnected)
    (hne' : ∀ j, (I' j).Nonempty)
    (e : familyModule (fun j => module (k := k) (I j) (hI j)) ≅
      familyModule (fun j => module (k := k) (I' j) (hI' j))) :
    ∃ σ : J ≃ J', ∀ j, I' (σ j) = I j := by
  let τ : ∀ S : Set ℝ, {j // I j = S} ≃ {j' // I' j' = S} := fun S =>
    Classical.choice (Cardinal.eq.mp (mk_support_fiber_eq_of_iso I hI hne I' hI' hne' e S))
  refine ⟨(Equiv.sigmaFiberEquiv I).symm.trans
    ((Equiv.sigmaCongrRight τ).trans (Equiv.sigmaFiberEquiv I')), fun j => ?_⟩
  exact (τ (I j) ⟨j, rfl⟩).2

/-- Two decompositions of one persistence module into nonempty interval modules are matched
by a bijection of the index types that preserves supports. -/
theorem exists_equiv_support_of_iso_of_iso {M : PModule.{u,0,u} k ℝ}
    (I : J → Set ℝ) (hI : ∀ j, (I j).OrdConnected) (hne : ∀ j, (I j).Nonempty)
    (I' : J' → Set ℝ) (hI' : ∀ j, (I' j).OrdConnected) (hne' : ∀ j, (I' j).Nonempty)
    (e : M ≅ familyModule (fun j => module (k := k) (I j) (hI j)))
    (e' : M ≅ familyModule (fun j => module (k := k) (I' j) (hI' j))) :
    ∃ σ : J ≃ J', ∀ j, I' (σ j) = I j :=
  exists_equiv_support_of_iso I hI hne I' hI' hne' (e.symm.trans e')

end Intervals

end TDA.Persistence.AlgebraicFamily
