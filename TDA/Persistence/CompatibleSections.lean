import TDA.Persistence.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.CategoryTheory.Limits.Types.Images
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Rat.Encodable

/-!
# Compatible sections over real subsets

A compatible section assigns a vector to each index and commutes with every forward
structure map. Surjective transition maps on a real subset give surjective evaluation
maps. The proof restricts to a decreasing countable coinitial sequence, uses the
surjective inverse-limit theorem for types, and extends the resulting section to all
indices. No finiteness assumption on the field or the underlying fibers is needed.
-/

universe u v w

namespace TDA.Persistence.CompatibleSections

open CategoryTheory CategoryTheory.Limits

/-- Every nonempty real subset has a decreasing coinitial sequence starting at any
specified member. A minimum is handled by an eventually constant sequence; otherwise
rational density supplies countably many points approaching every left end. -/
theorem exists_antitone_coinitial (I : Set ℝ) (t : I) :
    ∃ a : ℕ → I, a 0 = t ∧ Antitone a ∧ ∀ s : I, ∃ n, a n ≤ s := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat ℚ
  by_cases hmin : ∃ m : I, ∀ s : I, m ≤ s
  · obtain ⟨m, hm⟩ := hmin
    refine ⟨fun n => if n = 0 then t else m, by simp, ?_, ?_⟩
    · intro i j hij
      by_cases hj : j = 0
      · subst j
        have : i = 0 := Nat.eq_zero_of_le_zero hij
        subst i
        exact le_rfl
      · simp only [hj, ↓reduceIte]
        split_ifs <;> exact hm _
    · intro s
      exact ⟨1, hm s⟩
  · have hleft (s : I) : ∃ r : I, r < s := by
      by_contra hn
      apply hmin
      refine ⟨s, fun r => ?_⟩
      exact le_of_not_gt (fun hrs => hn ⟨r, hrs⟩)
    let b : ℕ → I := fun n =>
      if h : ∃ s : I, (s : ℝ) < e n then h.choose else t
    let a : ℕ → I := Nat.rec t (fun n p => min p (b n))
    have ha0 : a 0 = t := rfl
    have hasucc (n : ℕ) : a (n + 1) = min (a n) (b n) := rfl
    refine ⟨a, ha0, antitone_nat_of_succ_le (fun n => ?_), ?_⟩
    · rw [hasucc]
      exact min_le_left _ _
    · intro s
      obtain ⟨r, hrs⟩ := hleft s
      obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn (show (r : ℝ) < s from hrs)
      obtain ⟨n, hn⟩ := he q
      have hb : (b n : ℝ) < q := by
        have h : ∃ r : I, (r : ℝ) < e n := ⟨r, by simpa [hn] using hrq⟩
        simp only [b, dif_pos h]
        simpa [hn] using h.choose_spec
      refine ⟨n + 1, ?_⟩
      exact (min_le_right (a n) (b n)).trans (le_of_lt (show b n < s from hb.trans hqs))

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- The module of families commuting with all structure maps. -/
def sections (M : PModule.{u,v,w} R P) : Submodule R (∀ t, M.obj t) where
  carrier := {x | ∀ s t (h : s ≤ t), structureMapLinear M h (x s) = x t}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy s t h
    simp only [Pi.add_apply, map_add, hx s t h, hy s t h]
  smul_mem' := by
    intro r x hx s t h
    simp only [Pi.smul_apply, map_smul, hx s t h]

/-- A compatible section agrees with each forward structure map. -/
theorem compatible (M : PModule.{u,v,w} R P) (x : sections M)
    {s t : P} (h : s ≤ t) : structureMapLinear M h (x.val s) = x.val t :=
  x.property s t h

/-- Evaluation of a compatible section at one index. -/
def evaluation (M : PModule.{u,v,w} R P) (t : P) : sections M →ₗ[R] M.obj t where
  toFun x := x.val t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation returns the corresponding component of a section. -/
@[simp] theorem evaluation_apply (M : PModule.{u,v,w} R P) (t : P) (x : sections M) :
    evaluation M t x = x.val t := rfl

/-- The sections vanishing at one index form a submodule. -/
def vanishingAt (M : PModule.{u,v,w} R P) (t : P) : Submodule R (sections M) :=
  (evaluation M t).ker

/-- The evaluation kernel consists exactly of sections with zero value at that index. -/
@[simp] theorem mem_vanishingAt (M : PModule.{u,v,w} R P) (t : P) (x : sections M) :
    x ∈ vanishingAt M t ↔ x.val t = 0 := Iff.rfl

section Coinitial

variable (M : PModule.{u,v,w} R P)
    (a : ℕ → P) (ha : Antitone a)

/-- Compatible vectors on a decreasing countable sequence of indices. -/
def sequenceSections : Submodule R (∀ n, M.obj (a n)) where
  carrier := {x | ∀ i j (h : i ≤ j), structureMapLinear M (ha h) (x j) = x i}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i j h
    simp only [Pi.add_apply, map_add, hx i j h, hy i j h]
  smul_mem' := by
    intro r x hx i j h
    simp only [Pi.smul_apply, map_smul, hx i j h]

private def sequenceFunctor : ℕᵒᵖ ⥤ Type w where
  obj n := M.obj (a n.unop)
  map f := ↾fun x => structureMapLinear M (ha (leOfHom f.unop)) x
  map_id n := by
    ext x
    simp
  map_comp f g := by
    ext x
    exact LinearMap.congr_fun (structureMapLinear_comp M
      (ha (leOfHom f.unop)) (ha (leOfHom g.unop))) x

/-- Surjective forward structure maps give a compatible vector sequence through an
arbitrary vector at the first index, using the countable surjective-limit theorem. -/
theorem exists_sequenceSection
    (hsurj : ∀ s t (h : s ≤ t), Function.Surjective (structureMapLinear M h))
    (y : M.obj (a 0)) :
    ∃ x : sequenceSections M a ha, x.val 0 = y := by
  let F := sequenceFunctor M a ha
  have hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op) :=
    fun n => hsurj _ _ _
  obtain ⟨x, hx⟩ := Types.surjective_π_app_zero_of_surjective_map
    (Types.limitConeIsLimit F) hF y
  refine ⟨⟨fun n => x.val (Opposite.op n), ?_⟩, hx⟩
  intro i j h
  exact x.property (homOfLE h).op

private theorem transported_value_eq (x : sequenceSections M a ha)
    {s : P} {i j : ℕ} (hi : a i ≤ s) (hj : a j ≤ s) :
    structureMapLinear M hi (x.val i) = structureMapLinear M hj (x.val j) := by
  have hi' := x.property i (max i j) (le_max_left i j)
  have hj' := x.property j (max i j) (le_max_right i j)
  rw [← hi', ← hj']
  rw [← LinearMap.comp_apply, ← structureMapLinear_comp,
    ← LinearMap.comp_apply, ← structureMapLinear_comp]

variable (hcoin : ∀ s : P, ∃ n, a n ≤ s)

private noncomputable def extensionValue (x : sequenceSections M a ha) (s : P) : M.obj s :=
  structureMapLinear M (hcoin s).choose_spec (x.val (hcoin s).choose)

private theorem extensionValue_eq (x : sequenceSections M a ha) {s : P}
    {n : ℕ} (hn : a n ≤ s) :
    extensionValue M a ha hcoin x s = structureMapLinear M hn (x.val n) :=
  transported_value_eq M a ha x (hcoin s).choose_spec hn

/-- Extend a compatible sequence along a coinitial decreasing sequence. The value at
any index is the forward image of any sequence term below it; compatibility makes
this independent of the chosen term. -/
noncomputable def extend : sequenceSections M a ha →ₗ[R] sections M where
  toFun x := ⟨extensionValue M a ha hcoin x, by
    intro s t hst
    rw [extensionValue_eq M a ha hcoin x
      ((hcoin s).choose_spec.trans hst)]
    unfold extensionValue
    rw [← LinearMap.comp_apply, ← structureMapLinear_comp]⟩
  map_add' x y := by
    apply Subtype.ext
    funext s
    exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    funext s
    exact map_smul _ _ _

/-- The extension can be evaluated using any sequence index below the target. -/
theorem extend_apply (x : sequenceSections M a ha) {s : P} {n : ℕ} (hn : a n ≤ s) :
    (extend M a ha hcoin x).val s = structureMapLinear M hn (x.val n) :=
  extensionValue_eq M a ha hcoin x hn

/-- Extending a compatible sequence preserves every sequence value. -/
@[simp] theorem extend_at_sequence (x : sequenceSections M a ha) (n : ℕ) :
    (extend M a ha hcoin x).val (a n) = x.val n := by
  rw [extend_apply M a ha hcoin x (le_refl (a n))]
  simp

include ha hcoin in
/-- A countable decreasing coinitial sequence turns surjective structure maps into
surjective evaluation on the full compatible-section space. -/
theorem evaluation_surjective_of_coinitial
    (hsurj : ∀ s t (h : s ≤ t), Function.Surjective (structureMapLinear M h)) :
    Function.Surjective (evaluation M (a 0)) := by
  intro y
  obtain ⟨x, hx⟩ := exists_sequenceSection M a ha hsurj y
  refine ⟨extend M a ha hcoin x, ?_⟩
  change (extend M a ha hcoin x).val (a 0) = y
  rw [extend_at_sequence, hx]

end Coinitial

/-- On any real subset, surjective structure maps give a compatible section through
any prescribed vector. This includes singleton sets and unbounded or open intervals. -/
theorem evaluation_surjective_real {I : Set ℝ} (M : PModule.{u,0,w} R I)
    (hsurj : ∀ s t (h : s ≤ t), Function.Surjective (structureMapLinear M h)) (t : I) :
    Function.Surjective (evaluation M t) := by
  obtain ⟨a, ha0, ha, hcoin⟩ := exists_antitone_coinitial I t
  rw [← ha0]
  exact evaluation_surjective_of_coinitial M a ha hcoin hsurj

section Subspaces

variable (M : PModule.{u,v,w} R P) (I : Set P)
    (S : ∀ t : I, Submodule R (M.obj t.val))
    (hS : ∀ s t : I, ∀ (h : s ≤ t) (x : M.obj s.val),
      x ∈ S s → structureMapLinear M h x ∈ S t)

/-- Restriction of a structure map to preserved subspaces. -/
def subspaceMap {s t : I} (h : s ≤ t) : S s →ₗ[R] S t where
  toFun x := ⟨structureMapLinear M h x.val, hS s t h x.val x.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-- Preserved subspaces on a subset form a persistence module. -/
def subspaceModule : PModule.{u,v,w} R I where
  obj t := ModuleCat.of R (S t)
  map f := ModuleCat.ofHom (subspaceMap M I S hS (leOfHom f))
  map_id t := by
    ext x
    exact LinearMap.congr_fun (structureMapLinear_self M (le_refl t.val)) x.val
  map_comp f g := by
    ext x
    exact LinearMap.congr_fun (structureMapLinear_comp M (leOfHom f) (leOfHom g)) x.val

/-- The restricted module's structure map is the restricted linear map. -/
@[simp] theorem structureMapLinear_subspaceModule {s t : I} (h : s ≤ t) :
    structureMapLinear (subspaceModule M I S hS) h = subspaceMap M I S hS h := rfl

end Subspaces

/-- A surjective system of preserved subspaces over a real subset admits compatible
lifts through every prescribed vector. The inputs are preservation and ordinary
pairwise preimages, rather than a supplied coherent family. -/
theorem exists_compatible_lift_real (M : PModule.{u,0,w} R ℝ) (I : Set ℝ)
    (S : ∀ t : I, Submodule R (M.obj t.val))
    (hS : ∀ s t : I, ∀ (h : s ≤ t) (x : M.obj s.val),
      x ∈ S s → structureMapLinear M h x ∈ S t)
    (hsurj : ∀ s t : I, ∀ (h : s ≤ t) (y : M.obj t.val),
      y ∈ S t → ∃ x ∈ S s, structureMapLinear M h x = y)
    (t : I) (y : M.obj t.val) (hy : y ∈ S t) :
    ∃ x : ∀ s : I, M.obj s.val, x t = y ∧ (∀ s, x s ∈ S s) ∧
      ∀ s t : I, ∀ h : s ≤ t, structureMapLinear M h (x s) = x t := by
  have hsurj' : ∀ s t : I, ∀ h : s ≤ t,
      Function.Surjective (structureMapLinear (subspaceModule M I S hS) h) := by
    intro s t h y
    obtain ⟨x, hx, hxy⟩ := hsurj s t h y.val y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨x, hx⟩ := evaluation_surjective_real (subspaceModule M I S hS) hsurj' t ⟨y, hy⟩
  refine ⟨fun s => (x.val s).val, congrArg Subtype.val hx, fun s => (x.val s).property, ?_⟩
  intro s t h
  exact congrArg Subtype.val (compatible (subspaceModule M I S hS) x h)

section Quotient

variable (M : PModule.{u,v,w} R P) (t : P) (Q : Submodule R (M.obj t))

/-- Evaluate a compatible section modulo a specified subspace of the target fiber. -/
def quotientEvaluation : sections M →ₗ[R] (M.obj t ⧸ Q) :=
  Q.mkQ.comp (evaluation M t)

/-- The kernel of quotient evaluation is the inverse image of the target subspace. -/
theorem ker_quotientEvaluation :
    (quotientEvaluation M t Q).ker = Q.comap (evaluation M t) := by
  ext x
  change (Submodule.Quotient.mk (x.val t) : M.obj t ⧸ Q) = 0 ↔ x.val t ∈ Q
  exact Submodule.Quotient.mk_eq_zero Q

/-- Surjective evaluation remains surjective after passing to a target quotient. -/
theorem quotientEvaluation_surjective (he : Function.Surjective (evaluation M t)) :
    Function.Surjective (quotientEvaluation M t Q) :=
  Q.mkQ_surjective.comp he

end Quotient

end TDA.Persistence.CompatibleSections
