import TDA.Persistence.RankProjective
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks and composites of rank-exact deflations

The existing categorical pullback has the expected compatible pairs at
every grade. Principal-upset generators construct those elements and
prove that its projections distinguish them. These laws prove finite
dimensionality and the same-death lifting property for pullback quotients.
Composing two deflations lifts a dying vector successively through them.
The kernel criterion then supplies actual rank-exact kernel sequences.

These are the deflation-side closure laws from BOOS,
arXiv:2208.00300v3, §2.12, used in Appendix A's Lemma A.1. Persistent Schanuel
is proved in `TDA.Persistence.RankSchanuelResolution` and, without degree shifts,
in `TDA.Persistence.RankSchanuelUnshifted`; the kernel comparisons and the pushout
closure law are in `TDA.Persistence.RankExactKernel` and
`TDA.Persistence.RankExactPushout`. No `ExactCategory` instance is asserted.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

namespace PullbackFiber

section Ring

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]
    {M N T : PModule.{u,v,u} R P} (π : M ⟶ N) (f : T ⟶ N)

private theorem fromBirth_condition (p : P) (m : M.obj p) (t : T.obj p)
    (h : (π.app p).hom m = (f.app p).hom t) :
    HookInfinity.fromBirth p M m ≫ π = HookInfinity.fromBirth p T t ≫ f := by
  apply HookInfinity.hom_ext
  change (π.app p).hom (((HookInfinity.fromBirth p M m).app p).hom _) =
    (f.app p).hom (((HookInfinity.fromBirth p T t).app p).hom _)
  simpa only [HookInfinity.fromBirth_birth] using h

/-- A compatible pair is an element of the actual categorical pullback fiber. -/
noncomputable def mk (p : P) (m : M.obj p) (t : T.obj p)
    (h : (π.app p).hom m = (f.app p).hom t) : (pullback π f).obj p :=
  ((pullback.lift (HookInfinity.fromBirth p M m) (HookInfinity.fromBirth p T t)
    (fromBirth_condition π f p m t h)).app p).hom (HookInfinity.birth p)

/-- The first projection reads the first entry of the compatible pair. -/
@[simp] theorem fst_mk (p : P) (m : M.obj p) (t : T.obj p)
    (h : (π.app p).hom m = (f.app p).hom t) :
    ((pullback.fst π f).app p).hom (mk π f p m t h) = m := by
  have he := congrArg (fun α : HookInfinity.module (R := R) p ⟶ M =>
    (α.app p).hom (HookInfinity.birth p))
      (pullback.lift_fst (HookInfinity.fromBirth p M m)
        (HookInfinity.fromBirth p T t) (fromBirth_condition π f p m t h))
  exact he.trans (HookInfinity.fromBirth_birth p M m)

/-- The second projection reads the second entry of the compatible pair. -/
@[simp] theorem snd_mk (p : P) (m : M.obj p) (t : T.obj p)
    (h : (π.app p).hom m = (f.app p).hom t) :
    ((pullback.snd π f).app p).hom (mk π f p m t h) = t := by
  have he := congrArg (fun α : HookInfinity.module (R := R) p ⟶ T =>
    (α.app p).hom (HookInfinity.birth p))
      (pullback.lift_snd (HookInfinity.fromBirth p M m)
        (HookInfinity.fromBirth p T t) (fromBirth_condition π f p m t h))
  exact he.trans (HookInfinity.fromBirth_birth p T t)

/-- The two actual pullback projections distinguish vectors at every grade. -/
theorem element_ext (p : P) {x y : (pullback π f).obj p}
    (hfst : ((pullback.fst π f).app p).hom x = ((pullback.fst π f).app p).hom y)
    (hsnd : ((pullback.snd π f).app p).hom x = ((pullback.snd π f).app p).hom y) : x = y := by
  have h₁ : HookInfinity.fromBirth p (pullback π f) x ≫ pullback.fst π f =
      HookInfinity.fromBirth p (pullback π f) y ≫ pullback.fst π f := by
    apply HookInfinity.hom_ext
    change ((pullback.fst π f).app p).hom
        (((HookInfinity.fromBirth p (pullback π f) x).app p).hom _) =
      ((pullback.fst π f).app p).hom
        (((HookInfinity.fromBirth p (pullback π f) y).app p).hom _)
    simpa only [HookInfinity.fromBirth_birth] using hfst
  have h₂ : HookInfinity.fromBirth p (pullback π f) x ≫ pullback.snd π f =
      HookInfinity.fromBirth p (pullback π f) y ≫ pullback.snd π f := by
    apply HookInfinity.hom_ext
    change ((pullback.snd π f).app p).hom
        (((HookInfinity.fromBirth p (pullback π f) x).app p).hom _) =
      ((pullback.snd π f).app p).hom
        (((HookInfinity.fromBirth p (pullback π f) y).app p).hom _)
    simpa only [HookInfinity.fromBirth_birth] using hsnd
  have he := pullback.hom_ext h₁ h₂
  simpa only [HookInfinity.fromBirth_birth] using congrArg
    (fun α : HookInfinity.module (R := R) p ⟶ pullback π f =>
      (α.app p).hom (HookInfinity.birth p)) he

/-- The pair with two zero entries is the zero vector. -/
@[simp] theorem mk_zero (p : P) :
    mk π f p 0 0 (by simp) = 0 := by
  apply element_ext π f p <;> simp

variable {V : Type u} [AddCommGroup V] [Module R V]

/-- Compatible linear maps give a linear map into the actual pullback fiber. -/
noncomputable def liftLinear (p : P) (a : V →ₗ[R] M.obj p) (b : V →ₗ[R] T.obj p)
    (h : ∀ x, (π.app p).hom (a x) = (f.app p).hom (b x)) :
    V →ₗ[R] (pullback π f).obj p where
  toFun x := mk π f p (a x) (b x) (h x)
  map_add' x y := by
    apply element_ext π f p
    · simp only [fst_mk, map_add]
    · simp only [snd_mk, map_add]
  map_smul' c x := by
    apply element_ext π f p
    · simp only [fst_mk, map_smul, RingHom.id_apply]
    · simp only [snd_mk, map_smul, RingHom.id_apply]

/-- The first projection of a linear pullback lift is the given first map. -/
@[simp] theorem fst_liftLinear (p : P) (a : V →ₗ[R] M.obj p) (b : V →ₗ[R] T.obj p)
    (h : ∀ x, (π.app p).hom (a x) = (f.app p).hom (b x)) (x : V) :
    ((pullback.fst π f).app p).hom (liftLinear π f p a b h x) = a x :=
  fst_mk π f p (a x) (b x) (h x)

/-- The second projection of a linear pullback lift is the given second map. -/
@[simp] theorem snd_liftLinear (p : P) (a : V →ₗ[R] M.obj p) (b : V →ₗ[R] T.obj p)
    (h : ∀ x, (π.app p).hom (a x) = (f.app p).hom (b x)) (x : V) :
    ((pullback.snd π f).app p).hom (liftLinear π f p a b h x) = b x :=
  snd_mk π f p (a x) (b x) (h x)

end Ring

section Field

variable {k : Type u} [Field k] {P : Type v} [Preorder P]
    {M N T : PModule.{u,v,u} k P} (π : M ⟶ N) (f : T ⟶ N)

/-- The pullback fiber embeds linearly in the product of its two source fibers. -/
theorem finiteDimensional (p : P) [FiniteDimensional k (M.obj p)]
    [FiniteDimensional k (T.obj p)] : FiniteDimensional k ((pullback π f).obj p) := by
  let F := ((pullback.fst π f).app p).hom.prod ((pullback.snd π f).app p).hom
  apply FiniteDimensional.of_injective F
  intro x y h
  exact element_ext π f p (congrArg Prod.fst h) (congrArg Prod.snd h)

end Field

end PullbackFiber

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
    {M N T O : PModule.{u,0,u} k P}

/-- A rank-exact deflation occurs as the quotient of an actual rank-exact sequence. -/
def IsRankDeflation (π : M ⟶ N) : Prop :=
  ∃ (L : PModule.{u,0,u} k P) (ι : L ⟶ M), IsRankExact ι π

/-- An actual rank-exact sequence gives a deflation. -/
theorem IsRankExact.isRankDeflation {L : PModule.{u,0,u} k P}
    {ι : L ⟶ M} {π : M ⟶ N} (h : IsRankExact ι π) : IsRankDeflation π :=
  ⟨L, ι, h⟩

namespace IsRankDeflation

/-- Every rank deflation has its actual categorical rank-exact kernel sequence. -/
theorem rankExact_kernel {π : M ⟶ N} (h : IsRankDeflation π) :
    IsRankExact (kernel.ι π) π := by
  obtain ⟨L, ι, hs⟩ := h
  let : ∀ p, FiniteDimensional k (M.obj p) := hs.finiteDimensional
  exact RankKernel.rankExact π hs.surjective hs.lift_kernel

/-- Identity on a pfd module is a rank-exact deflation. -/
theorem id (M : PModule.{u,0,u} k P) [∀ p, FiniteDimensional k (M.obj p)] :
    IsRankDeflation (𝟙 M) := by
  apply IsRankExact.isRankDeflation (ι := kernel.ι (𝟙 M))
  apply RankKernel.rankExact
  · intro p
    exact Function.surjective_id
  · intro a b hab n hn
    exact ⟨n, rfl, hn⟩

/-- Successive same-death lifts prove closure under composition. -/
theorem comp {π : M ⟶ N} {σ : N ⟶ O}
    (hπ : IsRankDeflation π) (hσ : IsRankDeflation σ) : IsRankDeflation (π ≫ σ) := by
  obtain ⟨L, ι, hπ⟩ := hπ
  obtain ⟨K, κ, hσ⟩ := hσ
  let : ∀ p, FiniteDimensional k (M.obj p) := hπ.finiteDimensional
  apply IsRankExact.isRankDeflation (ι := kernel.ι (π ≫ σ))
  apply RankKernel.rankExact
  · intro p
    exact (hσ.surjective p).comp (hπ.surjective p)
  · intro a b hab n hn
    obtain ⟨m, hm, hmdie⟩ := hσ.lift_kernel hab n hn
    obtain ⟨l, hl, hldie⟩ := hπ.lift_kernel hab m hmdie
    refine ⟨l, ?_, hldie⟩
    change (σ.app a).hom ((π.app a).hom l) = n
    rw [hl, hm]

/-- Pullback along any map from a pfd module preserves rank-exact deflations.
The source is the actual categorical pullback; no lifting or rank equality is assumed. -/
theorem pullback_snd {π : M ⟶ N} (hπ : IsRankDeflation π) (f : T ⟶ N)
    [∀ p, FiniteDimensional k (T.obj p)] : IsRankDeflation (pullback.snd π f) := by
  obtain ⟨L, ι, hs⟩ := hπ
  let : ∀ p, FiniteDimensional k (M.obj p) := hs.finiteDimensional
  let : ∀ p, FiniteDimensional k ((pullback π f).obj p) :=
    fun p => PullbackFiber.finiteDimensional π f p
  apply IsRankExact.isRankDeflation (ι := kernel.ι (pullback.snd π f))
  apply RankKernel.rankExact
  · intro p n
    obtain ⟨m, hm⟩ := hs.surjective p ((f.app p).hom n)
    exact ⟨PullbackFiber.mk π f p m n hm, PullbackFiber.snd_mk π f p m n hm⟩
  · intro a b hab n hn
    have hfn : structureMapLinear N hab ((f.app a).hom n) = 0 := by
      have h := congrArg (fun α => α.hom n) (f.naturality (homOfLE hab))
      change (f.app b).hom (structureMapLinear T hab n) =
        structureMapLinear N hab ((f.app a).hom n) at h
      exact h.symm.trans (by rw [hn, map_zero])
    obtain ⟨m, hm, hmdie⟩ := hs.lift_kernel hab ((f.app a).hom n) hfn
    let x := PullbackFiber.mk π f a m n hm
    refine ⟨x, PullbackFiber.snd_mk π f a m n hm, ?_⟩
    apply PullbackFiber.element_ext π f b
    · have h := congrArg (fun α => α.hom x)
        ((pullback.fst π f).naturality (homOfLE hab))
      change ((pullback.fst π f).app b).hom
          (structureMapLinear (pullback π f) hab x) =
        structureMapLinear M hab (((pullback.fst π f).app a).hom x) at h
      rw [h]
      change structureMapLinear M hab
        (((pullback.fst π f).app a).hom (PullbackFiber.mk π f a m n hm)) = _
      rw [PullbackFiber.fst_mk, hmdie, map_zero]
    · have h := congrArg (fun α => α.hom x)
        ((pullback.snd π f).naturality (homOfLE hab))
      change ((pullback.snd π f).app b).hom
          (structureMapLinear (pullback π f) hab x) =
        structureMapLinear T hab (((pullback.snd π f).app a).hom x) at h
      rw [h]
      change structureMapLinear T hab
        (((pullback.snd π f).app a).hom (PullbackFiber.mk π f a m n hm)) = _
      rw [PullbackFiber.snd_mk, hn, map_zero]

end IsRankDeflation

end TDA.Persistence
