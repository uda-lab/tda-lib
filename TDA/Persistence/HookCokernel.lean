import TDA.Persistence.RankProjective
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Principal-upset quotients as hooks

The coefficient-preserving inclusion of the principal upset at `j` into the principal
upset at `i ≤ j` has cokernel the hook with endpoints `i,j`. The construction includes
equal endpoints, where both the hook and the cokernel vanish.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.HookCokernel

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]

/-- The coefficient-preserving inclusion of principal upsets. -/
noncomputable def inclusion {i j : P} (h : i ≤ j) :
    HookInfinity.module (R := k) j ⟶ HookInfinity.module (R := k) i :=
  HookInfinity.fromBirth j _
    (structureMapLinear (HookInfinity.module (R := k) i) h (HookInfinity.birth i))

/-- A hook with equal endpoints is the zero module. -/
theorem hook_isZero (i : P) : IsZero (Hook.module (k := k) i i) := by
  rw [Functor.isZero_iff]
  intro p
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro x y
  apply Subtype.ext
  have hp : p ∉ Hook.support i i := fun h => h.2 h.1
  exact (SupportInterval.val_eq_zero _ hp x).trans
    (SupportInterval.val_eq_zero _ hp y).symm

/-- The projection from the principal upset onto the finite-death hook. -/
noncomputable def projection (i j : P) :
    HookInfinity.module (R := k) i ⟶ Hook.module (k := k) i j := by
  classical
  exact if h : i ∈ Hook.support i j then HookInfinity.fromBirth i _
    (SupportInterval.one (Hook.support i j) h) else 0

/-- The hook projection has coefficient one on its birth generator when the endpoints differ. -/
@[simp] theorem projection_birth {i j : P} (h : i < j) :
    ((projection (k := k) i j).app i).hom (HookInfinity.birth i) =
      SupportInterval.one (Hook.support i j) (Hook.birth_mem h) := by
  unfold projection
  rw [dif_pos (Hook.birth_mem h)]
  exact HookInfinity.fromBirth_birth _ _ _

/-- The principal inclusion is killed by the hook projection, including equal endpoints. -/
@[reassoc (attr := simp)] theorem inclusion_projection {i j : P} (h : i ≤ j) :
    inclusion (k := k) h ≫ projection i j = 0 := by
  apply HookInfinity.hom_ext
  apply Subtype.ext
  exact SupportInterval.val_eq_zero _ (Hook.death_not_mem i j) _

private theorem dies {i j : P} (h : i ≤ j) {M : PModule.{u,0,u} k P}
    (φ : HookInfinity.module (R := k) i ⟶ M) (hφ : inclusion h ≫ φ = 0) :
    structureMapLinear M h ((φ.app i).hom (HookInfinity.birth i)) = 0 := by
  have hn := congrArg (fun t : (HookInfinity.module (R := k) i).obj i ⟶ M.obj j =>
    t.hom (HookInfinity.birth i)) (φ.naturality (homOfLE h))
  have hz := congrArg (fun t : HookInfinity.module (R := k) j ⟶ M =>
    (t.app j).hom (HookInfinity.birth j)) hφ
  simp only [NatTrans.comp_app, ModuleCat.comp_apply, inclusion,
    HookInfinity.fromBirth_birth, NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply] at hz
  exact hn.symm.trans hz

/-- A map killing the principal inclusion factors through the hook. -/
noncomputable def desc {i j : P} (h : i ≤ j) {M : PModule.{u,0,u} k P}
    (φ : HookInfinity.module (R := k) i ⟶ M) (hφ : inclusion h ≫ φ = 0) :
    Hook.module (k := k) i j ⟶ M := by
  classical
  exact if hij : i < j then
    Hook.fromGenerator hij M ((φ.app i).hom (HookInfinity.birth i)) (dies h φ hφ)
  else 0

/-- The hook factorization recovers the supplied principal-upset map. -/
@[reassoc (attr := simp)] theorem projection_desc {i j : P} (h : i ≤ j)
    {M : PModule.{u,0,u} k P} (φ : HookInfinity.module (R := k) i ⟶ M)
    (hφ : inclusion h ≫ φ = 0) :
    projection i j ≫ desc h φ hφ = φ := by
  classical
  by_cases hij : i < j
  · apply HookInfinity.hom_ext
    simp only [NatTrans.comp_app, ModuleCat.comp_apply, projection_birth hij]
    unfold desc
    rw [dif_pos hij]
    exact Hook.fromGenerator_birth hij _ _ _
  · have heq : i = j := eq_of_le_of_not_lt h hij
    subst j
    have hinc : inclusion (k := k) (le_rfl : i ≤ i) = 𝟙 _ := by
      apply HookInfinity.hom_ext
      simp [inclusion]
    have hzero : φ = 0 := by simpa [hinc] using hφ
    simp [desc, hzero]

/-- Maps out of a hook are determined after precomposition with its principal projection. -/
theorem hom_ext {i j : P} (h : i ≤ j) {M : PModule.{u,0,u} k P}
    {a b : Hook.module (k := k) i j ⟶ M}
    (hab : projection i j ≫ a = projection i j ≫ b) : a = b := by
  by_cases hij : i < j
  · apply Hook.hom_ext hij
    have he := congrArg (fun t : HookInfinity.module (R := k) i ⟶ M =>
      (t.app i).hom (HookInfinity.birth i)) hab
    simpa only [NatTrans.comp_app, ModuleCat.comp_apply, projection_birth hij] using he
  · have heq : i = j := eq_of_le_of_not_lt h hij
    subst j
    exact (hook_isZero (k := k) i).eq_of_src a b

/-- The finite-death hook satisfies the cokernel universal property. -/
noncomputable def isCokernel {i j : P} (h : i ≤ j) :
    IsColimit (CokernelCofork.ofπ (projection (k := k) i j) (inclusion_projection h)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun s hs => desc h s hs) (fun s hs => projection_desc h s hs)
    (fun s hs _m hm => hom_ext h (hm.trans (projection_desc h s hs).symm))

/-- The actual categorical cokernel is naturally the hook with the same endpoints. -/
noncomputable def iso {i j : P} (h : i ≤ j) :
    cokernel (inclusion (k := k) h) ≅ Hook.module (k := k) i j :=
  (cokernelIsCokernel (inclusion (k := k) h)).coconePointUniqueUpToIso
    (isCokernel (k := k) h)

/-- The canonical cokernel isomorphism identifies the actual projection with the hook projection. -/
@[reassoc (attr := simp)] theorem projection_iso {i j : P} (h : i ≤ j) :
    cokernel.π (inclusion (k := k) h) ≫ (iso (k := k) h).hom = projection i j := by
  exact (cokernelIsCokernel (inclusion (k := k) h)).comp_coconePointUniqueUpToIso_hom
    (isCokernel (k := k) h) WalkingParallelPair.one

/-- Hooks with weakly ordered endpoints are rank projective, including zero hooks. -/
theorem rankProjective {i j : P} (h : i ≤ j) :
    IsRankProjective (Hook.module (k := k) i j) := by
  by_cases hij : i < j
  · exact Hook.isRankProjective hij
  · have heq : i = j := eq_of_le_of_not_lt h hij
    subst j
    intro L M N ι π hs α
    exact ⟨0, (zero_comp).trans ((hook_isZero (k := k) i).eq_of_src 0 α)⟩

end TDA.Persistence.HookCokernel
