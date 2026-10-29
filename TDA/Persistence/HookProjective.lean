import TDA.Persistence.SupportInterval
import TDA.Persistence.RankExact
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Hook morphisms and lifting along rank exact sequences

For grades `i < j` in a partial order, the hook has support `{a | i ≤ a ∧ ¬ j ≤ a}`.
A morphism from this hook to a persistence module is determined by a vector at `i` killed
by the structure map to `j`. For pointwise finite-dimensional middle modules,
rank exactness permits lifting that vector while retaining its vanishing relation,
which constructs a lift of the entire hook morphism.

This proves the lifting property for hooks with a finite death grade, using the kernel
criterion in `RankExact`. Principal upsets are treated in `HookInfinity`; the finite-poset
classification for pointwise finite-dimensional modules is in
`FiniteRankProjectiveClassification`. Exact-category axioms and classification beyond
that finite setting remain separate. Hook supports here may be unbounded. See Botnan,
Oppermann, Oudot and Scoccola, arXiv:2208.00300v3, Section 2.14 and Theorem 2.7.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.Hook

open CategoryTheory

variable {k : Type u} [Field k] {P : Type v} [PartialOrder P]

/-- A hook contains the points above its birth and outside the upset of its death. -/
abbrev support (i j : P) : Set P := {a | i ≤ a ∧ ¬ j ≤ a}

/-- Hook supports are order convex. -/
theorem support_ordConnected (i j : P) : (support i j).OrdConnected where
  out' := by
    intro a ha c hc b hb
    exact ⟨ha.1.trans hb.1, fun hj => hc.2 (hj.trans hb.2)⟩

/-- The interval module on a hook support. -/
@[reducible]
noncomputable def module (i j : P) : PModule.{u,v,u} k P :=
  SupportInterval.module (support i j) (support_ordConnected i j)

/-- The birth grade belongs to every nonzero hook. -/
theorem birth_mem {i j : P} (hij : i < j) : i ∈ support i j :=
  ⟨le_rfl, not_le_of_gt hij⟩

/-- A hook excludes its death grade. -/
theorem death_not_mem (i j : P) : j ∉ support i j := fun h => h.2 le_rfl

/-- The value on the unit at birth determines a morphism from a nonzero hook. -/
theorem hom_ext {i j : P} (hij : i < j) {M : PModule.{u,v,u} k P}
    {α β : module (k := k) i j ⟶ M}
    (h : (α.app i).hom (SupportInterval.one (support i j) (birth_mem hij)) =
      (β.app i).hom (SupportInterval.one (support i j) (birth_mem hij))) : α = β := by
  classical
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases hp : p ∈ support i j
  · have hg : structureMapLinear (module (k := k) i j) hp.1
        (SupportInterval.one (support i j) (birth_mem hij)) =
          SupportInterval.one (support i j) hp := by
      apply Subtype.ext
      exact (SupportInterval.structureMap_val (support i j) (support_ordConnected i j)
        hp.1 (SupportInterval.one (support i j) (birth_mem hij))).trans (by
          simp [hp, SupportInterval.one])
    have hx : x = (x : k) • structureMapLinear (module i j) hp.1
        (SupportInterval.one (support i j) (birth_mem hij)) := by
      rw [hg]
      apply Subtype.ext
      simp [SupportInterval.one]
    have hα := congrArg (fun f => f.hom
      (SupportInterval.one (support i j) (birth_mem hij)))
        (α.naturality (homOfLE hp.1))
    have hβ := congrArg (fun f => f.hom
      (SupportInterval.one (support i j) (birth_mem hij)))
        (β.naturality (homOfLE hp.1))
    change (α.app p).hom (structureMapLinear (module i j) hp.1 _) =
      structureMapLinear M hp.1 ((α.app i).hom _) at hα
    change (β.app p).hom (structureMapLinear (module i j) hp.1 _) =
      structureMapLinear M hp.1 ((β.app i).hom _) at hβ
    rw [hx, map_smul, map_smul, hα, hβ, h]
  · have hx : x = 0 := Subtype.ext (SupportInterval.val_eq_zero (support i j) hp x)
    simp [hx]

/-- The generating element of a hook morphism dies at the hook's death grade. -/
theorem generator_dies {i j : P} (hij : i < j) {M : PModule.{u,v,u} k P}
    (α : module (k := k) i j ⟶ M) :
    structureMapLinear M hij.le
      ((α.app i).hom (SupportInterval.one (support i j) (birth_mem hij))) = 0 := by
  have hn := congrArg (fun f => f.hom
    (SupportInterval.one (support i j) (birth_mem hij)))
      (α.naturality (homOfLE hij.le))
  have hz : structureMapLinear (module (k := k) i j) hij.le = 0 :=
    (SupportInterval.structureMap_eq_zero_iff (support i j)
      (support_ordConnected i j) hij.le).mpr
      (fun h => death_not_mem i j h.2)
  change (α.app j).hom (structureMapLinear (module i j) hij.le _) = _ at hn
  rw [hz, LinearMap.zero_apply, map_zero] at hn
  exact hn.symm

private noncomputable def generatorLinear {i j : P} (M : PModule.{u,v,u} k P)
    (m : M.obj i) (p : P) : SupportInterval.fiber (k := k) (support i j) p →ₗ[k] M.obj p := by
  classical
  exact if hp : i ≤ p then
    (LinearMap.toSpanSingleton k (M.obj p) (structureMapLinear M hp m)).comp
      (SupportInterval.fiber (k := k) (support i j) p).subtype else 0

/-- A vector killed at the death grade defines a morphism out of the hook. -/
noncomputable def fromGenerator {i j : P} (hij : i < j) (M : PModule.{u,v,u} k P)
    (m : M.obj i) (hm : structureMapLinear M hij.le m = 0) : module i j ⟶ M where
  app p := ModuleCat.ofHom (generatorLinear M m p)
  naturality {p q} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change generatorLinear M m q (structureMapLinear (module i j) (leOfHom f) x) =
      structureMapLinear M (leOfHom f) (generatorLinear M m p x)
    by_cases hp : i ≤ p
    · have hq := hp.trans (leOfHom f)
      simp only [generatorLinear, dif_pos hp, dif_pos hq, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, map_smul]
      have hcomp : structureMapLinear M (leOfHom f) (structureMapLinear M hp m) =
          structureMapLinear M hq m := by
        exact (congrArg (fun g => g m)
          (structureMapLinear_comp M hp (leOfHom f))).symm
      rw [hcomp]
      change ((structureMapLinear (SupportInterval.module (support i j)
        (support_ordConnected i j)) (leOfHom f) x) : k) • structureMapLinear M hq m =
          (x : k) • structureMapLinear M hq m
      rw [SupportInterval.structureMap_val]
      by_cases hqs : q ∈ support i j
      · simp [hqs]
      · have hjq : j ≤ q := by
          by_contra hjq
          exact hqs ⟨hq, hjq⟩
        have hz : structureMapLinear M hq m = 0 := by
          rw [structureMapLinear_comp M hij.le hjq]
          simp [hm]
        simp [hqs, hz]
    · have hps : p ∉ support i j := fun h => hp h.1
      have hx : x = 0 := Subtype.ext (SupportInterval.val_eq_zero (support i j) hps x)
      simp [hx]

/-- The component of a generated morphism transports and scales its birth vector. -/
theorem fromGenerator_app {i j p : P} (hij : i < j) (M : PModule.{u,v,u} k P)
    (m : M.obj i) (hm : structureMapLinear M hij.le m = 0) (hip : i ≤ p)
    (x : SupportInterval.fiber (k := k) (support i j) p) :
    ((fromGenerator hij M m hm).app p).hom x = (x : k) • structureMapLinear M hip m := by
  classical
  change generatorLinear M m p x = _
  simp [generatorLinear, hip, LinearMap.toSpanSingleton_apply]

/-- The morphism built from a generator takes the unit at birth to that generator. -/
theorem fromGenerator_birth {i j : P} (hij : i < j) (M : PModule.{u,v,u} k P)
    (m : M.obj i) (hm : structureMapLinear M hij.le m = 0) :
    ((fromGenerator hij M m hm).app i).hom
      (SupportInterval.one (support i j) (birth_mem hij)) = m := by
  classical
  change generatorLinear M m i (SupportInterval.one (support i j) (birth_mem hij)) = m
  simp only [generatorLinear, dif_pos (le_refl i), LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]
  change (1 : k) • structureMapLinear M (le_refl i) m = m
  simp

/-- Morphisms from a nonzero hook correspond to vectors killed between its endpoints. -/
noncomputable def homEquivKernel {i j : P} (hij : i < j) (M : PModule.{u,v,u} k P) :
    (module (k := k) i j ⟶ M) ≃ LinearMap.ker (structureMapLinear M hij.le) where
  toFun α := ⟨(α.app i).hom (SupportInterval.one (support i j) (birth_mem hij)),
    generator_dies hij α⟩
  invFun x := fromGenerator hij M x.val x.property
  left_inv _α := hom_ext hij (fromGenerator_birth hij M _ _)
  right_inv _x := Subtype.ext (fromGenerator_birth hij M _ _)

/-- Hooks lift against rank exact quotient maps. The lift is obtained by lifting its
birth generator while preserving the death relation. -/
theorem exists_lift {i j : P} (hij : i < j)
    {L M N : PModule.{u,v,u} k P} {ι : L ⟶ M} {π : M ⟶ N}
    (hs : IsRankExact ι π)
    (α : module (k := k) i j ⟶ N) :
    ∃ β : module (k := k) i j ⟶ M, β ≫ π = α := by
  obtain ⟨m, hm, hdie⟩ := hs.lift_kernel hij.le
    ((α.app i).hom (SupportInterval.one (support i j) (birth_mem hij)))
    (generator_dies hij α)
  refine ⟨fromGenerator hij M m hdie, ?_⟩
  apply hom_ext hij
  change (π.app i).hom (((fromGenerator hij M m hdie).app i).hom _) = _
  rw [fromGenerator_birth]
  exact hm

end TDA.Persistence.Hook
