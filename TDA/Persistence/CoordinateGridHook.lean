import TDA.Persistence.CoordinateGridProjective
import TDA.Persistence.FiniteHookDeflation
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Hook modules under finite-grid left Kan extension

Finite-death hook fibers are compared through the canonical grid-floor
isomorphism. The coefficient comparison is the identity on the coefficient
ring, and the naturality proof uses the actual Kan transition maps.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence.CoordinateGrid

open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence

section Ring

variable {k : Type u} [Ring k] {n : ℕ} (G : CoordinateGrid n)

private theorem infinityFiber_subsingleton {P : Type v} [Preorder P]
    (i a : P) (hia : ¬ i ≤ a) :
    Subsingleton ((HookInfinity.module (R := k) i).obj a) := by
  constructor
  intro x y
  exact (HookInfinity.fiber_eq_zero_of_not_le hia x).trans
    (HookInfinity.fiber_eq_zero_of_not_le hia y).symm

private noncomputable def infinityFiberIso (i : G.Point) (a : Fin n → ℝ) :
    (G.lan.obj (HookInfinity.module (R := k) i)).obj a ≅
      (HookInfinity.module (R := k) (G.embedding i)).obj a := by
  classical
  by_cases ha : G.HasLowerPoint a
  · let p := G.floor a ha
    by_cases hi : G.embedding i ≤ a
    · have hip : i ≤ p := (G.le_floor_iff a ha i).mp hi
      exact (G.appIso (HookInfinity.module (R := k) i) a ha).trans
        ((HookInfinity.fiberEquivOfLe (R := k) hip).trans
          (HookInfinity.fiberEquivOfLe (R := k) hi).symm).toModuleIso
    · have hip : ¬ i ≤ p := by
        intro hip
        exact hi ((G.embedding.monotone hip).trans (G.floor_le a ha))
      letI : Subsingleton ((HookInfinity.module (R := k) i).obj p) :=
        infinityFiber_subsingleton (k := k) i p hip
      have hgrid : IsZero ((HookInfinity.module (R := k) i).obj p) :=
        ModuleCat.isZero_of_subsingleton _
      have hleft : IsZero ((G.lan.obj (HookInfinity.module (R := k) i)).obj a) :=
        hgrid.of_iso (G.appIso (HookInfinity.module (R := k) i) a ha)
      letI : Subsingleton
          ((HookInfinity.module (R := k) (G.embedding i)).obj a) :=
        infinityFiber_subsingleton (k := k) (G.embedding i) a hi
      exact hleft.iso (ModuleCat.isZero_of_subsingleton _)
  · have hleft : IsZero ((G.lan.obj (HookInfinity.module (R := k) i)).obj a) :=
      G.isZero_obj_of_not_hasLowerPoint _ a ha
    have hi : ¬ G.embedding i ≤ a := by
      intro hi
      exact ha ⟨i, hi⟩
    letI : Subsingleton
        ((HookInfinity.module (R := k) (G.embedding i)).obj a) :=
      infinityFiber_subsingleton (k := k) (G.embedding i) a hi
    exact hleft.iso (ModuleCat.isZero_of_subsingleton _)

private theorem infinityFiberIso_apply (i : G.Point) {a : Fin n → ℝ}
    (ha : G.HasLowerPoint a) (hia : G.embedding i ≤ a)
    (x : (G.lan.obj (HookInfinity.module (R := k) i)).obj a) :
    HookInfinity.fiberEquivOfLe (R := k) hia
        ((infinityFiberIso G i a).hom.hom x) =
      HookInfinity.fiberEquivOfLe (R := k) ((G.le_floor_iff a ha i).mp hia)
        ((G.appIso (HookInfinity.module (R := k) i) a ha).hom.hom x) := by
  simp [infinityFiberIso, ha, hia]

/-- The actual left Kan extension of an infinite-death hook is naturally
isomorphic to the principal upset born at the embedded grid point. -/
noncomputable def infinityLanIso (i : G.Point) :
    G.lan.obj (HookInfinity.module (R := k) i) ≅
      HookInfinity.module (R := k) (G.embedding i) := by
  classical
  refine NatIso.ofComponents (fun a => infinityFiberIso G i a) ?_
  intro a b hab
  let h : a ≤ b := leOfHom hab
  apply ModuleCat.hom_ext
  ext x
  by_cases hia : G.embedding i ≤ a
  · have hib : G.embedding i ≤ b := hia.trans h
    have ha : G.HasLowerPoint a := ⟨i, hia⟩
    have hb : G.HasLowerPoint b := ⟨i, hib⟩
    let hip := (G.le_floor_iff a ha i).mp hia
    let hiq := (G.le_floor_iff b hb i).mp hib
    let hpq : G.floor a ha ≤ G.floor b hb := G.floor_mono h ha hb
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    apply (HookInfinity.fiberEquivOfLe (R := k) hib).injective
    have hcoeffB := infinityFiberIso_apply G i hb hib
      (structureMapLinear (G.lan.obj (HookInfinity.module (R := k) i)) h x)
    have hcoeffA := infinityFiberIso_apply G i ha hia x
    calc
      _ = HookInfinity.fiberEquivOfLe (R := k) hiq
          ((G.appIso (HookInfinity.module (R := k) i) b hb).hom.hom
            (structureMapLinear (G.lan.obj (HookInfinity.module (R := k) i)) h x)) := hcoeffB
      _ = HookInfinity.fiberEquivOfLe (R := k) hiq
          (structureMapLinear (HookInfinity.module (R := k) i) hpq
            ((G.appIso (HookInfinity.module (R := k) i) a ha).hom.hom x)) := by
        rw [G.appIso_structureMap_apply (M := HookInfinity.module (R := k) i)
          h ha hb x]
      _ = HookInfinity.fiberEquivOfLe (R := k) hip
          ((G.appIso (HookInfinity.module (R := k) i) a ha).hom.hom x) := by
        rw [HookInfinity.fiberEquivOfLe_structureMap hip hpq]
      _ = HookInfinity.fiberEquivOfLe (R := k) hia
          ((infinityFiberIso G i a).hom.hom x) := hcoeffA.symm
      _ = HookInfinity.fiberEquivOfLe (R := k) hib
          (structureMapLinear
            (HookInfinity.module (R := k) (G.embedding i)) h
            ((infinityFiberIso G i a).hom.hom x)) := by
        rw [HookInfinity.fiberEquivOfLe_structureMap hia h]
  · haveI : Subsingleton
        ((HookInfinity.module (R := k) (G.embedding i)).obj a) :=
      infinityFiber_subsingleton (k := k) (G.embedding i) a hia
    have hx : (infinityFiberIso (k := k) G i a).hom.hom x = 0 :=
      Subsingleton.elim _ _
    have hinj : Function.Injective
        (infinityFiberIso (k := k) G i a).hom.hom :=
      (ModuleCat.mono_iff_injective
        (infinityFiberIso (k := k) G i a).hom).mp inferInstance
    have hx0 : x = 0 := hinj (by simpa using hx)
    simp [hx0]

/-- The principal-upset comparison preserves the actual generator coefficient
on every supported fiber. -/
theorem infinityLanIso_apply_coefficient (i : G.Point) {a : Fin n → ℝ}
    (ha : G.HasLowerPoint a) (hia : G.embedding i ≤ a)
    (x : (G.lan.obj (HookInfinity.module (R := k) i)).obj a) :
    HookInfinity.fiberEquivOfLe (R := k) hia
      (((G.infinityLanIso i).hom.app a).hom x) =
    HookInfinity.fiberEquivOfLe (R := k) ((G.le_floor_iff a ha i).mp hia)
      ((G.appIso (HookInfinity.module (R := k) i) a ha).hom.hom x) :=
  by simpa [infinityLanIso] using infinityFiberIso_apply G i ha hia x

end Ring

section Field

variable {k : Type u} [Field k] {n : ℕ} (G : CoordinateGrid n)

private theorem supportFiber_subsingleton {P : Type v} [Preorder P]
    (S : Set P) (a : P)
    (ha : a ∉ S) : Subsingleton (SupportInterval.fiber (k := k) S a) := by
  constructor
  intro x y
  apply Subtype.ext
  have hx : (x : k) = 0 := SupportInterval.val_eq_zero S ha x
  have hy : (y : k) = 0 := SupportInterval.val_eq_zero S ha y
  exact hx.trans hy.symm

private theorem hookSupport_floor_iff (i d : G.Point) {a : Fin n → ℝ}
    (ha : G.HasLowerPoint a) :
    Hook.support i d (G.floor a ha) ↔
      Hook.support (G.embedding i) (G.embedding d) a := by
  change (i ≤ G.floor a ha ∧ ¬ d ≤ G.floor a ha) ↔
    (G.embedding i ≤ a ∧ ¬ G.embedding d ≤ a)
  exact and_congr (Iff.symm (G.le_floor_iff a ha i))
    (not_congr (Iff.symm (G.le_floor_iff a ha d)))

private noncomputable def hookFiberIso (i d : G.Point) (a : Fin n → ℝ) :
    (G.lan.obj (Hook.module (k := k) i d)).obj a ≅
      (Hook.module (k := k) (G.embedding i) (G.embedding d)).obj a := by
  classical
  by_cases ha : G.HasLowerPoint a
  · let p := G.floor a ha
    have hfiber :
        SupportInterval.fiber (k := k) (Hook.support i d) p =
          SupportInterval.fiber (k := k)
            (Hook.support (G.embedding i) (G.embedding d)) a := by
      have hmem : p ∈ Hook.support i d ↔
          a ∈ Hook.support (G.embedding i) (G.embedding d) := by
        change Hook.support i d (G.floor a ha) ↔
          Hook.support (G.embedding i) (G.embedding d) a
        exact G.hookSupport_floor_iff i d ha
      unfold SupportInterval.fiber
      exact congrArg (fun s : Prop => if s then (⊤ : Submodule k k) else ⊥)
        (propext hmem)
    exact (G.appIso (Hook.module (k := k) i d) a ha).trans
      (LinearEquiv.ofEq _ _ hfiber).toModuleIso
  · have hleft : IsZero ((G.lan.obj (Hook.module (k := k) i d)).obj a) :=
      G.isZero_obj_of_not_hasLowerPoint _ a ha
    have hbirth : ¬ G.embedding i ≤ a := by
      intro hi
      exact ha ⟨i, hi⟩
    have hsupport : a ∉ Hook.support (G.embedding i) (G.embedding d) :=
      fun hs => hbirth hs.1
    letI : Subsingleton
        ((Hook.module (k := k) (G.embedding i) (G.embedding d)).obj a) :=
      supportFiber_subsingleton (k := k)
        (Hook.support (G.embedding i) (G.embedding d)) a hsupport
    exact hleft.iso (ModuleCat.isZero_of_subsingleton _)

private theorem hookFiberIso_hom_val (i d : G.Point) {a : Fin n → ℝ}
    (ha : G.HasLowerPoint a) (hsa : a ∈ Hook.support (G.embedding i) (G.embedding d))
    (x : (G.lan.obj (Hook.module (k := k) i d)).obj a) :
    (((hookFiberIso G i d a).hom.hom x :
      SupportInterval.fiber (k := k)
        (Hook.support (G.embedding i) (G.embedding d)) a) : k) =
      (((G.appIso (Hook.module (k := k) i d) a ha).hom.hom x :
        SupportInterval.fiber (k := k) (Hook.support i d) (G.floor a ha)) : k) := by
  let p := G.floor a ha
  have hsp : p ∈ Hook.support i d := (G.hookSupport_floor_iff i d ha).mpr hsa
  simp [hookFiberIso, ha, p, LinearEquiv.coe_ofEq_apply, hsp, hsa]

/-- The actual left Kan extension of every finite-death hook is naturally
isomorphic to the hook with the embedded endpoints. This statement also
covers coincident or reversed endpoints, whose supports are empty. -/
noncomputable def hookLanIso (i d : G.Point) :
    G.lan.obj (Hook.module (k := k) i d) ≅
      Hook.module (k := k) (G.embedding i) (G.embedding d) := by
  classical
  refine NatIso.ofComponents (hookFiberIso G i d) ?_
  intro a b hab
  let h : a ≤ b := leOfHom hab
  apply ModuleCat.hom_ext
  ext x
  by_cases hsa : a ∈ Hook.support (G.embedding i) (G.embedding d)
  · by_cases hsb : b ∈ Hook.support (G.embedding i) (G.embedding d)
    · let ha : G.HasLowerPoint a := ⟨i, hsa.1⟩
      let hb : G.HasLowerPoint b := ⟨i, hsb.1⟩
      let p := G.floor a ha
      let q := G.floor b hb
      have hpq : p ≤ q := G.floor_mono h ha hb
      have hqSupport : q ∈ Hook.support i d :=
        (G.hookSupport_floor_iff i d hb).mpr hsb
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      change (((hookFiberIso G i d b).hom.hom
          (structureMapLinear (G.lan.obj (Hook.module (k := k) i d)) h x) :
          SupportInterval.fiber _ _) : k) =
        (((structureMapLinear
          (Hook.module (k := k) (G.embedding i) (G.embedding d)) h)
          ((hookFiberIso G i d a).hom.hom x) :
          SupportInterval.fiber _ _) : k)
      have hcoeffB := hookFiberIso_hom_val G i d hb hsb
        (structureMapLinear (G.lan.obj (Hook.module (k := k) i d)) h x)
      have hcoeffA := hookFiberIso_hom_val G i d ha hsa x
      calc
        _ = ((G.appIso (Hook.module (k := k) i d) b hb).hom.hom
            (structureMapLinear (G.lan.obj (Hook.module (k := k) i d)) h x) : k) := hcoeffB
        _ = ((structureMapLinear (Hook.module (k := k) i d) hpq
            ((G.appIso (Hook.module (k := k) i d) a ha).hom.hom x)) : k) := by
          rw [G.appIso_structureMap_apply (M := Hook.module (k := k) i d)
            h ha hb x]
        _ = ((G.appIso (Hook.module (k := k) i d) a ha).hom.hom x : k) := by
          rw [SupportInterval.structureMap_val (Hook.support i d)
            (Hook.support_ordConnected i d) hpq, if_pos hqSupport]
        _ = ((hookFiberIso G i d a).hom.hom x : k) := hcoeffA.symm
        _ = (structureMapLinear
            (Hook.module (k := k) (G.embedding i) (G.embedding d)) h
            ((hookFiberIso G i d a).hom.hom x) : k) := by
          rw [SupportInterval.structureMap_val
            (Hook.support (G.embedding i) (G.embedding d))
            (Hook.support_ordConnected (G.embedding i) (G.embedding d)) h,
            if_pos hsb]
    · haveI : Subsingleton
          ((Hook.module (k := k) (G.embedding i) (G.embedding d)).obj b) :=
        supportFiber_subsingleton (k := k)
          (Hook.support (G.embedding i) (G.embedding d)) b hsb
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      have hleft : (((hookFiberIso G i d b).hom.hom
          (structureMapLinear (G.lan.obj (Hook.module (k := k) i d)) h x) :
          SupportInterval.fiber _ _) : k) = 0 :=
        SupportInterval.val_eq_zero _ hsb _
      have hright : (((structureMapLinear
          (Hook.module (k := k) (G.embedding i) (G.embedding d)) h)
          ((hookFiberIso G i d a).hom.hom x) :
          SupportInterval.fiber _ _) : k) = 0 := by
        rw [SupportInterval.structureMap_val, if_neg hsb]
      exact hleft.trans hright.symm
  · haveI : Subsingleton
        ((Hook.module (k := k) (G.embedding i) (G.embedding d)).obj a) := by
      exact supportFiber_subsingleton (k := k)
        (Hook.support (G.embedding i) (G.embedding d)) a hsa
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    have hx : (hookFiberIso G i d a).hom.hom x = 0 :=
      Subsingleton.elim _ _
    have hinj : Function.Injective (hookFiberIso (k := k) G i d a).hom.hom :=
      (ModuleCat.mono_iff_injective
        (hookFiberIso (k := k) G i d a).hom).mp inferInstance
    have hx0 : x = 0 := hinj (by simpa using hx)
    simp [hx0]

/-- The finite-hook comparison preserves the actual coefficient on every
supported fiber. -/
theorem hookLanIso_apply_coefficient (i d : G.Point) {a : Fin n → ℝ}
    (ha : G.HasLowerPoint a) (hsa : a ∈ Hook.support (G.embedding i) (G.embedding d))
    (x : (G.lan.obj (Hook.module (k := k) i d)).obj a) :
    (((G.hookLanIso i d).hom.app a).hom x :
      SupportInterval.fiber (k := k)
        (Hook.support (G.embedding i) (G.embedding d)) a) =
      (((G.appIso (Hook.module (k := k) i d) a ha).hom.hom x :
        SupportInterval.fiber (k := k) (Hook.support i d) (G.floor a ha)) : k) :=
  hookFiberIso_hom_val G i d ha hsa x

/-- The real-coordinate hook family corresponding to the original occurrence
indexing of `FiniteHookDeflation.family`. Repeated endpoints remain distinct. -/
noncomputable def embeddedCoverFamily
    (M : PModule.{u,0,u} k G.Point) :
    FiniteHookDeflation.Index M → PModule.{u,0,u} k (Fin n → ℝ)
  | .inl t =>
      Hook.module (G.embedding t.1.val.1) (G.embedding t.1.val.2)
  | .inr t => HookInfinity.module (R := k) (G.embedding t.1)

private noncomputable def embeddedCoverFamilyIso
    (M : PModule.{u,0,u} k G.Point) (t : FiniteHookDeflation.Index M) :
    G.lan.obj (FiniteHookDeflation.family M t) ≅ embeddedCoverFamily G M t := by
  cases t with
  | inl t => exact G.hookLanIso t.1.val.1 t.1.val.2
  | inr t => exact G.infinityLanIso t.1

/-- The actual Kan image of the occurrence-indexed finite grid hook sum is
isomorphic to the biproduct of its embedded real-coordinate hooks. -/
noncomputable def finiteHookDeflationLanIso
    (M : PModule.{u,0,u} k G.Point) :
    G.lan.obj (FiniteHookDeflation.module M) ≅
      ⨁ fun t => embeddedCoverFamily G M t := by
  classical
  exact (G.lanBiproductIso (FiniteHookDeflation.family M)).trans
    (biproduct.mapIso (embeddedCoverFamilyIso G M))

/-- Each projection of the embedded cover is the image of the original grid
projection, followed by its actual hook comparison isomorphism. -/
theorem finiteHookDeflationLanIso_hom_π
    (M : PModule.{u,0,u} k G.Point) (t : FiniteHookDeflation.Index M) :
    (G.finiteHookDeflationLanIso M).hom ≫
        biproduct.π (embeddedCoverFamily G M) t =
      G.lan.map (biproduct.π (FiniteHookDeflation.family M) t) ≫
        (embeddedCoverFamilyIso G M t).hom := by
  classical
  change (G.lanBiproductIso (FiniteHookDeflation.family M)).hom ≫
      biproduct.map (fun j => (embeddedCoverFamilyIso G M j).hom) ≫
        biproduct.π (embeddedCoverFamily G M) t = _
  calc
    _ = (G.lanBiproductIso (FiniteHookDeflation.family M)).hom ≫
        (biproduct.π (fun j => G.lan.obj (FiniteHookDeflation.family M j)) t ≫
          (embeddedCoverFamilyIso G M t).hom) := by
          rw [biproduct.map_π]
    _ = ((G.lanBiproductIso (FiniteHookDeflation.family M)).hom ≫
        biproduct.π (fun j => G.lan.obj (FiniteHookDeflation.family M j)) t) ≫
          (embeddedCoverFamilyIso G M t).hom := by rw [← Category.assoc]
    _ = _ := by rw [G.lanBiproductIso_hom_π]

/-- Each embedded occurrence inclusion, transported through the actual
comparison, is the Kan image of the original grid inclusion. -/
theorem finiteHookDeflationLanIso_inv_ι
    (M : PModule.{u,0,u} k G.Point) (t : FiniteHookDeflation.Index M) :
    biproduct.ι (embeddedCoverFamily G M) t ≫
        (G.finiteHookDeflationLanIso M).inv =
      (embeddedCoverFamilyIso G M t).inv ≫
        G.lan.map (biproduct.ι (FiniteHookDeflation.family M) t) := by
  classical
  change biproduct.ι (embeddedCoverFamily G M) t ≫
      biproduct.map (fun j => (embeddedCoverFamilyIso G M j).inv) ≫
        (G.lanBiproductIso (FiniteHookDeflation.family M)).inv = _
  calc
    _ = (biproduct.ι (embeddedCoverFamily G M) t ≫
        biproduct.map (fun j => (embeddedCoverFamilyIso G M j).inv)) ≫
          (G.lanBiproductIso (FiniteHookDeflation.family M)).inv := by
          rw [← Category.assoc]
    _ = ((embeddedCoverFamilyIso G M t).inv ≫
        biproduct.ι (fun j => G.lan.obj (FiniteHookDeflation.family M j)) t) ≫
          (G.lanBiproductIso (FiniteHookDeflation.family M)).inv := by
          rw [biproduct.ι_map]
    _ = (embeddedCoverFamilyIso G M t).inv ≫
        biproduct.ι (fun j => G.lan.obj (FiniteHookDeflation.family M j)) t ≫
          (G.lanBiproductIso (FiniteHookDeflation.family M)).inv := by
          rw [← Category.assoc]
    _ = _ := by rw [CoordinateGrid.lanBiproductIso_inv_ι]

end Field

end TDA.Persistence.CoordinateGrid
