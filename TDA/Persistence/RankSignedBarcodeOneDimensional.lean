import TDA.Persistence.FiniteRankProjectiveResolutionHookBetti
import TDA.Persistence.FiniteRankProjectiveResolutionDimension
import TDA.Persistence.FinitePresentationIndexLift
import TDA.Persistence.FinitePresentationGrid
import TDA.Persistence.FinitePresentationFiniteDimensional
import TDA.Persistence.ConstructibleIsometry
import TDA.Persistence.ConstructibleBarcode
import TDA.Persistence.RectangleBarcodeBridge
import TDA.Persistence.RealIntervalInterleaving
import TDA.Persistence.MatchingInterleaving
import TDA.Persistence.RankSignedStability

/-!
# One-dimensional signed hooks and ordinary barcodes

In one real coordinate, finite hooks have the right-open interval convention
and principal hooks are essential intervals.  This module connects the
degree-zero hook multiset of a minimal resolution to the existing real
barcode realization and finite-constructible isometry.  The endpoint
convention is the half-open convention used by Bauer--Lesnick, §§2.1--2.3;
the finite-presentation-to-grid step reuses the results from BOOS v3,
§§2.7--2.9 and Theorem 6.1.  The public module-level result keeps the original
small finite-presentation hypothesis on `CoordinateRealBridge.fromReal M`.
It proves the ordinary one-dimensional barcode isometry and does not identify
the signed hook bottleneck dissimilarity with ordinary bottleneck distance.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Classical

variable {k : Type u} [Field k]

/-- The endpoint pair represented by a one-coordinate finite hook or principal
hook.  Finite deaths are included as real values, while principal hooks have
death `⊤`. -/
def oneDimensionalHookEndpoints
    (t : RealHookTag (n := 1)) : ℝ × WithTop ℝ :=
  match t with
  | .inl ab => (ab.val.1 0, (ab.val.2 0 : WithTop ℝ))
  | .inr a => (a 0, ⊤)

/-- Every hook endpoint is a genuine nonempty half-open interval. -/
theorem oneDimensionalHookEndpoints_positive
    (t : RealHookTag (n := 1)) :
    (oneDimensionalHookEndpoints t).1 < (oneDimensionalHookEndpoints t).2 := by
  cases t with
  | inl ab =>
      have hle : ab.val.1 0 ≤ ab.val.2 0 := ab.property.1 0
      have hne : ab.val.1 0 ≠ ab.val.2 0 := by
        intro heq
        apply ab.property.2
        intro i
        fin_cases i
        exact heq.symm.le
      exact WithTop.coe_lt_coe.mpr (lt_of_le_of_ne hle hne)
  | inr a => exact WithTop.coe_lt_top _

private theorem oneDimensional_strictAt {a b : Fin 1 → ℝ} (hab : a < b) :
    a 0 < b 0 := by
  have hle : a 0 ≤ b 0 := hab.1 0
  have hne : a 0 ≠ b 0 := by
    intro heq
    apply hab.2
    intro i
    fin_cases i
    exact heq.symm.le
  exact lt_of_le_of_ne hle hne

private theorem finiteHook_support_eq_alive (a b : Fin 1 → ℝ) :
    Hook.support a b = {x : Fin 1 → ℝ |
      RealBarcode.alive (a 0, (b 0 : WithTop ℝ)) (x 0)} := by
  ext x
  simp [Hook.support, RealBarcode.alive, Pi.le_def,
    Fin.forall_fin_one, not_le]

/-- Each finite hook is naturally the corresponding half-open real interval,
with the original strict finite death endpoint. -/
noncomputable def finiteHook_intervalIso (a b : Fin 1 → ℝ) (hab : a < b) :
    Hook.module (k := k) a b ≅
      CoordinateRealBridge.fromReal
        (RealBarcode.intervalModule (k := k) (a 0, (b 0 : WithTop ℝ))) := by
  have hS := finiteHook_support_eq_alive a b
  have hOrd : ({x : Fin 1 → ℝ |
      RealBarcode.alive (a 0, (b 0 : WithTop ℝ)) (x 0)}).OrdConnected :=
    hS ▸ Hook.support_ordConnected a b
  have hmodule : Hook.module (k := k) a b =
      SupportInterval.module _ hOrd := by
    simp only [Hook.module, hS]
  have hinterval : SupportInterval.module
      ({x : Fin 1 → ℝ |
        RealBarcode.alive (a 0, (b 0 : WithTop ℝ)) (x 0)}) hOrd =
      CoordinateRealBridge.fromReal
        (RealBarcode.intervalModule (k := k) (a 0, (b 0 : WithTop ℝ))) := by
    rfl
  exact eqToIso (hmodule.trans hinterval)

private theorem principalHook_alive_iff (a x : Fin 1 → ℝ) :
    a ≤ x ↔ RealBarcode.alive (a 0, (⊤ : WithTop ℝ)) (x 0) := by
  constructor
  · intro h
    exact ⟨h 0, WithTop.coe_lt_top _⟩
  · intro h i
    fin_cases i
    exact h.1

private noncomputable def principalHookFiberEquiv (a x : Fin 1 → ℝ) :
    (HookInfinity.module (R := k) a).obj x ≃ₗ[k]
      RealBarcode.fiber (k := k) (a 0, (⊤ : WithTop ℝ)) (x 0) := by
  classical
  by_cases hax : a ≤ x
  · have halive := (principalHook_alive_iff a x).mp hax
    have htop : RealBarcode.fiber (k := k)
        (a 0, (⊤ : WithTop ℝ)) (x 0) = ⊤ := by
      simp [RealBarcode.fiber, halive]
    let eTop : (⊤ : Submodule k k) ≃ₗ[k] k := Submodule.topEquiv
    exact (HookInfinity.fiberEquivOfLe (R := k) hax).trans
      (eTop.symm.trans
        (LinearEquiv.ofEq _ _ htop).symm)
  · have hnot : ¬ RealBarcode.alive (a 0, (⊤ : WithTop ℝ)) (x 0) :=
      fun h => hax ((principalHook_alive_iff a x).mpr h)
    have hbot : RealBarcode.fiber (k := k)
        (a 0, (⊤ : WithTop ℝ)) (x 0) = (⊥ : Submodule k k) := by
      simp only [RealBarcode.fiber, if_neg hnot]
    rw [hbot]
    haveI hsrc : Subsingleton ((HookInfinity.module (R := k) a).obj x) := by
      refine ⟨fun v w => ?_⟩
      calc
        v = 0 := HookInfinity.fiber_eq_zero_of_not_le (R := k) hax v
        _ = w := (HookInfinity.fiber_eq_zero_of_not_le (R := k) hax w).symm
    haveI hdst : Subsingleton (⊥ : Submodule k k) := inferInstance
    exact LinearEquiv.ofBijective 0 ⟨
      (fun v w _ => hsrc.elim v w),
      (fun w => ⟨0, hdst.elim _ _⟩)⟩

private theorem principalHookFiberEquiv_val (a x : Fin 1 → ℝ)
    (hax : a ≤ x) (v : (HookInfinity.module (R := k) a).obj x) :
    (principalHookFiberEquiv (k := k) a x v).val =
      HookInfinity.fiberEquivOfLe (R := k) hax v := by
  have htop : RealBarcode.fiber (k := k)
      (a 0, (⊤ : WithTop ℝ)) (x 0) = ⊤ := by
    change (if RealBarcode.alive (a 0, (⊤ : WithTop ℝ)) (x 0) then
      (⊤ : Submodule k k) else (⊥ : Submodule k k)) = (⊤ : Submodule k k)
    rw [if_pos ((principalHook_alive_iff a x).mp hax)]
  simp [principalHookFiberEquiv, hax, htop, Submodule.topEquiv,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply]

/-- A principal hook is the existing essential half-open interval module. -/
noncomputable def principalHook_intervalIso (a : Fin 1 → ℝ) :
    HookInfinity.module (R := k) a ≅
      CoordinateRealBridge.fromReal
        (RealBarcode.intervalModule (k := k) (a 0, (⊤ : WithTop ℝ))) := by
  refine NatIso.ofComponents
    (fun x => (principalHookFiberEquiv (k := k) a x).toModuleIso) ?_
  intro x y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  by_cases hx : a ≤ x
  · have hy : a ≤ y := hx.trans (leOfHom f)
    have hsource : ((HookInfinity.module (R := k) a).map f).hom z =
        structureMapLinear (HookInfinity.module (R := k) a) (leOfHom f) z := rfl
    change principalHookFiberEquiv (k := k) a y
        (((HookInfinity.module (R := k) a).map f).hom z) =
      ((CoordinateRealBridge.fromReal
        (RealBarcode.intervalModule (k := k) (a 0, (⊤ : WithTop ℝ)))).map f).hom
        (show (CoordinateRealBridge.fromReal
          (RealBarcode.intervalModule (k := k) (a 0, (⊤ : WithTop ℝ)))).obj x from
          principalHookFiberEquiv (k := k) a x z)
    apply Subtype.ext
    change (principalHookFiberEquiv (k := k) a y
        (((HookInfinity.module (R := k) a).map f).hom z)).val =
      (((RealBarcode.intervalModule (k := k) (a 0, (⊤ : WithTop ℝ))).map
        (homOfLE ((leOfHom f) 0))).hom
          (principalHookFiberEquiv (k := k) a x z)).val
    rw [hsource, principalHookFiberEquiv_val a y hy]
    rw [HookInfinity.fiberEquivOfLe_structureMap (R := k) hx (leOfHom f)]
    rw [RealBarcode.map_val (k := k) (a 0, (⊤ : WithTop ℝ))
      (homOfLE ((leOfHom f) 0))
      (show RealBarcode.fiber (k := k) (a 0, (⊤ : WithTop ℝ)) (x 0) from
        principalHookFiberEquiv (k := k) a x z)]
    rw [if_pos ((principalHook_alive_iff a y).mp hy)]
    exact (principalHookFiberEquiv_val a x hx z).symm
  · have hz : z = 0 := HookInfinity.fiber_eq_zero_of_not_le (R := k) hx z
    subst z
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, map_zero]

private noncomputable def oneDimensionalTag_intervalIso
    (t : RealHookTag (n := 1)) :
    FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) t ≅
      CoordinateRealBridge.fromReal
        (RealBarcode.intervalModule (k := k) (oneDimensionalHookEndpoints t)) := by
  cases t with
  | inl ab => exact finiteHook_intervalIso ab.val.1 ab.val.2 ab.property
  | inr a => exact principalHook_intervalIso a

private noncomputable def oneDimensionalFamilyProjection
    {m : ℕ} (F : Fin m → PModule.{u,0,u} k ℝ) (i : Fin m) :
    RealBarcode.familyModule F ⟶ F i where
  app _ := ModuleCat.ofHom (LinearMap.proj i)
  naturality {s t} f := by ext x; rfl

private noncomputable def oneDimensionalFamilyCone
    {m : ℕ} (F : Fin m → PModule.{u,0,u} k ℝ) :
    Fan (fun i => CoordinateRealBridge.fromReal (F i)) :=
  Fan.mk (CoordinateRealBridge.fromReal (RealBarcode.familyModule F))
    (fun i => reindexNatTrans CoordinateRealBridge.evaluate
      (oneDimensionalFamilyProjection F i))

private noncomputable def oneDimensionalFamilyIsLimit
    {m : ℕ} (F : Fin m → PModule.{u,0,u} k ℝ) :
    IsLimit (oneDimensionalFamilyCone F) := by
  apply evaluationJointlyReflectsLimits
  intro a
  apply (IsLimit.postcomposeHomEquiv (Discrete.compNatIsoDiscrete _ _) _).toFun
  exact (ModuleCat.productConeIsLimit (fun i => (F i).obj (a 0))).ofIsoLimit
    (Cone.ext (Iso.refl _) (fun j => by
      change ModuleCat.ofHom (LinearMap.proj j.as :
        (∀ i, (F i).obj (a 0)) →ₗ[k] (F j.as).obj (a 0)) =
        𝟙 _ ≫ ModuleCat.ofHom (LinearMap.proj j.as :
          (∀ i, (F i).obj (a 0)) →ₗ[k] (F j.as).obj (a 0)) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]))

private noncomputable def oneDimensionalHookFamilyIso
    {m : ℕ} (T : Fin m → RealHookTag (n := 1)) :
    (⨁ fun i => FiniteRankProjectiveClassification.rankProjectiveHookModule
      (k := k) (T i)) ≅
      CoordinateRealBridge.fromReal (RealBarcode.familyModule
        (fun i => RealBarcode.intervalModule (k := k)
          (oneDimensionalHookEndpoints (T i)))) := by
  let F := fun i : Fin m => RealBarcode.intervalModule (k := k)
    (oneDimensionalHookEndpoints (T i))
  exact biproduct.mapIso (fun i => oneDimensionalTag_intervalIso (T i)) ≪≫
    (biproduct.isLimit _).conePointUniqueUpToIso (oneDimensionalFamilyIsLimit F)

private noncomputable def oneDimensionalFromRealIso
    {M N : PModule.{u,0,u} k ℝ} (e : M ≅ N) :
    CoordinateRealBridge.fromReal M ≅ CoordinateRealBridge.fromReal N :=
  NatIso.ofComponents (fun x => e.app (x 0)) (by
    intro a b f
    change M.map (homOfLE ((leOfHom f) 0)) ≫ e.hom.app (b 0) =
      e.hom.app (a 0) ≫ N.map (homOfLE ((leOfHom f) 0))
    exact e.hom.naturality (homOfLE ((leOfHom f) 0)))

private noncomputable def oneDimensionalReindexDiagonalIso
    {M N : PModule.{u,0,u} k (Fin 1 → ℝ)} (e : M ≅ N) :
    reindex CoordinateRealBridge.diagonal M ≅
      reindex CoordinateRealBridge.diagonal N :=
  NatIso.ofComponents (fun t => e.app (CoordinateRealBridge.diagonal t)) (by
    intro s t f
    change M.map (homOfLE (CoordinateRealBridge.diagonal.monotone (leOfHom f))) ≫
        e.hom.app (CoordinateRealBridge.diagonal t) =
      e.hom.app (CoordinateRealBridge.diagonal s) ≫
        N.map (homOfLE (CoordinateRealBridge.diagonal.monotone (leOfHom f)))
    exact e.hom.naturality
      (homOfLE (CoordinateRealBridge.diagonal.monotone (leOfHom f))))

private noncomputable def oneDimensionalDiagonalFromRealIso
    (M : PModule.{u,0,u} k ℝ) :
    reindex CoordinateRealBridge.diagonal (CoordinateRealBridge.fromReal M) ≅ M := by
  apply eqToIso
  calc
    reindex CoordinateRealBridge.diagonal (CoordinateRealBridge.fromReal M) =
        reindex (CoordinateRealBridge.evaluate.comp CoordinateRealBridge.diagonal) M := by
          rw [CoordinateRealBridge.fromReal, reindex_comp]
    _ = M := by
      have h : CoordinateRealBridge.evaluate.comp CoordinateRealBridge.diagonal =
          (OrderHom.id : ℝ →o ℝ) := by
        ext t
        rfl
      rw [h, reindex_id]

/-- The endpoint diagram of a finite hook family, retaining all occurrences. -/
noncomputable def oneDimensionalHookDiagram {m : ℕ}
    (T : Fin m → RealHookTag (n := 1)) : Diagram ℝ where
  points := (Finset.univ : Finset (Fin m)).val.map
    (fun i => oneDimensionalHookEndpoints (T i))
  offDiagonal := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hp
    exact ne_of_lt (oneDimensionalHookEndpoints_positive (T i))

theorem oneDimensionalHookDiagram_isPositive {m : ℕ}
    (T : Fin m → RealHookTag (n := 1)) :
    (oneDimensionalHookDiagram T).IsPositive := by
  intro p hp
  change p ∈ (Finset.univ : Finset (Fin m)).val.map
    (fun i => oneDimensionalHookEndpoints (T i)) at hp
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hp
  exact oneDimensionalHookEndpoints_positive (T i)

/-- The recursive hook multiset is exactly the finite list of occurrences. -/
theorem hookTagMultiset_eq_univ_map {m : ℕ}
    (T : Fin m → RealHookTag (n := 1)) :
    hookTagMultiset T = (Finset.univ : Finset (Fin m)).val.map T := by
  classical
  induction m with
  | zero => simp [hookTagMultiset]
  | succ m ih =>
      rw [hookTagMultiset]
      rw [ih (fun i : Fin m => T i.succ)]
      simp

/-- The diagram point multiset is the endpoint image of the exact hook
occurrence multiset. -/
theorem oneDimensionalHookDiagram_points {m : ℕ}
    (T : Fin m → RealHookTag (n := 1)) :
    (oneDimensionalHookDiagram T).points =
      Multiset.map oneDimensionalHookEndpoints (hookTagMultiset T) := by
  change (Finset.univ : Finset (Fin m)).val.map
      (fun i => oneDimensionalHookEndpoints (T i)) = _
  rw [hookTagMultiset_eq_univ_map]
  rw [Multiset.map_map]
  rfl

/-- Recover the finite or principal hook tag represented by any positive
right-open endpoint pair. -/
def oneDimensionalEndpointTag (p : ℝ × WithTop ℝ)
    (hp : (p.1 : WithTop ℝ) < p.2) : RealHookTag (n := 1) := by
  cases hdeath : p.2 with
  | top => exact .inr (fun _ => p.1)
  | coe d =>
      have hlt : p.1 < d := WithTop.coe_lt_coe.mp (by simpa [hdeath] using hp)
      refine .inl ⟨(fun _ => p.1, fun _ => d), ?_⟩
      constructor
      · intro i
        fin_cases i
        exact hlt.le
      · intro heq
        exact (not_le_of_gt hlt) (heq 0)

/-- The endpoint inverse preserves the exact finite/infinite endpoint pair. -/
theorem oneDimensionalHookEndpoints_endpointTag
    (p : ℝ × WithTop ℝ) (hp : (p.1 : WithTop ℝ) < p.2) :
    oneDimensionalHookEndpoints (oneDimensionalEndpointTag p hp) = p := by
  rcases p with ⟨b, d⟩
  cases d with
  | top => rfl
  | coe d =>
      simp [oneDimensionalEndpointTag, oneDimensionalHookEndpoints]

/-- The endpoint inverse recovers every actual finite or principal hook tag. -/
theorem oneDimensionalEndpointTag_endpoints
    (t : RealHookTag (n := 1)) :
    oneDimensionalEndpointTag (oneDimensionalHookEndpoints t)
      (oneDimensionalHookEndpoints_positive t) = t := by
  cases t with
  | inl ab =>
      rcases ab with ⟨⟨a, b⟩, hab⟩
      simp only [oneDimensionalHookEndpoints, oneDimensionalEndpointTag]
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · funext i
        fin_cases i
        rfl
      · funext i
        fin_cases i
        rfl
  | inr a =>
      simp only [oneDimensionalHookEndpoints, oneDimensionalEndpointTag]
      apply congrArg Sum.inr
      funext i
      fin_cases i
      rfl

/-- The positive-pair inverse packaged as a function on the endpoint subtype. -/
def oneDimensionalEndpointTagOnPositive
    (p : {p : ℝ × WithTop ℝ // (p.1 : WithTop ℝ) < p.2}) :
    RealHookTag (n := 1) :=
  oneDimensionalEndpointTag p.val p.property

/-- The packaged endpoint inverse recovers each hook tag. -/
theorem oneDimensionalEndpointTagOnPositive_endpoints
    (t : RealHookTag (n := 1)) :
    oneDimensionalEndpointTagOnPositive
      ⟨oneDimensionalHookEndpoints t, oneDimensionalHookEndpoints_positive t⟩ = t :=
  oneDimensionalEndpointTag_endpoints t

/-- Endpoint conversion is injective on the actual finite and principal tags. -/
theorem oneDimensionalHookEndpoints_injective :
    ∀ {a b : RealHookTag (n := 1)},
      oneDimensionalHookEndpoints a = oneDimensionalHookEndpoints b → a = b := by
  intro a b h
  let pa : {p : ℝ × WithTop ℝ // (p.1 : WithTop ℝ) < p.2} :=
    ⟨oneDimensionalHookEndpoints a, oneDimensionalHookEndpoints_positive a⟩
  let pb : {p : ℝ × WithTop ℝ // (p.1 : WithTop ℝ) < p.2} :=
    ⟨oneDimensionalHookEndpoints b, oneDimensionalHookEndpoints_positive b⟩
  have hp : pa = pb := Subtype.ext h
  have ht := congrArg oneDimensionalEndpointTagOnPositive hp
  calc
    a = oneDimensionalEndpointTagOnPositive pa :=
      (oneDimensionalEndpointTagOnPositive_endpoints a).symm
    _ = oneDimensionalEndpointTagOnPositive pb := ht
    _ = b := oneDimensionalEndpointTagOnPositive_endpoints b

/-- Every positive ordinary diagram has an actual finite hook-sum presentation
of its existing RealBarcode realization, one occurrence at a time. -/
noncomputable def positiveDiagram_hookPresentation (D : Diagram ℝ)
    (hD : D.IsPositive) :
    FiniteHookSumPresentation (k := k) (n := 1)
      (CoordinateRealBridge.fromReal (RealBarcode.realize (k := k) D)) := by
  let xs := D.points.toList
  let T : Fin xs.length → RealHookTag (n := 1) := fun i =>
    oneDimensionalEndpointTag (xs.get i) (hD (xs.get i) (by
      exact Multiset.mem_toList.mp (List.get_mem xs i)))
  have hEndpoints (i : Fin xs.length) :
      oneDimensionalHookEndpoints (T i) = xs.get i :=
    oneDimensionalHookEndpoints_endpointTag _ _
  let hfamily : RealBarcode.familyModule
      (fun i : Fin xs.length => RealBarcode.intervalModule (k := k) (xs.get i)) ≅
      RealBarcode.familyModule
        (fun i => RealBarcode.intervalModule (k := k)
          (oneDimensionalHookEndpoints (T i))) := by
    apply RealBarcode.familyIso (Equiv.refl (Fin xs.length))
    intro i
    exact eqToIso (congrArg (RealBarcode.intervalModule (k := k)) (hEndpoints i).symm)
  let e := (oneDimensionalFromRealIso (k := k) hfamily).trans
    (oneDimensionalHookFamilyIso (k := k) T).symm
  refine ⟨xs.length, T, ?_⟩
  change CoordinateRealBridge.fromReal
      (RealBarcode.familyModule
        (fun i : Fin xs.length => RealBarcode.intervalModule (k := k) (xs.get i))) ≅ _
  exact e

/-- The inverse-endpoint hook presentation recovers the complete existing
diagram point multiset, including all repetitions and essential bars. -/
theorem positiveDiagram_hookPresentation_diagram (D : Diagram ℝ)
    (hD : D.IsPositive) :
    oneDimensionalHookDiagram
        (positiveDiagram_hookPresentation (k := k) D hD).tag = D := by
  apply Diagram.ext
  let xs := D.points.toList
  let T : Fin xs.length → RealHookTag (n := 1) := fun i =>
    oneDimensionalEndpointTag (xs.get i) (hD (xs.get i) (by
      exact Multiset.mem_toList.mp (List.get_mem xs i)))
  have hEndpoints (i : Fin xs.length) :
      oneDimensionalHookEndpoints (T i) = xs.get i :=
    oneDimensionalHookEndpoints_endpointTag _ _
  unfold positiveDiagram_hookPresentation
  rw [oneDimensionalHookDiagram_points]
  change Multiset.map oneDimensionalHookEndpoints
      (hookTagMultiset T) = D.points
  rw [hookTagMultiset_eq_univ_map]
  calc
    Multiset.map oneDimensionalHookEndpoints
        ((Finset.univ : Finset (Fin xs.length)).val.map T) =
        (Finset.univ : Finset (Fin xs.length)).val.map
          (fun i => oneDimensionalHookEndpoints (T i)) := by
      rw [Multiset.map_map]
      rfl
    _ = (Finset.univ : Finset (Fin xs.length)).val.map (fun i => xs.get i) := by
      exact Multiset.map_congr rfl (fun i hi => hEndpoints i)
    _ = D.points := by
      rw [Fin.univ_val_map, List.ofFn_get]
      exact Multiset.coe_toList D.points

/-- The occurrence-indexed hook sum realizes its actual endpoint diagram. -/
noncomputable def finiteHookSum_realizationIso
    {M : PModule.{u,0,u} k (Fin 1 → ℝ)}
    (P : FiniteHookSumPresentation (k := k) (n := 1) M) :
    M ≅ CoordinateRealBridge.fromReal
      (RealBarcode.realize (k := k) (oneDimensionalHookDiagram P.tag)) := by
  let x := fun i : Fin P.count => oneDimensionalHookEndpoints (P.tag i)
  let D := oneDimensionalHookDiagram P.tag
  let xs := D.points.toList
  have hx : (Finset.univ : Finset (Fin xs.length)).val.map (fun i => xs.get i) =
      D.points := by
    rw [Fin.univ_val_map, List.ofFn_get]
    exact Multiset.coe_toList _
  let e := (presentationEquiv x (fun i : Fin xs.length => xs.get i)
    (by simpa [x, D, oneDimensionalHookDiagram] using hx.symm)).1
  have he := (presentationEquiv x (fun i : Fin xs.length => xs.get i)
    (by simpa [x, D, oneDimensionalHookDiagram] using hx.symm)).2
  have hfamily :
      RealBarcode.familyModule
          (fun i => RealBarcode.intervalModule (k := k) (x i)) ≅
        RealBarcode.familyModule
          (fun j : Fin xs.length => RealBarcode.intervalModule (k := k) (xs.get j)) := by
    apply RealBarcode.familyIso e
    intro j
    have hp : x (e.symm j) = xs.get j := by simpa [e] using (he (e.symm j)).symm
    exact eqToIso (congrArg (RealBarcode.intervalModule (k := k)) hp)
  exact (P.iso ≪≫ oneDimensionalHookFamilyIso (k := k) P.tag) ≪≫
    oneDimensionalFromRealIso (k := k) hfamily ≪≫
    eqToIso (by rfl)

private theorem oneDimensional_coordinate_le_iff
    (a : Fin 1 → ℝ) (t : ℝ) :
    a ≤ CoordinateRealBridge.diagonal t ↔ a 0 ≤ t := by
  constructor
  · intro h
    exact h 0
  · intro h i
    fin_cases i
    exact h

private theorem oneDimensional_grade_threshold_of_cell
    {n : ℕ} (c : Fin n ↪o ℝ) {critical : Set ℝ}
    (hcover : ∀ q, q ∈ critical → ∃ i, c i = q)
    {s t : ℝ} (hst : s ≤ t)
    (hsame : FiniteConstructible.cellIndex c s = FiniteConstructible.cellIndex c t)
    (q : ℝ) (hq : q ∈ critical) : q ≤ s ↔ q ≤ t := by
  obtain ⟨i, hi⟩ := hcover q hq
  constructor
  · exact fun h => h.trans hst
  · intro ht
    by_contra hs
    have hslt : s < c i := by simpa [hi] using lt_of_not_ge hs
    have hti : c i ≤ t := by simpa [hi] using ht
    have hcountT :=
      (FiniteConstructible.lt_cellIndex_iff c i t).mpr hti
    have hnotS : ¬ i.val < (FiniteConstructible.cellIndex c s).val := by
      intro h
      exact (not_le_of_gt hslt) ((FiniteConstructible.lt_cellIndex_iff c i s).mp h)
    have hcountS : (FiniteConstructible.cellIndex c s).val ≤ i.val :=
      Nat.le_of_not_gt hnotS
    have hval : (FiniteConstructible.cellIndex c s).val =
        (FiniteConstructible.cellIndex c t).val := congrArg Fin.val hsame
    omega

private theorem finitelyPresented_oneDimensional_constructible
    (M : PModule.{u,0,u} k (Fin 1 → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) M) :
    ∃ n : ℕ, ∃ c : Fin n ↪o ℝ,
      FiniteConstructible.IsConstructible c
        (reindex CoordinateRealBridge.diagonal M) ∧
      ∀ i, FiniteDimensional k
        ((reindex CoordinateRealBridge.diagonal M).obj (c i)) := by
  classical
  let hMlift := GradedFree.finitelyPresented_liftIndexUniverse M hM
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  let S : Finset ℝ := (D.criticalCoordinates_finite hD 0).toFinset ∪ {0}
  let n := S.card
  let c : Fin n ↪o ℝ := S.orderEmbOfFin (k := n) rfl
  have hrange : Set.range c = (S : Set ℝ) := by
    simpa [c] using (Finset.range_orderEmbOfFin S (k := n) rfl)
  have hcover : ∀ q, q ∈ D.criticalCoordinates 0 → ∃ i, c i = q := by
    intro q hq
    have hqS : q ∈ (S : Set ℝ) := by
      simp [S, hq]
    have hr : q ∈ Set.range c := by rw [hrange]; exact hqS
    exact Set.mem_range.mp hr
  let Mreal := reindex CoordinateRealBridge.diagonal M
  have hgrid : FiniteConstructible.IsConstructible c Mreal := by
    refine ⟨?_, ?_⟩
    · intro t ht
      have hfree : IsZero
          ((GradedFree.module (R := k) D.generators).obj
            (CoordinateRealBridge.diagonal t)) := by
        have hbelow (g : D.generators.Carrier) :
            ¬ D.generators.grade g ≤ CoordinateRealBridge.diagonal t := by
          have hg : D.generators.grade g 0 ∈ D.criticalCoordinates 0 :=
            Set.mem_union_left _ ⟨g, rfl⟩
          obtain ⟨i, hi⟩ := hcover _ hg
          have hti : t < D.generators.grade g 0 := by
            simpa [hi] using ht i
          intro h
          exact (not_le_of_gt hti)
            ((oneDimensional_coordinate_le_iff (D.generators.grade g) t).mp h)
        letI : IsEmpty
            {g : D.generators.Carrier // D.generators.grade g ≤
              CoordinateRealBridge.diagonal t} :=
          ⟨fun ⟨g, hg⟩ => hbelow g hg⟩
        have hsub : Subsingleton
            ({g : D.generators.Carrier // D.generators.grade g ≤
              CoordinateRealBridge.diagonal t} →₀ k) := by
          refine ⟨fun f g => ?_⟩
          apply Finsupp.ext
          intro i
          exact isEmptyElim i
        haveI : Subsingleton
            ((GradedFree.module (R := k) D.generators).obj
              (CoordinateRealBridge.diagonal t)) := by
          change Subsingleton (GradedFree.fiber (R := k) D.generators
            (CoordinateRealBridge.diagonal t))
          refine ⟨fun x y => ?_⟩
          apply (GradedFree.fiberEquiv (R := k) D.generators
            (CoordinateRealBridge.diagonal t)).injective
          exact hsub.elim _ _
        exact ModuleCat.isZero_of_subsingleton _
      have hpresented : IsZero (D.presented.obj (CoordinateRealBridge.diagonal t)) := by
        haveI : Subsingleton (D.presented.obj (CoordinateRealBridge.diagonal t)) := by
          refine ⟨fun x y => ?_⟩
          obtain ⟨x', hx'⟩ := D.cover_surjective (CoordinateRealBridge.diagonal t) x
          obtain ⟨y', hy'⟩ := D.cover_surjective (CoordinateRealBridge.diagonal t) y
          letI : Subsingleton
              ((GradedFree.module (R := k) D.generators).obj
                (CoordinateRealBridge.diagonal t)) :=
            ModuleCat.subsingleton_of_isZero hfree
          calc
            x = D.cover.app (CoordinateRealBridge.diagonal t) x' := hx'.symm
            _ = D.cover.app (CoordinateRealBridge.diagonal t) y' := by
              congr 1
              exact Subsingleton.elim x' y'
            _ = y := hy'
        exact ModuleCat.isZero_of_subsingleton _
      exact IsZero.of_iso hpresented (e.app (CoordinateRealBridge.diagonal t)).symm
    · intro s t hst hsame
      have hgrade (q : ℝ) (hq : q ∈ D.criticalCoordinates 0) :
          q ≤ s ↔ q ≤ t :=
        oneDimensional_grade_threshold_of_cell c hcover hst hsame q hq
      have hG (g : D.generators.Carrier) :
          D.generators.grade g ≤ CoordinateRealBridge.diagonal s ↔
            D.generators.grade g ≤ CoordinateRealBridge.diagonal t := by
        have hg : D.generators.grade g 0 ∈ D.criticalCoordinates 0 :=
          Set.mem_union_left _ ⟨g, rfl⟩
        constructor
        · intro h
          apply (oneDimensional_coordinate_le_iff _ _).mpr
          apply (hgrade _ hg).mp
          exact (oneDimensional_coordinate_le_iff _ _).mp h
        · intro h
          apply (oneDimensional_coordinate_le_iff _ _).mpr
          apply (hgrade _ hg).mpr
          exact (oneDimensional_coordinate_le_iff _ _).mp h
      have hY (y : D.relations.Carrier) :
          D.relations.grade y ≤ CoordinateRealBridge.diagonal s ↔
            D.relations.grade y ≤ CoordinateRealBridge.diagonal t := by
        have hy : D.relations.grade y 0 ∈ D.criticalCoordinates 0 :=
          Set.mem_union_right _ ⟨y, rfl⟩
        constructor
        · intro h
          apply (oneDimensional_coordinate_le_iff _ _).mpr
          apply (hgrade _ hy).mp
          exact (oneDimensional_coordinate_le_iff _ _).mp h
        · intro h
          apply (oneDimensional_coordinate_le_iff _ _).mpr
          apply (hgrade _ hy).mpr
          exact (oneDimensional_coordinate_le_iff _ _).mp h
      have hDmap : IsIso
          (structureMap D.presented (CoordinateRealBridge.diagonal.monotone hst)) :=
        D.structureMap_isIso_of_birth_iff (CoordinateRealBridge.diagonal.monotone hst) hG hY
      have hn := e.hom.naturality
        (homOfLE (CoordinateRealBridge.diagonal.monotone hst))
      have hcomp : IsIso
          (e.hom.app (CoordinateRealBridge.diagonal s) ≫
            M.map (homOfLE (CoordinateRealBridge.diagonal.monotone hst))) := by
        rw [← hn]
        exact IsIso.comp_isIso' hDmap (inferInstance : IsIso (e.hom.app (CoordinateRealBridge.diagonal t)))
      have hMmap : IsIso
          (M.map (homOfLE (CoordinateRealBridge.diagonal.monotone hst))) :=
        @IsIso.of_isIso_comp_left _ _ _ _ _
        (e.hom.app (CoordinateRealBridge.diagonal s))
        (M.map (homOfLE (CoordinateRealBridge.diagonal.monotone hst)))
        (inferInstance) hcomp
      change IsIso (M.map (homOfLE (CoordinateRealBridge.diagonal.monotone hst)))
      exact hMmap
  have hfd : ∀ i, FiniteDimensional k (Mreal.obj (c i)) := by
    intro i
    exact GradedFree.finitelyPresented_finiteDimensional M hMlift
      (CoordinateRealBridge.diagonal (c i))
  exact ⟨n, c, by simpa [Mreal] using hgrid, by simpa [Mreal] using hfd⟩

private theorem resolution_kernel_one_isZero
    (M : PModule.{u,0,u} k (Fin 1 → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 1 → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (hL : 0 < R.resolution.length) :
    IsZero (R.resolution.kernel (⟨1, by omega⟩ : Fin (R.resolution.length + 1))) := by
  classical
  by_cases hlt : 1 < R.resolution.length
  · let i : Fin R.resolution.length := ⟨1, hlt⟩
    have hterm : IsZero (R.resolution.term i) := by
      have h :=
        FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
          (k := k) (n := 1) (by omega) M hM R 1 (by omega)
      exact IsZero.of_iso h (eqToIso (R.termAt_eq hlt).symm)
    have hkernel : IsZero (R.resolution.kernel i.castSucc) := by
      apply Functor.isZero
      intro p
      letI hsrc : Subsingleton ((R.resolution.term i).obj p) :=
        ModuleCat.subsingleton_of_isZero (hterm.obj p)
      letI : Subsingleton ((R.resolution.kernel i.castSucc).obj p) := by
        refine ⟨fun x y => ?_⟩
        have hx : x = 0 := by
          obtain ⟨z, hz⟩ := (R.resolution.row_rank_exact i).surjective p x
          have hz0 : z = 0 := hsrc.elim z 0
          simpa [hz0] using hz.symm
        have hy : y = 0 := by
          obtain ⟨z, hz⟩ := (R.resolution.row_rank_exact i).surjective p y
          have hz0 : z = 0 := hsrc.elim z 0
          simpa [hz0] using hz.symm
        exact hx.trans hy.symm
      exact ModuleCat.isZero_of_subsingleton _
    have hidx : i.castSucc = (⟨1, by omega⟩ : Fin (R.resolution.length + 1)) := by
      apply Fin.ext
      rfl
    exact IsZero.of_iso hkernel
      (eqToIso (congrArg R.resolution.kernel hidx))
  · have hlen : R.resolution.length = 1 := by omega
    have hidx : (⟨1, by omega⟩ : Fin (R.resolution.length + 1)) =
        Fin.last R.resolution.length := by
      apply Fin.ext
      simpa [hlen]
    have eK : R.resolution.kernel ⟨1, by omega⟩ ≅ 0 :=
      (eqToIso (congrArg R.resolution.kernel hidx)).trans R.resolution.terminal_iso
    exact IsZero.of_iso (isZero_zero _) eK

/-- In one coordinate, the first term of every supplied minimal resolution is
actually isomorphic to the resolved module.  The degree bound kills the next
term, and the recorded rank-exact row then identifies the degree-zero cover. -/
noncomputable def minimalResolution_degreeZeroIso
    (M : PModule.{u,0,u} k (Fin 1 → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 1 → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    R.termAt 0 ≅ M := by
  classical
  by_cases hzero : R.resolution.length = 0
  · have hlen : R.resolution.length ≤ 0 := by omega
    have hidx : (0 : Fin (R.resolution.length + 1)) = Fin.last R.resolution.length := by
      apply Fin.ext
      simpa [hzero]
    let eK : R.resolution.kernel 0 ≅ 0 :=
      (eqToIso (congrArg R.resolution.kernel hidx)).trans R.resolution.terminal_iso
    exact (eqToIso (R.termAt_eq_zero hlen)).trans
      (eK.symm.trans R.resolution.initial_iso)
  · have hL : 0 < R.resolution.length := Nat.pos_of_ne_zero hzero
    let i : Fin R.resolution.length := ⟨0, hL⟩
    have hK : IsZero (R.resolution.kernel i.succ) := by
      simpa [i] using resolution_kernel_one_isZero M hM R hL
    let q := R.resolution.quotient i
    have hinj : ∀ p, Function.Injective (q.app p).hom := by
      intro p
      letI hsrc : Subsingleton ((R.resolution.kernel i.succ).obj p) :=
        ModuleCat.subsingleton_of_isZero (hK.obj p)
      let hs := R.resolution.row_rank_exact i
      have hker : LinearMap.ker (q.app p).hom = ⊥ := by
        ext x
        constructor
        · intro hx
          have hx' : x ∈ LinearMap.range ((R.resolution.inclusion i).app p).hom := by
            rw [hs.range_eq_ker p]
            exact hx
          obtain ⟨z, hz⟩ := hx'
          have hz0 : z = 0 := hsrc.elim z 0
          have hx0 : x = 0 := by
            simpa [hz0] using hz.symm
          simpa using hx0
        · intro hx
          have hx0 : x = 0 := by simpa using hx
          simp [hx0]
      exact LinearMap.ker_eq_bot.mp hker
    have hsurj : ∀ p, Function.Surjective (q.app p).hom :=
      fun p => (R.resolution.row_rank_exact i).surjective p
    let e (p : Fin 1 → ℝ) :
        (R.resolution.term i).obj p ≃ₗ[k] (R.resolution.kernel i.castSucc).obj p :=
      LinearEquiv.ofBijective (q.app p).hom ⟨hinj p, hsurj p⟩
    have hqIso : R.resolution.term i ≅ R.resolution.kernel i.castSucc :=
      NatIso.ofComponents (fun p => (e p).toModuleIso) (by
        intro a b f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hn := congrArg (fun g => g.hom x) (q.naturality f)
        change (q.app b).hom (((R.resolution.term i).map f).hom x) =
          ((R.resolution.kernel i.castSucc).map f).hom ((q.app a).hom x) at hn
        change (q.app b).hom (((R.resolution.term i).map f).hom x) =
          ((R.resolution.kernel i.castSucc).map f).hom ((q.app a).hom x)
        exact hn)
    have hidx : i.castSucc = (0 : Fin (R.resolution.length + 1)) := by
      apply Fin.ext
      rfl
    exact (eqToIso (R.termAt_eq hL)).trans
      (hqIso.trans ((eqToIso (congrArg R.resolution.kernel hidx)).trans
        R.resolution.initial_iso))

/-- In one coordinate the actual signed terms reduce to degree zero by
vanishing of every positive resolution term, with no cancellation. -/
theorem MinimalFiniteRankProjectiveResolution.signedHookBarcode_eq_degreeZero
    (M : PModule.{u,0,u} k (Fin 1 → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (P : FiniteHookSumPresentation (k := k) (n := 1) (R.termAt 0)) :
    (R.signedHookBarcode (k := k) (n := 1) (by omega) M
      (GradedFree.finitelyPresented_liftIndexUniverse M hM)).positive =
        hookTagMultiset P.tag ∧
    (R.signedHookBarcode (k := k) (n := 1) (by omega) M
      (GradedFree.finitelyPresented_liftIndexUniverse M hM)).negative = 0 := by
  let hM' := GradedFree.finitelyPresented_liftIndexUniverse M hM
  have hterm (j : ℕ) (hj : 0 < j) : IsZero (R.termAt j) := by
    exact FiniteRankProjectiveResolution.finitelyPresented_minimalFiniteRankProjectiveResolution_termAt_isZero
      (k := k) (n := 1) (by omega) M hM R j (by omega)
  have hbetti_zero (j : ℕ) (hj : 0 < j) :
      R.hookBettiMultiset (k := k) (n := 1) (by omega) M hM' j = 0 :=
    R.hookBettiMultiset_eq_zero_of_term_isZero (by omega) M hM' (hterm j hj)
  have hbetti_tag :
      R.hookBettiMultiset (k := k) (n := 1) (by omega) M hM' 0 =
        hookTagMultiset P.tag :=
    R.hookBettiMultiset_eq_tagMultiset (by omega) M hM' 0 P
  have heven :
      R.evenHookBetti (k := k) (n := 1) (by omega) M hM' =
        hookTagMultiset P.tag := by
    have hsum : R.evenHookBetti (k := k) (n := 1) (by omega) M hM' =
        R.hookBettiMultiset (k := k) (n := 1) (by omega) M hM' 0 := by
      classical
      by_cases hL : 0 < R.resolution.length
      · have h0 : 0 ∈ evenHookDegrees R.resolution.length := by
          simp [evenHookDegrees, hL]
        unfold MinimalFiniteRankProjectiveResolution.evenHookBetti evenHookDegrees
        rw [Finset.sum_eq_single 0]
        · intro j hj hj0
          have hjpos : 0 < j := by omega
          exact hbetti_zero j hjpos
        · intro hnot
          exact (hnot h0).elim
      · have hL0 : R.resolution.length = 0 := by omega
        have hzero := R.hookBettiMultiset_eq_zero_of_length_le
          (by omega) M hM' (j := 0) (by omega)
        simp [MinimalFiniteRankProjectiveResolution.evenHookBetti,
          evenHookDegrees, hL0, hzero]
    exact hsum.trans hbetti_tag
  have hodd : R.oddHookBetti (k := k) (n := 1) (by omega) M hM' = 0 := by
    classical
    unfold MinimalFiniteRankProjectiveResolution.oddHookBetti oddHookDegrees
    apply Finset.sum_eq_zero
    intro j hj
    have hoddj : Odd j := (Finset.mem_filter.mp hj).2
    exact hbetti_zero j hoddj.pos
  change (R.evenHookBetti (k := k) (n := 1) (by omega) M hM' =
        hookTagMultiset P.tag) ∧
      (R.oddHookBetti (k := k) (n := 1) (by omega) M hM' = 0)
  exact ⟨heven, hodd⟩

/-- The ordinary positive diagram of a signed hook barcode is the exact
endpoint image of its positive occurrence multiset. -/
noncomputable def oneDimensionalPositiveBarcodeDiagram
    (C : SignedHookBarcode 1) : Diagram ℝ where
  points := Multiset.map oneDimensionalHookEndpoints C.positive
  offDiagonal := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hp
    exact ne_of_lt (oneDimensionalHookEndpoints_positive t)

/-- Endpoint images of actual hooks are positive ordinary intervals. -/
theorem oneDimensionalPositiveBarcodeDiagram_isPositive
    (C : SignedHookBarcode 1) :
    (oneDimensionalPositiveBarcodeDiagram C).IsPositive := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hp
  exact oneDimensionalHookEndpoints_positive t

/-- The ordinary diagram attached to the existing module-level signed hook
barcode choice. The input is only the original finite presentation of its
one-coordinate module. -/
noncomputable def finitelyPresentedOneDimensionalBarcodeDiagram
    (M : PModule.{u,0,u} k ℝ)
    (hX : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M)) : Diagram ℝ :=
  oneDimensionalPositiveBarcodeDiagram
    (TDA.Persistence.finitelyPresentedSignedHookBarcode (k := k) (n := 1)
      (by omega) (CoordinateRealBridge.fromReal M) hX)

theorem finitelyPresentedOneDimensionalBarcodeDiagram_isPositive
    (M : PModule.{u,0,u} k ℝ)
    (hX : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M)) :
    (finitelyPresentedOneDimensionalBarcodeDiagram M hX).IsPositive :=
  oneDimensionalPositiveBarcodeDiagram_isPositive _

/-- A supplied resolution's actual degree-zero hook presentation has the same
endpoint diagram as the existing module-level signed choice. -/
theorem finitelyPresentedOneDimensionalBarcodeDiagram_eq_resolution
    (M : PModule.{u,0,u} k ℝ)
    (hX : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M))
    (R : MinimalFiniteRankProjectiveResolution
      (k := k) (M := CoordinateRealBridge.fromReal M))
    (P : FiniteHookSumPresentation (k := k) (n := 1)
      (R.termAt 0)) :
    finitelyPresentedOneDimensionalBarcodeDiagram M hX =
      oneDimensionalHookDiagram P.tag := by
  let X := CoordinateRealBridge.fromReal M
  let hX' := GradedFree.finitelyPresented_liftIndexUniverse X hX
  have hchoice := TDA.Persistence.finitelyPresentedSignedHookBarcode_eq
    (k := k) (n := 1) (by omega) X hX R
  have hterms := R.signedHookBarcode_eq_degreeZero X hX P
  have hpositive :
      (TDA.Persistence.finitelyPresentedSignedHookBarcode (k := k) (n := 1)
        (by omega) X hX).positive = hookTagMultiset P.tag := by
    exact (congrArg (fun C : SignedHookBarcode 1 => C.positive) hchoice).trans
      hterms.1
  apply Diagram.ext
  change Multiset.map oneDimensionalHookEndpoints
      (TDA.Persistence.finitelyPresentedSignedHookBarcode (k := k) (n := 1)
        (by omega) X hX).positive =
    (oneDimensionalHookDiagram P.tag).points
  rw [hpositive, oneDimensionalHookDiagram_points]

/-- Transport an actual degree-zero hook presentation to the module itself. -/
noncomputable def degreeZeroHookPresentation
    (M : PModule.{u,0,u} k ℝ)
    (hX : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M))
    (R : MinimalFiniteRankProjectiveResolution
      (k := k) (M := CoordinateRealBridge.fromReal M)) :
    FiniteHookSumPresentation (k := k) (n := 1)
      (CoordinateRealBridge.fromReal M) := by
  let X := CoordinateRealBridge.fromReal M
  let hX' := GradedFree.finitelyPresented_liftIndexUniverse X hX
  let P := Classical.choice
    (R.exists_hook_sum_presentation (k := k) (n := 1) (by omega) X hX' 0)
  exact ⟨P.count, P.tag,
    (minimalResolution_degreeZeroIso (k := k) X hX R).symm.trans P.iso⟩

/-- Under the original finite-presentation hypothesis, the module is actually
realized by the ordinary positive endpoint diagram of its signed barcode. -/
noncomputable def finitelyPresentedOneDimensionalBarcodeRealizationIso
    (M : PModule.{u,0,u} k ℝ)
    (hX : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M)) :
    M ≅ RealBarcode.realize (k := k)
      (finitelyPresentedOneDimensionalBarcodeDiagram M hX) := by
  let R := Classical.choice
    (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      (k := k) (n := 1) (by omega) (CoordinateRealBridge.fromReal M) hX)
  let X := CoordinateRealBridge.fromReal M
  let hX' := GradedFree.finitelyPresented_liftIndexUniverse X hX
  let P0 := Classical.choice
    (R.exists_hook_sum_presentation (k := k) (n := 1) (by omega) X hX' 0)
  let P : FiniteHookSumPresentation (k := k) (n := 1) X :=
    ⟨P0.count, P0.tag,
      (minimalResolution_degreeZeroIso (k := k) X hX R).symm.trans P0.iso⟩
  have eX : CoordinateRealBridge.fromReal M ≅
      CoordinateRealBridge.fromReal
        (RealBarcode.realize (k := k) (oneDimensionalHookDiagram P.tag)) :=
    finiteHookSum_realizationIso (k := k) P
  have hdiagram := finitelyPresentedOneDimensionalBarcodeDiagram_eq_resolution
    (k := k) M hX R P0
  have eReal : CoordinateRealBridge.fromReal M ≅
      CoordinateRealBridge.fromReal
        (RealBarcode.realize (k := k)
          (finitelyPresentedOneDimensionalBarcodeDiagram M hX)) :=
    eX ≪≫ eqToIso (congrArg
      (fun D => CoordinateRealBridge.fromReal (RealBarcode.realize (k := k) D))
      hdiagram.symm)
  exact (oneDimensionalDiagonalFromRealIso (k := k) M).symm ≪≫
    oneDimensionalReindexDiagonalIso (k := k) eReal ≪≫
    oneDimensionalDiagonalFromRealIso (k := k)
      (RealBarcode.realize (k := k)
        (finitelyPresentedOneDimensionalBarcodeDiagram M hX))

private theorem oneDimensionalIsConstructible_of_iso
    {r : ℕ} {c : Fin r ↪o ℝ} {M N : PModule.{u,0,u} k ℝ}
    (e : M ≅ N) (hM : FiniteConstructible.IsConstructible c M) :
    FiniteConstructible.IsConstructible c N := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact IsZero.of_iso (hM.zero_left t ht) (e.app t).symm
  · intro s t hst hcell
    have hMmap : IsIso (structureMap M hst) := hM.isIso_map s t hst hcell
    have hn := e.hom.naturality (homOfLE hst)
    have hcomp : IsIso (e.hom.app s ≫ structureMap N hst) := by
      change IsIso (e.hom.app s ≫ N.map (homOfLE hst))
      rw [hn.symm]
      exact IsIso.comp_isIso' hMmap (inferInstance : IsIso (e.hom.app t))
    exact @IsIso.of_isIso_comp_left _ _ _ _ _
      (e.hom.app s) (structureMap N hst) (inferInstance) hcomp

/-- The original finite presentation of `CoordinateRealBridge.fromReal M`
internally supplies a finite constructibility grid for the real module M. -/
theorem finitelyPresented_exists_oneDimensionalConstructible
    (M : PModule.{u,0,u} k ℝ)
    (hX : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M)) :
    ∃ r : ℕ, ∃ c : Fin r ↪o ℝ,
      FiniteConstructible.IsConstructible c M ∧
      ∀ i, FiniteDimensional k (M.obj (c i)) := by
  obtain ⟨r, c, hC, _hfd⟩ :=
    finitelyPresented_oneDimensional_constructible
      (k := k) (CoordinateRealBridge.fromReal M) hX
  let e := oneDimensionalDiagonalFromRealIso (k := k) M
  have hCM := oneDimensionalIsConstructible_of_iso (k := k) e hC
  let X := CoordinateRealBridge.fromReal M
  let hX' := GradedFree.finitelyPresented_liftIndexUniverse X hX
  have hfd : ∀ i, FiniteDimensional k (M.obj (c i)) := by
    intro i
    exact GradedFree.finitelyPresented_finiteDimensional X hX'
      (CoordinateRealBridge.diagonal (c i))
  exact ⟨r, c, hCM, hfd⟩

/-- Every admissible existing finite-constructible diagram has exactly the
endpoint multiset of the original module-level signed hook choice. -/
theorem finitelyPresentedOneDimensionalBarcodeDiagram_eq_moduleDiagram
    (M : PModule.{u,0,u} k ℝ)
    (hX : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M))
    {r : ℕ} (c : Fin r ↪o ℝ)
    (hC : FiniteConstructible.IsConstructible c M)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) :
    finitelyPresentedOneDimensionalBarcodeDiagram M hX =
      FiniteConstructible.moduleDiagram c M hfd := by
  let X := CoordinateRealBridge.fromReal M
  let hX' := GradedFree.finitelyPresented_liftIndexUniverse X hX
  let R := Classical.choice
    (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      (k := k) (n := 1) (by omega) X hX)
  let P0 := Classical.choice
    (R.exists_hook_sum_presentation (k := k) (n := 1) (by omega) X hX' 0)
  let PX : FiniteHookSumPresentation (k := k) (n := 1) X :=
    ⟨P0.count, P0.tag,
      (minimalResolution_degreeZeroIso (k := k) X hX R).symm.trans P0.iso⟩
  let D := FiniteConstructible.moduleDiagram c M hfd
  let Q := positiveDiagram_hookPresentation (k := k) D
    (FiniteConstructible.moduleDiagram_isPositive c M hfd)
  have e : X ≅ CoordinateRealBridge.fromReal (RealBarcode.realize (k := k) D) :=
    oneDimensionalFromRealIso (k := k)
      (FiniteConstructible.barcodeRealizationIso c M hC hfd)
  have htags : hookTagMultiset PX.tag = hookTagMultiset Q.tag :=
    PX.tagMultiset_eq_of_iso Q e
  have hPQ : oneDimensionalHookDiagram P0.tag = oneDimensionalHookDiagram Q.tag := by
    apply Diagram.ext
    rw [oneDimensionalHookDiagram_points, oneDimensionalHookDiagram_points, htags]
  have hP := finitelyPresentedOneDimensionalBarcodeDiagram_eq_resolution
    (k := k) M hX R P0
  have hQ := positiveDiagram_hookPresentation_diagram (k := k) D
    (FiniteConstructible.moduleDiagram_isPositive c M hfd)
  calc
    finitelyPresentedOneDimensionalBarcodeDiagram M hX =
        oneDimensionalHookDiagram P0.tag := hP
    _ = oneDimensionalHookDiagram Q.tag := hPQ
    _ = D := hQ

/-- The barcode built from the original finite presentation is isometric to
the real interleaving distance.  The finite-constructibility grid and its
fiber finiteness are derived from that presentation inside the proof. -/
theorem finitelyPresentedOneDimensionalBarcode_bottleneck_eq_distance
    (M N : PModule.{u,0,u} k ℝ)
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M))
    (hN : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal N)) :
    bottleneck (finitelyPresentedOneDimensionalBarcodeDiagram M hM)
        (finitelyPresentedOneDimensionalBarcodeDiagram N hN) =
      realInterleavingDistance M N := by
  obtain ⟨r, c, hC, hfd⟩ :=
    finitelyPresented_exists_oneDimensionalConstructible (k := k) M hM
  obtain ⟨s, d, hD, hgd⟩ :=
    finitelyPresented_exists_oneDimensionalConstructible (k := k) N hN
  rw [finitelyPresentedOneDimensionalBarcodeDiagram_eq_moduleDiagram
      (k := k) M hM c hC hfd,
    finitelyPresentedOneDimensionalBarcodeDiagram_eq_moduleDiagram
      (k := k) N hN d hD hgd]
  exact FiniteConstructible.bottleneck_eq_distance hC hD hfd hgd

/-- The same ordinary barcode isometry expressed with the one-coordinate
interleaving distance on the original real modules. -/
theorem finitelyPresentedOneDimensionalBarcode_bottleneck_eq_coordinateDistance
    (M N : PModule.{u,0,u} k ℝ)
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal M))
    (hN : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin 1 → ℝ) (CoordinateRealBridge.fromReal N)) :
    bottleneck (finitelyPresentedOneDimensionalBarcodeDiagram M hM)
        (finitelyPresentedOneDimensionalBarcodeDiagram N hN) =
      coordinateInterleavingDistance (CoordinateRealBridge.fromReal M)
        (CoordinateRealBridge.fromReal N) := by
  rw [finitelyPresentedOneDimensionalBarcode_bottleneck_eq_distance
    (k := k) M N hM hN, ← CoordinateRealBridge.distance_eq M N]

end TDA.Persistence
