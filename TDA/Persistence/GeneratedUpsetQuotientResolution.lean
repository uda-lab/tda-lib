import TDA.Persistence.GeneratedUpsetResolutionMap
import TDA.Persistence.RankExactGenerated
import TDA.Persistence.HookCokernel
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Hook quotients of generated-upset resolutions

For an occurrence-indexed finite family in a lattice with bottom, the inclusion into the
constant-bottom family induces a quotient of augmented resolutions. Its degree `r` is the
categorical cokernel on faces with `r + 1` occurrences. The quotient sequence is exact,
vanishes in degrees at least the family size, and has bottom-generated hook terms.
The construction is the quotient-resolution step of Botnan et al.,
arXiv:2208.00300v3, Proposition 5.14, using Proposition 5.1 and Lemmas 5.12–5.13.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GeneratedUpsetQuotientResolution

open CategoryTheory CategoryTheory.Limits
open scoped Classical
open GeneratedUpsetResolution GeneratedUpsetResolutionMap

variable {k : Type u} [Field k] {P : Type} [Lattice P] [OrderBot P]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The constant-bottom family, with the same occurrences as the given family. -/
abbrev bottomFamily (m : ℕ) : Fin m → P := fun _ => ⊥

/-- The actual inclusion of the degree-`r` resolutions. -/
noncomputable def inclusion {m : ℕ} (f : Fin m → P) (r : ℕ) :
    GeneratedUpsetResolution.term (k := k) f r ⟶
      GeneratedUpsetResolution.term (k := k) (bottomFamily m) r :=
  resolutionMap (f := f) (g := bottomFamily m) (fun _ => bot_le) r

/-- The actual inclusion of augmented support modules. -/
noncomputable def supportInclusion {m : ℕ} (f : Fin m → P) :=
  supportMap (k := k) (f := f) (g := bottomFamily m) (fun _ => bot_le)

/-- The degree-`r` categorical quotient of the two resolutions. -/
noncomputable abbrev term {m : ℕ} (f : Fin m → P) (r : ℕ) : PModule.{u,0,u} k P :=
  cokernel (inclusion (k := k) f r)

/-- The categorical quotient of the augmented support modules. -/
noncomputable abbrev target {m : ℕ} (f : Fin m → P) : PModule.{u,0,u} k P :=
  cokernel (supportInclusion (k := k) f)

/-- The differential induced by the original alternating deletion differential. -/
noncomputable def differential {m : ℕ} (f : Fin m → P) (r : ℕ) :
    term (k := k) f (r + 1) ⟶ term (k := k) f r :=
  cokernel.desc (inclusion (k := k) f (r + 1))
    (GeneratedUpsetResolution.differential (k := k) (bottomFamily m) r ≫
      cokernel.π (inclusion (k := k) f r)) (by
        rw [← Category.assoc, inclusion, resolutionMap_differential (g := bottomFamily m), Category.assoc]
        change GeneratedUpsetResolution.differential (k := k) f r ≫
          inclusion (k := k) f r ≫ cokernel.π (inclusion (k := k) f r) = 0
        rw [cokernel.condition, comp_zero])

/-- The augmentation induced by the original generated-support augmentation. -/
noncomputable def augmentation {m : ℕ} (f : Fin m → P) :
    term (k := k) f 0 ⟶ target (k := k) f :=
  cokernel.desc (inclusion (k := k) f 0)
    (GeneratedUpsetResolution.augmentation (k := k) (bottomFamily m) ≫
      cokernel.π (supportInclusion (k := k) f)) (by
        rw [← Category.assoc, inclusion, resolutionMap_augmentation (g := bottomFamily m), Category.assoc]
        change GeneratedUpsetResolution.augmentation (k := k) f ≫
          supportInclusion (k := k) f ≫ cokernel.π (supportInclusion (k := k) f) = 0
        rw [cokernel.condition, comp_zero])

/-- The induced differential commutes with the actual cokernel projections. -/
@[reassoc (attr := simp)] theorem projection_differential {m : ℕ}
    (f : Fin m → P) (r : ℕ) :
    cokernel.π (inclusion (k := k) f (r + 1)) ≫ differential (k := k) f r =
      GeneratedUpsetResolution.differential (k := k) (bottomFamily m) r ≫
        cokernel.π (inclusion (k := k) f r) := by
  apply cokernel.π_desc

/-- The induced augmentation commutes with the actual cokernel projections. -/
@[reassoc (attr := simp)] theorem projection_augmentation {m : ℕ} (f : Fin m → P) :
    cokernel.π (inclusion (k := k) f 0) ≫ augmentation (k := k) f =
      GeneratedUpsetResolution.augmentation (k := k) (bottomFamily m) ≫
        cokernel.π (supportInclusion (k := k) f) := by
  apply cokernel.π_desc

/-- Consecutive quotient differentials compose to zero. -/
theorem differential_comp_differential {m : ℕ} (f : Fin m → P) (r : ℕ) :
    differential (k := k) f (r + 1) ≫ differential (k := k) f r = 0 := by
  apply (cancel_epi (cokernel.π (inclusion (k := k) f (r + 2)))).mp
  rw [← Category.assoc, projection_differential, Category.assoc,
    projection_differential, ← Category.assoc,
    GeneratedUpsetResolution.differential_comp_differential, zero_comp, comp_zero]

/-- The degree-zero quotient differential is killed by the quotient augmentation. -/
theorem differential_comp_augmentation {m : ℕ} (f : Fin m → P) :
    differential (k := k) f 0 ≫ augmentation (k := k) f = 0 := by
  apply (cancel_epi (cokernel.π (inclusion (k := k) f 1))).mp
  rw [← Category.assoc, projection_differential, Category.assoc,
    projection_augmentation, ← Category.assoc,
    GeneratedUpsetResolution.differential_comp_augmentation, zero_comp, comp_zero]

omit [OrderBot P] in
private theorem cokernel_range_eq_ker {M N : PModule.{u,0,u} k P}
    (a : M ⟶ N) (p : P) :
    LinearMap.range (a.app p).hom = LinearMap.ker ((cokernel.π a).app p).hom := by
  have h := (ShortComplex.exact_cokernel a).map_of_epi_of_preservesCokernel
    ((evaluation P (ModuleCat k)).obj p) inferInstance inferInstance
  exact h.moduleCat_range_eq_ker

omit [OrderBot P] in
private theorem cokernel_projection_zero_iff {M N : PModule.{u,0,u} k P}
    (a : M ⟶ N) (p : P) (x : N.obj p) :
    ((cokernel.π a).app p).hom x = 0 ↔ x ∈ LinearMap.range (a.app p).hom := by
  rw [cokernel_range_eq_ker]
  rfl

omit [OrderBot P] in
private theorem comp_apply {M N O : PModule.{u,0,u} k P}
    {a : M ⟶ N} {b : N ⟶ O} {c : M ⟶ O} (h : a ≫ b = c)
    (p : P) (x : M.obj p) : (b.app p).hom ((a.app p).hom x) = (c.app p).hom x :=
  congrArg (fun t : M ⟶ O => (t.app p).hom x) h

omit [OrderBot P] in
private theorem quotient_exact_at
    {A B C A' B' C' : PModule.{u,0,u} k P}
    (uA : A ⟶ A') (uB : B ⟶ B') (uC : C ⟶ C')
    (b : B ⟶ C) (a' : A' ⟶ B') (b' : B' ⟶ C')
    (dA : cokernel uA ⟶ cokernel uB) (dB : cokernel uB ⟶ cokernel uC)
    (hA : cokernel.π uA ≫ dA = a' ≫ cokernel.π uB)
    (hB : cokernel.π uB ≫ dB = b' ≫ cokernel.π uC)
    (hsquare : uB ≫ b' = b ≫ uC)
    (htarget : ∀ p (x : B'.obj p), (b'.app p).hom x = 0 →
      ∃ y, (a'.app p).hom y = x)
    (hsource : ∀ p (x : C.obj p) (y : B'.obj p),
      (uC.app p).hom x = (b'.app p).hom y → ∃ z, (b.app p).hom z = x)
    (p : P) (x : (cokernel uB).obj p) (hx : (dB.app p).hom x = 0) :
    ∃ y, (dA.app p).hom y = x := by
  obtain ⟨x', rfl⟩ := GeneratedAtBottom.cokernel_projection_surjective uB p x
  have hcycle : ((cokernel.π uC).app p).hom ((b'.app p).hom x') = 0 := by
    have he := comp_apply hB p x'
    simpa only [NatTrans.comp_app, ModuleCat.comp_apply] using he.symm.trans hx
  obtain ⟨z, hz⟩ := (cokernel_projection_zero_iff uC p _).mp hcycle
  obtain ⟨w, hw⟩ := hsource p z x' hz
  have hcycle' : (b'.app p).hom (x' - (uB.app p).hom w) = 0 := by
    rw [map_sub, comp_apply hsquare p w]
    change (b'.app p).hom x' - (uC.app p).hom ((b.app p).hom w) = 0
    rw [hw, hz, sub_self]
  obtain ⟨y, hy⟩ := htarget p _ hcycle'
  refine ⟨((cokernel.π uA).app p).hom y, ?_⟩
  rw [comp_apply hA p y]
  change ((cokernel.π uB).app p).hom ((a'.app p).hom y) = _
  rw [hy, map_sub]
  have hzero : ((cokernel.π uB).app p).hom ((uB.app p).hom w) = 0 :=
    (cokernel_projection_zero_iff uB p _).mpr ⟨w, rfl⟩
  rw [hzero, sub_zero]

/-- The augmented quotient is surjective at every lattice element. -/
theorem augmentation_surjective_at {m : ℕ} (f : Fin m → P) (p : P) :
    Function.Surjective ((augmentation (k := k) f).app p).hom := by
  intro z
  obtain ⟨x, rfl⟩ := GeneratedAtBottom.cokernel_projection_surjective
    (supportInclusion (k := k) f) p z
  obtain ⟨y, rfl⟩ := GeneratedUpsetResolution.augmentation_surjective_at
    (k := k) (bottomFamily m) p x
  exact ⟨((cokernel.π (inclusion (k := k) f 0)).app p).hom y,
    comp_apply (projection_augmentation (k := k) f) p y⟩

/-- Every positive-degree cycle in the quotient resolution is a boundary. -/
theorem differential_exact_at_succ {m : ℕ} (f : Fin m → P) (p : P) (r : ℕ)
    (x : (term (k := k) f (r + 1)).obj p)
    (hx : ((differential (k := k) f r).app p).hom x = 0) :
    ∃ y : (term (k := k) f (r + 2)).obj p,
      ((differential (k := k) f (r + 1)).app p).hom y = x := by
  refine quotient_exact_at _ _ _
    (GeneratedUpsetResolution.differential (k := k) f r) _ _ _ _
    (projection_differential f (r + 1)) (projection_differential f r)
    (resolutionMap_differential (g := bottomFamily m) (fun _ => bot_le) r)
    (fun p y hy => GeneratedUpsetResolution.differential_exact_at_succ
      (bottomFamily m) p r y hy) ?_ p x hx
  intro q z y hz
  cases r with
  | zero =>
    apply GeneratedUpsetResolution.augmentation_exact_at_zero (k := k) f q z
    apply supportMap_app_injective (k := k) (g := bottomFamily m) (fun _ => bot_le) q
    rw [map_zero]
    have hs := comp_apply (resolutionMap_augmentation (k := k)
      (f := f) (g := bottomFamily m) (fun _ => bot_le)) q z
    change ((GeneratedUpsetResolution.augmentation (k := k) (bottomFamily m)).app q).hom
      (((inclusion (k := k) f 0).app q).hom z) =
      ((supportInclusion (k := k) f).app q).hom
        (((GeneratedUpsetResolution.augmentation (k := k) f).app q).hom z) at hs
    change ((supportInclusion (k := k) f).app q).hom
      (((GeneratedUpsetResolution.augmentation (k := k) f).app q).hom z) = 0
    rw [← hs, hz]
    exact comp_apply (GeneratedUpsetResolution.differential_comp_augmentation
      (k := k) (bottomFamily m)) q y
  | succ r =>
    apply GeneratedUpsetResolution.differential_exact_at_succ (k := k) f q r z
    apply resolutionMap_app_injective (k := k) (g := bottomFamily m)
      (fun _ => bot_le) r q
    rw [map_zero]
    have hs := comp_apply (resolutionMap_differential (k := k)
      (f := f) (g := bottomFamily m) (fun _ => bot_le) r) q z
    change ((GeneratedUpsetResolution.differential (k := k) (bottomFamily m) r).app q).hom
      (((inclusion (k := k) f (r + 1)).app q).hom z) =
      ((inclusion (k := k) f r).app q).hom
        (((GeneratedUpsetResolution.differential (k := k) f r).app q).hom z) at hs
    change ((inclusion (k := k) f r).app q).hom
      (((GeneratedUpsetResolution.differential (k := k) f r).app q).hom z) = 0
    rw [← hs, hz]
    exact comp_apply (GeneratedUpsetResolution.differential_comp_differential
      (k := k) (bottomFamily m) r) q y

/-- Every degree-zero quotient cycle is a boundary. -/
theorem augmentation_exact_at_zero {m : ℕ} (f : Fin m → P) (p : P)
    (x : (term (k := k) f 0).obj p)
    (hx : ((augmentation (k := k) f).app p).hom x = 0) :
    ∃ y : (term (k := k) f 1).obj p,
      ((differential (k := k) f 0).app p).hom y = x := by
  exact quotient_exact_at _ _ _ (GeneratedUpsetResolution.augmentation (k := k) f)
    _ _ _ _ (projection_differential f 0) (projection_augmentation f)
    (resolutionMap_augmentation (g := bottomFamily m) (fun _ => bot_le))
    (fun p y hy => GeneratedUpsetResolution.augmentation_exact_at_zero
      (bottomFamily m) p y hy)
    (fun p z _ _ => GeneratedUpsetResolution.augmentation_surjective_at f p z) p x hx

/-- The constant-bottom face birth is bottom in every nonempty occurrence face. -/
@[simp] theorem faceJoin_bottom {m r : ℕ} (A : FaceIndex m r) :
    faceJoin (bottomFamily (P := P) m) A = ⊥ := by
  apply le_antisymm
  · exact (faceJoin_le_iff _ _ _).mpr (fun _ _ => le_rfl)
  · exact bot_le

private noncomputable abbrev rawHook {m r : ℕ} (f : Fin m → P) (A : FaceIndex m r) :=
  Hook.module (k := k) (faceJoin (bottomFamily m) A) (faceJoin f A)

private theorem faceMap_eq_hookInclusion {m r : ℕ} (f : Fin m → P)
    (A : FaceIndex m r) :
    faceMap (k := k) (f := f) (g := bottomFamily m) (fun _ => bot_le) A =
      HookCokernel.inclusion (faceJoin_le_of_pointwise_le
        (f := f) (g := bottomFamily m) (fun _ => bot_le) A) := rfl

private noncomputable def rawProjection {m : ℕ} (f : Fin m → P) (r : ℕ) :
    GeneratedUpsetResolution.term (k := k) (bottomFamily m) r ⟶
      ⨁ (rawHook (k := k) (r := r) f) := by
  classical
  exact biproduct.map (fun A => HookCokernel.projection
    (faceJoin (bottomFamily m) A) (faceJoin f A))

private theorem rawProjection_ι {m : ℕ} (f : Fin m → P) (r : ℕ)
    (A : FaceIndex m r) :
    biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) (bottomFamily m) B) A ≫
      rawProjection (k := k) f r =
      HookCokernel.projection (faceJoin (bottomFamily m) A) (faceJoin f A) ≫
        biproduct.ι (rawHook (k := k) f) A := by
  classical
  exact biproduct.ι_map (fun B : FaceIndex m r => HookCokernel.projection
    (faceJoin (bottomFamily m) B) (faceJoin f B)) A

private theorem inclusion_rawProjection {m : ℕ} (f : Fin m → P) (r : ℕ) :
    inclusion (k := k) f r ≫ rawProjection (k := k) f r = 0 := by
  classical
  apply biproduct.hom_ext'
  intro A
  rw [← Category.assoc, inclusion, resolutionMap_ι, Category.assoc,
    rawProjection_ι, ← Category.assoc, faceMap_eq_hookInclusion,
    HookCokernel.inclusion_projection, zero_comp, comp_zero]

private noncomputable def rawDesc {m : ℕ} (f : Fin m → P) (r : ℕ)
    {M : PModule.{u,0,u} k P}
    (φ : GeneratedUpsetResolution.term (k := k) (bottomFamily m) r ⟶ M)
    (hφ : inclusion (k := k) f r ≫ φ = 0) : ⨁ (rawHook (k := k) (r := r) f) ⟶ M := by
  classical
  refine biproduct.desc (fun A => HookCokernel.desc
    (faceJoin_le_of_pointwise_le (f := f) (g := bottomFamily m) (fun _ => bot_le) A)
    (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) (bottomFamily m) B) A ≫ φ)
    ?_)
  rw [← faceMap_eq_hookInclusion, ← Category.assoc, ← resolutionMap_ι, Category.assoc]
  change biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A ≫
    (inclusion (k := k) f r ≫ φ) = 0
  rw [hφ, comp_zero]

private theorem rawProjection_desc {m : ℕ} (f : Fin m → P) (r : ℕ)
    {M : PModule.{u,0,u} k P}
    (φ : GeneratedUpsetResolution.term (k := k) (bottomFamily m) r ⟶ M)
    (hφ : inclusion (k := k) f r ≫ φ = 0) :
    rawProjection (k := k) f r ≫ rawDesc f r φ hφ = φ := by
  classical
  apply biproduct.hom_ext'
  intro A
  rw [← Category.assoc, rawProjection_ι, Category.assoc]
  simp only [rawDesc, biproduct.ι_desc]
  exact HookCokernel.projection_desc _ _ _

private theorem rawProjection_hom_ext {m : ℕ} (f : Fin m → P) (r : ℕ)
    {M : PModule.{u,0,u} k P} {a b : ⨁ (rawHook (k := k) (r := r) f) ⟶ M}
    (h : rawProjection (k := k) f r ≫ a = rawProjection f r ≫ b) : a = b := by
  classical
  apply biproduct.hom_ext'
  intro A
  apply HookCokernel.hom_ext
    (faceJoin_le_of_pointwise_le (f := f) (g := bottomFamily m) (fun _ => bot_le) A)
  have he := congrArg (fun t => biproduct.ι
    (fun B : FaceIndex m r => faceModule (k := k) (bottomFamily m) B) A ≫ t) h
  simpa only [← Category.assoc, rawProjection_ι] using he

private noncomputable def rawIsCokernel {m : ℕ} (f : Fin m → P) (r : ℕ) :
    IsColimit (CokernelCofork.ofπ (rawProjection (k := k) f r)
      (inclusion_rawProjection f r)) :=
  CokernelCofork.IsColimit.ofπ _ _ (rawDesc f r) (rawProjection_desc f r)
    (fun φ hφ _m hm => rawProjection_hom_ext f r
      (hm.trans (rawProjection_desc f r φ hφ).symm))

private noncomputable def rawIso {m : ℕ} (f : Fin m → P) (r : ℕ) :
    term (k := k) f r ≅ ⨁ (rawHook (k := k) (r := r) f) :=
  (cokernelIsCokernel (inclusion (k := k) f r)).coconePointUniqueUpToIso
    (rawIsCokernel f r)

private theorem projection_rawIso {m : ℕ} (f : Fin m → P) (r : ℕ) :
    cokernel.π (inclusion (k := k) f r) ≫ (rawIso f r).hom = rawProjection f r :=
  (cokernelIsCokernel (inclusion (k := k) f r)).comp_coconePointUniqueUpToIso_hom
    (rawIsCokernel f r) WalkingParallelPair.one

/-- Replacing the constant-bottom face birth by bottom in its hook. -/
noncomputable def faceHookIso {m r : ℕ} (f : Fin m → P) (A : FaceIndex m r) :
    Hook.module (k := k) (faceJoin (bottomFamily m) A) (faceJoin f A) ≅
      Hook.module (k := k) ⊥ (faceJoin f A) :=
  eqToIso (by simp only [faceJoin_bottom])

/-- The quotient term is the finite hook sum indexed by occurrence faces of size `r + 1`. -/
noncomputable def hookSumIso {m : ℕ} (f : Fin m → P) (r : ℕ) :
    term (k := k) f r ≅
      ⨁ (fun A : FaceIndex m r => Hook.module (k := k) ⊥ (faceJoin f A)) := by
  classical
  exact rawIso f r ≪≫ biproduct.mapIso (faceHookIso f)

/-- On each original target summand, the actual cokernel projection becomes its hook projection. -/
@[reassoc (attr := simp)] theorem projection_hookSumIso_ι {m : ℕ}
    (f : Fin m → P) (r : ℕ) (A : FaceIndex m r) :
    biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) (bottomFamily m) B) A ≫
      cokernel.π (inclusion (k := k) f r) ≫ (hookSumIso f r).hom =
    HookCokernel.projection (faceJoin (bottomFamily m) A) (faceJoin f A) ≫
      (faceHookIso f A).hom ≫
        biproduct.ι (fun B : FaceIndex m r => Hook.module (k := k) ⊥ (faceJoin f B)) A := by
  classical
  simp only [hookSumIso, Iso.trans_hom]
  rw [← Category.assoc (cokernel.π (inclusion (k := k) f r)), projection_rawIso,
    ← Category.assoc, rawProjection_ι, Category.assoc, biproduct.mapIso_hom,
    biproduct.ι_map]

/-- Every quotient term is pointwise finite dimensional over the arbitrary coefficient field. -/
@[instance] theorem term_finiteDimensional {m : ℕ} (f : Fin m → P) (r : ℕ) (p : P) :
    FiniteDimensional k ((term (k := k) f r).obj p) := by
  classical
  have := FiniteBiproduct.finiteDimensional
    (fun A : FaceIndex m r => Hook.module (k := k) ⊥ (faceJoin f A)) p
  exact (asIso ((hookSumIso (k := k) f r).hom.app p)).toLinearEquiv.symm.finiteDimensional

/-- Every quotient term is rank projective, including all degenerate zero-hook summands. -/
theorem term_rankProjective {m : ℕ} (f : Fin m → P) (r : ℕ) :
    IsRankProjective (term (k := k) f r) := by
  classical
  exact (IsRankProjective.biproduct
    (fun A : FaceIndex m r => Hook.module (k := k) ⊥ (faceJoin f A))
    (fun _ => HookCokernel.rankProjective bot_le)).of_iso (hookSumIso f r).symm

private theorem bottomTerm_generated (m r : ℕ) :
    GeneratedAtBottom (GeneratedUpsetResolution.term (k := k) (bottomFamily (P := P) m) r) := by
  classical
  let F : FaceIndex m r → PModule.{u,0,u} k P := fun A => faceModule (k := k) (bottomFamily m) A
  have hF : ∀ A : FaceIndex m r, GeneratedAtBottom (F A) := by
    intro A
    change GeneratedAtBottom (HookInfinity.module (R := k) (faceJoin (bottomFamily m) A))
    rw [faceJoin_bottom]
    intro p y
    refine ⟨(HookInfinity.fiberEquivOfLe (R := k) (le_rfl : (⊥ : P) ≤ ⊥)).symm
      (HookInfinity.fiberEquivOfLe (R := k) (bot_le : (⊥ : P) ≤ p) y), ?_⟩
    apply (HookInfinity.fiberEquivOfLe (R := k) (bot_le : (⊥ : P) ≤ p)).injective
    rw [HookInfinity.fiberEquivOfLe_structureMap]
    exact LinearEquiv.apply_symm_apply _ _
  intro p y
  choose x hx using fun A => hF A p (((biproduct.π F A).app p).hom y)
  let e := FiniteBiproduct.fiberIsoPi F ⊥
  refine ⟨e.inv.hom x, ?_⟩
  apply FiniteBiproduct.element_ext F p
  intro A
  have hcoord : ((biproduct.π F A).app ⊥).hom (e.inv.hom x) = x A := by
    have he := FiniteBiproduct.fiberIsoPi_hom_π F ⊥ A
    have ht := congrArg (fun t : (⨁ F).obj ⊥ ⟶ (F A).obj ⊥ => t.hom (e.inv.hom x)) he
    change (e.hom ≫ ModuleCat.ofHom (LinearMap.proj A)).hom (e.inv.hom x) = _ at ht
    have hinv : e.hom.hom (e.inv.hom x) = x := by
      exact congrArg (fun t => t.hom x) e.inv_hom_id
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_ofHom, LinearMap.proj_apply, hinv] using ht.symm
  have hn := congrArg (fun t : (⨁ F).obj ⊥ ⟶ (F A).obj p => t.hom (e.inv.hom x))
    ((biproduct.π F A).naturality (homOfLE (bot_le : (⊥ : P) ≤ p)))
  change ((biproduct.π F A).app p).hom
    (structureMapLinear (⨁ F) bot_le (e.inv.hom x)) =
      structureMapLinear (F A) bot_le (((biproduct.π F A).app ⊥).hom (e.inv.hom x)) at hn
  rw [hn, hcoord, hx]

/-- Generation at bottom descends from the actual constant-bottom resolution term. -/
theorem term_generatedAtBottom {m : ℕ} (f : Fin m → P) (r : ℕ) :
    GeneratedAtBottom (term (k := k) f r) :=
  GeneratedAtBottom.cokernel (inclusion (k := k) f r) (bottomTerm_generated m r)

omit [OrderBot P] in
private theorem range_eq_ker_of_cycles {A B C : PModule.{u,0,u} k P}
    (a : A ⟶ B) (b : B ⟶ C) (hz : a ≫ b = 0)
    (h : ∀ p (x : B.obj p), (b.app p).hom x = 0 → ∃ y, (a.app p).hom y = x)
    (p : P) : LinearMap.range (a.app p).hom = LinearMap.ker (b.app p).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact comp_apply hz p y
  · exact h p x

/-- Image and kernel agree at quotient degree zero. -/
theorem augmentation_range_eq_ker {m : ℕ} (f : Fin m → P) (p : P) :
    LinearMap.range ((differential (k := k) f 0).app p).hom =
      LinearMap.ker ((augmentation (k := k) f).app p).hom :=
  range_eq_ker_of_cycles _ _ (differential_comp_augmentation f)
    (augmentation_exact_at_zero f) p

/-- Image and kernel agree at every positive quotient degree. -/
theorem differential_range_eq_ker {m : ℕ} (f : Fin m → P) (r : ℕ) (p : P) :
    LinearMap.range ((differential (k := k) f (r + 1)).app p).hom =
      LinearMap.ker ((differential (k := k) f r).app p).hom :=
  range_eq_ker_of_cycles _ _ (differential_comp_differential f r)
    (fun p => differential_exact_at_succ f p r) p

/-- The augmented quotient is pointwise exact in every degree and surjective onto its target. -/
theorem resolution_pointwise_exact_at {m : ℕ} (f : Fin m → P) (p : P) :
    Function.Surjective ((augmentation (k := k) f).app p).hom ∧
      LinearMap.range ((differential (k := k) f 0).app p).hom =
        LinearMap.ker ((augmentation (k := k) f).app p).hom ∧
      ∀ r, LinearMap.range ((differential (k := k) f (r + 1)).app p).hom =
        LinearMap.ker ((differential (k := k) f r).app p).hom :=
  ⟨augmentation_surjective_at f p, augmentation_range_eq_ker f p,
    fun r => differential_range_eq_ker f r p⟩

omit [OrderBot P] in
private theorem kernelLift_surjective {A B C : PModule.{u,0,u} k P}
    {a : A ⟶ B} {b : B ⟶ C}
    (he : ∀ p, LinearMap.range (a.app p).hom = LinearMap.ker (b.app p).hom) (p : P) :
    Function.Surjective ((kernelRowLift he).app p).hom := by
  intro z
  have hz : ((kernel.ι b).app p).hom z ∈ LinearMap.ker (b.app p).hom := by
    exact comp_apply (kernel.condition b) p z
  rw [← he p] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, RankKernel.injective b p ?_⟩
  exact (comp_apply (kernelRowLift_ι he) p x).trans hx

/-- The actual augmentation kernel row is rank exact. -/
theorem augmentation_rankExact {m : ℕ} (f : Fin m → P) :
    IsRankExact (kernel.ι (augmentation (k := k) f)) (augmentation (k := k) f) := by
  apply IsPointwiseShortExact.rankExact_of_generatedAtBottom
    (RankKernel.shortExact _ (augmentation_surjective_at f))
  · exact GeneratedAtBottom.of_surjective (term_generatedAtBottom f 1)
      (kernelRowLift (augmentation_range_eq_ker f))
      (kernelLift_surjective (augmentation_range_eq_ker f))
  · exact term_finiteDimensional f 0

/-- The differential onto the actual augmentation kernel gives a rank-exact kernel row. -/
theorem zero_kernelRow_rankExact {m : ℕ} (f : Fin m → P) :
    IsRankExact (kernel.ι (differential (k := k) f 0))
      (kernelRowLift (augmentation_range_eq_ker (k := k) f)) :=
  rankExact_kernelRow (differential_range_eq_ker f 0) (augmentation_range_eq_ker f)
    (term_generatedAtBottom f 2) (term_finiteDimensional f 1)

/-- Every positive row uses the actual differential kernel and the categorical differential lift. -/
theorem succ_kernelRow_rankExact {m : ℕ} (f : Fin m → P) (r : ℕ) :
    IsRankExact (kernel.ι (differential (k := k) f (r + 1)))
      (kernelRowLift (differential_range_eq_ker (k := k) f r)) :=
  rankExact_kernelRow (differential_range_eq_ker f (r + 1))
    (differential_range_eq_ker f r) (term_generatedAtBottom f (r + 3))
    (term_finiteDimensional f (r + 2))

/-- Quotient terms vanish in every degree at least the size of the indexed family. -/
theorem term_isZero_of_degree_ge {m r : ℕ} (f : Fin m → P) (hmr : m ≤ r) :
    IsZero (term (k := k) f r) :=
  IsZero.of_epi (cokernel.π (inclusion (k := k) f r))
    (GeneratedUpsetResolution.term_isZero_of_degree_ge (bottomFamily m) hmr)

/-- A family constantly equal to bottom has zero quotient terms, including nonempty families. -/
theorem term_bottomFamily_isZero (m r : ℕ) :
    IsZero (term (k := k) (bottomFamily (P := P) m) r) := by
  have hi : inclusion (k := k) (bottomFamily (P := P) m) r = 𝟙 _ :=
    resolutionMap_identity _ r
  have : Epi (inclusion (k := k) (bottomFamily (P := P) m) r) := by
    rw [hi]
    infer_instance
  exact isZero_cokernel_of_epi _

/-- Every quotient term for the empty occurrence family is zero. -/
theorem term_fin_zero_isZero (f : Fin 0 → P) (r : ℕ) :
    IsZero (term (k := k) f r) := term_isZero_of_degree_ge f (Nat.zero_le r)

/-- The empty family's augmented quotient target is zero. -/
theorem target_fin_zero_isZero (f : Fin 0 → P) : IsZero (target (k := k) f) :=
  IsZero.of_epi (cokernel.π (supportInclusion (k := k) f))
    (generatedSupport_fin_zero_module_isZero (bottomFamily 0))

/-- The lower complement of the upset generated by the family. -/
def complementSupport {m : ℕ} (f : Fin m → P) : Set P :=
  {p | ¬ ∃ i, f i ≤ p}

omit [OrderBot P] in
/-- The complement support is a lower set and hence order convex. -/
theorem complementSupport_ordConnected {m : ℕ} (f : Fin m → P) :
    (complementSupport f).OrdConnected where
  out' := by
    intro p hp q hq r hprq
    rintro ⟨i, hi⟩
    exact hq ⟨i, hi.trans hprq.2⟩

/-- A nonempty constant-bottom family generates the whole lattice. -/
theorem mem_generatedSupport_bottom {m : ℕ} (hm : 0 < m) (p : P) :
    p ∈ generatedSupport (bottomFamily (P := P) m) :=
  ⟨⟨0, hm⟩, bot_le⟩

private theorem targetProjection_compat {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    ∀ p q, p ≤ q → p ∈ generatedSupport (bottomFamily m) → q ∈ complementSupport f →
      (q ∈ generatedSupport (bottomFamily m) ↔ p ∈ complementSupport f) := by
  intro p q hpq _ hq
  constructor
  · intro _ ⟨i, hi⟩
    exact hq ⟨i, hi.trans hpq⟩
  · intro _
    exact mem_generatedSupport_bottom hm q

/-- The coefficient projection from the constant-bottom support onto the lower complement. -/
noncomputable def targetProjection {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    SupportInterval.module (k := k) (generatedSupport (bottomFamily m))
        (generatedSupport_ordConnected (bottomFamily m)) ⟶
      SupportInterval.module (k := k) (complementSupport f) (complementSupport_ordConnected f) :=
  SupportInterval.comparison _ _ _ _ 1 (targetProjection_compat f hm)

/-- The lower-complement projection preserves coefficients precisely on the complement support. -/
theorem targetProjection_val {m : ℕ} (f : Fin m → P) (hm : 0 < m) (p : P)
    (x : SupportInterval.fiber (k := k) (generatedSupport (bottomFamily m)) p) :
    (((targetProjection f hm).app p).hom x : k) =
      if p ∈ complementSupport f then (x : k) else 0 := by
  classical
  simpa only [targetProjection, one_mul] using
    (SupportInterval.comparison_app_val (k := k) (generatedSupport (bottomFamily m))
      (complementSupport f) (generatedSupport_ordConnected (bottomFamily m))
      (complementSupport_ordConnected f) 1 (targetProjection_compat f hm) p x)

private theorem supportInclusion_targetProjection {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    supportInclusion (k := k) f ≫ targetProjection f hm = 0 := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((targetProjection f hm).app p).hom
    (((supportInclusion (k := k) f).app p).hom x) : k) = 0
  rw [targetProjection_val]
  by_cases hp : p ∈ complementSupport f
  · have hpf : p ∉ generatedSupport f := hp
    have hx0 : x = 0 := Subtype.ext (SupportInterval.val_eq_zero _ hpf x)
    rw [if_pos hp, hx0, map_zero]
    rfl
  · rw [if_neg hp]

private theorem targetProjection_surjective {m : ℕ} (f : Fin m → P) (hm : 0 < m) (p : P) :
    Function.Surjective ((targetProjection (k := k) f hm).app p).hom := by
  classical
  intro y
  by_cases hp : p ∈ complementSupport f
  · refine ⟨⟨(y : k), by simp [SupportInterval.fiber, mem_generatedSupport_bottom hm p]⟩, ?_⟩
    apply Subtype.ext
    rw [targetProjection_val, if_pos hp]
  · refine ⟨0, ?_⟩
    rw [map_zero]
    apply Subtype.ext
    exact (SupportInterval.val_eq_zero _ hp y).symm

private theorem targetProjection_zero_iff {m : ℕ} (f : Fin m → P) (hm : 0 < m) (p : P)
    (x : SupportInterval.fiber (k := k) (generatedSupport (bottomFamily m)) p) :
    ((targetProjection f hm).app p).hom x = 0 ↔
      x ∈ LinearMap.range ((supportInclusion (k := k) f).app p).hom := by
  classical
  constructor
  · intro hx
    by_cases hp : p ∈ complementSupport f
    · have hval := congrArg Subtype.val hx
      rw [targetProjection_val, if_pos hp] at hval
      have hx0 : x = 0 := Subtype.ext hval
      exact ⟨0, by simp [hx0]⟩
    · have hpf : p ∈ generatedSupport f := Classical.not_not.mp hp
      refine ⟨⟨(x : k), by simp [SupportInterval.fiber, hpf]⟩, ?_⟩
      apply Subtype.ext
      exact supportMap_app_val (k := k) (g := bottomFamily m) (fun _ => bot_le) hpf _
  · rintro ⟨y, rfl⟩
    exact comp_apply (supportInclusion_targetProjection f hm) p y

private noncomputable def targetComparison {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    target (k := k) f ⟶
      SupportInterval.module (k := k) (complementSupport f) (complementSupport_ordConnected f) :=
  cokernel.desc _ (targetProjection f hm) (supportInclusion_targetProjection f hm)

private theorem projection_targetComparison {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    cokernel.π (supportInclusion (k := k) f) ≫ targetComparison f hm = targetProjection f hm :=
  cokernel.π_desc _ _ _

private theorem targetComparison_bijective {m : ℕ} (f : Fin m → P) (hm : 0 < m) (p : P) :
    Function.Bijective ((targetComparison (k := k) f hm).app p).hom := by
  constructor
  · intro x y hxy
    have hz : ((targetComparison (k := k) f hm).app p).hom (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz'⟩ := GeneratedAtBottom.cokernel_projection_surjective
      (supportInclusion (k := k) f) p (x - y)
    have hproj : ((targetProjection (k := k) f hm).app p).hom z = 0 := by
      rw [← comp_apply (projection_targetComparison f hm) p z, hz', hz]
    have hpi : ((cokernel.π (supportInclusion (k := k) f)).app p).hom z = 0 :=
      (cokernel_projection_zero_iff _ p _).mpr ((targetProjection_zero_iff f hm p z).mp hproj)
    exact sub_eq_zero.mp (hz'.symm.trans hpi)
  · intro y
    obtain ⟨z, hz⟩ := targetProjection_surjective f hm p y
    exact ⟨((cokernel.π (supportInclusion (k := k) f)).app p).hom z,
      (comp_apply (projection_targetComparison f hm) p z).trans hz⟩

/-- For a nonempty family, the actual augmented target is the lower-complement interval module. -/
noncomputable def targetIso {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    target (k := k) f ≅
      SupportInterval.module (k := k) (complementSupport f) (complementSupport_ordConnected f) := by
  haveI : IsIso (targetComparison (k := k) f hm) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro p
    have : Mono ((targetComparison (k := k) f hm).app p) :=
      (ModuleCat.mono_iff_injective _).mpr (targetComparison_bijective f hm p).1
    have : Epi ((targetComparison (k := k) f hm).app p) :=
      (ModuleCat.epi_iff_surjective _).mpr (targetComparison_bijective f hm p).2
    exact isIso_of_mono_of_epi _
  exact asIso (targetComparison f hm)

/-- The lower-complement isomorphism takes the actual cokernel projection to coefficient projection. -/
@[reassoc (attr := simp)] theorem projection_targetIso {m : ℕ} (f : Fin m → P) (hm : 0 < m) :
    cokernel.π (supportInclusion (k := k) f) ≫ (targetIso f hm).hom = targetProjection f hm :=
  projection_targetComparison f hm

end TDA.Persistence.GeneratedUpsetQuotientResolution
