import TDA.Persistence.CoordinateGridProjective
import TDA.Persistence.FinitePresentationGridKan
import TDA.Persistence.FiniteRankProjectiveClassification
import TDA.Persistence.FiniteRankProjectiveResolution
import TDA.Persistence.RankDeflation
import TDA.Persistence.RankExactIso
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Finite rank-projective resolutions from finite presentations

Pointwise finite-dimensional modules on finite posets admit actual finite
rank-projective resolutions: shortest rank-exact hook-sum covers of successive
kernels move to strictly higher weights: each nonzero differential component
points from a higher-weight hook in a later cover to a lower-weight hook in the
preceding cover. The finite poset bounds those weights. A finite presentation
on a real coordinate poset reconstructs the module from a finite grid with pfd
fibers. The grid's actual left Kan extension transports each resolution row by
row, preserving rank exactness and relative projectivity. The resulting
existence theorem assumes no prior grid, pfd, or hook decomposition of the
real-indexed module.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory
open CategoryTheory.Limits
open scoped TDA.Persistence
open scoped ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

/-- A rank-projective cover is a rank-exact deflation from a rank-projective
object whose endomorphisms over the quotient are necessarily invertible. -/
structure IsRankProjectiveCover {P : Type} [PartialOrder P]
    {A B : PModule.{u,0,u} k P} (π : A ⟶ B) : Prop where
  term_rank_projective : IsRankProjective A
  row_rank_exact : IsRankExact (kernel.ι π) π
  endomorphism_isIso : ∀ u : End A, u ≫ π = π → IsIso u

/-- A finite rank-projective resolution together with the projective-cover
certificate for every indexed row quotient. -/
structure MinimalFiniteRankProjectiveResolution {P : Type} [PartialOrder P]
    {M : PModule.{u,0,u} k P} where
  resolution : FiniteRankProjectiveResolution M
  quotient_is_cover : ∀ i, IsRankProjectiveCover (resolution.quotient i)

namespace FiniteRankProjectiveResolution

/-- A nonzero map of finite-death hooks can only move both endpoints down in
the coordinatewise order. This is the finite-poset direction used to prove
termination of minimal hook resolutions. -/
theorem hook_hom_nonzero_implies_endpoint_order
    {P : Type} [PartialOrder P] {i j m n : P} (hij : i < j) (_hmn : m < n)
    (f : Hook.module (k := k) i j ⟶ Hook.module (k := k) m n) (hf : f ≠ 0) :
    m ≤ i ∧ n ≤ j := by
  let v := (Hook.homEquivKernel hij (Hook.module (k := k) m n)) f
  have hv : v.val ≠ 0 := by
    intro hzero
    apply hf
    exact (Hook.homEquivKernel hij (Hook.module (k := k) m n)).injective
      (Subtype.ext hzero)
  have hsupport : i ∈ Hook.support m n := by
    by_contra hi
    apply hv
    apply Subtype.ext
    exact SupportInterval.val_eq_zero (Hook.support m n) hi v.val
  refine ⟨hsupport.1, ?_⟩
  by_contra hnj
  have hdie : structureMapLinear (Hook.module (k := k) m n) hij.le v.val = 0 :=
    v.property
  have hdieval :
      (structureMapLinear (Hook.module (k := k) m n) hij.le v.val).val = 0 :=
    congrArg Subtype.val hdie
  have hjSupport : j ∈ Hook.support m n := ⟨hsupport.1.trans hij.le, hnj⟩
  have hval := SupportInterval.structureMap_val (Hook.support m n)
    (Hook.support_ordConnected m n) hij.le v.val
  rw [if_pos hjSupport] at hval
  have hvzero : v.val = 0 := by
    apply Subtype.ext
    exact hval.symm.trans hdieval
  exact hv hvzero

/-- Endpoint order for every nonzero morphism between finite-poset rank-projective
hook types. A finite hook cannot map nontrivially to an infinite hook; infinite
source hooks use their birth as the only finite endpoint. -/
def rankProjectiveHookHomOrder {P : Type} [PartialOrder P]
    (s t : FiniteRankProjectiveClassification.RankProjectiveHookTag P) : Prop :=
  match s, t with
  | .inl ab, .inl cd => cd.val.1 ≤ ab.val.1 ∧ cd.val.2 ≤ ab.val.2
  | .inl _, .inr _ => False
  | .inr a, .inl cd => cd.val.1 ≤ a
  | .inr a, .inr b => b ≤ a

/-- A finite hook sum with its actual rank-exact deflation onto `M`. The
occurrence index is retained, so isomorphic summands are not identified. -/
structure HookSumCover {P : Type} [PartialOrder P] [Fintype P]
    (M : PModule.{u,0,u} k P) where
  Index : Type
  instFintypeIndex : Fintype Index
  summand : Index → PModule.{u,0,u} k P
  tag : Index → FiniteRankProjectiveClassification.RankProjectiveHookTag P
  summand_eq_tag : ∀ i, summand i =
    FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (tag i)
  quotient : (⨁ summand) ⟶ M
  row_rank_exact : IsRankExact (kernel.ι quotient) quotient

attribute [instance] HookSumCover.instFintypeIndex

/-- The number of hook occurrences, counting isomorphic summands separately. -/
noncomputable def HookSumCover.length {P : Type} [PartialOrder P] [Fintype P]
    {M : PModule.{u,0,u} k P} (C : HookSumCover M) : ℕ := Fintype.card C.Index

/-- The finite middle term of a hook-sum cover is rank projective. -/
theorem HookSumCover.term_isRankProjective {P : Type} [PartialOrder P] [Fintype P]
    {M : PModule.{u,0,u} k P} (C : HookSumCover M) :
    IsRankProjective (⨁ C.summand) := by
  apply IsRankProjective.biproduct
  intro i
  have hTag : IsRankProjective
      (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (C.tag i)) := by
    cases C.tag i with
    | inl ab => exact Hook.isRankProjective ab.property
    | inr a => exact HookInfinity.isRankProjective a
  exact hTag.of_iso (eqToIso (C.summand_eq_tag i)).symm

private def canonicalHookTag {P : Type} [PartialOrder P]
    {M : PModule.{u,0,u} k P} : FiniteHookDeflation.Index M →
      FiniteRankProjectiveClassification.RankProjectiveHookTag P
  | .inl t => .inl t.1
  | .inr t => .inr t.1

private theorem canonicalFamily_eq_tag {P : Type} [PartialOrder P]
    {M : PModule.{u,0,u} k P} (t : FiniteHookDeflation.Index M) :
    FiniteHookDeflation.family M t =
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
        (canonicalHookTag t) := by
  cases t <;> rfl

/-- The finite-pfd hook deflation, retaining its canonical occurrence indices. -/
noncomputable def canonicalHookSumCover {P : Type} [PartialOrder P] [Fintype P]
    (M : PModule.{u,0,u} k P) (hfd : ∀ p, FiniteDimensional k (M.obj p)) :
    HookSumCover M := by
  classical
  letI : ∀ p, FiniteDimensional k (M.obj p) := hfd
  refine {
    Index := FiniteHookDeflation.Index M
    instFintypeIndex := FiniteHookDeflation.indexFintype M
    summand := FiniteHookDeflation.family M
    tag := canonicalHookTag
    summand_eq_tag := canonicalFamily_eq_tag
    quotient := ?_
    row_rank_exact := ?_
  }
  · exact FiniteHookDeflation.π M
  · exact FiniteHookDeflation.rankExact M

/-- A shortest hook-sum rank-exact deflation among all finite hook-sum
deflations onto `M`. -/
structure MinimalHookSumCover {P : Type} [PartialOrder P] [Fintype P]
    (M : PModule.{u,0,u} k P) where
  cover : HookSumCover M
  minimal : ∀ C : HookSumCover M, cover.length ≤ C.length

/-- Pointwise finite-dimensional modules on finite posets admit a shortest
finite hook-sum rank-exact cover. -/
theorem exists_minimalHookSumCover {P : Type} [PartialOrder P] [Fintype P]
    (M : PModule.{u,0,u} k P) (hfd : ∀ p, FiniteDimensional k (M.obj p)) :
    Nonempty (MinimalHookSumCover M) := by
  classical
  let hasCover : ℕ → Prop := fun m => ∃ C : HookSumCover M, C.length = m
  have hCover : ∃ m, hasCover m := by
    refine ⟨(canonicalHookSumCover M hfd).length, ?_⟩
    exact ⟨canonicalHookSumCover M hfd, rfl⟩
  let m := Nat.find hCover
  obtain ⟨C, hC⟩ := Nat.find_spec hCover
  refine ⟨⟨C, ?_⟩⟩
  intro D
  calc
    C.length = m := hC
    _ ≤ D.length := Nat.find_min' hCover (show hasCover D.length from ⟨D, rfl⟩)

/-- A rank-exact hook-sum cover can discard one occurrence whenever its quotient
kernel contains a copy of that occurrence which splits the corresponding
projection. The quotient is transported to the complementary finite sum by
the explicit section, preserving the dying-element lift condition. -/
theorem HookSumCover.exists_smaller_of_kernel_section
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : HookSumCover M) (i : C.Index)
    (s : C.summand i ⟶ ⨁ C.summand)
    (hs : s ≫ biproduct.π C.summand i = 𝟙 (C.summand i))
    (hq : s ≫ C.quotient = 0) :
    ∃ D : HookSumCover M, D.length < C.length := by
  classical
  let S := {j : C.Index // j ≠ i}
  let F := Subtype.restrict (fun j : C.Index => j ≠ i) C.summand
  let t : (⨁ C.summand) ⟶ ⨁ F :=
    biproduct.toSubtype C.summand fun j => j ≠ i
  let u : (⨁ F) ⟶ ⨁ C.summand :=
    biproduct.fromSubtype C.summand fun j => j ≠ i
  let h : C.summand i ⟶ ⨁ F := s ≫ t
  let r : (⨁ C.summand) ⟶ ⨁ F :=
    t - biproduct.π C.summand i ≫ h
  let q' : (⨁ F) ⟶ M := u ≫ C.quotient
  have hιtCompl (j : C.Index) (hji : j ≠ i) :
      biproduct.ι C.summand j ≫ t =
        biproduct.ι F ⟨j, hji⟩ := by
    dsimp [t, F]
    simpa using (biproduct.ι_toSubtype_subtype
      (f := C.summand) (p := fun j => j ≠ i) ⟨j, hji⟩)
  have hιtDrop : biproduct.ι C.summand i ≫ t = 0 := by
    dsimp [t]
    rw [biproduct.ι_toSubtype]
    simp
  have hprojection : t ≫ u = 𝟙 (⨁ C.summand) -
      biproduct.π C.summand i ≫ biproduct.ι C.summand i := by
    apply biproduct.hom_ext'
    intro j
    by_cases hij : j = i
    · subst j
      dsimp [t, u]
      calc
        biproduct.ι C.summand i ≫
            (biproduct.toSubtype C.summand (fun j => j ≠ i)) ≫
              (biproduct.fromSubtype C.summand (fun j => j ≠ i)) = 0 := by
          have h := congrArg (fun f => f ≫
              biproduct.fromSubtype C.summand (fun j => j ≠ i)) hιtDrop
          simpa [Category.assoc] using h
        _ = biproduct.ι C.summand i ≫
            (𝟙 (⨁ C.summand) - biproduct.π C.summand i ≫ biproduct.ι C.summand i) := by
          simp
    · calc
        biproduct.ι C.summand j ≫ t ≫ u =
            (biproduct.ι C.summand j ≫ t) ≫ u := by rw [Category.assoc]
        _ = biproduct.ι C.summand j := by
              rw [hιtCompl j hij]
              dsimp [u, F]
              exact biproduct.ι_fromSubtype C.summand (fun j => j ≠ i) ⟨j, hij⟩
        _ = biproduct.ι C.summand j ≫
            (𝟙 (⨁ C.summand) - biproduct.π C.summand i ≫ biproduct.ι C.summand i) := by
          simp [Category.assoc, hij]
  have hsection_complement : s ≫ t ≫ u = s - biproduct.ι C.summand i := by
    calc
      s ≫ t ≫ u = s ≫ (𝟙 (⨁ C.summand) -
          biproduct.π C.summand i ≫ biproduct.ι C.summand i) := by rw [hprojection]
      _ = s - (s ≫ biproduct.π C.summand i) ≫ biproduct.ι C.summand i := by
        simp [Category.assoc]
      _ = s - biproduct.ι C.summand i := by rw [hs]; simp
  have hr : r ≫ u = 𝟙 (⨁ C.summand) - biproduct.π C.summand i ≫ s := by
    dsimp [r, h]
    calc
      (t - biproduct.π C.summand i ≫ (s ≫ t)) ≫ u =
          t ≫ u - biproduct.π C.summand i ≫ (s ≫ t ≫ u) := by
            simp [Category.assoc]
      _ = (𝟙 (⨁ C.summand) - biproduct.π C.summand i ≫
          biproduct.ι C.summand i) - biproduct.π C.summand i ≫
            (s ≫ t ≫ u) := by rw [hprojection]
      _ = (𝟙 (⨁ C.summand) - biproduct.π C.summand i ≫
          biproduct.ι C.summand i) - biproduct.π C.summand i ≫
            (s - biproduct.ι C.summand i) := by rw [hsection_complement]
      _ = 𝟙 (⨁ C.summand) - biproduct.π C.summand i ≫ s := by
            simp only [CategoryTheory.Preadditive.comp_sub, Category.id_comp]
            abel
  have hfactor : C.quotient = r ≫ q' := by
    calc
      C.quotient = (𝟙 (⨁ C.summand) - biproduct.π C.summand i ≫ s) ≫ C.quotient := by
        symm
        rw [CategoryTheory.Preadditive.sub_comp, Category.id_comp, Category.assoc, hq]
        simp
      _ = (r ≫ u) ≫ C.quotient := by rw [hr]
      _ = r ≫ u ≫ C.quotient := Category.assoc _ _ _
      _ = r ≫ q' := by rfl
  have hfd (p : P) : FiniteDimensional k ((⨁ F).obj p) := by
    letI : ∀ j : S, FiniteDimensional k ((F j).obj p) := fun j => by
      let e := eqToIso (C.summand_eq_tag j.1)
      letI : FiniteDimensional k
          ((FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
            (C.tag j.1)).obj p) := by
        cases C.tag j.1 with
        | inl ab =>
            change FiniteDimensional k ((Hook.module (k := k) ab.val.1 ab.val.2).obj p)
            infer_instance
        | inr a =>
            change FiniteDimensional k ((HookInfinity.module (R := k) a).obj p)
            infer_instance
      exact (e.app p).toLinearEquiv.symm.finiteDimensional
    exact FiniteBiproduct.finiteDimensional F p
  letI : ∀ p, FiniteDimensional k ((⨁ F).obj p) := hfd
  have hsurj (p : P) : Function.Surjective (q'.app p).hom := by
    intro z
    obtain ⟨x, hx⟩ := C.row_rank_exact.surjective p z
    refine ⟨(r.app p).hom x, ?_⟩
    have he := congrArg (fun f : (⨁ C.summand).obj p ⟶ M.obj p => f.hom x)
      (congrArg (fun f : (⨁ C.summand) ⟶ M => f.app p) hfactor)
    simpa [NatTrans.comp_app, ModuleCat.hom_comp] using he.symm.trans hx
  have hlift {a b : P} (hab : a ≤ b) (z : M.obj a)
      (hz : structureMapLinear M hab z = 0) :
      ∃ x : (⨁ F).obj a,
        (q'.app a).hom x = z ∧
          structureMapLinear (⨁ F) hab x = 0 := by
    obtain ⟨x, hx, hdie⟩ := C.row_rank_exact.lift_kernel hab z hz
    refine ⟨(r.app a).hom x, ?_, ?_⟩
    · have he := congrArg (fun f : (⨁ C.summand).obj a ⟶ M.obj a => f.hom x)
        (congrArg (fun f : (⨁ C.summand) ⟶ M => f.app a) hfactor)
      simpa [NatTrans.comp_app, ModuleCat.hom_comp] using he.symm.trans hx
    · have hn := congrArg (fun f : (⨁ C.summand).obj a ⟶
        (⨁ F).obj b => f.hom x) (r.naturality (homOfLE hab))
      change (r.app b).hom (structureMapLinear (⨁ C.summand) hab x) =
        structureMapLinear (⨁ F) hab ((r.app a).hom x) at hn
      simpa [hdie] using hn.symm
  let D : HookSumCover M := {
    Index := S
    instFintypeIndex := inferInstance
    summand := F
    tag := fun j => C.tag j.1
    summand_eq_tag := fun j => C.summand_eq_tag j.1
    quotient := q'
    row_rank_exact := RankKernel.rankExact q' hsurj hlift
  }
  have hcard : Fintype.card S + 1 = Fintype.card C.Index := by
    have hcomp := Fintype.card_subtype_compl (fun j : C.Index => j = i)
    have hsingleton : Fintype.card {j : C.Index // j = i} = 1 := by simp
    change Fintype.card {j : C.Index // j ≠ i} + 1 = Fintype.card C.Index
    rw [hcomp, hsingleton]
    exact Nat.sub_add_cancel (by have hpos : 0 < Fintype.card C.Index := Fintype.card_pos_iff.mpr ⟨i⟩; omega)
  refine ⟨D, ?_⟩
  change Fintype.card S < Fintype.card C.Index
  omega

private noncomputable def rankProjectiveHookEndRingEquiv
    {P : Type} [PartialOrder P]
    (t : FiniteRankProjectiveClassification.RankProjectiveHookTag P) :
    End (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) t) ≃+* k := by
  cases t with
  | inl ab => exact Hook.endRingEquiv ab.property
  | inr a => exact HookInfinity.endRingEquiv a

private theorem rankProjectiveHookEnd_isIso_of_ne_zero
    {P : Type} [PartialOrder P]
    (t : FiniteRankProjectiveClassification.RankProjectiveHookTag P)
    (f : End (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) t))
    (hf : f ≠ 0) : IsIso f := by
  let e := rankProjectiveHookEndRingEquiv (k := k) t
  have he : e f ≠ 0 := by
    intro hz
    apply hf
    exact e.injective (by simpa using hz)
  have hunit : IsUnit (e f) := isUnit_iff_ne_zero.mpr he
  have hunit' : IsUnit f := by
    have hm := IsUnit.map e.symm.toRingHom hunit
    simpa [e] using hm
  exact CategoryTheory.isUnit_iff_isIso _ |>.mp hunit'

/-- In a shortest hook-sum rank-exact cover, every map from a summand into the
quotient kernel has zero diagonal component. A nonzero diagonal component is
an automorphism because the hook endomorphism ring is the field; it would split
off that occurrence and produce a shorter cover. -/
theorem MinimalHookSumCover.kernel_diagonal_component_eq_zero
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M) (i : C.cover.Index)
    (f : C.cover.summand i ⟶ kernel C.cover.quotient) :
    f ≫ kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i = 0 := by
  classical
  let e : C.cover.summand i ≅
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (C.cover.tag i) :=
    eqToIso (C.cover.summand_eq_tag i)
  let α : End (C.cover.summand i) :=
    f ≫ kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i
  by_contra hα
  let β : End (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
      (C.cover.tag i)) := e.inv ≫ α ≫ e.hom
  have hβ : β ≠ 0 := by
    intro hzero
    have hconj : α = e.hom ≫ β ≫ e.inv := by
      dsimp [β]
      simp [Category.assoc]
    have hαzero : α = 0 := by rw [hconj, hzero]; simp
    exact hα hαzero
  letI : IsIso β := rankProjectiveHookEnd_isIso_of_ne_zero (C.cover.tag i) β hβ
  let αInv : End (C.cover.summand i) := e.hom ≫ inv β ≫ e.inv
  have hβdef : β = e.inv ≫ α ≫ e.hom := rfl
  have hαInv : αInv ≫ α = 𝟙 (C.cover.summand i) := by
    dsimp [αInv]
    calc
      e.hom ≫ inv β ≫ e.inv ≫ α =
          e.hom ≫ inv β ≫ (e.inv ≫ α ≫ e.hom) ≫ e.inv := by
            simp [Category.assoc]
      _ = e.hom ≫ inv β ≫ β ≫ e.inv := by rw [← hβdef]
      _ = 𝟙 (C.cover.summand i) := by simp [Category.assoc]
  let s : C.cover.summand i ⟶ ⨁ C.cover.summand :=
    αInv ≫ f ≫ kernel.ι C.cover.quotient
  have hs : s ≫ biproduct.π C.cover.summand i = 𝟙 (C.cover.summand i) := by
    dsimp [s, α]
    calc
      αInv ≫ f ≫ kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i =
          αInv ≫ α := rfl
      _ = 𝟙 (C.cover.summand i) := hαInv
  have hq : s ≫ C.cover.quotient = 0 := by
    dsimp [s]
    simp [Category.assoc]
  obtain ⟨D, hD⟩ := HookSumCover.exists_smaller_of_kernel_section C.cover i s hs hq
  exact (not_lt_of_ge (C.minimal D)) hD

/-- A hook isomorphism type equal to a cover summand cannot map into the cover
kernel with a nonzero component on that occurrence. -/
theorem MinimalHookSumCover.kernel_component_eq_zero_of_iso
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M) (i : C.cover.Index)
    (X : PModule.{u,0,u} k P)
    (e : X ≅ FiniteRankProjectiveClassification.rankProjectiveHookModule
      (k := k) (C.cover.tag i))
    (f : X ⟶ kernel C.cover.quotient) :
    f ≫ kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i = 0 := by
  let eTarget : C.cover.summand i ≅
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (C.cover.tag i) :=
    eqToIso (C.cover.summand_eq_tag i)
  let eIso : X ≅ C.cover.summand i := e.trans eTarget.symm
  have hdiag := C.kernel_diagonal_component_eq_zero i (eIso.inv ≫ f)
  have hpre : eIso.hom ≫
      (eIso.inv ≫ f ≫ kernel.ι C.cover.quotient ≫
        biproduct.π C.cover.summand i) = 0 := by
    simpa [Category.assoc] using congrArg (fun g => eIso.hom ≫ g) hdiag
  calc
    f ≫ kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i =
        eIso.hom ≫ (eIso.inv ≫ f ≫ kernel.ι C.cover.quotient ≫
          biproduct.π C.cover.summand i) := by simp [Category.assoc]
    _ = 0 := by rw [hpre]

/-- Minimal covers have no unused hook occurrence: every summand has a nonzero
component in the quotient. Otherwise that summand itself splits off inside the
kernel and the deletion lemma shortens the cover. -/
theorem MinimalHookSumCover.quotient_component_ne_zero
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M) (i : C.cover.Index) :
    biproduct.ι C.cover.summand i ≫ C.cover.quotient ≠ 0 := by
  classical
  intro hzero
  have hs : biproduct.ι C.cover.summand i ≫ biproduct.π C.cover.summand i =
      𝟙 (C.cover.summand i) := biproduct.ι_π_self _ _
  obtain ⟨D, hD⟩ := HookSumCover.exists_smaller_of_kernel_section C.cover i
    (biproduct.ι C.cover.summand i) hs hzero
  exact (not_lt_of_ge (C.minimal D)) hD

/-- The size of a finite-poset hook is strictly monotone under every strict
endpoint decrease. Infinite hooks are placed above all finite hooks. -/
noncomputable def finitePosetRank {P : Type} [PartialOrder P] [Fintype P] (a : P) : ℕ :=
  by
    classical
    exact Fintype.card {b : P // b ≤ a}

theorem finitePosetRank_mono {P : Type} [PartialOrder P] [Fintype P]
    {a b : P} (hab : a ≤ b) : finitePosetRank a ≤ finitePosetRank b := by
  classical
  exact Fintype.card_le_of_injective
    (fun x : {p : P // p ≤ a} => (⟨x.1, x.2.trans hab⟩ : {p : P // p ≤ b}))
    (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : {p : P // p ≤ b} => (z : P)) h))

theorem finitePosetRank_strictMono {P : Type} [PartialOrder P] [Fintype P]
    {a b : P} (hab : a < b) : finitePosetRank a < finitePosetRank b := by
  classical
  change Fintype.card {p : P // p ≤ a} < Fintype.card {p : P // p ≤ b}
  apply Fintype.card_lt_of_injective_not_surjective
    (fun x : {p : P // p ≤ a} => (⟨x.1, x.2.trans hab.le⟩ : {p : P // p ≤ b}))
    (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : {p : P // p ≤ b} => (z : P)) h))
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj ⟨b, le_rfl⟩
  have hval : (x.1 : P) = b := congrArg (fun z : {p : P // p ≤ b} => (z : P)) hx
  have hba : b ≤ a := by simpa [hval] using x.2
  exact (not_le_of_gt hab) hba

noncomputable def rankProjectiveHookTagWeight
    {P : Type} [PartialOrder P] [Fintype P]
    (t : FiniteRankProjectiveClassification.RankProjectiveHookTag P) : ℕ :=
  match t with
  | .inl ab => finitePosetRank ab.val.1 + finitePosetRank ab.val.2
  | .inr a => finitePosetRank a + 2 * Fintype.card P + 1

theorem rankProjectiveHookHomOrder_weight_strict
    {P : Type} [PartialOrder P] [Fintype P]
    (s t : FiniteRankProjectiveClassification.RankProjectiveHookTag P)
    (h : rankProjectiveHookHomOrder s t) (hne : s ≠ t) :
    rankProjectiveHookTagWeight t < rankProjectiveHookTagWeight s := by
  classical
  cases s with
  | inl ab =>
    cases t with
    | inl cd =>
      have hbirth := finitePosetRank_mono h.1
      have hdeath := finitePosetRank_mono h.2
      by_cases hb : cd.val.1 = ab.val.1
      · have hd : cd.val.2 < ab.val.2 :=
          lt_of_le_of_ne h.2 (by
            intro heq
            apply hne
            congr 1
            exact Subtype.ext (Prod.ext hb.symm heq.symm))
        have hrank := finitePosetRank_strictMono hd
        simp only [rankProjectiveHookTagWeight]
        omega
      · have hb' : cd.val.1 < ab.val.1 := lt_of_le_of_ne h.1 hb
        have hrank := finitePosetRank_strictMono hb'
        simp only [rankProjectiveHookTagWeight]
        omega
    | inr a => exact h.elim
  | inr a =>
    cases t with
    | inl cd =>
      have hbirth := finitePosetRank_mono h
      have hdeath : finitePosetRank cd.val.2 ≤ Fintype.card P := by
        simpa [finitePosetRank] using
          (Fintype.card_subtype_le (fun b : P => b ≤ cd.val.2))
      simp only [rankProjectiveHookTagWeight]
      omega
    | inr b =>
      by_cases hab : b = a
      · subst b
        exact (hne rfl).elim
      · have hba : b < a := lt_of_le_of_ne h hab
        have hrank := finitePosetRank_strictMono hba
        simp only [rankProjectiveHookTagWeight]
        omega

/-- Every nonzero hook component follows the finite endpoint order. This is the
strictness input for finite termination once minimality rules out equal-hook
components in successive differentials. -/
theorem rankProjectiveHook_hom_nonzero_order
    {P : Type} [PartialOrder P]
    (s t : FiniteRankProjectiveClassification.RankProjectiveHookTag P)
    (f : FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) s ⟶
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) t)
    (hf : f ≠ 0) : rankProjectiveHookHomOrder s t := by
  cases s with
  | inl ab =>
    cases t with
    | inl cd =>
      exact hook_hom_nonzero_implies_endpoint_order ab.property cd.property f hf
    | inr b =>
      let v := (Hook.homEquivKernel ab.property
        (HookInfinity.module (R := k) b)) f
      have hv : v.val ≠ 0 := by
        intro hzero
        apply hf
        exact (Hook.homEquivKernel ab.property
          (HookInfinity.module (R := k) b)).injective (Subtype.ext hzero)
      have hbi : b ≤ ab.val.1 := by
        by_contra hbi
        exact hv (HookInfinity.fiber_eq_zero_of_not_le hbi v.val)
      have hdie : structureMapLinear (HookInfinity.module (R := k) b)
          ab.property.le v.val = 0 := v.property
      have hcoeff : HookInfinity.fiberEquivOfLe (R := k) hbi v.val = 0 := by
        calc
          HookInfinity.fiberEquivOfLe (R := k) hbi v.val =
              HookInfinity.fiberEquivOfLe (R := k) (hbi.trans ab.property.le)
                (structureMapLinear (HookInfinity.module (R := k) b)
                  ab.property.le v.val) := by
                    exact (HookInfinity.fiberEquivOfLe_structureMap hbi ab.property.le v.val).symm
          _ = 0 := by rw [hdie, map_zero]
      exact (False.elim (hv
        ((HookInfinity.fiberEquivOfLe (R := k) hbi).injective hcoeff)))
  | inr a =>
    cases t with
    | inl cd =>
      let v := (HookInfinity.homEquivFiber (R := k) a
        (Hook.module (k := k) cd.val.1 cd.val.2)) f
      have hv : v ≠ 0 := by
        intro hzero
        apply hf
        exact (HookInfinity.homEquivFiber (R := k) a
          (Hook.module (k := k) cd.val.1 cd.val.2)).injective hzero
      have hbirth : cd.val.1 ≤ a := by
        by_contra h
        have ha : a ∉ Hook.support cd.val.1 cd.val.2 := by
          intro ha
          exact h ha.1
        apply hv
        apply Subtype.ext
        exact SupportInterval.val_eq_zero (Hook.support cd.val.1 cd.val.2) ha v
      exact hbirth
    | inr b =>
      let v := (HookInfinity.homEquivFiber (R := k) a
        (HookInfinity.module (R := k) b)) f
      have hv : v ≠ 0 := by
        intro hzero
        apply hf
        exact (HookInfinity.homEquivFiber (R := k) a
          (HookInfinity.module (R := k) b)).injective hzero
      by_contra hba
      exact hv (HookInfinity.fiber_eq_zero_of_not_le hba v)

/-- The differential between two successive minimal hook-sum covers has only
strictly decreasing hook weights among its nonzero matrix components. Equal-tag
components vanish because they factor through the preceding cover's kernel. -/
theorem minimalHookCover_differential_component_weight_strict
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M)
    (D : MinimalHookSumCover (kernel C.cover.quotient))
    (i : C.cover.Index) (j : D.cover.Index)
    (hcomponent : biproduct.ι D.cover.summand j ≫ D.cover.quotient ≫
      kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i ≠ 0) :
    rankProjectiveHookTagWeight (C.cover.tag i) <
      rankProjectiveHookTagWeight (D.cover.tag j) := by
  classical
  let eSource : D.cover.summand j ≅
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (D.cover.tag j) :=
    eqToIso (D.cover.summand_eq_tag j)
  let eTarget : C.cover.summand i ≅
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (C.cover.tag i) :=
    eqToIso (C.cover.summand_eq_tag i)
  have htags : D.cover.tag j ≠ C.cover.tag i := by
    intro htag
    let eTag : FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
        (D.cover.tag j) ≅
        FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (C.cover.tag i) :=
      eqToIso (congrArg
        (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)) htag)
    let e : D.cover.summand j ≅
        FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (C.cover.tag i) :=
      eSource.trans eTag
    have hz := C.kernel_component_eq_zero_of_iso i _ e
      (biproduct.ι D.cover.summand j ≫ D.cover.quotient)
    apply hcomponent
    simpa [Category.assoc] using hz
  let f : D.cover.summand j ⟶ C.cover.summand i :=
    biproduct.ι D.cover.summand j ≫ D.cover.quotient ≫
      kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i
  let g : FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
        (D.cover.tag j) ⟶
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (C.cover.tag i) :=
    eSource.inv ≫ f ≫ eTarget.hom
  have hg : g ≠ 0 := by
    intro hz
    apply hcomponent
    have hrecover : eSource.hom ≫ g ≫ eTarget.inv = f := by
      dsimp [g, f]
      simp [Category.assoc]
    change f = 0
    rw [← hrecover, hz]
    simp
  have horder := rankProjectiveHook_hom_nonzero_order
    (D.cover.tag j) (C.cover.tag i) g hg
  exact rankProjectiveHookHomOrder_weight_strict
    (D.cover.tag j) (C.cover.tag i) horder htags

/-- For an endomorphism fixed by the quotient of a shortest hook-sum cover,
every nonzero component of its difference from the identity strictly lowers
the finite hook weight. Equal-tag components vanish, including components
between distinct repeated occurrences, by the shortest-cover property. -/
theorem MinimalHookSumCover.endomorphism_sub_id_component_weight_strict
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M)
    (u : End (⨁ C.cover.summand))
    (hu : u ≫ C.cover.quotient = C.cover.quotient)
    (i j : C.cover.Index)
    (hcomponent : biproduct.components (u - (1 : End (⨁ C.cover.summand))) i j ≠ 0) :
    rankProjectiveHookTagWeight (C.cover.tag j) <
      rankProjectiveHookTagWeight (C.cover.tag i) := by
  classical
  let δ : End (⨁ C.cover.summand) := u - (1 : End (⨁ C.cover.summand))
  have hδq : δ ≫ C.cover.quotient = 0 := by
    dsimp [δ]
    rw [CategoryTheory.Preadditive.sub_comp, Category.id_comp, hu]
    simp
  let e : (⨁ C.cover.summand) ⟶ kernel C.cover.quotient :=
    kernel.lift C.cover.quotient δ hδq
  have he : e ≫ kernel.ι C.cover.quotient = δ :=
    kernel.lift_ι C.cover.quotient δ hδq
  have hcomponent' : biproduct.components δ i j =
      biproduct.ι C.cover.summand i ≫ e ≫ kernel.ι C.cover.quotient ≫
        biproduct.π C.cover.summand j := by
    dsimp [biproduct.components]
    rw [← he]
    simp [Category.assoc]
  have htags : C.cover.tag i ≠ C.cover.tag j := by
    intro htag
    let eSource : C.cover.summand i ≅
        FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
          (C.cover.tag i) :=
      eqToIso (C.cover.summand_eq_tag i)
    let eTag : FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
        (C.cover.tag i) ≅
        FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
          (C.cover.tag j) :=
      eqToIso (congrArg
        (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)) htag)
    let eIso := eSource.trans eTag
    have hz := C.kernel_component_eq_zero_of_iso j _ eIso
      (biproduct.ι C.cover.summand i ≫ e)
    have hzero : biproduct.components δ i j = 0 := by
      rw [hcomponent']
      exact hz
    apply hcomponent
    simpa [δ] using hzero
  let eSource : C.cover.summand i ≅
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
        (C.cover.tag i) :=
    eqToIso (C.cover.summand_eq_tag i)
  let eTarget : C.cover.summand j ≅
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
        (C.cover.tag j) :=
    eqToIso (C.cover.summand_eq_tag j)
  let g : FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
      (C.cover.tag i) ⟶
      FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
        (C.cover.tag j) :=
    eSource.inv ≫ biproduct.components δ i j ≫ eTarget.hom
  have hrecover : eSource.hom ≫ g ≫ eTarget.inv = biproduct.components δ i j := by
    dsimp [g]
    simp [Category.assoc]
  have hg : g ≠ 0 := by
    intro hz
    have hzero : biproduct.components δ i j = 0 := by
      rw [← hrecover, hz]
      simp
    apply hcomponent
    simpa [δ] using hzero
  have horder := rankProjectiveHook_hom_nonzero_order
    (C.cover.tag i) (C.cover.tag j) g hg
  exact rankProjectiveHookHomOrder_weight_strict
    (C.cover.tag i) (C.cover.tag j) horder htags

/-- Every finite hook-sum term is pointwise finite dimensional. -/
theorem HookSumCover.term_finiteDimensional
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : HookSumCover M) (p : P) :
    FiniteDimensional k ((⨁ C.summand).obj p) := by
  classical
  letI : ∀ i, FiniteDimensional k ((C.summand i).obj p) := fun i => by
    let e := eqToIso (C.summand_eq_tag i)
    letI : FiniteDimensional k
        ((FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k)
          (C.tag i)).obj p) := by
      cases C.tag i with
      | inl ab => change FiniteDimensional k ((Hook.module (k := k) ab.val.1 ab.val.2).obj p); infer_instance
      | inr a => change FiniteDimensional k ((HookInfinity.module (R := k) a).obj p); infer_instance
    exact (e.app p).toLinearEquiv.symm.finiteDimensional
  exact FiniteBiproduct.finiteDimensional C.summand p

/-- The kernel of a hook-sum cover is pointwise finite dimensional whenever
the covered module is. -/
theorem HookSumCover.kernel_finiteDimensional
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : HookSumCover M) :
    ∀ p, FiniteDimensional k ((kernel C.quotient).obj p) := by
  intro p
  letI : FiniteDimensional k ((⨁ C.summand).obj p) := C.term_finiteDimensional p
  exact FiniteDimensional.of_injective ((kernel.ι C.quotient).app p).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- The empty biproduct is the categorical zero object. -/
noncomputable def emptyBiproductIsoZero
    {P : Type} [PartialOrder P] [Fintype P] {I : Type} [IsEmpty I]
    (F : I → PModule.{u,0,u} k P) : (⨁ F) ≅ 0 := by
  let hterm : IsTerminal (⨁ F) :=
    (isLimitEquivIsTerminalOfIsEmpty (PModule.{u,0,u} k P)
      (biproduct.bicone F).toCone) (biproduct.isLimit F)
  exact ((isZero_zero (PModule.{u,0,u} k P)).isoIsTerminal hterm).symm

/-- A hook-sum cover with no summands can only cover the zero module. -/
theorem HookSumCover.isZero_of_isEmpty_index
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : HookSumCover M) [IsEmpty C.Index] : IsZero M := by
  classical
  let e := emptyBiproductIsoZero C.summand
  have hterm (p : P) (x : (⨁ C.summand).obj p) : x = 0 := by
    apply (e.app p).toLinearEquiv.injective
    exact (ModuleCat.subsingleton_of_isZero (R := k)
      (Functor.zero_obj p)).elim _ _
  have hM (p : P) (y : M.obj p) : y = 0 := by
    obtain ⟨x, hx⟩ := C.row_rank_exact.surjective p y
    have hx0 : (C.quotient.app p).hom x = 0 := by rw [hterm p x]; simp
    rw [hx0] at hx
    exact hx.symm
  apply (IsZero.iff_id_eq_zero M).mpr
  ext p x
  simp [hM p x]

private abbrev PointwisePfdModule (P : Type) [PartialOrder P] [Fintype P] :=
  {M : PModule.{u,0,u} k P // ∀ p, FiniteDimensional k (M.obj p)}

private noncomputable def chosenMinimalHookSumCover
    {P : Type} [PartialOrder P] [Fintype P] (X : PointwisePfdModule (k := k) P) :
    MinimalHookSumCover X.1 :=
  Classical.choice (exists_minimalHookSumCover X.1 X.2)

private noncomputable def hookCoverKernelPfd
    {P : Type} [PartialOrder P] [Fintype P] (X : PointwisePfdModule (k := k) P) :
    PointwisePfdModule (k := k) P := by
  let C := chosenMinimalHookSumCover X
  exact ⟨kernel C.cover.quotient, C.cover.kernel_finiteDimensional⟩

private noncomputable def iteratedMinimalKernel
    {P : Type} [PartialOrder P] [Fintype P]
    (X : PointwisePfdModule (k := k) P) : ℕ → PointwisePfdModule (k := k) P
  | 0 => X
  | n + 1 => hookCoverKernelPfd (iteratedMinimalKernel X n)

private noncomputable def iteratedMinimalHookCover
    {P : Type} [PartialOrder P] [Fintype P]
    (X : PointwisePfdModule (k := k) P) (n : ℕ) :
    MinimalHookSumCover (iteratedMinimalKernel X n).1 :=
  chosenMinimalHookSumCover (iteratedMinimalKernel X n)

private theorem exists_nonzero_differential_component
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M)
    (D : MinimalHookSumCover (kernel C.cover.quotient)) (j : D.cover.Index) :
    ∃ i : C.cover.Index,
      biproduct.ι D.cover.summand j ≫ D.cover.quotient ≫
        kernel.ι C.cover.quotient ≫ biproduct.π C.cover.summand i ≠ 0 := by
  classical
  let f : D.cover.summand j ⟶ ⨁ C.cover.summand :=
    biproduct.ι D.cover.summand j ≫ D.cover.quotient ≫ kernel.ι C.cover.quotient
  have hf : f ≠ 0 := by
    intro hz
    have hzero : biproduct.ι D.cover.summand j ≫ D.cover.quotient = 0 := by
      apply (cancel_mono (kernel.ι C.cover.quotient)).mp
      simpa [f, Category.assoc] using hz
    exact D.quotient_component_ne_zero j hzero
  by_contra hnone
  push Not at hnone
  apply hf
  apply biproduct.hom_ext
  intro i
  simpa [f, Category.assoc] using hnone i

private theorem iteratedMinimalHookCover_weight_lower_bound
    {P : Type} [PartialOrder P] [Fintype P]
    (X : PointwisePfdModule (k := k) P) :
    ∀ n (i : (iteratedMinimalHookCover X n).cover.Index),
      n ≤ rankProjectiveHookTagWeight ((iteratedMinimalHookCover X n).cover.tag i) := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Nat.zero_le _
  | succ n ih =>
      intro j
      let C := iteratedMinimalHookCover X n
      let D := iteratedMinimalHookCover X (n + 1)
      obtain ⟨i, hcomponent⟩ := exists_nonzero_differential_component C D j
      have hstrict := minimalHookCover_differential_component_weight_strict
        C D i j hcomponent
      have hprevious := ih i
      change rankProjectiveHookTagWeight
          ((iteratedMinimalHookCover X n).cover.tag i) <
        rankProjectiveHookTagWeight
          ((iteratedMinimalHookCover X (n + 1)).cover.tag j) at hstrict
      change n ≤ rankProjectiveHookTagWeight
          ((iteratedMinimalHookCover X n).cover.tag i) at hprevious
      omega

private theorem finitePosetRank_le_card
    {P : Type} [PartialOrder P] [Fintype P] (a : P) :
    finitePosetRank a ≤ Fintype.card P := by
  classical
  unfold finitePosetRank
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

private theorem rankProjectiveHookTagWeight_le_card
    {P : Type} [PartialOrder P] [Fintype P]
    (t : FiniteRankProjectiveClassification.RankProjectiveHookTag P) :
    rankProjectiveHookTagWeight t ≤ 3 * Fintype.card P + 1 := by
  cases t with
  | inl ab =>
      have hb := finitePosetRank_le_card ab.val.1
      have hd := finitePosetRank_le_card ab.val.2
      change finitePosetRank ab.val.1 + finitePosetRank ab.val.2 ≤
        3 * Fintype.card P + 1
      omega
  | inr a =>
      have ha := finitePosetRank_le_card a
      change finitePosetRank a + 2 * Fintype.card P + 1 ≤
        3 * Fintype.card P + 1
      omega

private theorem biproduct_components_comp
    {P : Type} [PartialOrder P] [Fintype P]
    {I : Type} [Fintype I] (F : I → PModule.{u,0,u} k P)
    (f g : End (⨁ F)) (i j : I) :
    biproduct.components (f ≫ g) i j =
      ∑ l : I, biproduct.components f i l ≫ biproduct.components g l j := by
  classical
  change biproduct.ι F i ≫ (f ≫ g) ≫ biproduct.π F j = _
  calc
    biproduct.ι F i ≫ (f ≫ g) ≫ biproduct.π F j =
        (biproduct.ι F i ≫ f) ≫
          (∑ l : I, biproduct.π F l ≫ biproduct.ι F l) ≫
          (g ≫ biproduct.π F j) := by
            rw [biproduct.total]
            simp [Category.assoc]
    _ = ∑ l : I,
        ((biproduct.ι F i ≫ f) ≫ biproduct.π F l) ≫
          (biproduct.ι F l ≫ (g ≫ biproduct.π F j)) := by
            simp only [CategoryTheory.Preadditive.comp_sum,
              CategoryTheory.Preadditive.sum_comp, Category.assoc]
    _ = ∑ l : I,
        biproduct.components f i l ≫ biproduct.components g l j := by
          apply Finset.sum_congr rfl
          intro l hl
          simp [biproduct.components, Category.assoc]

/-- A finite biproduct endomorphism whose nonzero components strictly lower a
bounded natural-number weight is nilpotent. The index type remains the actual
occurrence family, so repeated isomorphic summands are counted separately. -/
private theorem nilpotent_of_strictly_lowering_biproduct_components
    {P : Type} [PartialOrder P] [Fintype P]
    {I : Type} [Fintype I] (F : I → PModule.{u,0,u} k P)
    (weight : I → ℕ) (bound : ℕ) (hbound : ∀ i, weight i ≤ bound)
    (f : End (⨁ F))
    (hstrict : ∀ i j, biproduct.components f i j ≠ 0 → weight j < weight i) :
    IsNilpotent f := by
  classical
  have hpower : ∀ r i j,
      biproduct.components (f ^ r) i j ≠ 0 → r + weight j ≤ weight i := by
    intro r
    induction r with
    | zero =>
        intro i j hcomponent
        by_cases hij : i = j
        · subst j
          simp
        · have hzero : biproduct.components (1 : End (⨁ F)) i j = 0 := by
            simp [biproduct.components, hij]
          have hneq : biproduct.components (1 : End (⨁ F)) i j ≠ 0 := by
            simpa only [pow_zero] using hcomponent
          exact False.elim (hneq hzero)
    | succ r ihr =>
        intro i j hcomponent
        have hpower_comp : (f ^ (r + 1) : End (⨁ F)) = f ≫ f ^ r := by
          rw [pow_succ, End.mul_def]
        have hmatrix := biproduct_components_comp F f (f ^ r) i j
        rw [← hpower_comp] at hmatrix
        have hterm : ∃ l : I,
            biproduct.components f i l ≫ biproduct.components (f ^ r) l j ≠ 0 := by
          by_contra hnone
          have hzero (l : I) :
              biproduct.components f i l ≫ biproduct.components (f ^ r) l j = 0 := by
            by_contra hne
            exact hnone ⟨l, hne⟩
          have hsum :
              ∑ l : I, biproduct.components f i l ≫
                biproduct.components (f ^ r) l j = 0 := by
            apply Finset.sum_eq_zero
            intro l hl
            exact hzero l
          apply hcomponent
          rw [hmatrix]
          exact hsum
        obtain ⟨l, hcomp⟩ := hterm
        have hleft : biproduct.components f i l ≠ 0 := by
          intro hz
          apply hcomp
          simp [hz]
        have hright : biproduct.components (f ^ r) l j ≠ 0 := by
          intro hz
          apply hcomp
          simp [hz]
        have hleftWeight := hstrict i l hleft
        have hrightWeight := ihr l j hright
        omega
  have hzero : (f ^ (bound + 1) : End (⨁ F)) = 0 := by
    apply (biproduct.matrixEquiv (f := F) (g := F)).injective
    funext i
    funext j
    change biproduct.components (f ^ (bound + 1)) i j =
      biproduct.components (0 : End (⨁ F)) i j
    have hcomponent : biproduct.components (f ^ (bound + 1)) i j = 0 := by
      by_contra hne
      have hle := hpower (bound + 1) i j hne
      have hle' := hbound i
      omega
    rw [hcomponent]
    simp [biproduct.components]
  exact ⟨bound + 1, hzero⟩

/-- Every endomorphism of the middle term of a shortest hook-sum cover that is
fixed by the quotient is an isomorphism. The difference from the identity has
strictly weight-lowering occurrence components, hence is nilpotent. -/
theorem MinimalHookSumCover.endomorphism_over_quotient_isIso
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M)
    (u : End (⨁ C.cover.summand))
    (hu : u ≫ C.cover.quotient = C.cover.quotient) : IsIso u := by
  classical
  let δ : End (⨁ C.cover.summand) := u - (1 : End (⨁ C.cover.summand))
  let weight : C.cover.Index → ℕ := fun i =>
    rankProjectiveHookTagWeight (C.cover.tag i)
  have hbound (i : C.cover.Index) : weight i ≤ 3 * Fintype.card P + 1 :=
    rankProjectiveHookTagWeight_le_card (C.cover.tag i)
  have hstrict : ∀ i j, biproduct.components δ i j ≠ 0 → weight j < weight i := by
    intro i j hcomponent
    apply C.endomorphism_sub_id_component_weight_strict u hu i j
    simpa [δ] using hcomponent
  have hnilpotent := nilpotent_of_strictly_lowering_biproduct_components
    C.cover.summand weight (3 * Fintype.card P + 1) hbound δ hstrict
  have hunit : IsUnit (1 + δ : End (⨁ C.cover.summand)) :=
    hnilpotent.isUnit_one_add
  have hu_eq : u = (1 : End (⨁ C.cover.summand)) + δ := by
    simpa [δ, add_comm] using
      (sub_add_cancel u (1 : End (⨁ C.cover.summand))).symm
  have hunit' : IsUnit u := by
    rw [hu_eq]
    exact hunit
  exact CategoryTheory.isUnit_iff_isIso _ |>.mp hunit'

/-- The quotient of any shortest hook-sum cover is a rank-projective cover. -/
theorem MinimalHookSumCover.isRankProjectiveCover
    {P : Type} [PartialOrder P] [Fintype P] {M : PModule.{u,0,u} k P}
    (C : MinimalHookSumCover M) : IsRankProjectiveCover C.cover.quotient := by
  refine ⟨C.cover.term_isRankProjective, C.cover.row_rank_exact, ?_⟩
  intro u hu
  exact C.endomorphism_over_quotient_isIso u hu

/-- Every pointwise-finite-dimensional module over a finite poset has an actual
finite rank-projective resolution. The proof repeatedly takes a shortest
rank-exact hook-sum cover of each kernel. Every nonzero differential component
has higher weight at its source (in the later cover) than at its target (in the
preceding cover). Thus successive kernel covers move to higher weights. Since
the finite-poset weights are bounded, the iterated kernel reaches zero. -/
private noncomputable def ofPointwisePfdFinitePoset
    {P : Type} [PartialOrder P] [Fintype P]
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    FiniteRankProjectiveResolution M := by
  classical
  let X : PointwisePfdModule (k := k) P := ⟨M, hM⟩
  let N := 3 * Fintype.card P + 2
  letI : IsEmpty (iteratedMinimalHookCover X N).cover.Index :=
    ⟨fun i => by
      have hlower := iteratedMinimalHookCover_weight_lower_bound X N i
      have hupper := rankProjectiveHookTagWeight_le_card
        ((iteratedMinimalHookCover X N).cover.tag i)
      omega⟩
  have hterminal : IsZero (iteratedMinimalKernel X N).1 :=
    (iteratedMinimalHookCover X N).cover.isZero_of_isEmpty_index
  refine ⟨{
    length := N
    kernel := fun i => (iteratedMinimalKernel X i.val).1
    term := fun i => ⨁ (iteratedMinimalHookCover X i.val).cover.summand
    inclusion := fun i => kernel.ι (iteratedMinimalHookCover X i.val).cover.quotient
    quotient := fun i => (iteratedMinimalHookCover X i.val).cover.quotient
    row_rank_exact := fun i => (iteratedMinimalHookCover X i.val).cover.row_rank_exact
    initial_iso := Iso.refl M
    terminal_iso := ?_
  }, ?_⟩
  · exact (IsZero.isoZero hterminal)
  · intro i
    exact (iteratedMinimalHookCover X i.val).cover.term_isRankProjective

/-- Every pointwise finite-dimensional module on a finite poset admits an
actual finite rank-projective resolution. -/
theorem exists_finiteRankProjectiveResolution_of_pfd_finitePoset
    {P : Type} [PartialOrder P] [Fintype P]
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    Nonempty (FiniteRankProjectiveResolution M) :=
  ⟨ofPointwisePfdFinitePoset M hM⟩

/-- Every pointwise finite-dimensional module on a finite poset has a finite
rank-projective resolution whose every row quotient is a rank-projective
cover. The certificate is obtained from the same iterated shortest covers as
the finite-resolution construction. -/
theorem exists_minimalFiniteRankProjectiveResolution_of_pfd_finitePoset
    {P : Type} [PartialOrder P] [Fintype P]
    (M : PModule.{u,0,u} k P) (hM : ∀ p, FiniteDimensional k (M.obj p)) :
    Nonempty (MinimalFiniteRankProjectiveResolution (k := k) (M := M)) := by
  classical
  let X : PointwisePfdModule (k := k) P := ⟨M, hM⟩
  refine ⟨⟨ofPointwisePfdFinitePoset M hM, ?_⟩⟩
  intro i
  change IsRankProjectiveCover ((iteratedMinimalHookCover X i.val).cover.quotient)
  exact (iteratedMinimalHookCover X i.val).isRankProjectiveCover

end FiniteRankProjectiveResolution

namespace FiniteRankProjectiveResolution

/-- Transport a finite rank-projective resolution across an actual module isomorphism. -/
def ofIso {P : Type} [PartialOrder P] {M N : PModule.{u,0,u} k P}
    (R : FiniteRankProjectiveResolution M) (e : M ≅ N) :
    FiniteRankProjectiveResolution N := by
  refine ⟨{
    length := R.length
    kernel := R.kernel
    term := R.term
    inclusion := R.inclusion
    quotient := R.quotient
    row_rank_exact := R.row_rank_exact
    initial_iso := R.initial_iso.trans e
    terminal_iso := R.terminal_iso
  }, R.term_rank_projective⟩

/-- A pointwise finite-dimensional rank-projective module has its actual
one-row identity resolution. -/
noncomputable def ofRankProjective {P : Type} [PartialOrder P]
    (M : PModule.{u,0,u} k P) (hfd : ∀ p, FiniteDimensional k (M.obj p))
    (hM : IsRankProjective M) : FiniteRankProjectiveResolution M := by
  let Z : PModule.{u,0,u} k P := 0
  let kernel : Fin 2 → PModule.{u,0,u} k P :=
    fun i => if i.val = 0 then M else Z
  let term : Fin 1 → PModule.{u,0,u} k P := fun _ => M
  let inclusion : ∀ i : Fin 1, kernel i.succ ⟶ term i := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change Z ⟶ M
    exact 0
  let quotient : ∀ i : Fin 1, term i ⟶ kernel i.castSucc := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change M ⟶ M
    exact 𝟙 M
  have zeroIdRankExact : IsRankExact (0 : Z ⟶ M) (𝟙 M) := by
    let : ∀ p, FiniteDimensional k (M.obj p) := hfd
    have hshort : IsPointwiseShortExact (0 : Z ⟶ M) (𝟙 M) := by
      constructor
      · intro p x y _
        simpa [Z] using (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim x y
      · intro p x
        exact ⟨x, rfl⟩
      · intro p
        simp
    exact hshort.rankExact_of_section (𝟙 M) (by simp)
  refine ⟨{
    length := 1
    kernel := kernel
    term := term
    inclusion := inclusion
    quotient := quotient
    row_rank_exact := ?_
    initial_iso := ?_
    terminal_iso := ?_
  }, ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change IsRankExact (0 : Z ⟶ M) (𝟙 M)
    exact zeroIdRankExact
  · change kernel 0 ≅ M
    exact Iso.refl M
  · change Z ≅ 0
    exact Iso.refl Z
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hM

end FiniteRankProjectiveResolution

namespace CoordinateGrid

/-- The Kan extension of the zero grid module is a zero object. -/
private noncomputable def lanZeroIso (G : CoordinateGrid n) :
    G.lan.obj (0 : PModule.{u,0,u} k G.Point) ≅ 0 := by
  have hzero : IsZero (G.lan.obj (0 : PModule.{u,0,u} k G.Point)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    have hz : (𝟙 (0 : PModule.{u,0,u} k G.Point)) = 0 :=
      (IsZero.iff_id_eq_zero _).mp (isZero_zero _)
    calc
      𝟙 (G.lan.obj (0 : PModule.{u,0,u} k G.Point)) =
          G.lan.map (𝟙 (0 : PModule.{u,0,u} k G.Point)) := by
            exact (G.lan.map_id _).symm
      _ = G.lan.map (0 : (0 : PModule.{u,0,u} k G.Point) ⟶ 0) := by rw [hz]
      _ = 0 := G.lan.map_zero _ _
  exact hzero.iso (isZero_zero _)

/-- Transfer every actual row of a finite rank-projective grid resolution through
the coordinate-grid left Kan extension. The same finite occurrence indexing is retained. -/
noncomputable def lanFiniteRankProjectiveResolution (G : CoordinateGrid n)
    {A : PModule.{u,0,u} k G.Point} (R : FiniteRankProjectiveResolution A) :
    FiniteRankProjectiveResolution (G.lan.obj A) := by
  refine ⟨{
    length := R.length
    kernel := fun i => G.lan.obj (R.kernel i)
    term := fun i => G.lan.obj (R.term i)
    inclusion := fun i => G.lan.map (R.inclusion i)
    quotient := fun i => G.lan.map (R.quotient i)
    row_rank_exact := fun i => G.lan_isRankExact (R.row_rank_exact i)
    initial_iso := G.lan.mapIso R.initial_iso
    terminal_iso := (G.lan.mapIso R.terminal_iso).trans (lanZeroIso G)
  }, ?_⟩
  intro i
  exact G.lan_isRankProjective (R.term i) (R.term_rank_projective i)

/-- Left Kan extension transfers the actual projective-cover certificate on
every row of a minimal finite-grid resolution. For the endomorphism condition,
the quotient-fixed map is lifted through the full-faithful Lan map, certified
on the grid, then mapped back through Lan. -/
theorem lanMinimalFiniteRankProjectiveResolution (G : CoordinateGrid n)
    {A : PModule.{u,0,u} k G.Point}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := A)) :
    Nonempty (MinimalFiniteRankProjectiveResolution (k := k) (M := G.lan.obj A)) := by
  classical
  refine ⟨{
    resolution := G.lanFiniteRankProjectiveResolution R.resolution
    quotient_is_cover := ?_
  }⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · exact G.lan_isRankProjective (R.resolution.term i)
      (R.resolution.term_rank_projective i)
  · exact (G.lan_isRankExact (R.quotient_is_cover i).row_rank_exact).isRankDeflation.rankExact_kernel
  · intro u hu
    let u₀ := G.lanMapPreimage u
    have hmap : G.lan.map u₀ = u := by
      dsimp [u₀]
      exact G.lan_map_preimage u
    have hquot :
        (G.lanFiniteRankProjectiveResolution R.resolution).quotient i =
          G.lan.map (R.resolution.quotient i) := rfl
    have hu₀ : u₀ ≫ R.resolution.quotient i = R.resolution.quotient i := by
      apply G.lan_map_injective
      calc
        G.lan.map (u₀ ≫ R.resolution.quotient i) =
            G.lan.map u₀ ≫ G.lan.map (R.resolution.quotient i) :=
          Functor.map_comp _ _ _
        _ = u ≫ (G.lanFiniteRankProjectiveResolution R.resolution).quotient i := by
          rw [hmap, ← hquot]
        _ = (G.lanFiniteRankProjectiveResolution R.resolution).quotient i := hu
    letI : IsIso u₀ := (R.quotient_is_cover i).endomorphism_isIso u₀ hu₀
    have hLanIso : IsIso (G.lan.map u₀) := Functor.map_isIso _ _
    rw [← hmap]
    exact hLanIso

/-- Transport a finite rank-projective resolution across the presentation-grid
reconstruction isomorphism, retaining all Lan-transferred rows. -/
noncomputable def lanFiniteRankProjectiveResolutionOfReconstruction
    (G : CoordinateGrid n) {A : PModule.{u,0,u} k G.Point}
    (R : FiniteRankProjectiveResolution A)
    {M : PModule.{u,0,u} k (Fin n → ℝ)} (e : G.lan.obj A ≅ M) :
    FiniteRankProjectiveResolution M :=
  FiniteRankProjectiveResolution.ofIso (G.lanFiniteRankProjectiveResolution R) e

end CoordinateGrid

namespace FiniteRankProjectiveResolution

/-- Every finitely presented module on a positive-dimensional real coordinate
poset has an actual finite rank-projective resolution. The finite presentation
is used only to reconstruct the module from a finite grid with pfd fibers;
resolution existence is then proved on that finite poset and transported by
the actual left Kan extension. -/
theorem finitelyPresented_exists_finiteRankProjectiveResolution
    {n : ℕ} (_hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin n → ℝ) M) :
    Nonempty (FiniteRankProjectiveResolution M) := by
  classical
  obtain ⟨G, A, hA, ⟨e⟩⟩ :=
    GradedFree.finitelyPresented_exists_pfd_finiteGridKan M hM
  let R := Classical.choice
    (exists_finiteRankProjectiveResolution_of_pfd_finitePoset A hA)
  exact ⟨CoordinateGrid.lanFiniteRankProjectiveResolutionOfReconstruction G R e⟩

/-- Every originally finitely presented module on a positive-dimensional real
coordinate poset has an actual finite rank-projective resolution whose every
quotient row is certified as a projective cover. The construction reconstructs
the presentation on a finite grid, transfers its minimal resolution through
the actual left Kan extension, then transports the rows across the reconstruction
isomorphism. -/
theorem finitelyPresented_exists_minimalFiniteRankProjectiveResolution
    {n : ℕ} (_hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0}
      (R := k) (P := Fin n → ℝ) M) :
    Nonempty (MinimalFiniteRankProjectiveResolution (k := k) (M := M)) := by
  classical
  obtain ⟨G, A, hA, ⟨e⟩⟩ :=
    GradedFree.finitelyPresented_exists_pfd_finiteGridKan M hM
  obtain ⟨R⟩ :=
    FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_of_pfd_finitePoset
      A hA
  obtain ⟨R'⟩ := G.lanMinimalFiniteRankProjectiveResolution R
  exact ⟨{
    resolution := R'.resolution.ofIso e
    quotient_is_cover := fun i => by
      change IsRankProjectiveCover (R'.resolution.quotient i)
      exact R'.quotient_is_cover i
  }⟩

end FiniteRankProjectiveResolution

end TDA.Persistence
