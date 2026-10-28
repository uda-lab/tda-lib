import TDA.Persistence.FinitePresentationColimits
import TDA.Persistence.FinitePresentationComparison
import TDA.Persistence.FinitePresentationFiniteDimensional
import TDA.Persistence.RankExactKernel
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Finite presentations of short exact extensions

An ordinary pointwise short exact extension of two finitely presented
persistence modules is finitely presented. The proof first splits the pullback
of the quotient map along a finite free cover of its target, then presents the
middle module as the cokernel of the lifted relations.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open GradedFree

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
variable {L M N T : PModule.{u,0,u} k P}
variable {ι : L ⟶ M} {π : M ⟶ N}

private instance : HasBinaryBiproducts (PModule.{u,0,u} k P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

namespace IsPointwiseShortExact

/-- The left map into the pullback of a pointwise short exact row is induced by
the original inclusion and the zero map. -/
noncomputable def pullbackInclusion (hs : IsPointwiseShortExact ι π)
    (f : T ⟶ N) : L ⟶ Limits.pullback π f :=
  Limits.pullback.lift ι 0 (by
    rw [zero_comp, hs.comp_eq_zero])

@[reassoc (attr := simp)]
theorem pullbackInclusion_fst (hs : IsPointwiseShortExact ι π) (f : T ⟶ N) :
    hs.pullbackInclusion f ≫ Limits.pullback.fst π f = ι :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackInclusion_snd (hs : IsPointwiseShortExact ι π) (f : T ⟶ N) :
    hs.pullbackInclusion f ≫ Limits.pullback.snd π f = 0 :=
  Limits.pullback.lift_snd _ _ _

/-- Pulling back the quotient map preserves ordinary pointwise short
exactness, with the actual categorical pullback and its second projection. -/
theorem pullback_pointwise (hs : IsPointwiseShortExact ι π) (f : T ⟶ N) :
    IsPointwiseShortExact (hs.pullbackInclusion f) (Limits.pullback.snd π f) where
  injective p := by
    intro x y hxy
    have hfst := congrArg ((Limits.pullback.fst π f).app p).hom hxy
    have hcomp : (hs.pullbackInclusion f ≫ Limits.pullback.fst π f).app p =
        (ι.app p) := by simp
    have hx := congrArg (fun g : L.obj p ⟶ M.obj p => g.hom x) hcomp
    have hy := congrArg (fun g : L.obj p ⟶ M.obj p => g.hom y) hcomp
    apply hs.injective p
    calc
      (ι.app p).hom x =
          ((Limits.pullback.fst π f).app p).hom
            (((hs.pullbackInclusion f).app p).hom x) := hx.symm
      _ = ((Limits.pullback.fst π f).app p).hom
          (((hs.pullbackInclusion f).app p).hom y) := hfst
      _ = (ι.app p).hom y := hy
  surjective p t := by
    obtain ⟨m, hm⟩ := hs.surjective p ((f.app p).hom t)
    exact ⟨PullbackFiber.mk π f p m t hm, PullbackFiber.snd_mk π f p m t hm⟩
  range_eq_ker p := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hcomp := congrArg (fun g : L ⟶ T => (g.app p).hom x)
        (hs.pullbackInclusion_snd f)
      change ((Limits.pullback.snd π f).app p).hom
        (((hs.pullbackInclusion f).app p).hom x) = 0
      have hcomp' : ((Limits.pullback.snd π f).app p).hom
          (((hs.pullbackInclusion f).app p).hom x) =
            ((0 : L ⟶ T).app p).hom x := by
        simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using hcomp
      exact hcomp'.trans (by simp)
    · intro hy
      change ((Limits.pullback.snd π f).app p).hom y = 0 at hy
      have hπy : (π.app p).hom (((Limits.pullback.fst π f).app p).hom y) = 0 := by
        have h := congrArg (fun g : Limits.pullback π f ⟶ N => (g.app p).hom y)
          (Limits.pullback.condition (f := π) (g := f))
        change (π.app p).hom (((Limits.pullback.fst π f).app p).hom y) =
          (f.app p).hom (((Limits.pullback.snd π f).app p).hom y) at h
        rw [hy] at h
        simpa using h
      have hmem : ((Limits.pullback.fst π f).app p).hom y ∈
          LinearMap.range (ι.app p).hom := by
        exact (hs.range_eq_ker p).symm ▸ (LinearMap.mem_ker.mpr hπy)
      obtain ⟨x, hx⟩ := hmem
      refine ⟨x, ?_⟩
      apply PullbackFiber.element_ext π f p
      ·
        have hcomp := congrArg (fun g : L ⟶ M => (g.app p).hom x)
          (hs.pullbackInclusion_fst f)
        calc
          ((Limits.pullback.fst π f).app p).hom
              (((hs.pullbackInclusion f).app p).hom x) = (ι.app p).hom x := by
            simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using hcomp
          _ = ((Limits.pullback.fst π f).app p).hom y := hx
      ·
        have hcomp := congrArg (fun g : L ⟶ T => (g.app p).hom x)
          (hs.pullbackInclusion_snd f)
        simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using
          (hcomp.trans hy.symm)

end IsPointwiseShortExact

/-- Finite presentation is closed under an ordinary pointwise short exact
extension. The result assumes finite presentations only for the two outer
objects, with no pointwise finite-dimensionality or rank-exactness hypothesis
on the given row. -/
theorem IsPointwiseShortExact.finitelyPresented_middle
    (hs : IsPointwiseShortExact ι π)
    (hL : FinitelyPresented.{u,0,0} (R := k) (P := P) L)
    (hN : FinitelyPresented.{u,0,0} (R := k) (P := P) N) :
    FinitelyPresented.{u,0,0} (R := k) (P := P) M := by
  classical
  obtain ⟨E, hE, ⟨e⟩⟩ := hN
  letI : Finite E.generators.Carrier := hE.1
  letI : Finite E.relations.Carrier := hE.2
  let Q := module (R := k) E.generators
  let c : Q ⟶ N := E.cover ≫ e.hom
  obtain ⟨b, hb⟩ := GradedFree.exists_lift_of_surjective
    (R := k) E.generators π hs.surjective c
  let s : Q ⟶ Limits.pullback π c :=
    Limits.pullback.lift b (𝟙 Q) (by simpa [c] using hb)
  have hssec : s ≫ Limits.pullback.snd π c = 𝟙 Q := by
    change Limits.pullback.lift b (𝟙 Q) _ ≫ Limits.pullback.snd π c = 𝟙 Q
    rw [Limits.pullback.lift_snd]
  let hpb := hs.pullback_pointwise c
  let S : ShortComplex (PModule.{u,0,u} k P) :=
    ShortComplex.mk (hs.pullbackInclusion c) (Limits.pullback.snd π c)
      hpb.comp_eq_zero
  have hS : S.ShortExact := by
    simpa [S] using hpb.shortExact
  let splitIso : Limits.pullback π c ≅ L ⊞ Q :=
    ShortComplex.Splitting.isoBinaryBiproduct
      (ShortComplex.Splitting.ofExactOfSection S hS.exact s hssec hS.mono_f)
  have hQ : FinitelyPresented.{u,0,0} (R := k) (P := P) Q := by
    change FinitelyPresented.{u,0,0} (R := k) (P := P)
      (module (R := k) E.generators)
    exact GradedFree.free_finitelyPresented E.generators
  have hPullback :
      FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.pullback π c) :=
    finitelyPresented_of_iso (finitelyPresented_biprod hL hQ) splitIso.symm
  let A := module (R := k) E.relations
  have hA : FinitelyPresented.{u,0,0} (R := k) (P := P) A := by
    change FinitelyPresented.{u,0,0} (R := k) (P := P)
      (module (R := k) E.relations)
    exact GradedFree.free_finitelyPresented E.relations
  have hrelPB : (0 : A ⟶ M) ≫ π = E.relationMap ≫ c := by
    rw [zero_comp, ← Category.assoc, E.relations_vanish]
    simp
  let r : A ⟶ Limits.pullback π c :=
    Limits.pullback.lift (f := π) (g := c) 0 E.relationMap hrelPB
  have hrSnd : r ≫ Limits.pullback.snd π c = E.relationMap :=
    Limits.pullback.lift_snd (f := π) (g := c) 0 E.relationMap hrelPB
  let q : Limits.pullback π c ⟶ M := Limits.pullback.fst π c
  have hrq : r ≫ q = 0 := by
    change Limits.pullback.lift 0 E.relationMap _ ≫ Limits.pullback.fst π c = 0
    rw [Limits.pullback.lift_fst]
  let C : ShortComplex (PModule.{u,0,u} k P) := ShortComplex.mk r q hrq
  have hKernelLift : ∀ p,
      Function.Surjective ((kernel.lift q r hrq).app p).hom := by
    intro p z
    let y := ((kernel.ι q).app p).hom z
    let t := ((Limits.pullback.snd π c).app p).hom y
    have hyq : (q.app p).hom y = 0 := by
      have h := congrArg (fun g : kernel q ⟶ M => (g.app p).hom z)
        (kernel.condition q)
      change (q.app p).hom (((kernel.ι q).app p).hom z) = 0 at h
      exact h
    have hfst : ((Limits.pullback.fst π c).app p).hom y = 0 := by
      simpa [q] using hyq
    have hcy : (c.app p).hom t = 0 := by
      have h := congrArg (fun g : Limits.pullback π c ⟶ N => (g.app p).hom y)
        (Limits.pullback.condition (f := π) (g := c))
      change (π.app p).hom (((Limits.pullback.fst π c).app p).hom y) =
        (c.app p).hom (((Limits.pullback.snd π c).app p).hom y) at h
      calc
        (c.app p).hom t = (π.app p).hom (((Limits.pullback.fst π c).app p).hom y) := by
          simpa [t] using h.symm
        _ = 0 := by rw [hfst]; simp
    have hcoverzero : (E.cover.app p).hom t = 0 := by
      have hinj : Function.Injective (e.hom.app p).hom :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      have hezero : (e.hom.app p).hom ((E.cover.app p).hom t) = 0 := by
        simpa only [c, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using hcy
      exact hinj (by simpa using hezero)
    obtain ⟨x, hx⟩ := (E.cover_eq_zero_iff_mem_relation_range p t).mp hcoverzero
    have hrx : (r.app p).hom x = y := by
      apply PullbackFiber.element_ext π c p
      · have h := congrArg (fun g : A ⟶ M => (g.app p).hom x) hrq
        have hfst_r : ((Limits.pullback.fst π c).app p).hom ((r.app p).hom x) = 0 := by
          simpa [q, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using h
        calc
          ((Limits.pullback.fst π c).app p).hom ((r.app p).hom x) = 0 := hfst_r
          _ = ((Limits.pullback.fst π c).app p).hom y := hfst.symm
      · have h := congrArg (fun g : A ⟶ Q => (g.app p).hom x) hrSnd
        calc
          ((Limits.pullback.snd π c).app p).hom ((r.app p).hom x) =
              (E.relationMap.app p).hom x := by
                simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using h
          _ = t := hx
          _ = ((Limits.pullback.snd π c).app p).hom y := rfl
    refine ⟨x, ?_⟩
    apply RankKernel.injective q p
    calc
      ((kernel.ι q).app p).hom (((kernel.lift q r hrq).app p).hom x) =
          (r.app p).hom x := by
            have h := congrArg (fun g : A ⟶ Limits.pullback π c => (g.app p).hom x)
              (kernel.lift_ι q r hrq)
            simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using h
      _ = y := hrx
  have hEpi : Epi (kernel.lift q r hrq) :=
    (NatTrans.epi_iff_epi_app _).2 (fun p =>
      (ModuleCat.epi_iff_surjective _).2 (hKernelLift p))
  have hExact : C.Exact := C.exact_iff_epi_kernel_lift.mpr hEpi
  letI : Epi E.cover := by
    change Epi (cokernel.π E.relationMap)
    infer_instance
  letI : Epi e.hom := inferInstance
  letI : Epi c := by
    dsimp [c]
    infer_instance
  have hqEpi : Epi q := by
    change Epi (Limits.pullback.fst π c)
    infer_instance
  letI : Epi C.g := by
    change Epi q
    exact hqEpi
  have cokerIso : Limits.cokernel r ≅ M :=
    (cokernelIsCokernel r).coconePointUniqueUpToIso hExact.gIsCokernel
  have hCoker :
      FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.cokernel r) :=
    finitelyPresented_cokernel r hA hPullback
  exact finitelyPresented_of_iso hCoker cokerIso

end TDA.Persistence
