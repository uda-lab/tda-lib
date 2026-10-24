import TDA.Persistence.RankExact
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Pushouts of rank-exact sequences

Pushing out the first map of a rank-exact short exact sequence along a map to a
pointwise finite-dimensional module gives another rank-exact short exact
sequence. The row is proved from the actual pushout:
its quotient is induced by the original quotient and zero, and its fibers are
finite dimensional because the actual pushout is a quotient of the biproduct
of the original middle fiber and the new left fiber. Rank additivity then
follows by sending the original same-death lifts into the pushout.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
variable {L M N L' : PModule.{u,0,u} k P}
variable {ι : L ⟶ M} {π : M ⟶ N}

private instance : HasBinaryBiproducts (PModule.{u,0,u} k P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

private theorem pointZero (hs : IsPointwiseShortExact ι π) (p : P) :
    (ι.app p) ≫ (π.app p) = 0 := by
  ext x
  have hx : (ι.app p).hom x ∈ LinearMap.range (ι.app p).hom := ⟨x, rfl⟩
  rw [hs.range_eq_ker p] at hx
  exact hx

private theorem pointwiseCompZero (hs : IsPointwiseShortExact ι π) : ι ≫ π = 0 := by
  ext p x
  have hx : (ι.app p).hom x ∈ LinearMap.range (ι.app p).hom := ⟨x, rfl⟩
  rw [hs.range_eq_ker p] at hx
  exact hx

namespace IsPointwiseShortExact

/-- The quotient of the pushout is induced by the original quotient and zero. -/
noncomputable def pushoutQuotient (hs : IsPointwiseShortExact ι π) (f : L ⟶ L') :
    Limits.pushout ι f ⟶ N :=
  Limits.pushout.desc π 0 (by rw [pointwiseCompZero hs]; simp)

@[reassoc (attr := simp)]
theorem pushoutQuotient_inl (hs : IsPointwiseShortExact ι π) (f : L ⟶ L') :
    Limits.pushout.inl ι f ≫ hs.pushoutQuotient f = π := by
  exact Limits.pushout.inl_desc π 0 _

@[reassoc (attr := simp)]
theorem pushoutQuotient_inr (hs : IsPointwiseShortExact ι π) (f : L ⟶ L') :
    Limits.pushout.inr ι f ≫ hs.pushoutQuotient f = 0 := by
  exact Limits.pushout.inr_desc π 0 _

private noncomputable def fiberPushoutQuotient (hs : IsPointwiseShortExact ι π) (p : P)
    (f : L.obj p ⟶ L'.obj p) : Limits.pushout (ι.app p) f ⟶ N.obj p :=
  Limits.pushout.desc (π.app p) 0 (by rw [pointZero hs p]; simp)

private theorem fiberPushoutShortExact (hs : IsPointwiseShortExact ι π) (p : P)
    (f : L.obj p ⟶ L'.obj p) :
    (ShortComplex.mk (Limits.pushout.inr (ι.app p) f) (fiberPushoutQuotient hs p f)
      (by
        change Limits.pushout.inr (ι.app p) f ≫
          Limits.pushout.desc (π.app p) (0 : L'.obj p ⟶ N.obj p) _ = 0
        exact Limits.pushout.inr_desc (π.app p) (0 : L'.obj p ⟶ N.obj p) _)).ShortExact := by
  let S : ShortComplex (ModuleCat.{u} k) :=
    ShortComplex.mk (ι.app p) (π.app p) (pointZero hs p)
  have hSExact : S.Exact := by
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker S).2
    exact hs.range_eq_ker p
  haveI : Mono (ι.app p) := (ModuleCat.mono_iff_injective _).2 (hs.injective p)
  haveI : Epi (π.app p) := (ModuleCat.epi_iff_surjective _).2 (hs.surjective p)
  have hSShort : S.ShortExact := ⟨hSExact⟩
  let q : Limits.pushout (ι.app p) f ⟶ N.obj p :=
    Limits.pushout.desc (π.app p) (0 : L'.obj p ⟶ N.obj p)
      (by rw [pointZero hs p]; simp)
  have hqInl : Limits.pushout.inl (ι.app p) f ≫ q = π.app p := by
    dsimp [q]
    exact Limits.pushout.inl_desc _ _ _
  have hqInr : Limits.pushout.inr (ι.app p) f ≫ q = 0 := by
    dsimp [q]
    exact Limits.pushout.inr_desc _ _ _
  have hqzero : Limits.pushout.inr (ι.app p) f ≫ q = 0 := by
    exact hqInr
  have hqcolim : IsColimit (CokernelCofork.ofπ q hqzero) := by
    let kill {Z : ModuleCat.{u} k} (v : Limits.pushout (ι.app p) f ⟶ Z)
        (hv : Limits.pushout.inr (ι.app p) f ≫ v = 0) :
        (ι.app p) ≫ (Limits.pushout.inl (ι.app p) f ≫ v) = 0 := by
      calc
        (ι.app p) ≫ (Limits.pushout.inl (ι.app p) f ≫ v) =
            ((ι.app p) ≫ Limits.pushout.inl (ι.app p) f) ≫ v := by simp only [Category.assoc]
        _ = (f ≫ Limits.pushout.inr (ι.app p) f) ≫ v := by rw [Limits.pushout.condition]
        _ = f ≫ (Limits.pushout.inr (ι.app p) f ≫ v) := by simp only [Category.assoc]
        _ = 0 := by rw [hv]; simp
    let factor {Z : ModuleCat.{u} k} (v : Limits.pushout (ι.app p) f ⟶ Z)
        (hv : Limits.pushout.inr (ι.app p) f ≫ v = 0) : N.obj p ⟶ Z :=
      (CokernelCofork.IsColimit.desc' hSShort.gIsCokernel
        (Limits.pushout.inl (ι.app p) f ≫ v) (kill v hv)).1
    have factor_fac {Z : ModuleCat.{u} k} (v : Limits.pushout (ι.app p) f ⟶ Z)
        (hv : Limits.pushout.inr (ι.app p) f ≫ v = 0) :
        (π.app p) ≫ factor v hv = Limits.pushout.inl (ι.app p) f ≫ v :=
      (CokernelCofork.IsColimit.desc' hSShort.gIsCokernel
        (Limits.pushout.inl (ι.app p) f ≫ v) (kill v hv)).2
    refine CokernelCofork.IsColimit.ofπ q hqzero
      (fun {Z} v hv => factor v hv)
      (fun {Z} v hv => by
        apply Limits.pushout.hom_ext
        · calc
            Limits.pushout.inl (ι.app p) f ≫ q ≫ factor v hv =
                (π.app p) ≫ factor v hv := by
                  rw [← Category.assoc, hqInl]
            _ = Limits.pushout.inl (ι.app p) f ≫ v := factor_fac v hv
        · calc
            Limits.pushout.inr (ι.app p) f ≫ q ≫ factor v hv = 0 := by
              rw [← Category.assoc, hqInr]
              simp
            _ = Limits.pushout.inr (ι.app p) f ≫ v := by rw [hv])
      (fun {Z} v hv m hm => by
        letI : Epi (π.app p) := hSShort.epi_g
        apply (cancel_epi (π.app p)).1
        calc
          (π.app p) ≫ m = (Limits.pushout.inl (ι.app p) f ≫ q) ≫ m := by
            rw [hqInl]
          _ = Limits.pushout.inl (ι.app p) f ≫ v := by rw [Category.assoc, hm]
          _ = (π.app p) ≫ factor v hv := (factor_fac v hv).symm)
  let T : ShortComplex (ModuleCat.{u} k) :=
    ShortComplex.mk (Limits.pushout.inr (ι.app p) f) q hqzero
  have hTExact : T.Exact := ShortComplex.exact_of_g_is_cokernel _ hqcolim
  haveI : Mono T.f := by
    dsimp [T]
    infer_instance
  haveI : Epi T.g := by
    dsimp [T]
    exact Cofork.IsColimit.epi hqcolim
  simpa [T, q, fiberPushoutQuotient] using (show T.ShortExact from ⟨hTExact⟩)

private theorem fiberPushout_injective (hs : IsPointwiseShortExact ι π) (p : P)
    (f : L.obj p ⟶ L'.obj p) :
    Function.Injective (Limits.pushout.inr (ι.app p) f).hom := by
  exact (ModuleCat.mono_iff_injective _).1
    (fiberPushoutShortExact hs p f).mono_f

private theorem fiberPushout_surjective (hs : IsPointwiseShortExact ι π) (p : P)
    (f : L.obj p ⟶ L'.obj p) :
    Function.Surjective (fiberPushoutQuotient hs p f).hom := by
  exact (ModuleCat.epi_iff_surjective _).1
    (fiberPushoutShortExact hs p f).epi_g

private theorem fiberPushout_range_eq_ker (hs : IsPointwiseShortExact ι π) (p : P)
    (f : L.obj p ⟶ L'.obj p) :
    LinearMap.range (Limits.pushout.inr (ι.app p) f).hom =
      LinearMap.ker (fiberPushoutQuotient hs p f).hom :=
  ShortComplex.Exact.moduleCat_range_eq_ker (fiberPushoutShortExact hs p f).exact

private theorem pushoutObjIso_quotient (hs : IsPointwiseShortExact ι π) (f : L ⟶ L')
    (p : P) :
    (Limits.pushoutObjIso ι f p).inv ≫ (hs.pushoutQuotient f).app p =
      fiberPushoutQuotient hs p (f.app p) := by
  refine Limits.pushout.hom_ext ?_ ?_
  · calc
      Limits.pushout.inl (ι.app p) (f.app p) ≫ (Limits.pushoutObjIso ι f p).inv ≫
          (hs.pushoutQuotient f).app p =
          (pushout.inl ι f).app p ≫ (hs.pushoutQuotient f).app p := by
            change (Limits.pushout.inl (ι.app p) (f.app p) ≫
              (Limits.pushoutObjIso ι f p).inv) ≫ (hs.pushoutQuotient f).app p = _
            rw [Limits.inl_comp_pushoutObjIso_inv]
      _ = (π.app p) := by
        have h := NatTrans.congr_app (pushoutQuotient_inl hs f) p
        change ((pushout.inl ι f).app p ≫ (hs.pushoutQuotient f).app p) = π.app p at h
        exact h
      _ = pushout.inl (ι.app p) (f.app p) ≫ fiberPushoutQuotient hs p (f.app p) := by
        exact (Limits.pushout.inl_desc (π.app p) 0 _).symm
  · calc
      Limits.pushout.inr (ι.app p) (f.app p) ≫ (Limits.pushoutObjIso ι f p).inv ≫
          (hs.pushoutQuotient f).app p =
          (pushout.inr ι f).app p ≫ (hs.pushoutQuotient f).app p := by
            change (Limits.pushout.inr (ι.app p) (f.app p) ≫
              (Limits.pushoutObjIso ι f p).inv) ≫ (hs.pushoutQuotient f).app p = _
            rw [Limits.inr_comp_pushoutObjIso_inv]
      _ = 0 := by
        have h := NatTrans.congr_app (pushoutQuotient_inr hs f) p
        change ((pushout.inr ι f).app p ≫ (hs.pushoutQuotient f).app p) = 0 at h
        exact h
      _ = pushout.inr (ι.app p) (f.app p) ≫ fiberPushoutQuotient hs p (f.app p) := by
        exact (Limits.pushout.inr_desc (π.app p) 0 _).symm

/-- Pushing out the first map preserves pointwise short exactness. -/
theorem pushout_pointwise (hs : IsPointwiseShortExact ι π) (f : L ⟶ L') :
    IsPointwiseShortExact (Limits.pushout.inr ι f) (hs.pushoutQuotient f) where
  injective p := by
    let e := Limits.pushoutObjIso ι f p
    have hinr := Limits.inr_comp_pushoutObjIso_hom ι f p
    have hinj := fiberPushout_injective hs p (f.app p)
    intro x y hxy
    have h := congrArg e.hom.hom hxy
    have hfiber : (Limits.pushout.inr (ι.app p) (f.app p)).hom x =
        (Limits.pushout.inr (ι.app p) (f.app p)).hom y := by
      calc
        (Limits.pushout.inr (ι.app p) (f.app p)).hom x =
            ((Limits.pushout.inr ι f).app p ≫ e.hom).hom x := by rw [hinr]
        _ = e.hom.hom (((Limits.pushout.inr ι f).app p).hom x) := by
            rw [ModuleCat.comp_apply]
        _ = e.hom.hom (((Limits.pushout.inr ι f).app p).hom y) := h
        _ = ((Limits.pushout.inr ι f).app p ≫ e.hom).hom y := by
            rw [ModuleCat.comp_apply]
        _ = (Limits.pushout.inr (ι.app p) (f.app p)).hom y := by rw [hinr]
    exact hinj hfiber
  surjective p := by
    let e := Limits.pushoutObjIso ι f p
    have hq := pushoutObjIso_quotient hs f p
    intro n
    obtain ⟨x, hx⟩ := fiberPushout_surjective hs p (f.app p) n
    refine ⟨e.inv.hom x, ?_⟩
    have h := congrArg (fun g : pushout (ι.app p) (f.app p) ⟶ N.obj p => g.hom x) hq
    simpa [hx] using h
  range_eq_ker p := by
    let e := Limits.pushoutObjIso ι f p
    have hinr := Limits.inr_comp_pushoutObjIso_hom ι f p
    have hq := pushoutObjIso_quotient hs f p
    have hq' : e.hom ≫ fiberPushoutQuotient hs p (f.app p) =
        (hs.pushoutQuotient f).app p := by
      calc
        e.hom ≫ fiberPushoutQuotient hs p (f.app p) =
            e.hom ≫ (e.inv ≫ (hs.pushoutQuotient f).app p) := by rw [hq]
        _ = (e.hom ≫ e.inv) ≫ (hs.pushoutQuotient f).app p := by
            rw [← Category.assoc]
        _ = (𝟙 _) ≫ (hs.pushoutQuotient f).app p := by rw [e.hom_inv_id]
        _ = (hs.pushoutQuotient f).app p := by simp
    have hexact := fiberPushout_range_eq_ker hs p (f.app p)
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have happ := NatTrans.congr_app (pushoutQuotient_inr hs f) p
      change ((Limits.pushout.inr ι f).app p ≫ (hs.pushoutQuotient f).app p) = 0 at happ
      change ((hs.pushoutQuotient f).app p).hom
        (((Limits.pushout.inr ι f).app p).hom y) = 0
      have hzero := congrArg (fun g : L'.obj p ⟶ N.obj p => g.hom y) happ
      simpa using hzero
    · intro hx
      change ((hs.pushoutQuotient f).app p).hom x = 0 at hx
      have hxq : (fiberPushoutQuotient hs p (f.app p)).hom (e.hom.hom x) = 0 := by
        have h := congrArg (fun g : (Limits.pushout ι f).obj p ⟶ N.obj p =>
          g.hom x) hq'
        simpa using h.trans hx
      have hxrange : e.hom.hom x ∈
          LinearMap.range (Limits.pushout.inr (ι.app p) (f.app p)).hom := by
        rw [hexact]
        exact hxq
      obtain ⟨y, hy⟩ := hxrange
      refine ⟨y, ?_⟩
      have he : Function.Injective e.hom.hom :=
        (ModuleCat.mono_iff_injective _).mp inferInstance
      apply he
      change e.hom.hom (((Limits.pushout.inr ι f).app p).hom y) = e.hom.hom x
      calc
        e.hom.hom (((Limits.pushout.inr ι f).app p).hom y) =
            ((Limits.pushout.inr ι f).app p ≫ e.hom).hom y := by
              rw [ModuleCat.comp_apply]
        _ = (Limits.pushout.inr (ι.app p) (f.app p)).hom y := by rw [hinr]
        _ = e.hom.hom x := hy

end IsPointwiseShortExact

private theorem pushoutFiber_finiteDimensional (hs : IsRankExact ι π) (f : L ⟶ L')
    [∀ p, FiniteDimensional k (L'.obj p)] (p : P) :
    FiniteDimensional k ((Limits.pushout ι f).obj p) := by
  letI : FiniteDimensional k (M.obj p) := hs.finiteDimensional p
  letI : FiniteDimensional k (M.obj p × L'.obj p) := inferInstance
  let sourceIso := ModuleCat.biprodIsoProd (M.obj p) (L'.obj p)
  let BP : ModuleCat.{u} k := M.obj p ⊞ L'.obj p
  let PO : ModuleCat.{u} k := Limits.pushout (ι.app p) (f.app p)
  letI : FiniteDimensional k BP :=
    FiniteDimensional.of_surjective sourceIso.inv.hom
      ((ModuleCat.epi_iff_surjective sourceIso.inv).mp inferInstance)
  let e := Limits.pushoutObjIso ι f p
  let φ : BP ⟶ PO :=
    CategoryTheory.Abelian.BiproductToPushoutIsCokernel.biproductToPushout
      (C := ModuleCat.{u} k) (ι.app p) (f.app p)
  have hφcolim :=
    CategoryTheory.Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout
      (C := ModuleCat.{u} k) (ι.app p) (f.app p)
  have hφepi : Epi φ := Cofork.IsColimit.epi hφcolim
  have hφsurj : Function.Surjective φ.hom := (ModuleCat.epi_iff_surjective _).1 hφepi
  haveI : FiniteDimensional k PO :=
    FiniteDimensional.of_surjective φ.hom hφsurj
  exact FiniteDimensional.of_injective e.hom.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- Pushout closure for rank-exact sequences over arbitrary partial orders. -/
theorem IsRankExact.pushout (hs : IsRankExact ι π) (f : L ⟶ L')
    [∀ p, FiniteDimensional k (L'.obj p)] :
    IsRankExact (Limits.pushout.inr ι f) (hs.toIsPointwiseShortExact.pushoutQuotient f) := by
  let hs' := hs.toIsPointwiseShortExact.pushout_pointwise f
  refine { toIsPointwiseShortExact := hs', finiteDimensional := ?_, rank_add := ?_ }
  · intro p
    exact pushoutFiber_finiteDimensional hs f p
  · intro a b hab
    letI : FiniteDimensional k ((Limits.pushout ι f).obj a) :=
      pushoutFiber_finiteDimensional hs f a
    apply (hs'.rank_add_iff_lift_kernel hab).mpr
    intro n hn
    obtain ⟨m, hm, hmdie⟩ := hs.lift_kernel hab n hn
    refine ⟨((Limits.pushout.inl ι f).app a).hom m, ?_, ?_⟩
    · have hq := congrArg (fun g : M ⟶ N => (g.app a).hom m)
        (hs.toIsPointwiseShortExact.pushoutQuotient_inl f)
      exact hq.trans hm
    · have h := congrArg
        (fun α : M.obj a ⟶ (Limits.pushout ι f).obj b => α.hom m)
        ((Limits.pushout.inl ι f).naturality (homOfLE hab))
      change ((Limits.pushout.inl ι f).app b).hom (structureMapLinear M hab m) =
        structureMapLinear (Limits.pushout ι f) hab (((Limits.pushout.inl ι f).app a).hom m) at h
      rw [hmdie, map_zero] at h
      exact h.symm

end TDA.Persistence
