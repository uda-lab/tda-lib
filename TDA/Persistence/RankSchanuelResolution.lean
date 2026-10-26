import TDA.Persistence.RankSchanuel
import TDA.Persistence.FiniteRankProjectiveResolution
import TDA.Persistence.RankExactIso
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Persistent Schanuel for finite rank-projective resolutions

The shifted alternating-sum comparison is built from the actual rank-exact
rows in the given resolutions.  This file develops the shift and resolution
operations needed for that construction.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject NNReal

variable {k : Type u} [Field k] {n : ℕ}

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private def translationNeg (ε : ℝ≥0) : (Fin n → ℝ) →o (Fin n → ℝ) where
  toFun a := fun i => a i - (ε : ℝ)
  monotone' a b h i := by
    change a i - (ε : ℝ) ≤ b i - (ε : ℝ)
    exact sub_le_sub_right (h i) _

private def shiftNeg (ε : ℝ≥0) :
    PModule.{u,0,u} k (Fin n → ℝ) ⥤ PModule.{u,0,u} k (Fin n → ℝ) where
  obj M := reindex (translationNeg ε) M
  map f := reindexNatTrans (translationNeg ε) f
  map_id := by intros; rfl
  map_comp := by intros; rfl

private theorem orderFunctor_map_eqToHom {P Q : Type} [Preorder P] [Preorder Q]
    (f : P →o Q) {a b : P} (h : a = b) :
    f.toFunctor.map (eqToHom h) = eqToHom (congrArg f h) := by
  cases h
  rfl

private def reindexIsoOfEq {α β : (Fin n → ℝ) →o (Fin n → ℝ)}
    (h : ∀ p, α p = β p) (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    reindex α M ≅ reindex β M :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun p => eqToIso (h p)) (by intros; apply Subsingleton.elim)) M

@[simp] private theorem reindexIsoOfEq_hom_app
    {α β : (Fin n → ℝ) →o (Fin n → ℝ)} (h : ∀ p, α p = β p)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (reindexIsoOfEq h M).hom.app p = M.map (eqToHom (h p)) := rfl

@[simp] private theorem reindexIsoOfEq_inv_app
    {α β : (Fin n → ℝ) →o (Fin n → ℝ)} (h : ∀ p, α p = β p)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (reindexIsoOfEq h M).inv.app p = M.map (eqToHom (h p).symm) := rfl

private theorem translationPosNeg_orderIso (ε : ℝ≥0) :
    (CoordinateShift.translation ε).comp (translationNeg (n := n) ε) =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) := by
  apply OrderHom.ext
  funext p
  funext i
  change (p i - (ε : ℝ)) + (ε : ℝ) = p i
  ring

private theorem translationNegPos_orderIso (ε : ℝ≥0) :
    (translationNeg (n := n) ε).comp (CoordinateShift.translation ε) =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) := by
  apply OrderHom.ext
  funext p
  funext i
  change (p i + (ε : ℝ)) - (ε : ℝ) = p i
  ring

private theorem translationPosNeg_eq_id (ε : ℝ≥0) (p : Fin n → ℝ) :
    (CoordinateShift.translation ε).comp (translationNeg (n := n) ε) p = p := by
  simpa using congrArg (fun f : (Fin n → ℝ) →o (Fin n → ℝ) => f p)
    (translationPosNeg_orderIso (n := n) ε)

private theorem translationNegPos_eq_id (ε : ℝ≥0) (p : Fin n → ℝ) :
    (translationNeg (n := n) ε).comp (CoordinateShift.translation ε) p = p := by
  simpa using congrArg (fun f : (Fin n → ℝ) →o (Fin n → ℝ) => f p)
    (translationNegPos_orderIso (n := n) ε)

private theorem translationPosNeg_eq_id' (ε : ℝ≥0) :
    ∀ p, (CoordinateShift.translation ε).comp (translationNeg (n := n) ε) p =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p := by
  intro p
  simpa using translationPosNeg_eq_id (n := n) ε p

private theorem translationNegPos_eq_id' (ε : ℝ≥0) :
    ∀ p, (translationNeg (n := n) ε).comp (CoordinateShift.translation ε) p =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p := by
  intro p
  simpa using translationNegPos_eq_id (n := n) ε p

private theorem reindexIsoOfEq_naturality {α β : (Fin n → ℝ) →o (Fin n → ℝ)}
    (h : ∀ p, α p = β p) {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (f : M ⟶ N) :
    (reindexIsoOfEq h M).hom ≫ reindexNatTrans β f =
      reindexNatTrans α f ≫ (reindexIsoOfEq h N).hom := by
  apply NatTrans.ext
  funext p
  change M.map (eqToHom (h p)) ≫ f.app (β p) =
    f.app (α p) ≫ N.map (eqToHom (h p))
  exact f.naturality (eqToHom (h p))

private def shiftNegPosNatIso (ε : ℝ≥0) :
    CoordinateShift.shift ε ⋙ shiftNeg (k := k) (n := n) ε ≅ 𝟭 _ := by
  let h := translationPosNeg_eq_id' (n := n) ε
  refine NatIso.ofComponents (fun M => ?_) ?_
  · change reindex ((CoordinateShift.translation ε).comp
      (translationNeg (n := n) ε)) M ≅ reindex OrderHom.id M
    exact reindexIsoOfEq h M
  · intro M N f
    have h' : ∀ p, ((CoordinateShift.translation ε).comp
        (translationNeg (n := n) ε)) p = (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p :=
      h
    change reindexNatTrans ((CoordinateShift.translation ε).comp
        (translationNeg (n := n) ε)) f ≫
          (reindexIsoOfEq (α := (CoordinateShift.translation ε).comp
            (translationNeg (n := n) ε)) (β := OrderHom.id) h' N).hom =
      (reindexIsoOfEq (α := (CoordinateShift.translation ε).comp
        (translationNeg (n := n) ε)) (β := OrderHom.id) h' M).hom ≫
        reindexNatTrans OrderHom.id f
    exact (reindexIsoOfEq_naturality
      (α := (CoordinateShift.translation ε).comp (translationNeg (n := n) ε))
      (β := OrderHom.id) h' f).symm

private def shiftPosNegNatIso (ε : ℝ≥0) :
    shiftNeg (k := k) (n := n) ε ⋙ CoordinateShift.shift ε ≅ 𝟭 _ := by
  let h := translationNegPos_eq_id' (n := n) ε
  refine NatIso.ofComponents (fun M => ?_) ?_
  · change reindex ((translationNeg (n := n) ε).comp
      (CoordinateShift.translation ε)) M ≅ reindex OrderHom.id M
    exact reindexIsoOfEq h M
  · intro M N f
    have h' : ∀ p, ((translationNeg (n := n) ε).comp
        (CoordinateShift.translation ε)) p = (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p :=
      h
    change reindexNatTrans ((translationNeg (n := n) ε).comp
        (CoordinateShift.translation ε)) f ≫
          (reindexIsoOfEq (α := (translationNeg (n := n) ε).comp
            (CoordinateShift.translation ε)) (β := OrderHom.id) h' N).hom =
      (reindexIsoOfEq (α := (translationNeg (n := n) ε).comp
        (CoordinateShift.translation ε)) (β := OrderHom.id) h' M).hom ≫
        reindexNatTrans OrderHom.id f
    exact (reindexIsoOfEq_naturality
      (α := (translationNeg (n := n) ε).comp (CoordinateShift.translation ε))
      (β := OrderHom.id) h' f).symm

private def shiftNegPosIso (ε : ℝ≥0) (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    (shiftNeg (k := k) (n := n) ε).obj ((CoordinateShift.shift ε).obj M) ≅ M :=
  (shiftNegPosNatIso (k := k) (n := n) ε).app M

private def shiftPosNegIso (ε : ℝ≥0) (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    (CoordinateShift.shift ε).obj ((shiftNeg (k := k) (n := n) ε).obj M) ≅ M :=
  (shiftPosNegNatIso (k := k) (n := n) ε).app M

@[simp] private theorem shiftNegPosIso_inv_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftNegPosIso (k := k) (n := n) ε M).inv.app p =
      M.map (eqToHom (translationPosNeg_eq_id' (n := n) ε p).symm) := by
  change (reindexIsoOfEq (translationPosNeg_eq_id' (n := n) ε) M).inv.app p = _
  rw [reindexIsoOfEq_inv_app]

@[simp] private theorem shiftNegPosIso_hom_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftNegPosIso (k := k) (n := n) ε M).hom.app p =
      M.map (eqToHom (translationPosNeg_eq_id' (n := n) ε p)) := by
  change (reindexIsoOfEq (translationPosNeg_eq_id' (n := n) ε) M).hom.app p = _
  rw [reindexIsoOfEq_hom_app]

@[simp] private theorem shiftPosNegIso_hom_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftPosNegIso (k := k) (n := n) ε M).hom.app p =
      M.map (eqToHom (translationNegPos_eq_id' (n := n) ε p)) := by
  change (reindexIsoOfEq (translationNegPos_eq_id' (n := n) ε) M).hom.app p = _
  rw [reindexIsoOfEq_hom_app]

@[simp] private theorem shiftPosNegIso_inv_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftPosNegIso (k := k) (n := n) ε M).inv.app p =
      M.map (eqToHom (translationNegPos_eq_id' (n := n) ε p).symm) := by
  change (reindexIsoOfEq (translationNegPos_eq_id' (n := n) ε) M).inv.app p = _
  rw [reindexIsoOfEq_inv_app]

private theorem shiftNegPos_inverse_coherence (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    (CoordinateShift.shift ε).map (shiftNegPosIso (k := k) (n := n) ε M).inv =
      (shiftPosNegIso (k := k) (n := n) ε
        ((CoordinateShift.shift ε).obj M)).inv := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  ext x
  rw [CoordinateShift.shift_map_app, shiftNegPosIso_inv_app,
    shiftPosNegIso_inv_app]
  change (M.map (eqToHom
      (translationPosNeg_eq_id' (n := n) ε (CoordinateShift.translation ε p)).symm)).hom x =
    (M.map ((CoordinateShift.translation ε).toFunctor.map (eqToHom
      (translationNegPos_eq_id' (n := n) ε p).symm))).hom x
  have hmap := orderFunctor_map_eqToHom (CoordinateShift.translation ε)
    (translationNegPos_eq_id' (n := n) ε p).symm
  have hproof : congrArg (CoordinateShift.translation ε)
      (translationNegPos_eq_id' (n := n) ε p).symm =
      (translationPosNeg_eq_id' (n := n) ε
        (CoordinateShift.translation ε p)).symm := Subsingleton.elim _ _
  have hmaps := hmap.trans (congrArg eqToHom hproof)
  exact congrArg (fun f => f.hom x) (congrArg M.map hmaps)

private theorem shiftNegPosIso_naturality (ε : ℝ≥0)
    {M N : PModule.{u,0,u} k (Fin n → ℝ)} (f : M ⟶ N) :
    (shiftNegPosIso (k := k) (n := n) ε M).hom ≫ f =
      (shiftNeg (k := k) (n := n) ε).map ((CoordinateShift.shift ε).map f) ≫
        (shiftNegPosIso (k := k) (n := n) ε N).hom := by
  change (shiftNegPosNatIso (k := k) (n := n) ε).hom.app M ≫ f =
    (shiftNeg (k := k) (n := n) ε).map
      ((CoordinateShift.shift ε).map f) ≫
      (shiftNegPosNatIso (k := k) (n := n) ε).hom.app N
  exact ((shiftNegPosNatIso (k := k) (n := n) ε).hom.naturality f).symm

private theorem shiftPosNegIso_naturality (ε : ℝ≥0)
    {M N : PModule.{u,0,u} k (Fin n → ℝ)} (f : M ⟶ N) :
    (shiftPosNegIso (k := k) (n := n) ε M).hom ≫ f =
      (CoordinateShift.shift ε).map ((shiftNeg (k := k) (n := n) ε).map f) ≫
        (shiftPosNegIso (k := k) (n := n) ε N).hom := by
  change (shiftPosNegNatIso (k := k) (n := n) ε).hom.app M ≫ f =
    (CoordinateShift.shift ε).map
      ((shiftNeg (k := k) (n := n) ε).map f) ≫
      (shiftPosNegNatIso (k := k) (n := n) ε).hom.app N
  exact ((shiftPosNegNatIso (k := k) (n := n) ε).hom.naturality f).symm

private instance shift_preservesZeroMorphisms (ε : ℝ≥0) :
    (CoordinateShift.shift (R := k) (n := n) ε).PreservesZeroMorphisms where
  map_zero _ _ := by
    apply NatTrans.ext
    funext a
    rfl

private theorem zero_isRankProjective :
    IsRankProjective (0 : PModule.{u,0,u} k (Fin n → ℝ)) := by
  intro L M N ι π hs α
  exact ⟨0, (isZero_zero _).eq_of_src _ _⟩

private theorem zeroTargetRow_rankExact {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (e : M ≅ 0) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ M) := by
  have hsub (p : Fin n → ℝ) : Subsingleton (M.obj p) := by
    refine ⟨fun x y => ?_⟩
    apply (ModuleCat.mono_iff_injective (e.hom.app p)).mp inferInstance
    exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
  refine {
    toIsPointwiseShortExact := {
      injective := fun p => by
        intro x y _
        letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
        exact Subsingleton.elim _ _
      surjective := fun p y => ⟨0, (hsub p).elim _ _⟩
      range_eq_ker := fun p => by
        letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
        ext x
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        simp
    }
    finiteDimensional := fun p => by
      letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
        ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
      letI : Finite ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) := Finite.of_subsingleton
      infer_instance
    rank_add := ?_
  }
  intro a b hab
  have hrange : Subsingleton
      (LinearMap.range (structureMapLinear M hab)) :=
    ⟨fun x y => Subtype.ext ((hsub b).elim x.val y.val)⟩
  letI := hrange
  have hrank : Module.finrank k (LinearMap.range (structureMapLinear M hab)) = 0 :=
    Module.finrank_zero_of_subsingleton
  change rankOfStructureMap (0 : PModule.{u,0,u} k (Fin n → ℝ)) hab =
    rankOfStructureMap (0 : PModule.{u,0,u} k (Fin n → ℝ)) hab +
      rankOfStructureMap M hab
  simp only [rankOfStructureMap_zero]
  change 0 = 0 + Module.finrank k (LinearMap.range (structureMapLinear M hab))
  rw [hrank]

private noncomputable def biprodFiberIso
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (A ⊞ B).obj p ≅ ModuleCat.of k (A.obj p × B.obj p) := by
  let F := (evaluation (Fin n → ℝ) (ModuleCat.{u} k)).obj p
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := A) (Y := B)
  exact Functor.mapBiprod F A B ≪≫ ModuleCat.biprodIsoProd (A.obj p) (B.obj p)

private theorem biprodFiberIso_fst
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
      (biprod.fst : A ⊞ B ⟶ A).app p := by
  let F := (evaluation (Fin n → ℝ) (ModuleCat.{u} k)).obj p
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := A) (Y := B)
  let e := ModuleCat.biprodIsoProd (A.obj p) (B.obj p)
  have he : e.hom ≫ ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
      biprod.fst := by
    calc
      e.hom ≫ ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
          e.hom ≫ e.inv ≫ biprod.fst := by
            rw [← ModuleCat.biprodIsoProd_inv_comp_fst]
      _ = biprod.fst := by simp
  calc
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
      (Functor.mapBiprod F A B).hom ≫ biprod.fst := by
        dsimp [biprodFiberIso]
        rw [Category.assoc, he]
        rfl
    _ = F.map biprod.fst := by
      change biprod.lift (F.map biprod.fst) (F.map biprod.snd) ≫ biprod.fst = _
      rw [biprod.lift_fst]
    _ = (biprod.fst : A ⊞ B ⟶ A).app p := rfl

private theorem biprodFiberIso_snd
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
      (biprod.snd : A ⊞ B ⟶ B).app p := by
  let F := (evaluation (Fin n → ℝ) (ModuleCat.{u} k)).obj p
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := A) (Y := B)
  let e := ModuleCat.biprodIsoProd (A.obj p) (B.obj p)
  have he : e.hom ≫ ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
      biprod.snd := by
    calc
      e.hom ≫ ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
          e.hom ≫ e.inv ≫ biprod.snd := by
            rw [← ModuleCat.biprodIsoProd_inv_comp_snd]
      _ = biprod.snd := by simp
  calc
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
      (Functor.mapBiprod F A B).hom ≫ biprod.snd := by
        dsimp [biprodFiberIso]
        rw [Category.assoc, he]
        rfl
    _ = F.map biprod.snd := by
      change biprod.lift (F.map biprod.fst) (F.map biprod.snd) ≫ biprod.snd = _
      rw [biprod.lift_snd]
    _ = (biprod.snd : A ⊞ B ⟶ B).app p := rfl

private theorem biprodMap_fiber
    {A B A' B' : PModule.{u,0,u} k (Fin n → ℝ)}
    (f : A ⟶ A') (g : B ⟶ B') (p : Fin n → ℝ) :
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom ((f.app p).hom.prodMap (g.app p).hom) =
      (biprod.map f g).app p ≫
        (biprodFiberIso (k := k) (n := n) A' B' p).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · have hsrc : ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).1 =
        ((biprod.fst : A ⊞ B ⟶ A).app p).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj p ⟶ A.obj p => q.hom x)
        (biprodFiberIso_fst (k := k) (n := n) A B p)
      simpa [ModuleCat.comp_apply] using h
    have htgt :
        (LinearMap.fst k (A'.obj p) (B'.obj p))
          ((biprodFiberIso (k := k) (n := n) A' B' p).hom.hom
            (((biprod.map f g).app p).hom x)) =
          ((biprod.fst : A' ⊞ B' ⟶ A').app p).hom (((biprod.map f g).app p).hom x) := by
      have h := congrArg (fun q : (A' ⊞ B').obj p ⟶ A'.obj p =>
        q.hom (((biprod.map f g).app p).hom x))
        (biprodFiberIso_fst (k := k) (n := n) A' B' p)
      simpa [ModuleCat.comp_apply] using h
    have hnat : ((biprod.fst : A' ⊞ B' ⟶ A').app p).hom (((biprod.map f g).app p).hom x) =
        (f.app p).hom (((biprod.fst : A ⊞ B ⟶ A).app p).hom x) := by
      have h := congrArg (fun q : A ⊞ B ⟶ A' => (q.app p).hom x)
        (biprod.map_fst (f := f) (g := g))
      exact h
    calc
      _ = (f.app p).hom (((biprod.fst : A ⊞ B ⟶ A).app p).hom x) := by
        change (f.app p).hom ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).1 = _
        rw [hsrc]
      _ = ((biprod.fst : A' ⊞ B' ⟶ A').app p).hom (((biprod.map f g).app p).hom x) := hnat.symm
      _ = _ := htgt.symm

  · have hsrc : ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).2 =
        ((biprod.snd : A ⊞ B ⟶ B).app p).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj p ⟶ B.obj p => q.hom x)
        (biprodFiberIso_snd (k := k) (n := n) A B p)
      simpa [ModuleCat.comp_apply] using h
    have htgt :
        (LinearMap.snd k (A'.obj p) (B'.obj p))
          ((biprodFiberIso (k := k) (n := n) A' B' p).hom.hom
            (((biprod.map f g).app p).hom x)) =
          ((biprod.snd : A' ⊞ B' ⟶ B').app p).hom (((biprod.map f g).app p).hom x) := by
      have h := congrArg (fun q : (A' ⊞ B').obj p ⟶ B'.obj p =>
        q.hom (((biprod.map f g).app p).hom x))
        (biprodFiberIso_snd (k := k) (n := n) A' B' p)
      simpa [ModuleCat.comp_apply] using h
    have hnat : ((biprod.snd : A' ⊞ B' ⟶ B').app p).hom (((biprod.map f g).app p).hom x) =
        (g.app p).hom (((biprod.snd : A ⊞ B ⟶ B).app p).hom x) := by
      have h := congrArg (fun q : A ⊞ B ⟶ B' => (q.app p).hom x)
        (biprod.map_snd (f := f) (g := g))
      exact h
    calc
      _ = (g.app p).hom (((biprod.snd : A ⊞ B ⟶ B).app p).hom x) := by
        change (g.app p).hom ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).2 = _
        rw [hsrc]
      _ = ((biprod.snd : A' ⊞ B' ⟶ B').app p).hom (((biprod.map f g).app p).hom x) := hnat.symm
      _ = _ := htgt.symm


private theorem biprodMap_fiber_apply
    {A B A' B' : PModule.{u,0,u} k (Fin n → ℝ)}
    (f : A ⟶ A') (g : B ⟶ B') (p : Fin n → ℝ)
    (x : (A ⊞ B).obj p) :
    ((biprodFiberIso (k := k) (n := n) A' B' p).hom.hom
      (((biprod.map f g).app p).hom x)) =
      (f.app p).hom.prodMap (g.app p).hom
        ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x) := by
  have h := congrArg (fun q : (A ⊞ B).obj p ⟶
      ModuleCat.of k (A'.obj p × B'.obj p) => q.hom x)
    (biprodMap_fiber (k := k) (n := n) f g p)
  simpa [ModuleCat.comp_apply] using h.symm

private theorem biprodStructureMap_fiber
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) {a b : Fin n → ℝ}
    (hab : a ≤ b) (x : (A ⊞ B).obj a) :
    ((biprodFiberIso (k := k) (n := n) A B b).hom.hom
      (structureMapLinear (A ⊞ B) hab x)) =
      (structureMapLinear A hab).prodMap (structureMapLinear B hab)
        ((biprodFiberIso (k := k) (n := n) A B a).hom.hom x) := by
  let ea := biprodFiberIso (k := k) (n := n) A B a
  let eb := biprodFiberIso (k := k) (n := n) A B b
  apply Prod.ext
  · have hsrc : (ea.hom.hom x).1 =
        ((biprod.fst : A ⊞ B ⟶ A).app a).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj a ⟶ A.obj a => q.hom x)
        (biprodFiberIso_fst (k := k) (n := n) A B a)
      simpa [ModuleCat.comp_apply] using h
    have htgt : (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).1 =
        ((biprod.fst : A ⊞ B ⟶ A).app b).hom (structureMapLinear (A ⊞ B) hab x) := by
      have h := congrArg (fun q : (A ⊞ B).obj b ⟶ A.obj b =>
        q.hom (structureMapLinear (A ⊞ B) hab x))
        (biprodFiberIso_fst (k := k) (n := n) A B b)
      simpa [ModuleCat.comp_apply] using h
    have hnat := congrArg (fun q : (A ⊞ B).obj a ⟶ A.obj b => q.hom x)
      ((biprod.fst : A ⊞ B ⟶ A).naturality (homOfLE hab))
    change ((biprod.fst : A ⊞ B ⟶ A).app b).hom
        (structureMapLinear (A ⊞ B) hab x) =
      (structureMapLinear A hab)
        (((biprod.fst : A ⊞ B ⟶ A).app a).hom x) at hnat
    calc
      (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).1 =
          ((biprod.fst : A ⊞ B ⟶ A).app b).hom
            (structureMapLinear (A ⊞ B) hab x) := htgt
      _ = (structureMapLinear A hab)
          (((biprod.fst : A ⊞ B ⟶ A).app a).hom x) := hnat
      _ = (structureMapLinear A hab) ((ea.hom.hom x).1) := by rw [hsrc]
      _ = ((structureMapLinear A hab).prodMap (structureMapLinear B hab)
          (ea.hom.hom x)).1 := rfl
  · have hsrc : (ea.hom.hom x).2 =
        ((biprod.snd : A ⊞ B ⟶ B).app a).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj a ⟶ B.obj a => q.hom x)
        (biprodFiberIso_snd (k := k) (n := n) A B a)
      simpa [ModuleCat.comp_apply] using h
    have htgt : (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).2 =
        ((biprod.snd : A ⊞ B ⟶ B).app b).hom (structureMapLinear (A ⊞ B) hab x) := by
      have h := congrArg (fun q : (A ⊞ B).obj b ⟶ B.obj b =>
        q.hom (structureMapLinear (A ⊞ B) hab x))
        (biprodFiberIso_snd (k := k) (n := n) A B b)
      simpa [ModuleCat.comp_apply] using h
    have hnat := congrArg (fun q : (A ⊞ B).obj a ⟶ B.obj b => q.hom x)
      ((biprod.snd : A ⊞ B ⟶ B).naturality (homOfLE hab))
    change ((biprod.snd : A ⊞ B ⟶ B).app b).hom
        (structureMapLinear (A ⊞ B) hab x) =
      (structureMapLinear B hab)
        (((biprod.snd : A ⊞ B ⟶ B).app a).hom x) at hnat
    calc
      (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).2 =
          ((biprod.snd : A ⊞ B ⟶ B).app b).hom
            (structureMapLinear (A ⊞ B) hab x) := htgt
      _ = (structureMapLinear B hab)
          (((biprod.snd : A ⊞ B ⟶ B).app a).hom x) := hnat
      _ = (structureMapLinear B hab) ((ea.hom.hom x).2) := by rw [hsrc]
      _ = ((structureMapLinear A hab).prodMap (structureMapLinear B hab)
          (ea.hom.hom x)).2 := rfl

namespace IsPointwiseShortExact

/-- Pointwise short exactness is preserved by binary biproducts.  The proof
identifies each evaluated biproduct with the product of its two fibers and
checks exactness in the two coordinates. -/
private theorem biprod
    {A A' A'' B B' B'' : PModule.{u,0,u} k (Fin n → ℝ)}
    {f : A ⟶ A'} {g : A' ⟶ A''} {f' : B ⟶ B'} {g' : B' ⟶ B''}
    (hA : IsPointwiseShortExact f g) (hB : IsPointwiseShortExact f' g') :
    IsPointwiseShortExact (biprod.map f f') (biprod.map g g') where
  injective p := by
    let e₀ := biprodFiberIso (k := k) (n := n) A B p
    let e₁ := biprodFiberIso (k := k) (n := n) A' B' p
    intro x y h
    apply (ModuleCat.mono_iff_injective e₀.hom).mp inferInstance
    apply Prod.ext
    · have hx := biprodMap_fiber_apply (k := k) (n := n) f f' p x
      have hy := biprodMap_fiber_apply (k := k) (n := n) f f' p y
      have heq := congrArg e₁.hom.hom h
      have hc : (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom x) =
          (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom y) := by
        rw [← hx, ← hy]
        exact heq
      exact hA.injective p (congrArg Prod.fst hc)
    · have hx := biprodMap_fiber_apply (k := k) (n := n) f f' p x
      have hy := biprodMap_fiber_apply (k := k) (n := n) f f' p y
      have heq := congrArg e₁.hom.hom h
      have hc : (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom x) =
          (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom y) := by
        rw [← hx, ← hy]
        exact heq
      exact hB.injective p (congrArg Prod.snd hc)
  surjective p := by
    let e₀ := biprodFiberIso (k := k) (n := n) A B p
    let e₁ := biprodFiberIso (k := k) (n := n) A' B' p
    let e₂ := biprodFiberIso (k := k) (n := n) A'' B'' p
    intro z
    obtain ⟨x, hx⟩ := hA.surjective p (e₂.hom.hom z).1
    obtain ⟨y, hy⟩ := hB.surjective p (e₂.hom.hom z).2
    refine ⟨e₁.inv.hom (x, y), ?_⟩
    apply (ModuleCat.mono_iff_injective e₂.hom).mp inferInstance
    calc
      e₂.hom.hom (((biprod.map g g').app p).hom (e₁.inv.hom (x, y))) =
          (g.app p).hom.prodMap (g'.app p).hom
            (e₁.hom.hom (e₁.inv.hom (x, y))) :=
        biprodMap_fiber_apply (k := k) (n := n) g g' p _
      _ = e₂.hom.hom z := by simp [hx, hy]
  range_eq_ker p := by
    let e₀ := biprodFiberIso (k := k) (n := n) A B p
    let e₁ := biprodFiberIso (k := k) (n := n) A' B' p
    let e₂ := biprodFiberIso (k := k) (n := n) A'' B'' p
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      apply (ModuleCat.mono_iff_injective e₂.hom).mp inferInstance
      change (e₂.hom.hom (((biprod.map g g').app p).hom
          (((biprod.map f f').app p).hom x))) = e₂.hom.hom 0
      calc
        e₂.hom.hom (((biprod.map g g').app p).hom
            (((biprod.map f f').app p).hom x)) =
            (g.app p).hom.prodMap (g'.app p).hom
              (e₁.hom.hom (((biprod.map f f').app p).hom x)) :=
          biprodMap_fiber_apply (k := k) (n := n) g g' p _
        _ = (g.app p).hom.prodMap (g'.app p).hom
            ((f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom x)) := by
          rw [biprodMap_fiber_apply (k := k) (n := n) f f' p x]
        _ = 0 := by
          apply Prod.ext
          · have hmem : (f.app p).hom (e₀.hom.hom x).1 ∈
                LinearMap.range (f.app p).hom := ⟨(e₀.hom.hom x).1, rfl⟩
            rw [hA.range_eq_ker p] at hmem
            exact LinearMap.mem_ker.mp hmem
          · have hmem : (f'.app p).hom (e₀.hom.hom x).2 ∈
                LinearMap.range (f'.app p).hom := ⟨(e₀.hom.hom x).2, rfl⟩
            rw [hB.range_eq_ker p] at hmem
            exact LinearMap.mem_ker.mp hmem
        _ = e₂.hom.hom 0 := by simp
    · intro hz
      change ((biprod.map g g').app p).hom z = 0 at hz
      have hz' : (g.app p).hom.prodMap (g'.app p).hom (e₁.hom.hom z) = 0 := by
        rw [← biprodMap_fiber_apply (k := k) (n := n) g g' p z]
        simp [hz]
      have hxker : (e₁.hom.hom z).1 ∈ LinearMap.ker (g.app p).hom :=
        LinearMap.mem_ker.mpr (by simpa using congrArg Prod.fst hz')
      have hyker : (e₁.hom.hom z).2 ∈ LinearMap.ker (g'.app p).hom :=
        LinearMap.mem_ker.mpr (by simpa using congrArg Prod.snd hz')
      rw [← hA.range_eq_ker p] at hxker
      rw [← hB.range_eq_ker p] at hyker
      obtain ⟨x, hx⟩ := hxker
      obtain ⟨y, hy⟩ := hyker
      refine ⟨e₀.inv.hom (x, y), ?_⟩
      apply (ModuleCat.mono_iff_injective e₁.hom).mp inferInstance
      calc
        e₁.hom.hom (((biprod.map f f').app p).hom (e₀.inv.hom (x, y))) =
            (f.app p).hom.prodMap (f'.app p).hom
              (e₀.hom.hom (e₀.inv.hom (x, y))) :=
          biprodMap_fiber_apply (k := k) (n := n) f f' p _
        _ = e₁.hom.hom z := by simp [hx, hy]

end IsPointwiseShortExact

namespace IsRankExact

/-- Binary biproducts preserve rank exactness.  The lifting criterion is
applied coordinatewise through the evaluated biproduct/product isomorphisms. -/
private theorem biprod
    {A A' A'' B B' B'' : PModule.{u,0,u} k (Fin n → ℝ)}
    {f : A ⟶ A'} {g : A' ⟶ A''} {f' : B ⟶ B'} {g' : B' ⟶ B''}
    (hA : IsRankExact f g) (hB : IsRankExact f' g') :
    IsRankExact (biprod.map f f') (biprod.map g g') := by
  let hshort := hA.toIsPointwiseShortExact.biprod hB.toIsPointwiseShortExact
  refine {
    toIsPointwiseShortExact := hshort
    finiteDimensional := ?_
    rank_add := ?_
  }
  · intro p
    let e := biprodFiberIso (k := k) (n := n) A' B' p
    letI : FiniteDimensional k (A'.obj p) := hA.finiteDimensional p
    letI : FiniteDimensional k (B'.obj p) := hB.finiteDimensional p
    letI : FiniteDimensional k (A'.obj p × B'.obj p) := inferInstance
    have hsurj : Function.Surjective e.inv.hom := by
      intro x
      exact ⟨e.hom.hom x, by simp⟩
    exact FiniteDimensional.of_surjective e.inv.hom hsurj
  · intro a b hab
    let hmidA := biprodFiberIso (k := k) (n := n) A' B' a
    let hmidB := biprodFiberIso (k := k) (n := n) A' B' b
    let hquotA := biprodFiberIso (k := k) (n := n) A'' B'' a
    letI : FiniteDimensional k (A'.obj a) := hA.finiteDimensional a
    letI : FiniteDimensional k (B'.obj a) := hB.finiteDimensional a
    letI : FiniteDimensional k (A'.obj a × B'.obj a) := inferInstance
    have hsurj : Function.Surjective hmidA.inv.hom := by
      intro x
      exact ⟨hmidA.hom.hom x, by simp⟩
    letI : FiniteDimensional k ((A' ⊞ B').obj a) :=
      FiniteDimensional.of_surjective hmidA.inv.hom hsurj
    apply (hshort.rank_add_iff_lift_kernel hab).mpr
    intro z hz
    have hzpair : (structureMapLinear A'' hab).prodMap
        (structureMapLinear B'' hab) (hquotA.hom.hom z) = 0 := by
      rw [← biprodStructureMap_fiber (k := k) (n := n) A'' B'' hab z]
      simp [hz]
    have hza : structureMapLinear A'' hab (hquotA.hom.hom z).1 = 0 := by
      simpa using congrArg Prod.fst hzpair
    have hzb : structureMapLinear B'' hab (hquotA.hom.hom z).2 = 0 := by
      simpa using congrArg Prod.snd hzpair
    obtain ⟨x, hx, hxdie⟩ := hA.lift_kernel hab (hquotA.hom.hom z).1 hza
    obtain ⟨y, hy, hydie⟩ := hB.lift_kernel hab (hquotA.hom.hom z).2 hzb
    let w := hmidA.inv.hom (x, y)
    refine ⟨w, ?_, ?_⟩
    · apply (ModuleCat.mono_iff_injective hquotA.hom).mp inferInstance
      calc
        hquotA.hom.hom (((biprod.map g g').app a).hom w) =
            (g.app a).hom.prodMap (g'.app a).hom
              (hmidA.hom.hom w) :=
          biprodMap_fiber_apply (k := k) (n := n) g g' a w
        _ = hquotA.hom.hom z := by simp [w, hx, hy]
    · apply (ModuleCat.mono_iff_injective hmidB.hom).mp inferInstance
      rw [biprodStructureMap_fiber (k := k) (n := n) A' B' hab w]
      have hw : hmidA.hom.hom w = (x, y) := by
        change hmidA.hom.hom (hmidA.inv.hom (x, y)) = (x, y)
        have h := congrArg (fun q : ModuleCat.of k (A'.obj a × B'.obj a) ⟶
            ModuleCat.of k (A'.obj a × B'.obj a) => q.hom (x, y))
          hmidA.inv_hom_id
        simpa [ModuleCat.comp_apply] using h
      rw [hw]
      have hpair : (structureMapLinear A' hab).prodMap
          (structureMapLinear B' hab) (x, y) = 0 := Prod.ext hxdie hydie
      simpa using hpair

end IsRankExact

namespace IsRankProjective

/-- The binary biproduct of two rank-projectives is rank-projective. -/
private theorem biprod {P Q : PModule.{u,0,u} k (Fin n → ℝ)}
    (hP : IsRankProjective P) (hQ : IsRankProjective Q) :
    IsRankProjective (P ⊞ Q) := by
  intro L M N ι π hs α
  obtain ⟨βP, hβP⟩ := hP L M N ι π hs (biprod.inl ≫ α)
  obtain ⟨βQ, hβQ⟩ := hQ L M N ι π hs (biprod.inr ≫ α)
  refine ⟨biprod.desc βP βQ, ?_⟩
  apply biprod.hom_ext'
  · simpa only [← Category.assoc, biprod.inl_desc] using hβP
  · simpa only [← Category.assoc, biprod.inr_desc] using hβQ

end IsRankProjective

private theorem isZeroZeroBiprod :
    IsZero ((0 : PModule.{u,0,u} k (Fin n → ℝ)) ⊞ 0) := by
  refine ⟨?_, ?_⟩
  · intro Y
    refine ⟨{ default := (0 : (0 ⊞ 0) ⟶ Y), uniq := ?_ }⟩
    intro f
    apply biprod.hom_ext'
    · exact (isZero_zero _).eq_of_src
        (biprod.inl ≫ f) 0
    · exact (isZero_zero _).eq_of_src
        (biprod.inr ≫ f) 0
  · intro Y
    refine ⟨{ default := (0 : Y ⟶ (0 ⊞ 0)), uniq := ?_ }⟩
    intro f
    apply biprod.hom_ext
    · exact (isZero_zero _).eq_of_tgt
        (f ≫ biprod.fst) (0 ≫ biprod.fst)
    · exact (isZero_zero _).eq_of_tgt
        (f ≫ biprod.snd) (0 ≫ biprod.snd)

private noncomputable def zeroBiprodIso :
    (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⊞ 0 ≅
      (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
  isZeroZeroBiprod.iso (isZero_zero _)

private theorem projectiveIdentityRow
    (P : PModule.{u,0,u} k (Fin n → ℝ))
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ P) (𝟙 P) := by
  letI : ∀ p, FiniteDimensional k (P.obj p) := hfd
  have hs : IsPointwiseShortExact
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ P) (𝟙 P) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p y
      exact ⟨y, by simp⟩
    · intro p
      ext x
      simp
  exact hs.rankExact_of_section (𝟙 P) (by simp)

/-- The length-one identity resolution of a rank-projective module with
pointwise finite-dimensional fibers. -/
noncomputable def FiniteRankProjectiveResolution.identity
    (P : PModule.{u,0,u} k (Fin n → ℝ)) (hP : IsRankProjective P)
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) :
    FiniteRankProjectiveResolution P := by
  let kernel : Fin 2 → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun _ => P)
  have h0 : kernel (0 : Fin 2) = P := by
    change Fin.lastCases (0 : PModule.{u,0,u} k (Fin n → ℝ))
        (fun _ : Fin 1 => P) ((0 : Fin 1).castSucc) = P
    rw [Fin.lastCases_castSucc]
  have hlast : kernel (Fin.last 1) =
      (0 : PModule.{u,0,u} k (Fin n → ℝ)) := by
    change @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
        (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P) (Fin.last 1) = 0
    rw [Fin.lastCases_last]
  refine {
    toFiniteRankExactResolution := {
      length := 1
      kernel := kernel
      term := fun _ => P
      inclusion := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        change @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
            (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P) (Fin.last 1) ⟶ P
        rw [Fin.lastCases_last]
        exact 0
      quotient := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        change P ⟶ @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
            (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P)
            ((0 : Fin 1).castSucc)
        rw [Fin.lastCases_castSucc]
        exact 𝟙 P
      row_rank_exact := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        exact projectiveIdentityRow P hfd
      initial_iso := eqToIso h0
      terminal_iso := (eqToIso hlast) ≪≫ Iso.refl _
    }
    term_rank_projective := fun _ => hP
  }


namespace FiniteRankProjectiveResolution

/-- A binary biproduct of two finite rank-projective resolutions of the same
length is again an actual finite rank-projective resolution. -/
noncomputable def biprod {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) :
    FiniteRankProjectiveResolution (M ⊞ N) where
  toFiniteRankExactResolution := {
    length := R.length
    kernel := fun i => R.kernel i ⊞ S.kernel (Fin.cast (congrArg Nat.succ hlen) i)
    term := fun i => R.term i ⊞ S.term (Fin.cast hlen i)
    inclusion := fun i => biprod.map (R.inclusion i)
      (S.inclusion (Fin.cast hlen i))
    quotient := fun i => biprod.map (R.quotient i)
      (S.quotient (Fin.cast hlen i))
    row_rank_exact := fun i => (R.row_rank_exact i).biprod
      (S.row_rank_exact (Fin.cast hlen i))
    initial_iso := biprod.mapIso R.initial_iso S.initial_iso
    terminal_iso :=
      (biprod.mapIso R.terminal_iso
        ((eqToIso (by
          congr 1
          apply Fin.ext
          simp)).trans S.terminal_iso)) ≪≫ zeroBiprodIso
  }
  term_rank_projective := fun i =>
    (R.term_rank_projective i).biprod
      (S.term_rank_projective (Fin.cast hlen i))

end FiniteRankProjectiveResolution


/-- Append one zero projective term to an actual finite resolution.  The old
rows are transported along the canonical finite-index equalities, and the new
last row is rank exact because the old terminal kernel is zero. -/
noncomputable def FiniteRankProjectiveResolution.appendZero
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) : FiniteRankProjectiveResolution M := by
  let kernel : Fin (R.length + 2) → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun i => R.kernel i)
  let term : Fin (R.length + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun i => R.term i)
  let hL (i : Fin R.length) : R.kernel i.succ = kernel (i.castSucc).succ := by
    simp only [kernel, Fin.succ_castSucc, Fin.lastCases_castSucc]
  let hM (i : Fin R.length) : R.term i = term i.castSucc := by
    simp only [term, Fin.lastCases_castSucc]
  let hN (i : Fin R.length) : R.kernel i.castSucc = kernel i.castSucc.castSucc := by
    simp only [kernel, Fin.lastCases_castSucc]
  let inclusion : ∀ i, kernel i.succ ⟶ term i := fun i => Fin.lastCases
    (by simp only [kernel, term, Fin.lastCases_last, Fin.succ_last]; exact 0)
    (fun i => (eqToIso (hL i)).inv ≫ R.inclusion i ≫ (eqToIso (hM i)).hom)
    i
  let quotient : ∀ i, term i ⟶ kernel i.castSucc := fun i => Fin.lastCases
    (by
      simpa only [kernel, term, Fin.lastCases_last, Fin.lastCases_castSucc] using
        (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ R.kernel (Fin.last R.length)))
    (fun i => (eqToIso (hM i)).inv ≫ R.quotient i ≫ (eqToIso (hN i)).hom)
    i
  refine {
    toFiniteRankExactResolution := {
      length := R.length + 1
      kernel := kernel
      term := term
      inclusion := inclusion
      quotient := quotient
      row_rank_exact := ?_
      initial_iso := ?_
      terminal_iso := by simpa only [kernel, Fin.lastCases_last] using (Iso.refl 0)
    }
    term_rank_projective := ?_
  }
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · have hL : (0 : PModule.{u,0,u} k (Fin n → ℝ)) =
          kernel (Fin.last R.length).succ := by
        simp only [kernel, Fin.succ_last, Fin.lastCases_last]
      have hM : (0 : PModule.{u,0,u} k (Fin n → ℝ)) =
          term (Fin.last R.length) := by
        simp only [term, Fin.lastCases_last]
      have hN : R.kernel (Fin.last R.length) =
          kernel (Fin.last R.length).castSucc := by
        simp only [kernel, Fin.lastCases_castSucc]
      let eL := eqToIso hL
      let eM := eqToIso hM
      let eN := eqToIso hN
      have hs := (zeroTargetRow_rankExact R.terminal_iso).of_iso eL eM eN
      have hι : inclusion (Fin.last R.length) =
          eL.inv ≫ (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0) ≫ eM.hom := by
        have hsource : IsZero (kernel (Fin.last R.length).succ) :=
          IsZero.of_iso (isZero_zero _) eL.symm
        exact hsource.eq_of_src _ _
      have hπ : quotient (Fin.last R.length) =
          eM.inv ≫ (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶
            R.kernel (Fin.last R.length)) ≫ eN.hom := by
        have hsource : IsZero (term (Fin.last R.length)) :=
          IsZero.of_iso (isZero_zero _) eM.symm
        exact hsource.eq_of_src _ _
      rw [hι, hπ]
      exact hs
    · intro i
      simpa only [inclusion, quotient, Fin.lastCases_castSucc] using
        (R.row_rank_exact i).of_iso (eqToIso (hL i)) (eqToIso (hM i))
          (eqToIso (hN i))
  · have hzero : (0 : Fin (R.length + 2)) = (0 : Fin (R.length + 1)).castSucc := by
      ext
      rfl
    simpa only [kernel, hzero, Fin.lastCases_castSucc] using R.initial_iso
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · have hM : (0 : PModule.{u,0,u} k (Fin n → ℝ)) = term (Fin.last R.length) := by
        simp only [term, Fin.lastCases_last]
      exact zero_isRankProjective.of_iso (eqToIso hM)
    · intro i
      exact (R.term_rank_projective i).of_iso (eqToIso (hM i))

namespace FiniteRankProjectiveResolution

/-- Repeatedly append zero terms, preserving the resolved module and every
existing resolution row. -/
noncomputable def appendZeros {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) :
    (count : ℕ) → FiniteRankProjectiveResolution M
  | 0 => R
  | count + 1 => (appendZeros R count).appendZero

theorem appendZeros_length {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (count : ℕ) :
    (R.appendZeros count).length = R.length + count := by
  induction count with
  | zero => simp [appendZeros]
  | succ count ih =>
      simp [appendZeros, appendZero, ih, Nat.add_assoc]

/-- The degree-`j` term of a finite resolution, extended by zero after its
last indexed projective. -/
noncomputable def termAt {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (j : ℕ) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  if hj : j < R.length then R.term ⟨j, hj⟩ else 0

@[simp] theorem termAt_eq_term {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) {j : ℕ} (hj : j < R.length) :
    R.termAt j = R.term ⟨j, hj⟩ := by
  simp [termAt, hj]

@[simp] theorem termAt_eq_zero {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) {j : ℕ} (hj : R.length ≤ j) :
    R.termAt j = 0 := by
  simp [termAt, not_lt.mpr hj]

theorem termAt_appendZero {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (j : ℕ) :
    (R.appendZero).termAt j = R.termAt j := by
  by_cases hj : j < R.length
  · have hj' : j < (R.appendZero).length := by
      simp [FiniteRankProjectiveResolution.appendZero]
      omega
    rw [termAt_eq_term (R := R.appendZero) hj', termAt_eq_term (R := R) hj]
    change (Fin.lastCases (0 : PModule.{u,0,u} k (Fin n → ℝ))
      (fun i => R.term i) ⟨j, hj'⟩) = R.term ⟨j, hj⟩
    have hidx : (⟨j, hj'⟩ : Fin (R.length + 1)) = (⟨j, hj⟩ : Fin R.length).castSucc := by
      ext
      rfl
    rw [hidx, Fin.lastCases_castSucc]
  · rw [termAt_eq_zero (R := R) (Nat.le_of_not_gt hj)]
    by_cases hj' : j < (R.appendZero).length
    · have hlast : j = R.length := by
        simp [FiniteRankProjectiveResolution.appendZero] at hj'
        omega
      subst j
      rw [termAt_eq_term (R := R.appendZero) (by
        simp [FiniteRankProjectiveResolution.appendZero])]
      change @Fin.lastCases R.length
          (fun _ : Fin (R.length + 1) => PModule.{u,0,u} k (Fin n → ℝ))
          (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun i => R.term i)
          (Fin.last R.length) = 0
      simp
    · simp [termAt, hj']

theorem termAt_appendZeros {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (count j : ℕ) :
    (R.appendZeros count).termAt j = R.termAt j := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [appendZeros, termAt_appendZero, ih]

end FiniteRankProjectiveResolution

private noncomputable def schanuelLeftAt
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) {L : ℕ} (j : Fin L) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  (CoordinateShift.shift ((j.val : ℝ≥0) * ε)).obj
    (if Even j.val then R.termAt j.val else S.termAt j.val)

private noncomputable def schanuelRightAt
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) {L : ℕ} (j : Fin L) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  (CoordinateShift.shift ((j.val : ℝ≥0) * ε)).obj
    (if Even j.val then S.termAt j.val else R.termAt j.val)

namespace FiniteRankProjectiveResolution

/-- Degree-`j` summand in the shifted alternating resolution comparison:
even degrees use the first resolution, odd degrees the second. -/
noncomputable def schanuelLeftSummand
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (j : Fin (max R.length S.length)) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  schanuelLeftAt R S ε j

/-- Degree-`j` summand in the shifted alternating resolution comparison with
the two resolutions exchanged. -/
noncomputable def schanuelRightSummand
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (j : Fin (max R.length S.length)) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  schanuelRightAt R S ε j

/-- The finite biproduct of all shifted alternating summands, with every
resolution extended by its canonical zero terms to the common maximum length. -/
noncomputable def schanuelLeftBiproduct
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) : PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ schanuelLeftSummand R S ε

/-- The finite biproduct of the shifted alternating summands with the two
resolutions exchanged. -/
noncomputable def schanuelRightBiproduct
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) : PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ schanuelRightSummand R S ε

private theorem identity_termAt
    (P : PModule.{u,0,u} k (Fin n → ℝ)) (hP : IsRankProjective P)
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) (j : ℕ) :
    (FiniteRankProjectiveResolution.identity P hP hfd).termAt j =
      if j = 0 then P else 0 := by
  by_cases hj : j = 0
  · subst j
    rw [termAt_eq_term (R := FiniteRankProjectiveResolution.identity P hP hfd) (by
      simp [FiniteRankProjectiveResolution.identity])]
    rfl
  · have hjlen : (FiniteRankProjectiveResolution.identity P hP hfd).length ≤ j := by
      simp [FiniteRankProjectiveResolution.identity]
      omega
    rw [termAt_eq_zero (R := FiniteRankProjectiveResolution.identity P hP hfd) hjlen]
    simp [hj]

private noncomputable def termAt_biprodIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (j : ℕ) :
    (R.biprod S hlen).termAt j ≅ R.termAt j ⊞ S.termAt j := by
  by_cases hj : j < R.length
  · have hjS : j < S.length := by omega
    rw [termAt_eq_term (R := R.biprod S hlen) hj,
      termAt_eq_term (R := R) hj, termAt_eq_term (R := S) hjS]
    change (R.term ⟨j, hj⟩ ⊞ S.term (Fin.cast hlen ⟨j, hj⟩)) ≅
      R.term ⟨j, hj⟩ ⊞ S.term ⟨j, hjS⟩
    have hidx : Fin.cast hlen (⟨j, hj⟩ : Fin R.length) = ⟨j, hjS⟩ := by
      apply Fin.ext
      rfl
    exact biprod.mapIso (Iso.refl _) (eqToIso (congrArg S.term hidx))
  · have hjS : S.length ≤ j := by omega
    rw [termAt_eq_zero (R := R.biprod S hlen) (by simpa [FiniteRankProjectiveResolution.biprod] using Nat.le_of_not_gt hj),
      termAt_eq_zero (R := R) (Nat.le_of_not_gt hj),
      termAt_eq_zero (R := S) hjS]
    exact (zeroBiprodIso (k := k) (n := n)).symm

private noncomputable def biprodRightZeroIso
    (P : PModule.{u,0,u} k (Fin n → ℝ)) : P ⊞ 0 ≅ P where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp
    · exact (isZero_zero _).eq_of_src _ _
  inv_hom_id := by simp

private noncomputable def biprodLeftZeroIso
    (P : PModule.{u,0,u} k (Fin n → ℝ)) : 0 ⊞ P ≅ P where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · exact (isZero_zero _).eq_of_src _ _
    · simp
  inv_hom_id := by simp

/-- The one-projective-term case of persistent Schanuel.  The terminal kernels
are identified with zero by the supplied resolution structures, so the actual
one-step interleaving descends to the two degree-zero projectives. -/
noncomputable def interleaving_of_length_one
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hRlen : R.length = 1) (hSlen : S.length = 1)
    (ε : ℝ≥0) (i : CoordinateInterleaving ε M N) :
    CoordinateInterleaving ε (R.term ⟨0, by omega⟩) (S.term ⟨0, by omega⟩) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let iS : Fin S.length := ⟨0, by omega⟩
  have hRrow := (R.row_rank_exact iR).of_iso
    (Iso.refl _) (Iso.refl _) R.initial_iso
  have hSrow := (S.row_rank_exact iS).of_iso
    (Iso.refl _) (Iso.refl _) S.initial_iso
  let oneStep := RankSchanuel.interleavingOfSequences
    (α := R.quotient iR ≫ R.initial_iso.hom)
    (β := S.quotient iS ≫ S.initial_iso.hom) (i := i)
    hRrow hSrow (R.term_rank_projective iR) (S.term_rank_projective iS)
  have hRidx : iR.succ = Fin.last R.length := by
    apply Fin.ext
    simp [iR, hRlen]
  have hSidx : iS.succ = Fin.last S.length := by
    apply Fin.ext
    simp [iS, hSlen]
  let eR : R.kernel iR.succ ≅ 0 := (eqToIso (congrArg R.kernel hRidx)) ≪≫ R.terminal_iso
  let eS : S.kernel iS.succ ≅ 0 := (eqToIso (congrArg S.kernel hSidx)) ≪≫ S.terminal_iso
  let eR' : (CoordinateShift.shift ε).obj (R.kernel iR.succ) ≅ 0 :=
    (CoordinateShift.shift ε).mapIso eR ≪≫
      Functor.mapZeroObject (CoordinateShift.shift ε)
  let eS' : (CoordinateShift.shift ε).obj (S.kernel iS.succ) ≅ 0 :=
    (CoordinateShift.shift ε).mapIso eS ≪≫
      Functor.mapZeroObject (CoordinateShift.shift ε)
  have hRterm : R.term iR = R.term ⟨0, by omega⟩ := by
    apply congrArg R.term
    apply Fin.ext
    rfl
  have hSterm : S.term iS = S.term ⟨0, by omega⟩ := by
    apply congrArg S.term
    apply Fin.ext
    rfl
  exact oneStep.congr
    ((biprod.mapIso (eqToIso hRterm) eS').trans
      (biprodRightZeroIso (R.term ⟨0, by omega⟩)))
    ((biprod.mapIso eR' (eqToIso hSterm)).trans
      (biprodLeftZeroIso (S.term ⟨0, by omega⟩)))

end FiniteRankProjectiveResolution


/-- Remove the first row of a nonempty finite resolution.  The resulting
resolution resolves the actual next kernel; every shifted index is transported
along its explicit finite-index equality. -/
noncomputable def FiniteRankProjectiveResolution.tail
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (hpos : 0 < R.length) :
    FiniteRankProjectiveResolution
      (R.kernel (⟨1, by omega⟩ : Fin (R.length + 1))) := by
  let m : ℕ := R.length - 1
  have hlen : m + 1 = R.length := by dsimp [m]; omega
  let kidx : Fin (m + 1) → Fin (R.length + 1) := fun i =>
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
  let tidx : Fin m → Fin R.length := fun i =>
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
  let kernel : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun i => R.kernel (kidx i)
  let term : Fin m → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun i => R.term (tidx i)
  have hL (i : Fin m) : R.kernel (tidx i).succ = kernel i.succ := by
    apply congrArg R.kernel
    apply Fin.ext
    rfl
  have hM (i : Fin m) : R.term (tidx i) = term i := rfl
  have hN (i : Fin m) : R.kernel (tidx i).castSucc = kernel i.castSucc := by
    apply congrArg R.kernel
    apply Fin.ext
    rfl
  let inclusion : ∀ i, kernel i.succ ⟶ term i := fun i =>
    (eqToIso (hL i)).inv ≫ R.inclusion (tidx i) ≫ (eqToIso (hM i)).hom
  let quotient : ∀ i, term i ⟶ kernel i.castSucc := fun i =>
    (eqToIso (hM i)).inv ≫ R.quotient (tidx i) ≫ (eqToIso (hN i)).hom
  have h0 : kernel (0 : Fin (m + 1)) =
      R.kernel (⟨1, by omega⟩ : Fin (R.length + 1)) := by
    apply congrArg R.kernel
    apply Fin.ext
    rfl
  have hlast : kernel (Fin.last m) = R.kernel (Fin.last R.length) := by
    apply congrArg R.kernel
    apply Fin.ext
    simp [kidx, hlen]
  refine {
    toFiniteRankExactResolution := {
      length := m
      kernel := kernel
      term := term
      inclusion := inclusion
      quotient := quotient
      row_rank_exact := ?_
      initial_iso := eqToIso h0
      terminal_iso := (eqToIso hlast) ≪≫ R.terminal_iso
    }
    term_rank_projective := ?_
  }
  · intro i
    exact (R.row_rank_exact (tidx i)).of_iso
      (eqToIso (hL i)) (eqToIso (hM i)) (eqToIso (hN i))
  · intro i
    exact (R.term_rank_projective (tidx i)).of_iso (eqToIso (hM i))

@[simp] theorem FiniteRankProjectiveResolution.length_tail
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (hpos : 0 < R.length) :
    (R.tail hpos).length = R.length - 1 := rfl

theorem FiniteRankProjectiveResolution.termAt_tail
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (hpos : 0 < R.length) (j : ℕ) :
    (R.tail hpos).termAt j = R.termAt (j + 1) := by
  by_cases hj : j < R.length - 1
  · have hj' : j < (R.tail hpos).length := by simpa using hj
    have hjR : j + 1 < R.length := by omega
    rw [termAt_eq_term (R := R.tail hpos) hj', termAt_eq_term (R := R) hjR]
    rfl
  · have hj' : (R.tail hpos).length ≤ j := by simpa using Nat.le_of_not_gt hj
    have hjR : R.length ≤ j + 1 := by omega
    rw [termAt_eq_zero (R := R.tail hpos) hj', termAt_eq_zero (R := R) hjR]

/-- Relative projectivity is preserved by coordinate shifts.  This uses that
translation of `Fin n → ℝ` is an order equivalence, so a rank-exact lifting
problem can be transported back along the inverse translation. -/
private theorem IsRankProjective.shift {Q : PModule.{u,0,u} k (Fin n → ℝ)}
    (hQ : IsRankProjective Q) (ε : ℝ≥0) :
    IsRankProjective ((CoordinateShift.shift ε).obj Q) := by
  intro L M N ι π hs α
  let hs' : IsRankExact ((shiftNeg (k := k) (n := n) ε).map ι)
      ((shiftNeg (k := k) (n := n) ε).map π) :=
    hs.reindex (translationNeg (n := n) ε)
  let α' : Q ⟶ (shiftNeg (k := k) (n := n) ε).obj N :=
    (shiftNegPosIso (k := k) (n := n) ε Q).inv ≫
      (shiftNeg (k := k) (n := n) ε).map α
  obtain ⟨β', hβ'⟩ := hQ _ _ _
    ((shiftNeg (k := k) (n := n) ε).map ι)
    ((shiftNeg (k := k) (n := n) ε).map π) hs' α'
  refine ⟨(CoordinateShift.shift ε).map β' ≫
    (shiftPosNegIso (k := k) (n := n) ε M).hom, ?_⟩
  calc
    ((CoordinateShift.shift ε).map β' ≫
          (shiftPosNegIso (k := k) (n := n) ε M).hom) ≫ π =
        (CoordinateShift.shift ε).map β' ≫
          (CoordinateShift.shift ε).map
            ((shiftNeg (k := k) (n := n) ε).map π) ≫
          (shiftPosNegIso (k := k) (n := n) ε N).hom := by
            rw [Category.assoc, shiftPosNegIso_naturality (k := k) (n := n) ε π]
    _ = (CoordinateShift.shift ε).map
          (β' ≫ (shiftNeg (k := k) (n := n) ε).map π) ≫
          (shiftPosNegIso (k := k) (n := n) ε N).hom := by
            exact congrArg (fun f => f ≫ (shiftPosNegIso (k := k) (n := n) ε N).hom)
              ((CoordinateShift.shift ε).map_comp β'
                ((shiftNeg (k := k) (n := n) ε).map π))
    _ = (CoordinateShift.shift ε).map α' ≫
          (shiftPosNegIso (k := k) (n := n) ε N).hom := by rw [hβ']
    _ = α := by
          dsimp [α']
          rw [Functor.map_comp, shiftNegPos_inverse_coherence]
          calc
            ((shiftPosNegIso (k := k) (n := n) ε
                ((CoordinateShift.shift ε).obj Q)).inv ≫
                (CoordinateShift.shift ε).map
                  ((shiftNeg (k := k) (n := n) ε).map α)) ≫
                (shiftPosNegIso (k := k) (n := n) ε N).hom =
                (shiftPosNegIso (k := k) (n := n) ε
                  ((CoordinateShift.shift ε).obj Q)).inv ≫
                  ((CoordinateShift.shift ε).map
                    ((shiftNeg (k := k) (n := n) ε).map α) ≫
                    (shiftPosNegIso (k := k) (n := n) ε N).hom) :=
                  Category.assoc _ _ _
            _ = (shiftPosNegIso (k := k) (n := n) ε
                  ((CoordinateShift.shift ε).obj Q)).inv ≫
                  ((shiftPosNegIso (k := k) (n := n) ε
                    ((CoordinateShift.shift ε).obj Q)).hom ≫ α) := by
                  exact congrArg _
                    (shiftPosNegIso_naturality (k := k) (n := n) ε α).symm
            _ = α := by simp

/-- Shift every object and row of an actual finite rank-projective resolution.
The row witnesses are transported by reindexing, rather than assumed. -/
noncomputable def FiniteRankProjectiveResolution.shift
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (ε : ℝ≥0) :
    FiniteRankProjectiveResolution ((CoordinateShift.shift ε).obj M) where
  toFiniteRankExactResolution := {
    length := R.length
    kernel := fun i => (CoordinateShift.shift ε).obj (R.kernel i)
    term := fun i => (CoordinateShift.shift ε).obj (R.term i)
    inclusion := fun i => (CoordinateShift.shift ε).map (R.inclusion i)
    quotient := fun i => (CoordinateShift.shift ε).map (R.quotient i)
    row_rank_exact := fun i => (R.row_rank_exact i).reindex
      (CoordinateShift.translation ε)
    initial_iso := (CoordinateShift.shift ε).mapIso R.initial_iso
    terminal_iso := (CoordinateShift.shift ε).mapIso R.terminal_iso ≪≫
      Functor.mapZeroObject (CoordinateShift.shift ε)
  }
  term_rank_projective := fun i =>
    (R.term_rank_projective i).shift ε

private noncomputable def termAt_shiftIso
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (ε : ℝ≥0) (j : ℕ) :
    (R.shift ε).termAt j ≅ (CoordinateShift.shift ε).obj (R.termAt j) := by
  by_cases hj : j < R.length
  · have hj' : j < (R.shift ε).length := by
      simpa [FiniteRankProjectiveResolution.shift] using hj
    rw [FiniteRankProjectiveResolution.termAt_eq_term (R := R.shift ε) hj',
      FiniteRankProjectiveResolution.termAt_eq_term (R := R) hj]
    rfl
  · have hle : R.length ≤ j := Nat.le_of_not_gt hj
    have hle' : (R.shift ε).length ≤ j := by
      simpa [FiniteRankProjectiveResolution.shift] using hle
    rw [FiniteRankProjectiveResolution.termAt_eq_zero (R := R.shift ε) hle',
      FiniteRankProjectiveResolution.termAt_eq_zero (R := R) hle]
    exact (Functor.mapZeroObject (CoordinateShift.shift ε)).symm

private noncomputable def crossLeftResolution
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    FiniteRankProjectiveResolution
      ((CoordinateShift.shift ε).obj
        (R.kernel ⟨1, by omega⟩) ⊞ S.term ⟨0, by omega⟩) := by
  let iS : Fin S.length := ⟨0, by rw [← hlen]; omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idS := FiniteRankProjectiveResolution.identity (S.term iS)
    (S.term_rank_projective iS) (fun p => (S.row_rank_exact iS).finiteDimensional p)
  let paddedIdS := idS.appendZeros (R.length - 2)
  have hlen' : (tailR.shift ε).length = paddedIdS.length := by
    have htail : tailR.length = R.length - 1 :=
      FiniteRankProjectiveResolution.length_tail R (by omega)
    have hid : idS.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idS (R.length - 2)
    calc
      (tailR.shift ε).length = tailR.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idS.length + (R.length - 2) := by rw [hid]
      _ = paddedIdS.length := hpad.symm
  exact (tailR.shift ε).biprod paddedIdS hlen'

private noncomputable def crossRightResolution
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    FiniteRankProjectiveResolution
      ((CoordinateShift.shift ε).obj
        (S.kernel ⟨1, by rw [← hlen]; omega⟩) ⊞ R.term ⟨0, by omega⟩) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idR := FiniteRankProjectiveResolution.identity (R.term iR)
    (R.term_rank_projective iR) (fun p => (R.row_rank_exact iR).finiteDimensional p)
  let paddedIdR := idR.appendZeros (R.length - 2)
  have hlen' : (tailS.shift ε).length = paddedIdR.length := by
    have htail : tailS.length = R.length - 1 := by
      calc
        tailS.length = S.length - 1 :=
          FiniteRankProjectiveResolution.length_tail S (by rw [← hlen]; omega)
        _ = R.length - 1 := by rw [hlen]
    have hid : idR.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idR (R.length - 2)
    calc
      (tailS.shift ε).length = tailS.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idR.length + (R.length - 2) := by rw [hid]
      _ = paddedIdR.length := hpad.symm
  exact (tailS.shift ε).biprod paddedIdR hlen'

private noncomputable def crossLeftTermAtIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (j : ℕ) :
    (crossLeftResolution R S hlen hpos ε).termAt j ≅
      (CoordinateShift.shift ε).obj (R.termAt (j + 1)) ⊞
        (if j = 0 then S.termAt 0 else 0) := by
  let iS : Fin S.length := ⟨0, by rw [← hlen]; omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idS := FiniteRankProjectiveResolution.identity (S.term iS)
    (S.term_rank_projective iS) (fun p => (S.row_rank_exact iS).finiteDimensional p)
  let paddedIdS := idS.appendZeros (R.length - 2)
  have hlen' : (tailR.shift ε).length = paddedIdS.length := by
    have htail : tailR.length = R.length - 1 :=
      FiniteRankProjectiveResolution.length_tail R (by omega)
    have hid : idS.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idS (R.length - 2)
    calc
      (tailR.shift ε).length = tailR.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idS.length + (R.length - 2) := by rw [hid]
      _ = paddedIdS.length := hpad.symm
  have hP : S.term iS = S.termAt 0 := by
    rw [FiniteRankProjectiveResolution.termAt_eq_term (R := S) (by omega)]
  have htail : tailR.termAt j = R.termAt (j + 1) :=
    FiniteRankProjectiveResolution.termAt_tail R (by omega) j
  have hid : idS.termAt j = if j = 0 then S.term iS else 0 :=
    FiniteRankProjectiveResolution.identity_termAt (S.term iS)
      (S.term_rank_projective iS)
      (fun p => (S.row_rank_exact iS).finiteDimensional p) j
  have htarget : (if j = 0 then S.term iS else 0) =
      (if j = 0 then S.termAt 0 else 0) := by
    split_ifs <;> simp [hP]
  have hpadTerm : paddedIdS.termAt j = if j = 0 then S.termAt 0 else 0 :=
    (FiniteRankProjectiveResolution.termAt_appendZeros idS (R.length - 2) j).trans
      (hid.trans htarget)
  change ((tailR.shift ε).biprod paddedIdS hlen').termAt j ≅ _
  exact (FiniteRankProjectiveResolution.termAt_biprodIso
      (tailR.shift ε) paddedIdS hlen' j).trans
    (biprod.mapIso
      ((termAt_shiftIso tailR ε j).trans
        (eqToIso (congrArg (fun X => (CoordinateShift.shift ε).obj X) htail)))
      (eqToIso hpadTerm))

private noncomputable def crossRightTermAtIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (j : ℕ) :
    (crossRightResolution R S hlen hpos ε).termAt j ≅
      (CoordinateShift.shift ε).obj (S.termAt (j + 1)) ⊞
        (if j = 0 then R.termAt 0 else 0) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idR := FiniteRankProjectiveResolution.identity (R.term iR)
    (R.term_rank_projective iR) (fun p => (R.row_rank_exact iR).finiteDimensional p)
  let paddedIdR := idR.appendZeros (R.length - 2)
  have hlen' : (tailS.shift ε).length = paddedIdR.length := by
    have htail : tailS.length = R.length - 1 := by
      calc
        tailS.length = S.length - 1 :=
          FiniteRankProjectiveResolution.length_tail S (by rw [← hlen]; omega)
        _ = R.length - 1 := by rw [hlen]
    have hid : idR.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idR (R.length - 2)
    calc
      (tailS.shift ε).length = tailS.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idR.length + (R.length - 2) := by rw [hid]
      _ = paddedIdR.length := hpad.symm
  have hP : R.term iR = R.termAt 0 := by
    rw [FiniteRankProjectiveResolution.termAt_eq_term (R := R) (by omega)]
  have htail : tailS.termAt j = S.termAt (j + 1) :=
    FiniteRankProjectiveResolution.termAt_tail S (by rw [← hlen]; omega) j
  have hid : idR.termAt j = if j = 0 then R.term iR else 0 :=
    FiniteRankProjectiveResolution.identity_termAt (R.term iR)
      (R.term_rank_projective iR)
      (fun p => (R.row_rank_exact iR).finiteDimensional p) j
  have htarget : (if j = 0 then R.term iR else 0) =
      (if j = 0 then R.termAt 0 else 0) := by
    split_ifs <;> simp [hP]
  have hpadTerm : paddedIdR.termAt j = if j = 0 then R.termAt 0 else 0 :=
    (FiniteRankProjectiveResolution.termAt_appendZeros idR (R.length - 2) j).trans
      (hid.trans htarget)
  change ((tailS.shift ε).biprod paddedIdR hlen').termAt j ≅ _
  exact (FiniteRankProjectiveResolution.termAt_biprodIso
      (tailS.shift ε) paddedIdR hlen' j).trans
    (biprod.mapIso
      ((termAt_shiftIso tailS ε j).trans
        (eqToIso (congrArg (fun X => (CoordinateShift.shift ε).obj X) htail)))
      (eqToIso hpadTerm))

private instance (δ : ℝ≥0) : (CoordinateShift.shift (R := k) (n := n) δ).Additive where
  map_add := by intros; rfl

private noncomputable def crossLeftTailTermIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0)
    (j : ℕ) (hj : 0 < j) :
    (CoordinateShift.shift ((j : ℝ≥0) * ε)).obj
        ((crossLeftResolution R S hlen hpos ε).termAt j) ≅
      (CoordinateShift.shift (((j + 1 : ℕ) : ℝ≥0) * ε)).obj
        (R.termAt (j + 1)) := by
  let θ : ℝ≥0 := (j : ℝ≥0) * ε
  let X := R.termAt (j + 1)
  have hscalar : θ + ε = (((j + 1 : ℕ) : ℝ≥0) * ε) := by
    dsimp [θ]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hterm := (CoordinateShift.shift θ).mapIso
    (crossLeftTermAtIso R S hlen hpos ε j)
  have hterm' : (CoordinateShift.shift θ).obj
      ((crossLeftResolution R S hlen hpos ε).termAt j) ≅
        (CoordinateShift.shift θ).obj ((CoordinateShift.shift ε).obj X ⊞ 0) := by
    simpa [X, Nat.ne_of_gt hj] using hterm
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct
    (CoordinateShift.shift (R := k) (n := n) θ)
    (X := (CoordinateShift.shift ε).obj X) (Y := (0 : PModule.{u,0,u} k (Fin n → ℝ)))
  exact hterm'.trans
    ((Functor.mapBiprod (CoordinateShift.shift θ) ((CoordinateShift.shift ε).obj X) 0).trans
      ((biprod.mapIso (CoordinateShift.compIso θ ε X)
        (Functor.mapZeroObject (CoordinateShift.shift θ))).trans
        ((FiniteRankProjectiveResolution.biprodRightZeroIso
          ((CoordinateShift.shift (θ + ε)).obj X)).trans
          (CoordinateShift.congrIso hscalar X))))

private noncomputable def crossRightTailTermIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0)
    (j : ℕ) (hj : 0 < j) :
    (CoordinateShift.shift ((j : ℝ≥0) * ε)).obj
        ((crossRightResolution R S hlen hpos ε).termAt j) ≅
      (CoordinateShift.shift (((j + 1 : ℕ) : ℝ≥0) * ε)).obj
        (S.termAt (j + 1)) := by
  let θ : ℝ≥0 := (j : ℝ≥0) * ε
  let X := S.termAt (j + 1)
  have hscalar : θ + ε = (((j + 1 : ℕ) : ℝ≥0) * ε) := by
    dsimp [θ]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hterm := (CoordinateShift.shift θ).mapIso
    (crossRightTermAtIso R S hlen hpos ε j)
  have hterm' : (CoordinateShift.shift θ).obj
      ((crossRightResolution R S hlen hpos ε).termAt j) ≅
        (CoordinateShift.shift θ).obj ((CoordinateShift.shift ε).obj X ⊞ 0) := by
    simpa [X, Nat.ne_of_gt hj] using hterm
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct
    (CoordinateShift.shift (R := k) (n := n) θ)
    (X := (CoordinateShift.shift ε).obj X) (Y := (0 : PModule.{u,0,u} k (Fin n → ℝ)))
  exact hterm'.trans
    ((Functor.mapBiprod (CoordinateShift.shift θ) ((CoordinateShift.shift ε).obj X) 0).trans
      ((biprod.mapIso (CoordinateShift.compIso θ ε X)
        (Functor.mapZeroObject (CoordinateShift.shift θ))).trans
        ((FiniteRankProjectiveResolution.biprodRightZeroIso
          ((CoordinateShift.shift (θ + ε)).obj X)).trans
          (CoordinateShift.congrIso hscalar X))))

private noncomputable def crossLeftHeadIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    (CoordinateShift.shift 0).obj
        ((crossLeftResolution R S hlen hpos ε).termAt 0) ≅
      (CoordinateShift.shift 0).obj (S.termAt 0) ⊞
        (CoordinateShift.shift ε).obj (R.termAt 1) := by
  exact (CoordinateShift.zeroIso _).trans
    ((crossLeftTermAtIso R S hlen hpos ε 0).trans
      ((biprod.braiding _ _).trans
        (biprod.mapIso (CoordinateShift.zeroIso (S.termAt 0)).symm (Iso.refl _))))

private noncomputable def crossRightHeadIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    (CoordinateShift.shift 0).obj
        ((crossRightResolution R S hlen hpos ε).termAt 0) ≅
      (CoordinateShift.shift 0).obj (R.termAt 0) ⊞
        (CoordinateShift.shift ε).obj (S.termAt 1) := by
  exact (CoordinateShift.zeroIso _).trans
    ((crossRightTermAtIso R S hlen hpos ε 0).trans
      ((biprod.braiding _ _).trans
        (biprod.mapIso (CoordinateShift.zeroIso (R.termAt 0)).symm (Iso.refl _))))

private noncomputable def resolutionBiproductSplitFinSucc {m : ℕ}
    (F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ)) :
    F 0 ⊞ (⨁ fun j : Fin m => F j.succ) ≅ ⨁ F := by
  classical
  let tail : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let b : Bicone F := {
    pt := F 0 ⊞ ⨁ tail
    π := Fin.cases biprod.fst (fun j => biprod.snd ≫ biproduct.π tail j)
    ι := Fin.cases biprod.inl (fun j => biproduct.ι tail j ≫ biprod.inr)
    ι_π := by
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [Category.assoc]
        · simp [Category.assoc] <;> intro h <;> cases h
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [Category.assoc] <;> intro h <;> cases h
        · by_cases h : i = j
          · subst j
            simp [tail, Category.assoc, biproduct.ι_π]
          · simp [tail, Category.assoc, h, biproduct.ι_π]
  }
  have htotal : ∑ j : Fin (m + 1), b.π j ≫ b.ι j = 𝟙 b.pt := by
    rw [Fin.sum_univ_succ]
    change biprod.fst ≫ biprod.inl +
      ∑ j : Fin m, (biprod.snd ≫ biproduct.π tail j) ≫
        (biproduct.ι tail j ≫ biprod.inr) = 𝟙 _
    have hsum : ∑ j : Fin m, (biprod.snd ≫ biproduct.π tail j) ≫
          (biproduct.ι tail j ≫ biprod.inr (X := F 0) (Y := ⨁ tail)) =
        biprod.snd (X := F 0) (Y := ⨁ tail) ≫
          (∑ j : Fin m, biproduct.π tail j ≫ biproduct.ι tail j) ≫
            biprod.inr (X := F 0) (Y := ⨁ tail) := by
      symm
      rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Category.assoc]
    rw [hsum]
    rw [biproduct.total]
    change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr =
      𝟙 (F 0 ⊞ ⨁ tail)
    exact biprod.total
  exact biproduct.uniqueUpToIso F (isBilimitOfTotal b htotal)

private theorem resolutionBiproductSplitFinSucc_inl_hom {m : ℕ}
    (F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ)) :
    biprod.inl ≫ (resolutionBiproductSplitFinSucc F).hom = biproduct.ι F 0 := by
  apply biproduct.hom_ext
  intro j
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [resolutionBiproductSplitFinSucc, biproduct.uniqueUpToIso,
      Category.assoc, biproduct.lift_π,
      biproduct.ι_π_ne _ (Fin.succ_ne_zero _).symm]

private theorem resolutionBiproductSplitFinSucc_inv_fst {m : ℕ}
    (F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ)) :
    (resolutionBiproductSplitFinSucc F).inv ≫ biprod.fst = biproduct.π F 0 := by
  apply biproduct.hom_ext'
  intro j
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [resolutionBiproductSplitFinSucc, biproduct.uniqueUpToIso,
      Category.assoc, biproduct.ι_desc,
      biproduct.ι_π_ne _ (Fin.succ_ne_zero _).symm]

private noncomputable def resolutionBiproductPairIso {m : ℕ}
    (F G : Fin m → PModule.{u,0,u} k (Fin n → ℝ)) :
    (⨁ fun j => F j ⊞ G j) ≅ (⨁ F) ⊞ (⨁ G) := by
  classical
  let H : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j ⊞ G j
  let b : Bicone H := {
    pt := (⨁ F) ⊞ ⨁ G
    π := fun j => biprod.lift (biprod.fst ≫ biproduct.π F j)
      (biprod.snd ≫ biproduct.π G j)
    ι := fun j => biprod.desc (biproduct.ι F j ≫ biprod.inl)
      (biproduct.ι G j ≫ biprod.inr)
    ι_π := by
      intro i j
      by_cases h : i = j
      · subst j
        simp [H, Category.assoc, biprod.desc_eq, biprod.lift_eq,
          biproduct.ι_π]
      · simp [H, Category.assoc, biprod.desc_eq, biprod.lift_eq, h,
          biproduct.ι_π]
  }
  have htotal : ∑ j : Fin m, b.π j ≫ b.ι j = 𝟙 b.pt := by
    have hcomp (j : Fin m) : b.π j ≫ b.ι j =
        (biprod.fst ≫ biproduct.π F j ≫ biproduct.ι F j ≫ biprod.inl) +
          (biprod.snd ≫ biproduct.π G j ≫ biproduct.ι G j ≫ biprod.inr) := by
      simp [b, Category.assoc, biprod.lift_desc]
    calc
      _ = ∑ j : Fin m,
          ((biprod.fst ≫ biproduct.π F j ≫ biproduct.ι F j ≫ biprod.inl) +
            (biprod.snd ≫ biproduct.π G j ≫ biproduct.ι G j ≫ biprod.inr)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcomp j
      _ = (biprod.fst ≫ (∑ j : Fin m, biproduct.π F j ≫ biproduct.ι F j) ≫ biprod.inl) +
          (biprod.snd ≫ (∑ j : Fin m, biproduct.π G j ≫ biproduct.ι G j) ≫ biprod.inr) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · symm
            rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Category.assoc]
          · symm
            rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Category.assoc]
      _ = 𝟙 b.pt := by
          rw [biproduct.total, biproduct.total]
          change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr =
            𝟙 ((⨁ F) ⊞ ⨁ G)
          exact biprod.total
  exact (biproduct.uniqueUpToIso H (isBilimitOfTotal b htotal)).symm

private theorem isZero_biproduct_of_isZero {ι : Type} [Finite ι]
    (F : ι → PModule.{u,0,u} k (Fin n → ℝ)) (hF : ∀ i, IsZero (F i)) :
    IsZero (⨁ F) := by
  refine ⟨?_, ?_⟩
  · intro Y
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply biproduct.hom_ext'
    intro i
    exact (hF i).eq_of_src _ _
  · intro Y
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply biproduct.hom_ext
    intro i
    exact (hF i).eq_of_tgt _ _

private noncomputable def resolutionBiproductHeadZeroIsoOfPos {m : ℕ}
    (hm : 0 < m) (P : PModule.{u,0,u} k (Fin n → ℝ)) :
    (⨁ fun j : Fin m => if j = (⟨0, hm⟩ : Fin m) then P else 0) ≅ P := by
  classical
  let q : ℕ := m - 1
  have hq : q + 1 = m := by dsimp [q]; omega
  let e : Fin (q + 1) ≃ Fin m := finCongr hq
  let head : Fin m := ⟨0, hm⟩
  let G : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => if j = head then P else 0
  let F : Fin (q + 1) → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G (e j)
  have he0 : e (0 : Fin (q + 1)) = head := by
    apply Fin.ext
    rfl
  have hzero : F 0 = P := by simp [F, G, he0, head]
  have htail : ∀ j : Fin q, F j.succ = 0 := by
    intro j
    have he : e j.succ ≠ head := by
      intro h
      have heq : e j.succ = e (0 : Fin (q + 1)) := h.trans he0.symm
      have : j.succ = 0 := e.injective heq
      exact Fin.succ_ne_zero _ this
    change G (e j.succ) = 0
    simp only [G, if_neg he]
  have htailZero : ∀ j : Fin q, IsZero (F j.succ) := by
    intro j
    rw [htail j]
    exact isZero_zero _
  let tail : Fin q → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let eTail : (⨁ tail) ≅ (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    (isZero_biproduct_of_isZero tail htailZero).iso (isZero_zero _)
  have htailDef : tail = fun j : Fin q => F j.succ := rfl
  let reduce : P ⊞ (0 : PModule.{u,0,u} k (Fin n → ℝ)) ≅ P := {
    hom := biprod.fst
    inv := biprod.inl
    hom_inv_id := by
      apply biprod.hom_ext'
      · simp
      · exact (isZero_zero _).eq_of_src _ _
    inv_hom_id := by simp
  }
  simpa only [F, G, head, htailDef] using
    ((biproduct.reindex e G).symm ≪≫
      (resolutionBiproductSplitFinSucc F).symm ≪≫
      biprod.mapIso (eqToIso hzero) eTail ≪≫ reduce)

private noncomputable def crossResolutionInterleaving
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0)
    (i : CoordinateInterleaving ε M N) :
    CoordinateInterleaving ε
      ((CoordinateShift.shift ε).obj (R.kernel ⟨1, by omega⟩) ⊞
        S.term ⟨0, by omega⟩)
      ((CoordinateShift.shift ε).obj
        (S.kernel ⟨1, by rw [← hlen]; omega⟩) ⊞ R.term ⟨0, by omega⟩) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let iS : Fin S.length := ⟨0, by rw [← hlen]; omega⟩
  let hR := (R.row_rank_exact iR).of_iso
    (Iso.refl _) (Iso.refl _) R.initial_iso
  let hS := (S.row_rank_exact iS).of_iso
    (Iso.refl _) (Iso.refl _) S.initial_iso
  let oneStep := RankSchanuel.interleavingOfSequences
    (α := R.quotient iR ≫ R.initial_iso.hom)
    (β := S.quotient iS ≫ S.initial_iso.hom) (i := i)
    hR hS (R.term_rank_projective iR) (S.term_rank_projective iS)
  exact oneStep.symm.congr (Iso.refl _)
    (biprod.braiding (R.term iR)
      ((CoordinateShift.shift ε).obj (S.kernel iS.succ)))

private noncomputable def crossLeftResolutionBiproductIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (m : ℕ)
    (hR : R.length = m + 2) (hS : S.length = m + 2) :
    (⨁ schanuelLeftAt
      (crossLeftResolution R S hlen hpos ε)
      (crossRightResolution R S hlen hpos ε) ε (L := m + 1)) ≅
    (⨁ schanuelRightAt R S ε (L := m + 2)) := by
  classical
  let U := crossLeftResolution R S hlen hpos ε
  let V := crossRightResolution R S hlen hpos ε
  let F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelLeftAt U V ε j
  let G : Fin (m + 2) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelRightAt R S ε j
  have hhead : F 0 ≅ G 0 ⊞ G 1 := by
    simpa [F, G, U, schanuelLeftAt, schanuelRightAt] using
      (crossLeftHeadIso R S hlen hpos ε)
  let Ftail : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let Gtail1 : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ
  let Gtail2 : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ.succ
  have htail (q : Fin m) : Ftail q ≅ Gtail2 q := by
    let j : ℕ := q.val + 1
    have hj : 0 < j := by dsimp [j]; omega
    by_cases hEven : Even j
    · have hNotEvenNext : ¬ Even (j + 1) := by
        simp [Nat.even_add_one, hEven]
      simpa [Ftail, Gtail2, G, F, U, j, schanuelLeftAt,
        schanuelRightAt, hEven, hNotEvenNext] using
          (crossLeftTailTermIso R S hlen hpos ε j hj)
    · have hEvenNext : Even (j + 1) := by
        rw [Nat.even_add_one]
        exact hEven
      simpa [Ftail, Gtail2, G, F, V, j, schanuelLeftAt,
        schanuelRightAt, hEven, hEvenNext] using
          (crossRightTailTermIso R S hlen hpos ε j hj)
  let splitF := resolutionBiproductSplitFinSucc F
  let splitG := resolutionBiproductSplitFinSucc G
  let splitGtail := resolutionBiproductSplitFinSucc Gtail1
  exact splitF.symm ≪≫
    biprod.mapIso hhead (biproduct.mapIso htail) ≪≫
    biprod.associator (G 0) (G 1) (⨁ Gtail2) ≪≫
    biprod.mapIso (Iso.refl _) splitGtail ≪≫ splitG

private noncomputable def crossRightResolutionBiproductIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (m : ℕ)
    (hR : R.length = m + 2) (hS : S.length = m + 2) :
    (⨁ schanuelRightAt
      (crossLeftResolution R S hlen hpos ε)
      (crossRightResolution R S hlen hpos ε) ε (L := m + 1)) ≅
    (⨁ schanuelLeftAt R S ε (L := m + 2)) := by
  classical
  let U := crossLeftResolution R S hlen hpos ε
  let V := crossRightResolution R S hlen hpos ε
  let F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelRightAt U V ε j
  let G : Fin (m + 2) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelLeftAt R S ε j
  have hhead : F 0 ≅ G 0 ⊞ G 1 := by
    simpa [F, G, V, schanuelLeftAt, schanuelRightAt] using
      (crossRightHeadIso R S hlen hpos ε)
  let Ftail : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let Gtail1 : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ
  let Gtail2 : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ.succ
  have htail (q : Fin m) : Ftail q ≅ Gtail2 q := by
    let j : ℕ := q.val + 1
    have hj : 0 < j := by dsimp [j]; omega
    by_cases hEven : Even j
    · have hNotEvenNext : ¬ Even (j + 1) := by
        simp [Nat.even_add_one, hEven]
      simpa [Ftail, Gtail2, G, F, V, j, schanuelRightAt,
        schanuelLeftAt, hEven, hNotEvenNext] using
          (crossRightTailTermIso R S hlen hpos ε j hj)
    · have hEvenNext : Even (j + 1) := by
        rw [Nat.even_add_one]
        exact hEven
      simpa [Ftail, Gtail2, G, F, U, j, schanuelRightAt,
        schanuelLeftAt, hEven, hEvenNext] using
          (crossLeftTailTermIso R S hlen hpos ε j hj)
  let splitF := resolutionBiproductSplitFinSucc F
  let splitG := resolutionBiproductSplitFinSucc G
  let splitGtail := resolutionBiproductSplitFinSucc Gtail1
  exact splitF.symm ≪≫
    biprod.mapIso hhead (biproduct.mapIso htail) ≪≫
    biprod.associator (G 0) (G 1) (⨁ Gtail2) ≪≫
    biprod.mapIso (Iso.refl _) splitGtail ≪≫ splitG

private noncomputable def resolutionBiproductFinOneIso
    (P : PModule.{u,0,u} k (Fin n → ℝ)) :
    (⨁ fun _ : Fin 1 => P) ≅ P := by
  classical
  let F : Fin 1 → PModule.{u,0,u} k (Fin n → ℝ) := fun _ => P
  let tail : Fin 0 → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let eTail : (⨁ tail) ≅ (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    (isZero_biproduct_of_isZero tail (by intro j; exact Fin.elim0 j)).iso
      (isZero_zero _)
  exact (resolutionBiproductSplitFinSucc F).symm ≪≫
    biprod.mapIso (Iso.refl P) eTail ≪≫
      FiniteRankProjectiveResolution.biprodRightZeroIso P

private noncomputable def schanuelLeftFinOneIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (hR : R.length = 1) :
    (⨁ schanuelLeftAt R S ε (L := 1)) ≅ R.term ⟨0, by omega⟩ := by
  classical
  let F : Fin 1 → PModule.{u,0,u} k (Fin n → ℝ) := fun j => schanuelLeftAt R S ε j
  have hR0 : R.termAt 0 = R.term ⟨0, by omega⟩ :=
    FiniteRankProjectiveResolution.termAt_eq_term R (by omega)
  have hterm (j : Fin 1) : F j ≅ R.term ⟨0, by omega⟩ := by
    have hj : j = 0 := by apply Fin.ext; omega
    subst j
    simpa [F, schanuelLeftAt] using
      (CoordinateShift.zeroIso (R.termAt 0)).trans (eqToIso hR0)
  exact biproduct.mapIso hterm ≪≫ resolutionBiproductFinOneIso _

private noncomputable def schanuelRightFinOneIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (hS : S.length = 1) :
    (⨁ schanuelRightAt R S ε (L := 1)) ≅ S.term ⟨0, by omega⟩ := by
  classical
  let F : Fin 1 → PModule.{u,0,u} k (Fin n → ℝ) := fun j => schanuelRightAt R S ε j
  have hS0 : S.termAt 0 = S.term ⟨0, by omega⟩ :=
    FiniteRankProjectiveResolution.termAt_eq_term S (by omega)
  have hterm (j : Fin 1) : F j ≅ S.term ⟨0, by omega⟩ := by
    have hj : j = 0 := by apply Fin.ext; omega
    subst j
    simpa [F, schanuelRightAt] using
      (CoordinateShift.zeroIso (S.termAt 0)).trans (eqToIso hS0)
  exact biproduct.mapIso hterm ≪≫ resolutionBiproductFinOneIso _

private noncomputable def schanuelAtLength (L : ℕ) :
    ∀ {M N : PModule.{u,0,u} k (Fin n → ℝ)}
      (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
      (hR : R.length = L) (hS : S.length = L) (ε : ℝ≥0)
      (i : CoordinateInterleaving ε M N),
      CoordinateInterleaving ε
        (⨁ schanuelLeftAt R S ε (L := L))
        (⨁ schanuelRightAt R S ε (L := L)) := by
  induction L with
  | zero =>
    intro M N R S hR hS ε i
    have hA : IsZero (⨁ schanuelLeftAt R S ε (L := 0)) :=
      isZero_biproduct_of_isZero _ (by intro j; exact Fin.elim0 j)
    have hB : IsZero (⨁ schanuelRightAt R S ε (L := 0)) :=
      isZero_biproduct_of_isZero _ (by intro j; exact Fin.elim0 j)
    exact (CoordinateInterleaving.refl ε (0 : PModule.{u,0,u} k (Fin n → ℝ))).congr
      (hA.iso (isZero_zero _)).symm (hB.iso (isZero_zero _)).symm
  | succ L ih =>
    cases L with
    | zero =>
      intro M N R S hR hS ε i
      have hRlen : R.length = 1 := hR
      have hSlen : S.length = 1 := hS
      exact (FiniteRankProjectiveResolution.interleaving_of_length_one
          R S hRlen hSlen ε i).congr
        (schanuelLeftFinOneIso R S ε hRlen).symm
        (schanuelRightFinOneIso R S ε hSlen).symm
    | succ m =>
      intro M N R S hR hS ε i
      have hpos : 1 < R.length := by omega
      have hlen : R.length = S.length := hR.trans hS.symm
      let U := crossLeftResolution R S hlen hpos ε
      let V := crossRightResolution R S hlen hpos ε
      have hULen : U.length = m + 1 := by
        dsimp [U, crossLeftResolution, FiniteRankProjectiveResolution.biprod,
          FiniteRankProjectiveResolution.shift]
        simp [FiniteRankProjectiveResolution.length_tail, hR]
      have hVLen : V.length = m + 1 := by
        dsimp [V, crossRightResolution, FiniteRankProjectiveResolution.biprod,
          FiniteRankProjectiveResolution.shift]
        simp [FiniteRankProjectiveResolution.length_tail, hR, hS]
      have iUV := crossResolutionInterleaving R S hlen hpos ε i
      have ihUV := ih U V hULen hVLen ε iUV
      have hR' : R.length = m + 2 := by omega
      have hS' : S.length = m + 2 := by omega
      exact (ihUV.congr
        (crossLeftResolutionBiproductIso R S hlen hpos ε m hR' hS')
        (crossRightResolutionBiproductIso R S hlen hpos ε m hR' hS')).symm

/-- Persistent Schanuel comparison for arbitrary finite rank-projective
resolutions.  Each resolution is extended by zero terms to the larger length;
the alternating summands are shifted by their homological degree.  The proof
constructs the interleaving maps and both composite equations by induction on
that common length. -/
noncomputable def schanuelInterleavingOfResolutions
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (i : CoordinateInterleaving ε M N) :
    CoordinateInterleaving ε
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct R S ε)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct R S ε) := by
  classical
  let L := max R.length S.length
  let R' := FiniteRankProjectiveResolution.appendZeros R (L - R.length)
  let S' := FiniteRankProjectiveResolution.appendZeros S (L - S.length)
  have hR' : R'.length = L := by
    dsimp [R']
    rw [FiniteRankProjectiveResolution.appendZeros_length]
    dsimp [L]
    omega
  have hS' : S'.length = L := by
    dsimp [S']
    rw [FiniteRankProjectiveResolution.appendZeros_length]
    dsimp [L]
    omega
  have hmaxPad : max R'.length S'.length = L := by rw [hR', hS']; simp
  have hleft (j : Fin L) : schanuelLeftAt R' S' ε j = schanuelLeftAt R S ε j := by
    unfold schanuelLeftAt
    by_cases hEven : Even j.val <;>
      simp [hEven, R', S', FiniteRankProjectiveResolution.termAt_appendZeros]
  have hright (j : Fin L) : schanuelRightAt R' S' ε j = schanuelRightAt R S ε j := by
    unfold schanuelRightAt
    by_cases hEven : Even j.val <;>
      simp [hEven, R', S', FiniteRankProjectiveResolution.termAt_appendZeros]
  let eLeft0 : (⨁ schanuelLeftAt R' S' ε (L := L)) ≅
      (⨁ schanuelLeftAt R S ε (L := L)) :=
    biproduct.mapIso (fun j => eqToIso (hleft j))
  let eRight0 : (⨁ schanuelRightAt R' S' ε (L := L)) ≅
      (⨁ schanuelRightAt R S ε (L := L)) :=
    biproduct.mapIso (fun j => eqToIso (hright j))
  have eLeft :
      FiniteRankProjectiveResolution.schanuelLeftBiproduct R' S' ε ≅
        FiniteRankProjectiveResolution.schanuelLeftBiproduct R S ε := by
    change (⨁ schanuelLeftAt R' S' ε
      (L := max R'.length S'.length)) ≅
        (⨁ schanuelLeftAt R S ε (L := max R.length S.length))
    rw [hmaxPad]
    change (⨁ schanuelLeftAt R' S' ε (L := L)) ≅
      (⨁ schanuelLeftAt R S ε (L := L))
    exact eLeft0
  have eRight :
      FiniteRankProjectiveResolution.schanuelRightBiproduct R' S' ε ≅
        FiniteRankProjectiveResolution.schanuelRightBiproduct R S ε := by
    change (⨁ schanuelRightAt R' S' ε
      (L := max R'.length S'.length)) ≅
        (⨁ schanuelRightAt R S ε (L := max R.length S.length))
    rw [hmaxPad]
    change (⨁ schanuelRightAt R' S' ε (L := L)) ≅
      (⨁ schanuelRightAt R S ε (L := L))
    exact eRight0
  have ih0 := schanuelAtLength L R' S' hR' hS' ε i
  have ih : CoordinateInterleaving ε
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct R' S' ε)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct R' S' ε) := by
    change CoordinateInterleaving ε
      (⨁ schanuelLeftAt R' S' ε (L := max R'.length S'.length))
      (⨁ schanuelRightAt R' S' ε (L := max R'.length S'.length))
    rw [hmaxPad]
    exact ih0
  exact ih.congr eLeft eRight

end TDA.Persistence
