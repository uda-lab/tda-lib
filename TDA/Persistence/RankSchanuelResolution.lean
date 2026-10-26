import TDA.Persistence.RankSchanuel
import TDA.Persistence.FiniteRankProjectiveResolution
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

/-- Relative projectivity is preserved by coordinate shifts.  This uses that
translation of `Fin n → ℝ` is an order equivalence, so a rank-exact lifting
problem can be transported back along the inverse translation. -/
theorem IsRankProjective.shift {Q : PModule.{u,0,u} k (Fin n → ℝ)}
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

end TDA.Persistence
