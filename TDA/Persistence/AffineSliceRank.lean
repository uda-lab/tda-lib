import TDA.Persistence.AffineSliceHooks
import TDA.Persistence.RealBarcodeRankUniqueness

/-!
# Rank counts of sliced hook sums

Actual finite hook presentations become finite interval families upon restriction
along a positive affine line. Their structure-map ranks count precisely the
retained intervals spanning two observations. The same calculation applies to
each term of the original multidimensional resolution; it does not require a
minimal or projective resolution after restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace TDA.Persistence.PositiveAffineLine
open CategoryTheory CategoryTheory.Limits
open scoped TDA.Persistence ZeroObject Classical
variable {k : Type u} [Field k] {n : ℕ} [NeZero n]
variable (L : PositiveAffineLine n)

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

omit [NeZero n] in
private theorem fiberIsoPi_hom_apply {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ)
    (x : (⨁ F).obj p) (i : J) :
    ((FiniteBiproduct.fiberIsoPi F p).hom.hom x) i =
      ((biproduct.π F i).app p).hom x := by
  have h := congrArg (fun f : (⨁ F).obj p ⟶ (F i).obj p => f.hom x)
    (FiniteBiproduct.fiberIsoPi_hom_π F p i)
  exact h

private noncomputable def reindexBiproductFamilyIso {J : Type} [Fintype J]
    (F : J → PModule.{u,0,u} k (Fin n → ℝ)) :
    reindex L.orderHom (⨁ F) ≅
      RealBarcode.familyModule (fun i => reindex L.orderHom (F i)) := by
  refine NatIso.ofComponents (fun t => FiniteBiproduct.fiberIsoPi F (L.orderHom t)) ?_
  intro s t f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change ((FiniteBiproduct.fiberIsoPi F (L.orderHom t)).hom.hom
      (structureMapLinear (⨁ F) (L.orderHom.monotone (leOfHom f)) x)) i =
    structureMapLinear (F i) (L.orderHom.monotone (leOfHom f))
      (((FiniteBiproduct.fiberIsoPi F (L.orderHom s)).hom.hom x) i)
  rw [fiberIsoPi_hom_apply, fiberIsoPi_hom_apply]
  exact congrArg (fun h : (⨁ F).obj (L.orderHom s) ⟶ (F i).obj (L.orderHom t) => h.hom x)
    ((biproduct.π F i).naturality (homOfLE (L.orderHom.monotone (leOfHom f))))

private noncomputable def retainedEndpointsOrDiagonal (tag : RealHookTag (n := n)) : ℝ × WithTop ℝ :=
  (L.hookEndpoints tag).getD (0, ((0 : ℝ) : WithTop ℝ))

private noncomputable def hookRestrictionIntervalIso (tag : RealHookTag (n := n)) :
    reindex L.orderHom
      (FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) tag) ≅
      RealBarcode.intervalModule (k := k) (retainedEndpointsOrDiagonal L tag) := by
  cases he : L.hookEndpoints tag with
  | none =>
    have hs := L.hookTag_reindex_isZero_of_none (k := k) tag he
    have ht := RectangleBarcodeBridge.empty_interval_isZero (k := k) (0, 0) le_rfl
    simpa only [retainedEndpointsOrDiagonal, he, Option.getD_none] using (hs.isoZero ≪≫ ht.isoZero.symm)
  | some p =>
    simpa only [retainedEndpointsOrDiagonal, he, Option.getD_some] using
      (L.hookTag_reindexIso_of_some (k := k) tag p he)

private noncomputable def hookPresentationIntervalFamilyIso
    {M : PModule.{u,0,u} k (Fin n → ℝ)} (Q : FiniteHookSumPresentation M) :
    reindex L.orderHom M ≅
      RealBarcode.familyModule (fun i => RealBarcode.intervalModule (k := k)
        (retainedEndpointsOrDiagonal L (Q.tag i))) :=
  Functor.isoWhiskerLeft L.orderHom.toFunctor Q.iso ≪≫
    reindexBiproductFamilyIso L _ ≪≫
      RealBarcode.familyIso (Equiv.refl _) _ _ (fun i => hookRestrictionIntervalIso L (Q.tag i))

private theorem countP_sliceHookMultiset_tagMultiset {m : ℕ} (T : Fin m → RealHookTag (n := n))
    (s t : ℝ) (hst : s ≤ t) :
    (L.sliceHookMultiset (hookTagMultiset T)).countP
        (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) =
      ∑ i : Fin m, if (retainedEndpointsOrDiagonal L (T i)).1 ≤ s ∧
        (t : WithTop ℝ) < (retainedEndpointsOrDiagonal L (T i)).2 then 1 else 0 := by
  induction m with
  | zero => simp [hookTagMultiset]
  | succ m ih =>
    rw [hookTagMultiset, L.sliceHookMultiset_add, Multiset.countP_add,
      Fin.sum_univ_succ, ih (fun i => T i.succ)]
    congr 1
    rw [L.sliceHookMultiset_singleton]
    cases he : L.hookEndpoints (T 0) with
    | none =>
      simp [he, retainedEndpointsOrDiagonal]
      intro hs
      exact hs.trans hst
    | some p =>
      simp only [he, retainedEndpointsOrDiagonal, Option.getD_some, Option.toList_some]
      rw [Multiset.coe_countP]
      simp [List.countP_cons]
/-- The actual structure-map rank of a presented hook sum along the line is
the number of retained intervals spanning the observations, with multiplicity.
Collapsed finite hooks contribute zero and principal deaths remain infinite. -/
theorem rankOfStructureMap_hookPresentation_eq_countP
    {M : PModule.{u,0,u} k (Fin n → ℝ)} (Q : FiniteHookSumPresentation M)
    (s t : ℝ) (hst : s ≤ t) :
    rankOfStructureMap M (L.orderHom.monotone hst) =
      (L.sliceHookMultiset (hookTagMultiset Q.tag)).countP
        (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) := by
  calc
    _ = rankOfStructureMap (reindex L.orderHom M) hst := rfl
    _ = rankOfStructureMap (RealBarcode.familyModule
        (fun i => RealBarcode.intervalModule (k := k) (retainedEndpointsOrDiagonal L (Q.tag i)))) hst :=
      rankOfStructureMap_iso hst (hookPresentationIntervalFamilyIso L Q)
    _ = ∑ i : Fin Q.count, if (retainedEndpointsOrDiagonal L (Q.tag i)).1 ≤ s ∧
        (t : WithTop ℝ) < (retainedEndpointsOrDiagonal L (Q.tag i)).2 then 1 else 0 :=
      RealBarcode.rank_intervalFamily _ s t hst
    _ = _ := (countP_sliceHookMultiset_tagMultiset L Q.tag s t hst).symm

/-- Each actual term of a certified minimal ambient resolution has the rank
counts of its sliced hook Betti multiset. The term presentation is constructed
from the proved hook-sum existence theorem. -/
theorem resolution_term_rank_eq_sliceHookMultiset_countP
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,u} (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (j : Fin R.resolution.length) (s t : ℝ) (hst : s ≤ t) :
    rankOfStructureMap (R.resolution.term j) (L.orderHom.monotone hst) =
      (L.sliceHookMultiset (R.hookBettiMultiset M
        (GradedFree.finitelyPresented_lowerIndexUniverse M hM) j.val)).countP
        (fun p => p.1 ≤ s ∧ (t : WithTop ℝ) < p.2) := by
  let hM0 := GradedFree.finitelyPresented_lowerIndexUniverse M hM
  let Q0 := Classical.choice (R.exists_hook_sum_presentation M hM0 j.val)
  let Q : FiniteHookSumPresentation (R.resolution.term j) :=
    ⟨Q0.count, Q0.tag, (eqToIso (R.termAt_eq j.isLt)).symm ≪≫ Q0.iso⟩
  have h := rankOfStructureMap_hookPresentation_eq_countP L Q s t hst
  rw [R.hookBettiMultiset_eq_tagMultiset M hM0 j.val Q0]
  exact h

private noncomputable def sliceHookMultisetHom :
    Multiset (RealHookTag (n := n)) →+ Multiset (ℝ × WithTop ℝ) where
  toFun := L.sliceHookMultiset
  map_zero' := L.sliceHookMultiset_zero
  map_add' := L.sliceHookMultiset_add

/-- Slicing the even hook multiset preserves the finite parity sum, including
every retained occurrence and every collision of sliced endpoints. -/
theorem sliceHookMultiset_evenHookBetti
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,u} (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    L.sliceHookMultiset (R.evenHookBetti M
        (GradedFree.finitelyPresented_lowerIndexUniverse M hM)) =
      ∑ j : Fin R.resolution.length, if Even j.val then
        L.sliceHookMultiset (R.hookBettiMultiset M
          (GradedFree.finitelyPresented_lowerIndexUniverse M hM) j.val) else 0 := by
  let hM0 := GradedFree.finitelyPresented_lowerIndexUniverse M hM
  change (sliceHookMultisetHom L) (∑ j ∈ evenHookDegrees R.resolution.length,
    R.hookBettiMultiset M hM0 j) = _
  rw [map_sum, evenHookDegrees, Finset.sum_filter, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- Slicing the odd hook multiset preserves the finite parity sum. -/
theorem sliceHookMultiset_oddHookBetti
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,u} (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    L.sliceHookMultiset (R.oddHookBetti M
        (GradedFree.finitelyPresented_lowerIndexUniverse M hM)) =
      ∑ j : Fin R.resolution.length, if Odd j.val then
        L.sliceHookMultiset (R.hookBettiMultiset M
          (GradedFree.finitelyPresented_lowerIndexUniverse M hM) j.val) else 0 := by
  let hM0 := GradedFree.finitelyPresented_lowerIndexUniverse M hM
  change (sliceHookMultisetHom L) (∑ j ∈ oddHookDegrees R.resolution.length,
    R.hookBettiMultiset M hM0 j) = _
  rw [map_sum, oddHookDegrees, Finset.sum_filter, ← Fin.sum_univ_eq_sum_range]
  rfl
end TDA.Persistence.PositiveAffineLine
