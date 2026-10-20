import TDA.Mapper.CategoricalMapper
import TDA.Reeb.ConstructibleCosheaf
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Gluing components over interval-cover saturations

A fixed cover interval meets the members of any interval cover in a connected chain.
Consequently compatible functions on saturated inverse-image components agree on each
original cover component. This is the gluing mechanism that makes categorical Mapper an
interval cosheaf, despite saturation not preserving intersections strictly.
-/

open Set CategoryTheory

universe u v w z

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval

noncomputable section

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {κ : Type w} {A : Type z}
variable (f : C(X, ℝ)) (U : ι → OpenInterval) (K : κ → OpenInterval)

/-- An original cover-component map into a saturated test interval. -/
def memberToCoverComponents (i : ι) (k : κ) (h : ((U i : Set ℝ) ∩ K k).Nonempty) :
    (intervalComponents f).obj (U i) → (coverComponents f U).obj (K k) :=
  (componentFunctor f).map (homOfLE (coverMember_le_saturation U (K k) ⟨i, h⟩))

variable (a : ∀ k, (coverComponents f U).obj (K k) → A)
variable (ha : ∀ k l (c : (coverComponents f U).obj (K k ⊓ K l)),
  a k ((coverComponents f U).map (homOfLE inf_le_left) c) =
    a l ((coverComponents f U).map (homOfLE inf_le_right) c))

include ha in
/-- A point in the triple intersection gives compatibility on every component of a member. -/
theorem coverComponents_memberAgreementAt (i : ι) (k l : κ) (y : ℝ)
    (hyU : y ∈ U i) (hyk : y ∈ K k) (hyl : y ∈ K l)
    (c : (intervalComponents f).obj (U i)) :
    a k (memberToCoverComponents f U K i k ⟨y, hyU, hyk⟩ c) =
      a l (memberToCoverComponents f U K i l ⟨y, hyU, hyl⟩ c) := by
  induction c using ZerothHomotopy.rec with
  | mk x =>
    exact ha k l (ZerothHomotopy.mk ⟨x.val,
      mem_coverSaturation.mpr ⟨i, x.property, y, hyU, hyk, hyl⟩⟩)

include ha in
/-- Compatibility propagates along an interval cover through the connected member interval. -/
theorem coverComponents_memberAgreement {J : OpenInterval}
    (hJ : ⋃ k, (K k : Set ℝ) = J) (i : ι) (k l : κ)
    (hk : ((U i : Set ℝ) ∩ K k).Nonempty)
    (hl : ((U i : Set ℝ) ∩ K l).Nonempty)
    (c : (intervalComponents f).obj (U i)) :
    a k (memberToCoverComponents f U K i k hk c) =
      a l (memberToCoverComponents f U K i l hl c) := by
  classical
  let W := U i ⊓ J
  have hcover (p : W) : ∃ m, p.val ∈ K m := by
    have hp : p.val ∈ (J : Set ℝ) := p.property.2
    rw [← hJ] at hp
    exact mem_iUnion.mp hp
  let label (p : W) : κ := (hcover p).choose
  have hlabel (p : W) : p.val ∈ K (label p) := (hcover p).choose_spec
  let value (p : W) : A :=
    a (label p) (memberToCoverComponents f U K i (label p)
      ⟨p.val, p.property.1, hlabel p⟩ c)
  have hvalue (p : W) (m : κ) (hm : p.val ∈ K m) :
      value p = a m (memberToCoverComponents f U K i m
        ⟨p.val, p.property.1, hm⟩ c) :=
    coverComponents_memberAgreementAt f U K a ha i (label p) m p.val
      p.property.1 (hlabel p) hm c
  have hlocal : IsLocallyConstant value := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    refine ⟨{q : W | q.val ∈ K (label p)},
      (K (label p)).isOpen.preimage continuous_subtype_val, hlabel p, ?_⟩
    intro q hq
    exact (hvalue q (label p) hq).trans (by rfl)
  let : PreconnectedSpace W :=
    isPreconnected_iff_preconnectedSpace.mp (U i ⊓ J).ordConnected.isPreconnected
  obtain ⟨y, hyU, hyk⟩ := hk
  obtain ⟨t, htU, htl⟩ := hl
  let p : W := ⟨y, hyU, le_of_iUnion_eq hJ k hyk⟩
  let q : W := ⟨t, htU, le_of_iUnion_eq hJ l htl⟩
  have hconst : value p = value q :=
    (⟨value, hlocal⟩ : LocallyConstant W A).apply_eq_of_preconnectedSpace p q
  exact (hvalue p k hyk).symm.trans (hconst.trans (hvalue q l htl))

include ha in
/-- Compatible functions on saturated components glue uniquely over every interval cover. -/
theorem coverComponents_existsUnique_glue {J : OpenInterval}
    (hJ : ⋃ k, (K k : Set ℝ) = J) :
    ∃! g : (coverComponents f U).obj J → A,
      ∀ k (e : (coverComponents f U).obj (K k)),
        g ((coverComponents f U).map (homOfLE (le_of_iUnion_eq hJ k)) e) = a k e := by
  classical
  have hex (i : ActiveCoverMember U J) : ∃ k, ((U i.val : Set ℝ) ∩ K k).Nonempty := by
    obtain ⟨y, hyU, hyJ⟩ := i.property
    rw [← hJ] at hyJ
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hyJ
    exact ⟨k, y, hyU, hyk⟩
  choose test htest using hex
  let b (i : ActiveCoverMember U J) (e : (intervalComponents f).obj (U i.val)) : A :=
    a (test i) (memberToCoverComponents f U K i.val (test i) (htest i) e)
  have hb (i j : ActiveCoverMember U J)
      (e : (componentFunctor f).obj (toOpens (U i.val) ⊓ toOpens (U j.val))) :
      b i ((componentFunctor f).map (homOfLE inf_le_left) e) =
        b j ((componentFunctor f).map (homOfLE inf_le_right) e) := by
    induction e using ZerothHomotopy.rec with
    | mk x =>
      obtain ⟨y, hyi, hyj, hyJ⟩ := intervalTripleIntersection_nonempty
        (U i.val) (U j.val) J ⟨f x.val, x.property.1, x.property.2⟩ i.property j.property
      change y ∈ (J : Set ℝ) at hyJ
      rw [← hJ] at hyJ
      obtain ⟨k, hyk⟩ := mem_iUnion.mp hyJ
      exact (coverComponents_memberAgreement f U K a ha hJ i.val (test i) k
        (htest i) ⟨y, hyi, hyk⟩ (ZerothHomotopy.mk ⟨x.val, x.property.1⟩)).trans
        (coverComponents_memberAgreement f U K a ha hJ j.val (test j) k
          (htest j) ⟨y, hyj, hyk⟩ (ZerothHomotopy.mk ⟨x.val, x.property.2⟩)).symm
  have hcov : coverSaturation U J ≤ ⨆ i : ActiveCoverMember U J, toOpens (U i.val) := by
    intro x hx
    obtain ⟨i, hxi, y, hyU, hyJ⟩ := mem_coverSaturation.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, y, hyU, hyJ⟩, hxi⟩
  obtain ⟨g, hg, huniq⟩ := componentFunctor_existsUnique_glue f
    (fun i : ActiveCoverMember U J => toOpens (U i.val))
    (coverMember_le_saturation U J) hcov b hb
  refine ⟨g, ?_, ?_⟩
  · intro k e
    obtain ⟨p, rfl⟩ := coverComponentGenerator_surjective f U (K k) e
    rcases p with ⟨⟨i, hi⟩, c⟩
    have hiJ : ((U i : Set ℝ) ∩ J).Nonempty := by
      obtain ⟨y, hyU, hyk⟩ := hi
      exact ⟨y, hyU, le_of_iUnion_eq hJ k hyk⟩
    let j : ActiveCoverMember U J := ⟨i, hiJ⟩
    have hmap : (coverComponents f U).map (homOfLE (le_of_iUnion_eq hJ k))
          (coverComponentGenerator f U (K k) ⟨⟨i, hi⟩, c⟩) =
        (componentFunctor f).map (homOfLE (coverMember_le_saturation U J j)) c := by
      induction c using ZerothHomotopy.rec with
      | mk x => rfl
    rw [hmap, hg j c]
    exact coverComponents_memberAgreement f U K a ha hJ i (test j) k (htest j) hi c
  · intro g' hg'
    apply huniq g'
    intro i e
    have hmap : (componentFunctor f).map (homOfLE (coverMember_le_saturation U J i)) e =
        (coverComponents f U).map (homOfLE (le_of_iUnion_eq hJ (test i)))
          (memberToCoverComponents f U K i.val (test i) (htest i) e) := by
      induction e using ZerothHomotopy.rec with
      | mk x => rfl
    rw [hmap, hg']

/-- Saturated inverse-image components satisfy the interval cosheaf gluing condition. -/
theorem coverComponents_isIntervalCosheaf : IsIntervalCosheaf.{w} (coverComponents f U) := by
  intro κ K J hJ
  let F := coverComponents f U
  let lift (c : CategoryTheory.Limits.Cocone
      (CategoryTheory.Pairwise.diagram K ⋙ F)) : F.obj J → c.pt :=
    (coverComponents_existsUnique_glue f U K
      (fun k => c.ι.app (.single k)) (fun k l e => by
        exact (c.w_apply (CategoryTheory.Pairwise.Hom.left k l) e).trans
          (c.w_apply (CategoryTheory.Pairwise.Hom.right k l) e).symm) hJ).choose
  have hfac (c : CategoryTheory.Limits.Cocone (CategoryTheory.Pairwise.diagram K ⋙ F))
      (k : κ) (e : F.obj (K k)) :
      lift c (F.map (homOfLE (le_of_iUnion_eq hJ k)) e) = c.ι.app (.single k) e :=
    (coverComponents_existsUnique_glue f U K
      (fun k => c.ι.app (.single k)) (fun k l e => by
        exact (c.w_apply (CategoryTheory.Pairwise.Hom.left k l) e).trans
          (c.w_apply (CategoryTheory.Pairwise.Hom.right k l) e).symm) hJ).choose_spec.1 k e
  refine ⟨{ desc := fun c => TypeCat.ofHom (lift c), fac := ?_, uniq := ?_ }⟩
  · intro c o
    cases o with
    | single k =>
      ext e
      exact hfac c k e
    | pair k l =>
      ext e
      have he := hfac c k (F.map (homOfLE inf_le_left) e)
      have hw := c.w_apply (CategoryTheory.Pairwise.Hom.left k l) e
      have hmap : F.map (homOfLE (le_of_iUnion_eq hJ k))
          (F.map (homOfLE inf_le_left) e) =
          F.map (homOfLE (inf_le_left.trans (le_of_iUnion_eq hJ k))) e := by
        exact TDA.Topology.map_map_apply_of_thin F _ _ _ e
      rw [hmap] at he
      exact he.trans hw
  · intro c m hm
    have heq : (fun x => m x) = lift c := by
      apply (coverComponents_existsUnique_glue f U K
        (fun k => c.ι.app (.single k)) (fun k l e => by
          exact (c.w_apply (CategoryTheory.Pairwise.Hom.left k l) e).trans
            (c.w_apply (CategoryTheory.Pairwise.Hom.right k l) e).symm) hJ).choose_spec.2
      intro k e
      exact ConcreteCategory.congr_hom (hm (.single k)) e
    ext e
    exact congrFun heq e

end

end TDA.Mapper
