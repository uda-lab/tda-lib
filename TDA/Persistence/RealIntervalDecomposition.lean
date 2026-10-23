import TDA.Persistence.CutDecomposition
import TDA.Persistence.AlgebraicFamilyIso
import TDA.Persistence.SupportInterval
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Pi

/-!
# Scalar interval decomposition over the reals

Choose a finite basis of each compatible-section complement in the internal cut
interval decomposition. Its basis sections give natural scalar interval summands.
Regrouping the algebraic sums gives a natural isomorphism for every pointwise
finite-dimensional real module. The chosen occurrence family may be uncountable;
finite activity at each parameter is a consequence.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealIntervalDecomposition

open CategoryTheory
open TDA.Persistence.Cut
open TDA.Persistence.CutDecomposition

variable {k : Type u} [Field k]
  (M : PModule.{u,0,u} k ℝ) [∀ t, FiniteDimensional k (M.obj t)]

/-- Every pair of cuts has order-convex support. -/
theorem support_ordConnected (l r : Cut ℝ) : (support l r).OrdConnected := by
  refine ⟨?_⟩
  intro a ha b hb x hx
  exact ⟨upper_of_le hx.1 ha.1, lower_of_le hx.2 hb.2⟩

noncomputable abbrev globalComplement (i : IntervalIndex) :=
  sectionComplement M i.val.1 i.val.2 (anchor i)

private noncomputable instance globalComplement_finiteDimensional (i : IntervalIndex) :
    FiniteDimensional k (globalComplement M i) := by
  let e := sectionComplementQuotientEquiv_real M i.val.1 i.val.2 (anchor i) (anchor i)
  exact Module.Finite.equiv e.symm

private noncomputable def globalBasis (i : IntervalIndex) :
    Module.Basis (Fin (Module.finrank k (globalComplement M i))) k
      (globalComplement M i) := by
  letI : Module.Free k (globalComplement M i) :=
    Module.Free.of_divisionRing k (globalComplement M i)
  exact Module.finBasis k (globalComplement M i)

noncomputable def cutIntervalModule (i : IntervalIndex) : PModule.{u,0,u} k ℝ :=
  SupportInterval.module (k := k) (support i.val.1 i.val.2)
    (support_ordConnected i.val.1 i.val.2)

/-- Evaluate a coherent global section in the chosen interval subfunctor,
with zero value outside its support. -/
private noncomputable def globalEval (i : IntervalIndex) (t : ℝ) :
    globalComplement M i →ₗ[k] (intervalFamily M i).obj t := by
  classical
  let e : globalComplement M i →ₗ[k] M.obj t :=
    if ht : t ∈ support i.val.1 i.val.2 then
      (intervalPlus M i.val.1 i.val.2 t).subtype.comp
        ((intervalPlusEvaluation M i.val.1 i.val.2 ⟨t, ht⟩).comp
          (globalComplement M i).subtype)
    else 0
  change globalComplement M i →ₗ[k] chosenFiber M t i
  refine e.codRestrict (chosenFiber M t i) ?_
  intro w
  by_cases ht : t ∈ support i.val.1 i.val.2
  · change e w ∈ sectionComplementFiber M i.val.1 i.val.2 (anchor i) t
    rw [sectionComplementFiber, dif_pos ht]
    refine ⟨intervalPlusEvaluation M i.val.1 i.val.2 ⟨t, ht⟩ w.val,
      ⟨w.val, w.property, rfl⟩, ?_⟩
    simp only [e, dif_pos ht, LinearMap.comp_apply]
    rfl
  · change e w ∈ sectionComplementFiber M i.val.1 i.val.2 (anchor i) t
    simp [e, ht]

omit [∀ t, FiniteDimensional k (M.obj t)] in
private theorem globalEval_val_on_support (i : IntervalIndex) (t : ℝ)
    (ht : t ∈ support i.val.1 i.val.2) (w : globalComplement M i) :
    (globalEval M i t w).val =
      (intervalPlusEvaluation M i.val.1 i.val.2 ⟨t, ht⟩ w.val).val := by
  classical
  simp [globalEval, ht]
  rfl

/-- At every supported point, evaluation from the single global complement
onto the chosen fiber is bijective. -/
private theorem globalEval_bijective_on_support (i : IntervalIndex) (t : ℝ)
    (ht : t ∈ support i.val.1 i.val.2) :
    Function.Bijective (globalEval M i t) := by
  classical
  constructor
  · intro x y hxy
    have he : intervalPlusEvaluation M i.val.1 i.val.2 ⟨t, ht⟩ x.val =
        intervalPlusEvaluation M i.val.1 i.val.2 ⟨t, ht⟩ y.val := by
      apply Subtype.ext
      have h := congrArg Subtype.val hxy
      rw [globalEval_val_on_support M i t ht x,
        globalEval_val_on_support M i t ht y] at h
      exact h
    exact (sectionComplement_quotientEvaluation_bijective_real M
      i.val.1 i.val.2 (anchor i) ⟨t, ht⟩).1
      (congrArg (intervalMinusInPlus M i.val.1 i.val.2 t).mkQ he)
  · intro x
    have hx : x.val ∈ sectionComplementFiber M i.val.1 i.val.2 (anchor i) t :=
      x.property
    simp only [sectionComplementFiber, dif_pos ht] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    obtain ⟨w, hw, hwz⟩ := hz
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    rw [globalEval_val_on_support M i t ht]
    rw [hwz]
    exact hzx

omit [∀ t, FiniteDimensional k (M.obj t)] in
private theorem globalEval_map_on_support (i : IntervalIndex)
    {p q : ℝ} (hpq : p ≤ q)
    (hp : p ∈ support i.val.1 i.val.2)
    (hq : q ∈ support i.val.1 i.val.2)
    (w : globalComplement M i) :
    structureMapLinear (intervalFamily M i) hpq (globalEval M i p w) =
      globalEval M i q w := by
  apply Subtype.ext
  change structureMapLinear M hpq (globalEval M i p w).val =
    (globalEval M i q w).val
  rw [globalEval_val_on_support M i p hp,
    globalEval_val_on_support M i q hq]
  have he := CompatibleSections.compatible
    (intervalPlusModule M i.val.1 i.val.2) w.val
    (show (⟨p, hp⟩ : support i.val.1 i.val.2) ≤ ⟨q, hq⟩ from hpq)
  have he' := congrArg Subtype.val he
  change structureMapLinear M hpq
      (intervalPlusEvaluation M i.val.1 i.val.2 ⟨p, hp⟩ w.val).val =
    (intervalPlusEvaluation M i.val.1 i.val.2 ⟨q, hq⟩ w.val).val at he'
  exact he'

/-- A scalar coefficient multiplies one basis section, then evaluates it. -/
private noncomputable def basisComponent (i : IntervalIndex)
    (a : Fin (Module.finrank k (globalComplement M i))) (t : ℝ) :
    (cutIntervalModule (k := k) i).obj t →ₗ[k] (intervalFamily M i).obj t where
  toFun x := (x.val : k) • globalEval M i t (globalBasis M i a)
  map_add' x y := by
    change ((x.val + y.val : k) • globalEval M i t (globalBasis M i a)) =
      (x.val : k) • globalEval M i t (globalBasis M i a) +
        (y.val : k) • globalEval M i t (globalBasis M i a)
    exact add_smul _ _ _
  map_smul' c x := by
    change ((c * x.val : k) • globalEval M i t (globalBasis M i a)) =
      c • ((x.val : k) • globalEval M i t (globalBasis M i a))
    exact mul_smul _ _ _

/-- Each vector of the one global basis gives a natural scalar-interval
summand map. -/
private noncomputable def basisInclusion (i : IntervalIndex)
    (a : Fin (Module.finrank k (globalComplement M i))) :
    cutIntervalModule (k := k) i ⟶ intervalFamily M i where
  app t := ModuleCat.ofHom (basisComponent M i a t)
  naturality {p q} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let hpq : p ≤ q := leOfHom f
    by_cases hq : q ∈ support i.val.1 i.val.2
    · by_cases hp : p ∈ support i.val.1 i.val.2
      · change (((structureMapLinear (cutIntervalModule (k := k) i) hpq x).val : k) •
          globalEval M i q (globalBasis M i a)) =
          structureMapLinear (intervalFamily M i) hpq
            ((x.val : k) • globalEval M i p (globalBasis M i a))
        rw [map_smul, globalEval_map_on_support M i hpq hp hq]
        congr 1
        exact by
          have h := SupportInterval.structureMap_val (k := k)
            (support i.val.1 i.val.2) (support_ordConnected i.val.1 i.val.2)
            hpq x
          convert h using 1 <;> simp [cutIntervalModule, hq]; rfl
      · have hx : x = 0 := by
          apply Subtype.ext
          exact SupportInterval.val_eq_zero (k := k)
            (support i.val.1 i.val.2) hp x
        subst x
        simp [basisComponent]
    · have hsub : Subsingleton ((intervalFamily M i).obj q) := by
        change Subsingleton (sectionComplementFiber M i.val.1 i.val.2 (anchor i) q)
        rw [sectionComplementFiber_eq_bot M i.val.1 i.val.2 (anchor i) hq]
        infer_instance
      exact @Subsingleton.elim _ hsub _ _

private noncomputable abbrev copies (i : IntervalIndex) :
    Fin (Module.finrank k (globalComplement M i)) → PModule.{u,0,u} k ℝ :=
  fun _ => cutIntervalModule (k := k) i

private noncomputable def copiesToInterval (i : IntervalIndex) :
    AlgebraicFamily.familyModule (copies M i) ⟶ intervalFamily M i :=
  AlgebraicFamily.desc (copies M i) (basisInclusion M i)

/-- A supported scalar fiber is linearly equivalent to the field. -/
private noncomputable def scalarFiberEquiv (i : IntervalIndex) (t : ℝ)
    (ht : t ∈ support i.val.1 i.val.2) :
    (cutIntervalModule (k := k) i).obj t ≃ₗ[k] k := by
  classical
  let L : (cutIntervalModule (k := k) i).obj t →ₗ[k] k :=
    (SupportInterval.fiber (k := k) (support i.val.1 i.val.2) t).subtype
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext hxy
  · intro c
    refine ⟨⟨c, ?_⟩, rfl⟩
    simp [SupportInterval.fiber, ht]

private noncomputable def globalEvalEquiv (i : IntervalIndex) (t : ℝ)
    (ht : t ∈ support i.val.1 i.val.2) :
    globalComplement M i ≃ₗ[k] (intervalFamily M i).obj t :=
  LinearEquiv.ofBijective (globalEval M i t)
    (globalEval_bijective_on_support M i t ht)

/-- At a supported point, finite scalar copies, basis coordinates, and
global-section evaluation give a fiber equivalence. -/
private noncomputable def copiesFiberEquiv (i : IntervalIndex) (t : ℝ)
    (ht : t ∈ support i.val.1 i.val.2) :
    (AlgebraicFamily.familyModule (copies M i)).obj t ≃ₗ[k]
      (intervalFamily M i).obj t := by
  classical
  let e₁ := DirectSum.linearEquivFunOnFintype k
    (Fin (Module.finrank k (globalComplement M i)))
    (fun _ => (cutIntervalModule (k := k) i).obj t)
  let e₂ := LinearEquiv.piCongrRight
    (fun _ : Fin (Module.finrank k (globalComplement M i)) =>
      scalarFiberEquiv (k := k) i t ht)
  let e₃ := (Finsupp.linearEquivFunOnFinite k k
    (Fin (Module.finrank k (globalComplement M i)))).symm
  exact e₁.trans (e₂.trans (e₃.trans
    ((globalBasis M i).repr.symm.trans (globalEvalEquiv M i t ht))))

set_option maxHeartbeats 800000 in
private theorem copiesFiberEquiv_lof (i : IntervalIndex) (t : ℝ)
    (ht : t ∈ support i.val.1 i.val.2)
    (a : Fin (Module.finrank k (globalComplement M i)))
    (x : (cutIntervalModule (k := k) i).obj t) :
    copiesFiberEquiv M i t ht
      (DirectSum.lof k _ (fun _ => (cutIntervalModule (k := k) i).obj t) a x) =
      (x.val : k) • globalEval M i t (globalBasis M i a) := by
  classical
  change globalEvalEquiv M i t ht
      ((globalBasis M i).repr.symm
        ((Finsupp.linearEquivFunOnFinite k k
          (Fin (Module.finrank k (globalComplement M i)))).symm
          ((LinearEquiv.piCongrRight
            (fun _ : Fin (Module.finrank k (globalComplement M i)) =>
              scalarFiberEquiv (k := k) i t ht))
            ((DirectSum.linearEquivFunOnFintype k _
              (fun _ => (cutIntervalModule (k := k) i).obj t))
              (DirectSum.lof k _ (fun _ => (cutIntervalModule (k := k) i).obj t) a x))))) = _
  rw [DirectSum.linearEquivFunOnFintype_lof]
  have hpi : (LinearEquiv.piCongrRight
      (fun _ : Fin (Module.finrank k (globalComplement M i)) =>
        scalarFiberEquiv (k := k) i t ht)) (Pi.single a x) =
      Pi.single a (x.val : k) := by
    funext b
    by_cases hab : a = b
    · subst b
      simp only [LinearEquiv.piCongrRight_apply, Pi.single_apply]
      change scalarFiberEquiv (k := k) i t ht x = x.val
      rfl
    · have hba : b ≠ a := Ne.symm hab
      simp only [LinearEquiv.piCongrRight_apply, Pi.single_apply, if_neg hba, map_zero]
  rw [hpi, Finsupp.linearEquivFunOnFinite_symm_single]
  simp [globalEvalEquiv]

private theorem copiesToInterval_app_supported (i : IntervalIndex) (t : ℝ)
    (ht : t ∈ support i.val.1 i.val.2) :
    ((copiesToInterval M i).app t).hom =
      (copiesFiberEquiv M i t ht).toLinearMap := by
  classical
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro x
  change (cutIntervalModule (k := k) i).obj t at x
  change DirectSum.toModule k _ ((intervalFamily M i).obj t)
      (fun j => ((basisInclusion M i j).app t).hom)
      (DirectSum.lof k _ (fun _ => (cutIntervalModule (k := k) i).obj t) a x) =
    copiesFiberEquiv M i t ht
      (DirectSum.lof k _ (fun _ => (cutIntervalModule (k := k) i).obj t) a x)
  rw [DirectSum.toModule_lof, copiesFiberEquiv_lof]
  rfl

private theorem copiesToInterval_app_bijective (i : IntervalIndex) (t : ℝ) :
    Function.Bijective ((copiesToInterval M i).app t).hom := by
  classical
  by_cases ht : t ∈ support i.val.1 i.val.2
  · rw [copiesToInterval_app_supported M i t ht]
    exact (copiesFiberEquiv M i t ht).bijective
  · have hscalar : Subsingleton ((cutIntervalModule (k := k) i).obj t) := by
      constructor
      intro x y
      apply Subtype.ext
      rw [SupportInterval.val_eq_zero (k := k)
        (support i.val.1 i.val.2) ht x,
        SupportInterval.val_eq_zero (k := k)
        (support i.val.1 i.val.2) ht y]
    have htarget : Subsingleton ((intervalFamily M i).obj t) := by
      change Subsingleton (sectionComplementFiber M i.val.1 i.val.2 (anchor i) t)
      rw [sectionComplementFiber_eq_bot M i.val.1 i.val.2 (anchor i) ht]
      infer_instance
    constructor
    · intro x y _
      apply DirectSum.ext_component k
      intro a
      exact @Subsingleton.elim _ (show Subsingleton ((copies M i a).obj t) from hscalar) _ _
    · intro y
      exact ⟨0, @Subsingleton.elim _ htarget _ _⟩

private noncomputable def copiesIso (i : IntervalIndex) :
    AlgebraicFamily.familyModule (copies M i) ≅ intervalFamily M i :=
  NatIso.ofComponents
    (fun t => (LinearEquiv.ofBijective (((copiesToInterval M i).app t).hom)
      (copiesToInterval_app_bijective M i t)).toModuleIso)
    (fun {_ _} f => (copiesToInterval M i).naturality f)

abbrev ScalarIndex :=
  Σ i : IntervalIndex, Fin (Module.finrank k (globalComplement M i))

noncomputable abbrev scalarFamily (j : ScalarIndex M) : PModule.{u,0,u} k ℝ :=
  cutIntervalModule (k := k) j.1


def scalarSupport (j : ScalarIndex M) : Set ℝ :=
  support j.1.val.1 j.1.val.2

omit [∀ t, FiniteDimensional k (M.obj t)] in
theorem scalarSupport_nonempty (j : ScalarIndex M) :
    (scalarSupport M j).Nonempty :=
  j.1.property

omit [∀ t, FiniteDimensional k (M.obj t)] in
theorem scalarSupport_ordConnected (j : ScalarIndex M) :
    (scalarSupport M j).OrdConnected :=
  support_ordConnected j.1.val.1 j.1.val.2

omit [∀ t, FiniteDimensional k (M.obj t)] in
theorem scalarFiber_nontrivial_iff (j : ScalarIndex M) (t : ℝ) :
    Nontrivial ((scalarFamily M j).obj t) ↔ t ∈ scalarSupport M j := by
  classical
  by_cases ht : t ∈ scalarSupport M j
  · constructor
    · intro _; exact ht
    · intro _
      change Nontrivial (SupportInterval.fiber (k := k) (scalarSupport M j) t)
      refine ⟨⟨0, by simp [SupportInterval.fiber, ht]⟩,
        ⟨1, by simp [SupportInterval.fiber, ht]⟩, ?_⟩
      intro h
      exact zero_ne_one (congrArg Subtype.val h)
  · constructor
    · intro hn
      have hsub : Subsingleton ((scalarFamily M j).obj t) := by
        constructor
        intro x y
        apply Subtype.ext
        rw [SupportInterval.val_eq_zero (k := k)
          (scalarSupport M j) ht x,
          SupportInterval.val_eq_zero (k := k)
          (scalarSupport M j) ht y]
      exact False.elim (not_nontrivial ((scalarFamily M j).obj t) hn)
    · intro h; exact (ht h).elim


/-- Scalar interval decomposition, indexed by a dependent sum of all
nonempty cut intervals and basis coordinates of their global complements. -/
noncomputable def scalarIso :
    AlgebraicFamily.familyModule (scalarFamily M) ≅ M :=
  (AlgebraicFamily.sigmaIso (scalarFamily M)).trans
    ((AlgebraicFamily.familyIso
      (fun i : IntervalIndex => AlgebraicFamily.familyModule (copies M i))
      (intervalFamily M) (copiesIso M)).trans (sumIso M))

/-- Pointwise finite dimension forces only finitely many scalar occurrences
through each parameter. -/
theorem scalar_finite_active (t : ℝ) :
    Set.Finite {j : ScalarIndex M | t ∈ scalarSupport M j} := by
  have h := AlgebraicFamily.finite_nontrivial_of_iso
    (scalarFamily M) (scalarIso M).symm
    (fun t => inferInstance) t
  have heq : {j : ScalarIndex M | t ∈ scalarSupport M j} =
      {j : ScalarIndex M | Nontrivial ((scalarFamily M j).obj t)} := by
    ext j
    exact (scalarFiber_nontrivial_iff M j t).symm
  rwa [heq]


/-- Every pointwise finite-dimensional real persistence module admits an
algebraic interval decomposition with finite activity at every parameter. -/
theorem exists_interval_decomposition :
    ∃ (J : Type) (I : J → Set ℝ) (hI : ∀ j, (I j).OrdConnected),
      (∀ j, (I j).Nonempty) ∧
      Nonempty (M ≅ AlgebraicFamily.familyModule
        (fun j => SupportInterval.module (k := k) (I j) (hI j))) ∧
      ∀ t, Set.Finite {j | t ∈ I j} := by
  exact ⟨ScalarIndex M, scalarSupport M, scalarSupport_ordConnected M,
    scalarSupport_nonempty M, ⟨(scalarIso M).symm⟩, scalar_finite_active M⟩

end TDA.Persistence.RealIntervalDecomposition
