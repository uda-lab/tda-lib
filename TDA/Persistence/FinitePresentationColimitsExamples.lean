import TDA.Persistence.FinitePresentationPushout
import TDA.Persistence.FinitePresentationRedundant
import TDA.Persistence.FinitePresentationKanExamples

/-!
# Consumers of finite-presentation colimit closure

These examples use the existing repeated-grade presentation with a genuine
relation, add a redundant generator and relation, and apply the colimit
theorems to actual categorical objects. The cokernel theorem is applied to the
nonzero relation map between free modules born at grades `0` and `2` (distinct for `n > 0`),
and also to zero sources. The rank-exact consumer works over an arbitrary field with finite
presentation-index universes.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FinitePresentationColimitsExamples

open CategoryTheory CategoryTheory.Limits GradedFree
open scoped ZeroObject

private def emptyGenerators (P : Type) : GradedGenerators.{0,0} P where
  Carrier := Empty
  grade := Empty.elim

private theorem zero_finitelyPresented {k : Type u} [Field k] {n : ℕ} :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ)
      (0 : PModule.{u,0,u} k (Fin n → ℝ)) := by
  let W : GradedGenerators.{0,0} (Fin n → ℝ) := emptyGenerators (Fin n → ℝ)
  letI : Finite W.Carrier := inferInstanceAs (Finite Empty)
  have hzero : IsZero (GradedFree.module (R := k) W) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply GradedFree.hom_ext_birth W
    intro g
    exact g.elim
  exact GradedFree.finitelyPresented_of_iso (GradedFree.free_finitelyPresented W)
    hzero.isoZero

private theorem repeatedPresentation_finitelyPresented
    {k : Type u} [Field k] {n : ℕ} :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ)
      (FinitePresentationKanExamples.presentation k n).presented :=
  (FinitePresentationKanExamples.presentation k n).finitelyPresented
    (FinitePresentationKanExamples.presentation_finite k n)

/-- A nonzero quotient of the repeated-grade, genuinely related example has a
finite presentation as an actual categorical cokernel. -/
theorem repeated_nonzero_quotient_cokernel_finitelyPresented
    {k : Type u} [Field k] {n : ℕ} :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ)
        (Limits.cokernel
          (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶
            (FinitePresentationKanExamples.presentation k n).presented)) ∧
      ∃ x : (Limits.cokernel
        (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶
          (FinitePresentationKanExamples.presentation k n).presented)).obj
            ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2)),
        x ≠ 0 := by
  let D := FinitePresentationKanExamples.presentation k n
  let e : Limits.cokernel (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ D.presented) ≅
      D.presented := Limits.cokernelZeroIsoTarget
  refine ⟨GradedFree.finitelyPresented_cokernel
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ D.presented)
      zero_finitelyPresented (repeatedPresentation_finitelyPresented), ?_⟩
  refine ⟨(e.inv.app ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2))).hom
      (FinitePresentationKanExamples.secondValue k n), ?_⟩
  intro hx
  have hv : (e.hom.app ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2))).hom
      ((e.inv.app ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2))).hom
        (FinitePresentationKanExamples.secondValue k n)) = 0 := by
    rw [hx, map_zero]
  have hzero : FinitePresentationKanExamples.secondValue k n = 0 := by
    simpa using hv
  exact FinitePresentationKanExamples.surviving_generator n hzero

/-- The actual cokernel of the nonzero relation map, from the free module on
the relation born at grade two to the free module on two generators born at
grade zero, is finitely presented and keeps a nonzero vector at grade zero. -/
theorem relation_cokernel_finitelyPresented {k : Type u} [Field k] {n : ℕ} :
    (FinitePresentationKanExamples.presentation k n).relationMap ≠ 0 ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ)
        (Limits.cokernel (FinitePresentationKanExamples.presentation k n).relationMap) ∧
      ∃ x : (Limits.cokernel (FinitePresentationKanExamples.presentation k n).relationMap).obj
          ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2)),
        x ≠ 0 :=
  ⟨FinitePresentationKanExamples.relation_nonzero k n,
    GradedFree.finitelyPresented_cokernel
      (FinitePresentationKanExamples.presentation k n).relationMap
      (GradedFree.free_finitelyPresented (FinitePresentationKanExamples.relations n))
      (GradedFree.free_finitelyPresented (FinitePresentationKanExamples.generators n)),
    ⟨FinitePresentationKanExamples.secondValue k n,
      FinitePresentationKanExamples.surviving_generator n⟩⟩

private abbrev redundantGenerators (n : ℕ) : GradedGenerators (Fin n → ℝ) where
  Carrier := Unit
  grade _ := (FinitePresentationKanExamples.generators n).grade (0 : Fin 2)

/-- Repeated births and redundant relations remain separate finite occurrences
in the explicit presentation after the redundant-generator construction. -/
theorem repeated_redundant_presentation_finitelyPresented
    {k : Type u} [Field k] {n : ℕ} :
    let D := FinitePresentationKanExamples.presentation k n
    let E := D.adjoinRedundant (redundantGenerators n)
      (fun _ => (D.cover.app ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2))).hom
        (GradedFree.birth (FinitePresentationKanExamples.generators n) (0 : Fin 2)))
    E.IsFinite ∧ FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) E.presented := by
  dsimp only
  let D := FinitePresentationKanExamples.presentation k n
  let V := redundantGenerators n
  let E := D.adjoinRedundant V
    (fun _ => (D.cover.app ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2))).hom
      (GradedFree.birth (FinitePresentationKanExamples.generators n) (0 : Fin 2)))
  have hD : D.IsFinite := FinitePresentationKanExamples.presentation_finite k n
  have hE : E.IsFinite := D.adjoinRedundant_finite (V := V) (chosen := fun _ =>
    (D.cover.app ((FinitePresentationKanExamples.generators n).grade (0 : Fin 2))).hom
      (GradedFree.birth (FinitePresentationKanExamples.generators n) (0 : Fin 2))) hD
  exact ⟨hE, E.finitelyPresented hE⟩

/-- Empty generators and relations give the zero object, and the actual
cokernel and pushout boundary objects remain finitely presented. -/
theorem empty_zero_colimits_finitelyPresented {k : Type u} [Field k] {n : ℕ} :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ)
        (Limits.cokernel (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)) ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ)
        (Limits.pushout (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)
          (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)) := by
  exact ⟨GradedFree.finitelyPresented_cokernel (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)
      zero_finitelyPresented zero_finitelyPresented,
    GradedFree.finitelyPresented_pushout (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)
      zero_finitelyPresented zero_finitelyPresented zero_finitelyPresented⟩

private theorem identityQuotient_rankExact
    {k : Type u} [Field k] {P : Type} [PartialOrder P]
    {M : PModule.{u,0,u} k P}
    (hM : FinitelyPresented.{u,0,0} (R := k) (P := P) M) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k P) ⟶ M) (𝟙 M) := by
  letI : ∀ p : P, FiniteDimensional k (M.obj p) :=
    fun p => GradedFree.finitelyPresented_finiteDimensional M hM p
  have hs : IsPointwiseShortExact
      (0 : (0 : PModule.{u,0,u} k P) ⟶ M) (𝟙 M) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p x
      exact ⟨x, rfl⟩
    · intro p
      simp
  exact hs.rankExact_of_section (𝟙 M) (by simp)

/-- For every field, the original repeated-grade presentation supports the
actual rank-exact pushout consumer with the smallest presentation-index
universe. The resulting middle object is the actual pushout and is nonzero. -/
theorem arbitrary_field_rank_exact_pushout_finitelyPresented
    {k : Type u} [Field k] :
    let D := FinitePresentationKanExamples.presentation k 2
    let hs := identityQuotient_rankExact (repeatedPresentation_finitelyPresented (k := k) (n := 2))
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (Limits.pushout
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)) ∧
      IsRankExact (Limits.pushout.inr
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented))
        (hs.toIsPointwiseShortExact.pushoutQuotient
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)) ∧
      ∃ x : (Limits.pushout
        (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)
        (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)).obj
          ((FinitePresentationKanExamples.generators 2).grade (1 : Fin 2)),
        x ≠ 0 := by
  dsimp only
  let D := FinitePresentationKanExamples.presentation k 2
  let f : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented := 0
  have hD : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) D.presented :=
    repeatedPresentation_finitelyPresented
  have hs : IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)
      (𝟙 D.presented) := identityQuotient_rankExact hD
  have hout := hs.pushout_finitelyPresented f zero_finitelyPresented hD hD
  let p := (FinitePresentationKanExamples.generators 2).grade (1 : Fin 2)
  refine ⟨hout.1, hout.2, ?_⟩
  have hsecond : FinitePresentationKanExamples.secondValue k 2 ≠ 0 :=
    FinitePresentationKanExamples.surviving_generator 2
  refine ⟨((Limits.pushout.inr (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented) f).app p).hom
    (FinitePresentationKanExamples.secondValue k 2), ?_⟩
  intro hx
  have hx' : ((Limits.pushout.inr
      (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented) f).app p).hom
      (FinitePresentationKanExamples.secondValue k 2) =
    ((Limits.pushout.inr
      (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented) f).app p).hom 0 := by
    rw [map_zero]
    exact hx
  have hzero := hout.2.toIsPointwiseShortExact.injective p hx'
  exact hsecond hzero

end TDA.Persistence.FinitePresentationColimitsExamples
