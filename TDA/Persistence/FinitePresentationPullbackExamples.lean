import TDA.Persistence.FinitePresentationPullback
import TDA.Persistence.FinitePresentationKanExamples

/-!
# Consumers of finite-presentation extension and pullback closure

The examples reuse the repeated-grade presentation with its genuine relation.
They check the ordinary extension theorem and the actual pullback/kernel row
over every field, then check the empty-presentation zero case.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FinitePresentationPullbackExamples

open CategoryTheory CategoryTheory.Limits GradedFree
open scoped ZeroObject

private def emptyGenerators (P : Type) : GradedGenerators.{0,0} P where
  Carrier := Empty
  grade := Empty.elim

private theorem zero_finitelyPresented {k : Type u} [Field k] {P : Type}
    [PartialOrder P] :
    FinitelyPresented.{u,0,0} (R := k) (P := P) (0 : PModule.{u,0,u} k P) := by
  let W : GradedGenerators.{0,0} P := emptyGenerators P
  letI : Finite W.Carrier := inferInstanceAs (Finite Empty)
  have hzero : IsZero (GradedFree.module (R := k) W) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply GradedFree.hom_ext_birth W
    intro g
    exact g.elim
  exact GradedFree.finitelyPresented_of_iso (GradedFree.free_finitelyPresented W)
    hzero.isoZero

private theorem identityQuotient_rankExact
    {k : Type u} [Field k] {P : Type} [PartialOrder P]
    {M : PModule.{u,0,u} k P}
    (hM : FinitelyPresented.{u,0,0} (R := k) (P := P) M) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k P) ⟶ M) (𝟙 M) := by
  letI : ∀ p : P, FiniteDimensional k (M.obj p) :=
    fun p => GradedFree.finitelyPresented_finiteDimensional M hM p
  have hs : IsPointwiseShortExact (0 : (0 : PModule.{u,0,u} k P) ⟶ M) (𝟙 M) := by
    constructor
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p x
      exact ⟨x, rfl⟩
    · intro p
      simp
  exact hs.rankExact_of_section (𝟙 M) (by simp)

/-- The repeated-grade, genuinely related finite presentation supports the
ordinary extension theorem and the actual rank-exact pullback consumer over
every field. The resulting actual pullback has a nonzero fiber. -/
theorem arbitrary_field_repeated_extension_and_pullback
    {k : Type u} [Field k] :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (FinitePresentationKanExamples.presentation k 2).presented ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (Limits.pullback (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)) ∧
      FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (Limits.kernel (Limits.pullback.snd
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented))) ∧
      IsRankExact
        (Limits.kernel.ι (Limits.pullback.snd
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)))
        (Limits.pullback.snd
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)) ∧
      ∃ x : (Limits.pullback
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)
          (𝟙 (FinitePresentationKanExamples.presentation k 2).presented)).obj
          ((FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)),
        x ≠ 0 := by
  let D := FinitePresentationKanExamples.presentation k 2
  have hD : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) D.presented :=
    D.finitelyPresented (FinitePresentationKanExamples.presentation_finite k 2)
  have hs : IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶ D.presented)
      (𝟙 D.presented) := identityQuotient_rankExact hD
  have hMiddle := hs.toIsPointwiseShortExact.finitelyPresented_middle
    zero_finitelyPresented hD
  have hPullback := hs.pullback_finitelyPresented (𝟙 D.presented)
    zero_finitelyPresented hD
  let p := (FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)
  let x := PullbackFiber.mk (𝟙 D.presented) (𝟙 D.presented) p
    (FinitePresentationKanExamples.secondValue k 2)
    (FinitePresentationKanExamples.secondValue k 2) (by simp)
  have hx : x ≠ 0 := by
    intro h
    have he := congrArg ((Limits.pullback.fst (𝟙 D.presented) (𝟙 D.presented)).app p).hom h
    have hz : FinitePresentationKanExamples.secondValue k 2 = 0 := by
      simpa [x, PullbackFiber.fst_mk] using he
    exact FinitePresentationKanExamples.surviving_generator 2 hz
  exact ⟨hMiddle, hPullback.1, hPullback.2.1, hPullback.2.2, ⟨x, hx⟩⟩

/-- An empty generator and relation family presents zero; its actual pullback
and canonical kernel row satisfy the same closure result. -/
theorem empty_zero_pullback_finitelyPresented {k : Type u} [Field k] :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (Limits.pullback (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))) ∧
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (Limits.kernel (Limits.pullback.snd
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ))))) ∧
    IsRankExact
      (Limits.kernel.ι (Limits.pullback.snd
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))))
      (Limits.pullback.snd
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
        (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))) := by
  have hzero : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := zero_finitelyPresented
  have hs := identityQuotient_rankExact hzero
  exact hs.pullback_finitelyPresented (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))
    hzero hzero

end TDA.Persistence.FinitePresentationPullbackExamples
