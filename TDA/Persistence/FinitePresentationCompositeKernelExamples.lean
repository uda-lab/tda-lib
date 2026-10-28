import TDA.Persistence.FinitePresentationCompositeKernel
import TDA.Persistence.FinitePresentationKanExamples

/-!
# Consumers of composite-kernel finite-presentation closure

The examples use the repeated-grade presentation with a genuine relation over
an arbitrary field, and the empty presentation of zero. The nonzero case
checks an actual composite kernel, rather than only its isomorphism class.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FinitePresentationCompositeKernelExamples

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

private theorem rankExact_zeroQuotient
    {k : Type u} [Field k] {P : Type} [PartialOrder P]
    {M : PModule.{u,0,u} k P}
    (hM : FinitelyPresented.{u,0,0} (R := k) (P := P) M) :
    IsRankExact (𝟙 M) (0 : M ⟶ (0 : PModule.{u,0,u} k P)) := by
  letI : ∀ p : P, FiniteDimensional k (M.obj p) :=
    fun p => GradedFree.finitelyPresented_finiteDimensional M hM p
  have hs : IsPointwiseShortExact (𝟙 M) (0 : M ⟶ (0 : PModule.{u,0,u} k P)) := by
    constructor
    · intro p
      exact Function.injective_id
    · intro p x
      exact ⟨0, (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _⟩
    · intro p
      ext x
      simp
  exact hs.rankExact_of_section (0 : (0 : PModule.{u,0,u} k P) ⟶ M) (by simp)

/-- An arbitrary-field repeated-grade example has finitely presented original
left terms and a nonzero actual kernel of the composite deflation. -/
theorem arbitrary_field_nonzero_composite_kernel {k : Type u} [Field k] :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (Limits.kernel
        ((0 : (FinitePresentationKanExamples.presentation k 2).presented ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) ≫
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))))) ∧
    IsRankExact
      (Limits.kernel.ι
        ((0 : (FinitePresentationKanExamples.presentation k 2).presented ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) ≫
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))))
      ((0 : (FinitePresentationKanExamples.presentation k 2).presented ⟶
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) ≫
        (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))) ∧
    ∃ x : (Limits.kernel
        ((0 : (FinitePresentationKanExamples.presentation k 2).presented ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) ≫
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))))).obj
        ((FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)),
      x ≠ 0 := by
  let D := (FinitePresentationKanExamples.presentation k 2).presented
  let π : D ⟶ (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := 0
  let σ : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := 0
  have hD : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) D :=
    (FinitePresentationKanExamples.presentation k 2).finitelyPresented
      (FinitePresentationKanExamples.presentation_finite k 2)
  have hzero : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := zero_finitelyPresented
  have hsπ : IsRankExact (𝟙 D) π := rankExact_zeroQuotient hD
  have hsσ : IsRankExact (𝟙 (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) σ :=
    rankExact_zeroQuotient hzero
  have hresult := hsπ.comp_finitelyPresented hsσ hD hzero
  let lift : D ⟶ Limits.kernel (π ≫ σ) :=
    Limits.kernel.lift (π ≫ σ) (𝟙 D) (by simp [π, σ])
  let p := (FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)
  let x := (lift.app p).hom (FinitePresentationKanExamples.secondValue k 2)
  have hx : x ≠ 0 := by
    intro hx
    have hLift : lift ≫ Limits.kernel.ι (π ≫ σ) = 𝟙 D := by
      dsimp [lift]
      rw [Limits.kernel.lift_ι]
    have hvalue : ((Limits.kernel.ι (π ≫ σ)).app p).hom
        ((lift.app p).hom (FinitePresentationKanExamples.secondValue k 2)) =
          FinitePresentationKanExamples.secondValue k 2 := by
      have h := congrArg (fun f : D ⟶ D => (f.app p).hom
        (FinitePresentationKanExamples.secondValue k 2)) hLift
      simpa using h
    have hzeroValue : ((Limits.kernel.ι (π ≫ σ)).app p).hom
        ((lift.app p).hom (FinitePresentationKanExamples.secondValue k 2)) = 0 := by
      simpa [x] using congrArg ((Limits.kernel.ι (π ≫ σ)).app p).hom hx
    exact FinitePresentationKanExamples.surviving_generator 2 (hvalue.symm.trans hzeroValue)
  exact ⟨hresult.1, hresult.2, ⟨x, hx⟩⟩

/-- The empty zero presentation also has a finitely presented composite kernel
and its canonical rank-exact kernel row. -/
theorem empty_zero_composite_kernel_finitelyPresented {k : Type u} [Field k] :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (Limits.kernel
        ((0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) ≫
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))))) ∧
    IsRankExact
      (Limits.kernel.ι
        ((0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) ≫
          (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
            (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))))
      ((0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ))) ≫
        (0 : (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) ⟶
          (0 : PModule.{u,0,u} k (Fin 2 → ℝ)))) := by
  have hzero : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (0 : PModule.{u,0,u} k (Fin 2 → ℝ)) := zero_finitelyPresented
  let hs := rankExact_zeroQuotient hzero
  simpa using hs.comp_finitelyPresented hs hzero hzero

end TDA.Persistence.FinitePresentationCompositeKernelExamples
