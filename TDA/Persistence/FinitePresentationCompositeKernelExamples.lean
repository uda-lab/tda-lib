import TDA.Persistence.FinitePresentationCompositeKernel
import TDA.Persistence.FinitePresentationKanExamples

/-!
# Consumers of composite-kernel finite-presentation closure

The examples use the repeated-grade presentation `X` with a genuine relation
over an arbitrary field, and the empty presentation of zero. The first nonzero
case checks an actual composite kernel, rather than only its isomorphism
class, for zero deflations. The second uses the split deflations
`X ⊞ (X ⊞ X) ⟶ X ⊞ X ⟶ X`, whose rows have nonzero outer terms, and exhibits a
composite-kernel vector outside the kernel of the first deflation.
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

private instance {k : Type u} [Field k] {P : Type} [PartialOrder P] :
    HasBinaryBiproducts (PModule.{u,0,u} k P) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The canonical split row of a binary biproduct is rank exact. -/
private theorem split_rankExact {k : Type u} [Field k] {P : Type} [PartialOrder P]
    (A B : PModule.{u,0,u} k P)
    [∀ p, FiniteDimensional k (A.obj p)] [∀ p, FiniteDimensional k (B.obj p)] :
    IsRankExact (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) := by
  have h : ∀ p : P,
      ((ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) (by simp)).map
        ((evaluation P (ModuleCat.{u} k)).obj p)).ShortExact := fun p =>
    ((ShortComplex.Splitting.ofHasBinaryBiproduct A B).map
      ((evaluation P (ModuleCat.{u} k)).obj p)).shortExact
  have hs : IsPointwiseShortExact (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) :=
    ⟨fun p => (h p).moduleCat_injective_f, fun p => (h p).moduleCat_surjective_g,
      fun p => (h p).exact.moduleCat_range_eq_ker⟩
  let : ∀ p, FiniteDimensional k ((A ⊞ B).obj p) := fun p =>
    Module.Finite.of_exact (f := ((biprod.inl : A ⟶ A ⊞ B).app p).hom)
      (g := ((biprod.snd : A ⊞ B ⟶ B).app p).hom)
      (LinearMap.exact_iff.mpr (hs.range_eq_ker p).symm) (hs.surjective p)
  exact hs.rankExact_of_section biprod.inr (by simp)

/-- The repeated-grade module with a genuine relation. -/
private noncomputable abbrev presentedModule (k : Type u) [Field k] :
    PModule.{u,0,u} k (Fin 2 → ℝ) :=
  (FinitePresentationKanExamples.presentation k 2).presented

/-- The first split deflation `X ⊞ (X ⊞ X) ⟶ X ⊞ X`. -/
private noncomputable abbrev firstSplitQuotient (k : Type u) [Field k] :
    presentedModule k ⊞ (presentedModule k ⊞ presentedModule k) ⟶
      presentedModule k ⊞ presentedModule k :=
  biprod.snd

/-- The second split deflation `X ⊞ X ⟶ X`. -/
private noncomputable abbrev secondSplitQuotient (k : Type u) [Field k] :
    presentedModule k ⊞ presentedModule k ⟶ presentedModule k :=
  biprod.snd

/-- The composite-kernel theorem on two split rank-exact rows whose outer terms
are all the nonzero repeated-grade module `X`. The actual composite kernel is
finitely presented, its kernel row is rank exact, and it contains a vector at
grade zero whose image under the first deflation is nonzero. -/
theorem arbitrary_field_split_composite_kernel {k : Type u} [Field k] :
    FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
        (Limits.kernel (firstSplitQuotient k ≫ secondSplitQuotient k)) ∧
      IsRankExact (Limits.kernel.ι (firstSplitQuotient k ≫ secondSplitQuotient k))
        (firstSplitQuotient k ≫ secondSplitQuotient k) ∧
      ∃ x : (Limits.kernel (firstSplitQuotient k ≫ secondSplitQuotient k)).obj
          ((FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)),
        ((Limits.kernel.ι (firstSplitQuotient k ≫ secondSplitQuotient k) ≫
          firstSplitQuotient k).app
            ((FinitePresentationKanExamples.generators 2).grade (0 : Fin 2))).hom x ≠ 0 := by
  let X := presentedModule k
  have hX : FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ) X :=
    (FinitePresentationKanExamples.presentation k 2).finitelyPresented
      (FinitePresentationKanExamples.presentation_finite k 2)
  let : ∀ p, FiniteDimensional k (X.obj p) :=
    fun p => GradedFree.finitelyPresented_finiteDimensional X hX p
  have hsσ := split_rankExact X X
  let : ∀ p, FiniteDimensional k ((X ⊞ X).obj p) := hsσ.finiteDimensional
  have hsπ := split_rankExact X (X ⊞ X)
  have hresult := hsπ.comp_finitelyPresented hsσ hX hX
  let j : X ⟶ X ⊞ (X ⊞ X) := biprod.inl ≫ biprod.inr
  have hj : j ≫ (firstSplitQuotient k ≫ secondSplitQuotient k) = 0 := by simp [j, X]
  let lift := Limits.kernel.lift (firstSplitQuotient k ≫ secondSplitQuotient k) j hj
  let p := (FinitePresentationKanExamples.generators 2).grade (0 : Fin 2)
  refine ⟨hresult.1, hresult.2,
    (lift.app p).hom (FinitePresentationKanExamples.secondValue k 2), ?_⟩
  intro h0
  have hcomp : lift ≫ Limits.kernel.ι (firstSplitQuotient k ≫ secondSplitQuotient k) ≫
      firstSplitQuotient k ≫ biprod.fst = 𝟙 X := by
    simp [lift, j, X]
  have hv := congrArg (fun f : X ⟶ X =>
    (f.app p).hom (FinitePresentationKanExamples.secondValue k 2)) hcomp
  change ((biprod.fst : X ⊞ X ⟶ X).app p).hom
      (((Limits.kernel.ι (firstSplitQuotient k ≫ secondSplitQuotient k) ≫
        firstSplitQuotient k).app p).hom
          ((lift.app p).hom (FinitePresentationKanExamples.secondValue k 2))) =
    FinitePresentationKanExamples.secondValue k 2 at hv
  rw [h0, map_zero] at hv
  exact FinitePresentationKanExamples.surviving_generator 2 hv.symm

end TDA.Persistence.FinitePresentationCompositeKernelExamples
