import TDA.Persistence.FinitePresentationPullback
import TDA.Persistence.RankDeflation

/-!
# Finite presentations of composite-deflation kernels

The actual kernel of a composite deflation is identified with the actual
pullback of the first deflation along the second kernel inclusion. This
comparison and the resulting finite-presentation theorem use the existing
kernel, pullback, and rank-exact deflation APIs.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open GradedFree

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
variable {L M N K O : PModule.{u,0,u} k P}
variable {ι : L ⟶ M} {π : M ⟶ N} {κ : K ⟶ N} {σ : N ⟶ O}

private noncomputable def compositeKernelPullbackInverse (π : M ⟶ N) (σ : N ⟶ O) :
    Limits.pullback π (Limits.kernel.ι σ) ⟶ Limits.kernel (π ≫ σ) :=
  Limits.kernel.lift (π ≫ σ) (Limits.pullback.fst π (Limits.kernel.ι σ)) (by
    calc
      Limits.pullback.fst π (Limits.kernel.ι σ) ≫ (π ≫ σ) =
          (Limits.pullback.fst π (Limits.kernel.ι σ) ≫ π) ≫ σ := by
            rw [← Category.assoc]
      _ = (Limits.pullback.snd π (Limits.kernel.ι σ) ≫ Limits.kernel.ι σ) ≫ σ := by
            rw [Limits.pullback.condition]
      _ = Limits.pullback.snd π (Limits.kernel.ι σ) ≫
          (Limits.kernel.ι σ ≫ σ) := by rw [Category.assoc]
      _ = 0 := by simp)

private noncomputable def compositeKernelToSecond (π : M ⟶ N) (σ : N ⟶ O) :
    Limits.kernel (π ≫ σ) ⟶ Limits.kernel σ :=
  Limits.kernel.lift σ (Limits.kernel.ι (π ≫ σ) ≫ π) (by
    rw [Category.assoc, Limits.kernel.condition])

private noncomputable def compositeKernelPullbackForward (π : M ⟶ N) (σ : N ⟶ O) :
    Limits.kernel (π ≫ σ) ⟶ Limits.pullback π (Limits.kernel.ι σ) := by
  let hcompat : Limits.kernel.ι (π ≫ σ) ≫ π =
      compositeKernelToSecond π σ ≫ Limits.kernel.ι σ := by
    rw [compositeKernelToSecond]
    exact (Limits.kernel.lift_ι σ (Limits.kernel.ι (π ≫ σ) ≫ π) (by
      rw [Category.assoc, Limits.kernel.condition])).symm
  exact Limits.pullback.lift (Limits.kernel.ι (π ≫ σ))
    (compositeKernelToSecond π σ) hcompat

/-- The actual kernel of a composite is the pullback of the first map along the
actual kernel inclusion of the second. No exactness, finite-presentation, or
epimorphism assumptions are needed. -/
noncomputable def kernelCompIsoPullback (π : M ⟶ N) (σ : N ⟶ O) :
    Limits.kernel (π ≫ σ) ≅ Limits.pullback π (Limits.kernel.ι σ) where
  hom := compositeKernelPullbackForward π σ
  inv := compositeKernelPullbackInverse π σ
  hom_inv_id := by
    apply Limits.equalizer.hom_ext
    change (compositeKernelPullbackForward π σ ≫ compositeKernelPullbackInverse π σ) ≫
      Limits.kernel.ι (π ≫ σ) = Limits.kernel.ι (π ≫ σ)
    rw [Category.assoc, compositeKernelPullbackInverse, Limits.kernel.lift_ι,
      compositeKernelPullbackForward, Limits.pullback.lift_fst]
  inv_hom_id := by
    have hInvI : compositeKernelPullbackInverse π σ ≫ Limits.kernel.ι (π ≫ σ) =
        Limits.pullback.fst π (Limits.kernel.ι σ) := by
      rw [compositeKernelPullbackInverse, Limits.kernel.lift_ι]
    apply Limits.pullback.hom_ext
    · change (compositeKernelPullbackInverse π σ ≫ compositeKernelPullbackForward π σ) ≫
        Limits.pullback.fst π (Limits.kernel.ι σ) = Limits.pullback.fst π (Limits.kernel.ι σ)
      rw [Category.assoc, compositeKernelPullbackForward, Limits.pullback.lift_fst,
        compositeKernelPullbackInverse, Limits.kernel.lift_ι]
    · apply (cancel_mono (Limits.kernel.ι σ)).1
      simp only [Category.assoc]
      calc
        compositeKernelPullbackInverse π σ ≫ compositeKernelPullbackForward π σ ≫
            Limits.pullback.snd π (Limits.kernel.ι σ) ≫ Limits.kernel.ι σ
            = compositeKernelPullbackInverse π σ ≫ compositeKernelToSecond π σ ≫
                Limits.kernel.ι σ := by
                  rw [compositeKernelPullbackForward, Limits.pullback.lift_snd_assoc]
        _ = compositeKernelPullbackInverse π σ ≫ Limits.kernel.ι (π ≫ σ) ≫ π := by
              simpa only [compositeKernelToSecond] using
                congrArg (fun f => compositeKernelPullbackInverse π σ ≫ f)
                  (Limits.kernel.lift_ι σ (Limits.kernel.ι (π ≫ σ) ≫ π) (by
                    simp [Category.assoc]))
        _ = Limits.pullback.fst π (Limits.kernel.ι σ) ≫ π := by
              exact congrArg (fun f => f ≫ π) hInvI
        _ = Limits.pullback.snd π (Limits.kernel.ι σ) ≫ Limits.kernel.ι σ :=
              Limits.pullback.condition

/-- The comparison's first projection is the canonical inclusion into the
source of the composite. -/
@[reassoc (attr := simp)]
theorem kernelCompIsoPullback_hom_fst (π : M ⟶ N) (σ : N ⟶ O) :
    (kernelCompIsoPullback π σ).hom ≫ Limits.pullback.fst π (Limits.kernel.ι σ) =
      Limits.kernel.ι (π ≫ σ) := by
  change compositeKernelPullbackForward π σ ≫ Limits.pullback.fst π (Limits.kernel.ι σ) = _
  rw [compositeKernelPullbackForward, Limits.pullback.lift_fst]

/-- The comparison's second projection is the canonical factor into the
second actual kernel. -/
@[reassoc (attr := simp)]
theorem kernelCompIsoPullback_hom_snd (π : M ⟶ N) (σ : N ⟶ O) :
    (kernelCompIsoPullback π σ).hom ≫ Limits.pullback.snd π (Limits.kernel.ι σ) =
      Limits.kernel.lift σ (Limits.kernel.ι (π ≫ σ) ≫ π) (by simp [Category.assoc]) := by
  change compositeKernelPullbackForward π σ ≫ Limits.pullback.snd π (Limits.kernel.ι σ) = _
  rw [compositeKernelPullbackForward, Limits.pullback.lift_snd, compositeKernelToSecond]

/-- The inverse comparison followed by the composite-kernel inclusion is the
first pullback projection. -/
@[reassoc (attr := simp)]
theorem kernelCompIsoPullback_inv_ι (π : M ⟶ N) (σ : N ⟶ O) :
    (kernelCompIsoPullback π σ).inv ≫ Limits.kernel.ι (π ≫ σ) =
      Limits.pullback.fst π (Limits.kernel.ι σ) := by
  change compositeKernelPullbackInverse π σ ≫ Limits.kernel.ι (π ≫ σ) = _
  rw [compositeKernelPullbackInverse, Limits.kernel.lift_ι]

/-- Composites of rank-exact deflations have finitely presented actual kernels
when the original left terms in the two supplied rows are finitely presented.
The canonical actual kernel row is rank exact. -/
theorem IsRankExact.comp_finitelyPresented
    (hsπ : IsRankExact ι π) (hsσ : IsRankExact κ σ)
    (hL : FinitelyPresented.{u,0,0} (R := k) (P := P) L)
    (hK : FinitelyPresented.{u,0,0} (R := k) (P := P) K) :
    FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.kernel (π ≫ σ)) ∧
      IsRankExact (Limits.kernel.ι (π ≫ σ)) (π ≫ σ) := by
  have hKernelσ : FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.kernel σ) :=
    finitelyPresented_of_iso hK hsσ.toIsPointwiseShortExact.kernelIso
  have hPullback :
      FinitelyPresented.{u,0,0} (R := k) (P := P)
        (Limits.pullback π (Limits.kernel.ι σ)) :=
    hsπ.toIsPointwiseShortExact.finitelyPresented_pullback
      (Limits.kernel.ι σ) hL hKernelσ
  have hCompositeKernel :
      FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.kernel (π ≫ σ)) :=
    finitelyPresented_of_iso hPullback (kernelCompIsoPullback π σ).symm
  exact ⟨hCompositeKernel,
    (hsπ.isRankDeflation.comp hsσ.isRankDeflation).rankExact_kernel⟩

end TDA.Persistence
