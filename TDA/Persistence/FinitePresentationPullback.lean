import TDA.Persistence.FinitePresentationExtensions
import TDA.Persistence.RankDeflation
import TDA.Persistence.FinitePresentationFiniteDimensional

/-!
# Finite presentations of actual pullbacks

An ordinary pointwise short exact row gives finite presentation of the actual
pullback of maps `π : M ⟶ N` and `f : T ⟶ N` whenever its left term and `T` are
finitely presented. In the rank-exact case, the same pullback has its
canonical kernel and rank-exact kernel row.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open GradedFree

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
variable {L M N T : PModule.{u,0,u} k P}
variable {ι : L ⟶ M} {π : M ⟶ N}

/-- For `π : M ⟶ N` in a pointwise short exact row and `f : T ⟶ N`, the actual
categorical pullback is finitely presented when `L` and `T` are finitely
presented. -/
theorem IsPointwiseShortExact.finitelyPresented_pullback
    (hs : IsPointwiseShortExact ι π) (f : T ⟶ N)
    (hL : FinitelyPresented.{u,0,0} (R := k) (P := P) L)
    (hT : FinitelyPresented.{u,0,0} (R := k) (P := P) T) :
    FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.pullback π f) := by
  exact (hs.pullback_pointwise f).finitelyPresented_middle hL hT

/-- For an actual rank-exact deflation `π : M ⟶ N` and any map `f : T ⟶ N`,
the pullback has a finitely presented middle object, its actual categorical
kernel is finitely presented, and the canonical kernel row is rank exact. -/
theorem IsRankExact.pullback_finitelyPresented
    (hs : IsRankExact ι π) (f : T ⟶ N)
    (hL : FinitelyPresented.{u,0,0} (R := k) (P := P) L)
    (hT : FinitelyPresented.{u,0,0} (R := k) (P := P) T) :
    FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.pullback π f) ∧
      FinitelyPresented.{u,0,0} (R := k) (P := P)
        (Limits.kernel (Limits.pullback.snd π f)) ∧
      IsRankExact (Limits.kernel.ι (Limits.pullback.snd π f))
        (Limits.pullback.snd π f) := by
  let hsPB := hs.toIsPointwiseShortExact.pullback_pointwise f
  have hPB : FinitelyPresented.{u,0,0} (R := k) (P := P) (Limits.pullback π f) :=
    hsPB.finitelyPresented_middle hL hT
  have hKernel :
      FinitelyPresented.{u,0,0} (R := k) (P := P)
        (Limits.kernel (Limits.pullback.snd π f)) :=
    finitelyPresented_of_iso hL hsPB.kernelIso
  letI : ∀ p : P, FiniteDimensional k (T.obj p) :=
    fun p => GradedFree.finitelyPresented_finiteDimensional T hT p
  have hPBDeflation : IsRankDeflation (Limits.pullback.snd π f) :=
    hs.isRankDeflation.pullback_snd f
  exact ⟨hPB, hKernel, hPBDeflation.rankExact_kernel⟩

end TDA.Persistence
