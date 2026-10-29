import TDA.Persistence.RankExactKernel
import TDA.Persistence.RankDeflation
import TDA.Persistence.CoordinateInterleaving
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# One-step persistent Schanuel

The crossed pullbacks of two covers inherit an actual interleaving from
their quotients. Rank-exact pullback closure and relative projectivity
then split their projections. Kernel comparisons identify the resulting
summands with the original terms of the two rank-exact sequences.

This is the rank-exact specialization of BOOS, arXiv:2208.00300v3,
Appendix A Lemma A.1. Finite resolutions and their length estimates are
separate inputs to the later resolution theorem.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RankSchanuel

open CategoryTheory CategoryTheory.Limits CoordinateShift
open scoped TDA.Persistence NNReal

section Ring

variable {R : Type u} [Ring R] {n : ℕ} {ε : ℝ≥0}
    {M N P Q : PModule.{u,0,u} R (Fin n → ℝ)}
    (α : P ⟶ M) (β : Q ⟶ N) (i : CoordinateInterleaving ε M N)

/-- The first crossed pullback has a projection to the first cover. -/
noncomputable abbrev leftPullback : PModule.{u,0,u} R (Fin n → ℝ) :=
  pullback ((shift ε).map β) (α ≫ i.φ)

/-- The symmetric crossed pullback has a projection to the second cover. -/
noncomputable abbrev rightPullback : PModule.{u,0,u} R (Fin n → ℝ) :=
  leftPullback β α i.symm

private theorem app_naturality {A B : PModule.{u,0,u} R (Fin n → ℝ)}
    (η : A ⟶ B) {a b : Fin n → ℝ} (hab : a ≤ b) (x : A.obj a) :
    (η.app b).hom (structureMapLinear A hab x) =
      structureMapLinear B hab ((η.app a).hom x) :=
  congrArg (fun f => f.hom x) (η.naturality (homOfLE hab))

private theorem structure_square (A : PModule.{u,0,u} R (Fin n → ℝ))
    {a b c d : Fin n → ℝ} (hab : a ≤ b) (hbd : b ≤ d)
    (hac : a ≤ c) (hcd : c ≤ d) (x : A.obj a) :
    structureMapLinear A hbd (structureMapLinear A hab x) =
      structureMapLinear A hcd (structureMapLinear A hac x) := by
  rw [← LinearMap.comp_apply, ← structureMapLinear_comp,
    ← LinearMap.comp_apply, ← structureMapLinear_comp]

private noncomputable def forwardFirst (a : Fin n → ℝ) :
    (leftPullback α β i).obj a →ₗ[R] P.obj (translation ε (translation ε a)) :=
  (structureMapLinear P (CoordinateInterleaving.twice_le ε a)).comp
    ((pullback.snd ((shift ε).map β) (α ≫ i.φ)).app a).hom

private noncomputable def forwardSecond (a : Fin n → ℝ) :
    (leftPullback α β i).obj a →ₗ[R] Q.obj (translation ε a) :=
  ((pullback.fst ((shift ε).map β) (α ≫ i.φ)).app a).hom

private theorem forward_condition (a : Fin n → ℝ) (x : (leftPullback α β i).obj a) :
    (((shift ε).map α).app (translation ε a)).hom (forwardFirst α β i a x) =
      ((β ≫ i.ψ).app (translation ε a)).hom (forwardSecond α β i a x) := by
  let p := ((pullback.snd ((shift ε).map β) (α ≫ i.φ)).app a).hom x
  have hc := congrArg (fun f : leftPullback α β i ⟶ (shift ε).obj N => (f.app a).hom x)
    (pullback.condition (f := (shift ε).map β) (g := α ≫ i.φ))
  change (β.app (translation ε a)).hom (forwardSecond α β i a x) =
    (i.φ.app a).hom ((α.app a).hom p) at hc
  have hi := congrArg (fun f => f.hom ((α.app a).hom p)) (i.φ_ψ_structureMap a)
  change (i.ψ.app (translation ε a)).hom ((i.φ.app a).hom ((α.app a).hom p)) =
    structureMapLinear M (CoordinateInterleaving.twice_le ε a) ((α.app a).hom p) at hi
  change (α.app (translation ε (translation ε a))).hom
      (structureMapLinear P (CoordinateInterleaving.twice_le ε a) p) =
    (i.ψ.app (translation ε a)).hom
      ((β.app (translation ε a)).hom (forwardSecond α β i a x))
  exact (app_naturality α (CoordinateInterleaving.twice_le ε a) p).trans
    (hi.symm.trans (congrArg (i.ψ.app (translation ε a)).hom hc.symm))

private noncomputable def forwardLinear (a : Fin n → ℝ) :
    (leftPullback α β i).obj a →ₗ[R] (rightPullback α β i).obj (translation ε a) :=
  PullbackFiber.liftLinear ((shift ε).map α) (β ≫ i.ψ) (translation ε a)
    (forwardFirst α β i a) (forwardSecond α β i a) (forward_condition α β i a)

private theorem forwardLinear_fst (a : Fin n → ℝ) (x : (leftPullback α β i).obj a) :
    ((pullback.fst ((shift ε).map α) (β ≫ i.ψ)).app (translation ε a)).hom
      (forwardLinear α β i a x) = forwardFirst α β i a x :=
  PullbackFiber.fst_liftLinear ((shift ε).map α) (β ≫ i.ψ) (translation ε a)
    (forwardFirst α β i a) (forwardSecond α β i a) (forward_condition α β i a) x

private theorem forwardLinear_snd (a : Fin n → ℝ) (x : (leftPullback α β i).obj a) :
    ((pullback.snd ((shift ε).map α) (β ≫ i.ψ)).app (translation ε a)).hom
      (forwardLinear α β i a x) = forwardSecond α β i a x :=
  PullbackFiber.snd_liftLinear ((shift ε).map α) (β ≫ i.ψ) (translation ε a)
    (forwardFirst α β i a) (forwardSecond α β i a) (forward_condition α β i a) x

/-- The actual forward map transports the first cover by twice ε and retains
the already shifted second-cover coordinate. -/
noncomputable def forward : leftPullback α β i ⟶ (shift ε).obj (rightPullback α β i) where
  app a := ModuleCat.ofHom (forwardLinear α β i a)
  naturality {a b} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let hab := leOfHom f
    let ht := (translation ε).monotone hab
    change forwardLinear α β i b (structureMapLinear (leftPullback α β i) hab x) =
      structureMapLinear (rightPullback α β i) ht (forwardLinear α β i a x)
    apply PullbackFiber.element_ext ((shift ε).map α) (β ≫ i.ψ) (translation ε b)
    · have h₁ := forwardLinear_fst α β i b
        (structureMapLinear (leftPullback α β i) hab x)
      have h₂ := congrArg (structureMapLinear P (CoordinateInterleaving.twice_le ε b))
        (app_naturality (pullback.snd ((shift ε).map β) (α ≫ i.φ)) hab x)
      have h₃ := structure_square P hab (CoordinateInterleaving.twice_le ε b)
        (CoordinateInterleaving.twice_le ε a) ((translation ε).monotone ht)
        (((pullback.snd ((shift ε).map β) (α ≫ i.φ)).app a).hom x)
      have h₄ := congrArg (structureMapLinear P ((translation ε).monotone ht))
        (forwardLinear_fst α β i a x).symm
      have h₅ := (app_naturality (pullback.fst ((shift ε).map α) (β ≫ i.ψ)) ht
        (forwardLinear α β i a x)).symm
      exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
    · have h₁ := forwardLinear_snd α β i b
        (structureMapLinear (leftPullback α β i) hab x)
      have h₂ := app_naturality (pullback.fst ((shift ε).map β) (α ≫ i.φ)) hab x
      have h₃ := congrArg (structureMapLinear Q ht) (forwardLinear_snd α β i a x).symm
      have h₄ := (app_naturality (pullback.snd ((shift ε).map α) (β ≫ i.ψ)) ht
        (forwardLinear α β i a x)).symm
      exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The first output coordinate is the first cover's double transition. -/
theorem forward_fst_app (a : Fin n → ℝ) (x : (leftPullback α β i).obj a) :
    ((pullback.fst ((shift ε).map α) (β ≫ i.ψ)).app (translation ε a)).hom
      (((forward α β i).app a).hom x) =
        structureMapLinear P (CoordinateInterleaving.twice_le ε a)
          (((pullback.snd ((shift ε).map β) (α ≫ i.φ)).app a).hom x) :=
  forwardLinear_fst α β i a x

/-- The second output coordinate retains the already shifted second cover. -/
theorem forward_snd_app (a : Fin n → ℝ) (x : (leftPullback α β i).obj a) :
    ((pullback.snd ((shift ε).map α) (β ≫ i.ψ)).app (translation ε a)).hom
      (((forward α β i).app a).hom x) =
        ((pullback.fst ((shift ε).map β) (α ≫ i.φ)).app a).hom x :=
  forwardLinear_snd α β i a x

/-- The reverse crossed-pullback map is the symmetric construction. -/
noncomputable def reverse : rightPullback α β i ⟶ (shift ε).obj (leftPullback α β i) :=
  forward β α i.symm

/-- The first reverse coordinate transports the second cover by twice ε. -/
theorem reverse_fst_app (a : Fin n → ℝ) (x : (rightPullback α β i).obj a) :
    ((pullback.fst ((shift ε).map β) (α ≫ i.φ)).app (translation ε a)).hom
      (((reverse α β i).app a).hom x) =
        structureMapLinear Q (CoordinateInterleaving.twice_le ε a)
          (((pullback.snd ((shift ε).map α) (β ≫ i.ψ)).app a).hom x) :=
  forward_fst_app β α i.symm a x

/-- The second reverse coordinate retains the already shifted first cover. -/
theorem reverse_snd_app (a : Fin n → ℝ) (x : (rightPullback α β i).obj a) :
    ((pullback.snd ((shift ε).map β) (α ≫ i.φ)).app (translation ε a)).hom
      (((reverse α β i).app a).hom x) =
        ((pullback.fst ((shift ε).map α) (β ≫ i.ψ)).app a).hom x :=
  forward_snd_app β α i.symm a x

/-- The two actual crossed maps compose to the double transition. -/
theorem forward_reverse_app (a : Fin n → ℝ) :
    (forward α β i).app a ≫ (reverse α β i).app (translation ε a) =
      structureMap (leftPullback α β i) (CoordinateInterleaving.twice_le ε a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply PullbackFiber.element_ext ((shift ε).map β) (α ≫ i.φ)
    (translation ε (translation ε a))
  · have h₁ := reverse_fst_app α β i (translation ε a) (((forward α β i).app a).hom x)
    have h₂ := congrArg (structureMapLinear Q (CoordinateInterleaving.twice_le ε (translation ε a)))
      (forward_snd_app α β i a x)
    have h₃ := (app_naturality (pullback.fst ((shift ε).map β) (α ≫ i.φ))
      (CoordinateInterleaving.twice_le ε a) x).symm
    exact h₁.trans (h₂.trans h₃)
  · have h₁ := reverse_snd_app α β i (translation ε a) (((forward α β i).app a).hom x)
    have h₂ := forward_fst_app α β i a x
    have h₃ := (app_naturality (pullback.snd ((shift ε).map β) (α ≫ i.φ))
      (CoordinateInterleaving.twice_le ε a) x).symm
    exact h₁.trans (h₂.trans h₃)

/-- The symmetric composite is the other double transition. -/
theorem reverse_forward_app (a : Fin n → ℝ) :
    (reverse α β i).app a ≫ (forward α β i).app (translation ε a) =
      structureMap (rightPullback α β i) (CoordinateInterleaving.twice_le ε a) :=
  forward_reverse_app β α i.symm a

/-- Crossed pullbacks inherit an actual interleaving, before any splitting assumption. -/
noncomputable def pullbackInterleaving :
    CoordinateInterleaving ε (leftPullback α β i) (rightPullback α β i) :=
  CoordinateInterleaving.ofStructureMapEquations (forward α β i) (reverse α β i)
    (forward_reverse_app α β i) (reverse_forward_app α β i)

private instance shift_preservesZeroMorphisms (δ : ℝ≥0) :
    (shift (R := R) (n := n) δ).PreservesZeroMorphisms where
  map_zero _ _ := by
    apply NatTrans.ext
    funext a
    rfl

private instance shift_preservesKernel (δ : ℝ≥0)
    {A B : PModule.{u,0,u} R (Fin n → ℝ)} (f : A ⟶ B) :
    PreservesLimit (parallelPair f 0) (shift δ) := by
  change PreservesLimit (parallelPair f 0)
    ((Functor.whiskeringLeft (Fin n → ℝ) (Fin n → ℝ) (ModuleCat.{u} R)).obj
      (translation δ).toFunctor)
  infer_instance

private noncomputable def kernelProjectionIso :
    kernel (pullback.snd ((shift ε).map β) (α ≫ i.φ)) ≅ (shift ε).obj (kernel β) := by
  let sq : IsPullback (pullback.fst ((shift ε).map β) (α ≫ i.φ))
      (pullback.snd ((shift ε).map β) (α ≫ i.φ)) ((shift ε).map β) (α ≫ i.φ) :=
    IsPullback.of_hasPullback _ _
  let μ := kernel.map (pullback.snd ((shift ε).map β) (α ≫ i.φ)) ((shift ε).map β)
    (pullback.fst ((shift ε).map β) (α ≫ i.φ)) (α ≫ i.φ) sq.flip.w
  let : IsIso μ := isIso_kernel_map_of_isPullback sq.flip
  exact asIso μ ≪≫ (PreservesKernel.iso (shift ε) β).symm

end Ring

section Field

variable {k : Type u} [Field k] {n : ℕ} {ε : ℝ≥0}
    {M N P Q : PModule.{u,0,u} k (Fin n → ℝ)}
    (α : P ⟶ M) (β : Q ⟶ N) (i : CoordinateInterleaving ε M N)

private instance : HasBinaryBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasBinaryBiproducts.of_hasBinaryProducts

private theorem shift_deflation {A B : PModule.{u,0,u} k (Fin n → ℝ)}
    {f : A ⟶ B} (hf : IsRankDeflation f) (δ : ℝ≥0) : IsRankDeflation ((shift δ).map f) := by
  obtain ⟨K, ι, hs⟩ := hf
  exact (hs.reindex (translation δ)).isRankDeflation

private noncomputable def leftSumIso (hα : IsRankDeflation α) (hβ : IsRankDeflation β)
    (hP : IsRankProjective P) :
    leftPullback α β i ≅ P ⊞ (shift ε).obj (kernel β) := by
  let : ∀ a, FiniteDimensional k (P.obj a) := hα.rankExact_kernel.finiteDimensional
  let hs := (shift_deflation hβ ε).pullback_snd (α ≫ i.φ)
  exact hs.splitKernelIso hP ≪≫
    biprod.mapIso (kernelProjectionIso α β i) (Iso.refl P) ≪≫ biprod.braiding _ _

private noncomputable def rightSumIso (hα : IsRankDeflation α) (hβ : IsRankDeflation β)
    (hQ : IsRankProjective Q) :
    rightPullback α β i ≅ (shift ε).obj (kernel α) ⊞ Q :=
  leftSumIso β α i.symm hβ hα hQ ≪≫ biprod.braiding _ _

/-- One-step rank-exact persistent Schanuel for the actual categorical kernels.
Splittings and the crossed-pullback interleaving are constructed from the inputs. -/
noncomputable def interleaving (hα : IsRankDeflation α) (hβ : IsRankDeflation β)
    (hP : IsRankProjective P) (hQ : IsRankProjective Q) :
    CoordinateInterleaving ε (P ⊞ (shift ε).obj (kernel β))
      ((shift ε).obj (kernel α) ⊞ Q) :=
  (pullbackInterleaving α β i).congr (leftSumIso α β i hα hβ hP) (rightSumIso α β i hα hβ hQ)

/-- The rank-exact specialization of BOOS Appendix A Lemma A.1 for the
original given sequence terms, without assuming kernel identifications or sections. -/
noncomputable def interleavingOfSequences
    {K L : PModule.{u,0,u} k (Fin n → ℝ)} {ι : K ⟶ P} {κ : L ⟶ Q}
    (hα : IsRankExact ι α) (hβ : IsRankExact κ β)
    (hP : IsRankProjective P) (hQ : IsRankProjective Q) :
    CoordinateInterleaving ε (P ⊞ (shift ε).obj L) ((shift ε).obj K ⊞ Q) :=
  (interleaving α β i hα.isRankDeflation hβ.isRankDeflation hP hQ).congr
    (biprod.mapIso (Iso.refl P) ((shift ε).mapIso hβ.toIsPointwiseShortExact.kernelIso).symm)
    (biprod.mapIso ((shift ε).mapIso hα.toIsPointwiseShortExact.kernelIso).symm (Iso.refl Q))

/-- Static Schanuel is the width-zero specialization with the actual kernel terms. -/
noncomputable def kernelSumIso {A B Z : PModule.{u,0,u} k (Fin n → ℝ)}
    (f : A ⟶ Z) (g : B ⟶ Z) (hf : IsRankDeflation f) (hg : IsRankDeflation g)
    (hA : IsRankProjective A) (hB : IsRankProjective B) :
    A ⊞ kernel g ≅ kernel f ⊞ B :=
  ((interleaving f g (CoordinateInterleaving.refl 0 Z) hf hg hA hB).congr
    (biprod.mapIso (Iso.refl A) (zeroIso (kernel g)))
    (biprod.mapIso (zeroIso (kernel f)) (Iso.refl B))).toIso

end Field

end TDA.Persistence.RankSchanuel
