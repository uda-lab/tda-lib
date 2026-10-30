import TDA.Persistence.FiniteRankProjectiveResolutionKan
import TDA.Persistence.RankExactKernel
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Uniqueness of minimal rank-projective resolution terms

Certified rank-projective covers of a fixed target are unique up to an
isomorphism commuting with the quotient. Iterating that fact through the
short-exact rows identifies the terms of any two minimal finite resolutions.
Terms are compared after padding each resolution by zero modules; the raw
lengths need not agree.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
variable {M : PModule.{u,0,u} k P}

namespace IsRankProjectiveCover

/-- Transport a cover certificate along isomorphisms of its source and target.
The quotient map is conjugated by the actual isomorphisms. -/
theorem ofIso {A₀ B₀ A B : PModule.{u,0,u} k P} {π : A₀ ⟶ B₀}
    (hπ : IsRankProjectiveCover π) (eA : A₀ ≅ A) (eB : B₀ ≅ B) :
    IsRankProjectiveCover (eA.inv ≫ π ≫ eB.hom) := by
  let π' : A ⟶ B := eA.inv ≫ π ≫ eB.hom
  let eK : kernel π ≅ kernel π' :=
    kernel.mapIso π π' eA eB (by simp [π'])
  refine ⟨hπ.term_rank_projective.of_iso eA, ?_, ?_⟩
  · simpa [π', eK] using hπ.row_rank_exact.of_iso eK eA eB
  · intro u hu
    let u₀ : End A₀ := eA.hom ≫ u ≫ eA.inv
    have hu₀ : u₀ ≫ π = π := by
      apply (cancel_mono eB.hom).1
      simpa [u₀, π', Category.assoc] using congrArg (fun f => eA.hom ≫ f) hu
    haveI : IsIso u₀ := hπ.endomorphism_isIso u₀ hu₀
    have hu_eq : u = eA.inv ≫ u₀ ≫ eA.hom := by
      simp [u₀, Category.assoc]
    rw [hu_eq]
    infer_instance

/-- Postcomposing a rank-projective cover with an isomorphism of targets
preserves its cover certificate. -/
theorem postcomposeIso {A B C : PModule.{u,0,u} k P} {π : A ⟶ B}
    (hπ : IsRankProjectiveCover π) (e : B ≅ C) :
    IsRankProjectiveCover (π ≫ e.hom) := by
  simpa using hπ.ofIso (Iso.refl A) e

/-- The zero module is a rank-projective cover of itself. -/
private theorem zero_identity :
    IsRankProjectiveCover (𝟙 (0 : PModule.{u,0,u} k P)) := by
  let hsub : ∀ p, Subsingleton ((0 : PModule.{u,0,u} k P).obj p) := fun p =>
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
  letI : ∀ p, Subsingleton ((0 : PModule.{u,0,u} k P).obj p) := hsub
  let hfd : ∀ p, FiniteDimensional k ((0 : PModule.{u,0,u} k P).obj p) := by
    intro p
    infer_instance
  letI : ∀ p, FiniteDimensional k ((0 : PModule.{u,0,u} k P).obj p) := hfd
  have hzero : IsRankProjective (0 : PModule.{u,0,u} k P) := by
    intro L A B ι π hs α
    exact ⟨0, (isZero_zero _).eq_of_src _ _⟩
  exact IsRankProjectiveCover.of_identity hfd hzero

private theorem zero_map :
    IsRankProjectiveCover (0 : (0 : PModule.{u,0,u} k P) ⟶ 0) := by
  have hEq : (0 : (0 : PModule.{u,0,u} k P) ⟶ 0) = 𝟙 0 :=
    (isZero_zero _).eq_of_src _ _
  rw [hEq]
  exact IsRankProjectiveCover.zero_identity (k := k) (P := P)

end IsRankProjectiveCover

/-- The term in degree `j`, extended by zero beyond the finite resolution. -/
noncomputable def MinimalFiniteRankProjectiveResolution.termAt
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    PModule.{u,0,u} k P :=
  if h : j < R.resolution.length then R.resolution.term ⟨j, h⟩ else 0

@[simp] theorem MinimalFiniteRankProjectiveResolution.termAt_eq_zero
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) {j : ℕ}
    (h : R.resolution.length ≤ j) : R.termAt j = 0 := by
  simp [MinimalFiniteRankProjectiveResolution.termAt, Nat.not_lt.mpr h]

theorem MinimalFiniteRankProjectiveResolution.termAt_eq
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) {j : ℕ}
    (h : j < R.resolution.length) :
    R.termAt j = R.resolution.term ⟨j, h⟩ := by
  simp [MinimalFiniteRankProjectiveResolution.termAt, h]

section CoordinateTermAtComparison
variable {n : ℕ}

/-- The zero-padded term convention for a certified minimal resolution agrees
with the existing finite-resolution term convention. -/
@[simp] theorem MinimalFiniteRankProjectiveResolution.termAt_eq_resolution_termAt
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    R.termAt j = R.resolution.termAt j := by
  simp [MinimalFiniteRankProjectiveResolution.termAt,
    FiniteRankProjectiveResolution.termAt]

end CoordinateTermAtComparison

private noncomputable def MinimalFiniteRankProjectiveResolution.kernelAt
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    PModule.{u,0,u} k P :=
  if h : j ≤ R.resolution.length then R.resolution.kernel ⟨j, by omega⟩ else 0

private theorem MinimalFiniteRankProjectiveResolution.kernelAt_eq_recorded
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) {j : ℕ}
    (h : j ≤ R.resolution.length) :
    R.kernelAt j = R.resolution.kernel ⟨j, Nat.lt_succ_of_le h⟩ := by
  unfold MinimalFiniteRankProjectiveResolution.kernelAt
  rw [dif_pos h]

private theorem MinimalFiniteRankProjectiveResolution.kernelAt_eq_castSucc
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) {j : ℕ}
    (h : j < R.resolution.length) :
    R.kernelAt j = R.resolution.kernel (Fin.castSucc (⟨j, h⟩ : Fin R.resolution.length)) := by
  calc
    R.kernelAt j = R.resolution.kernel ⟨j, Nat.lt_succ_of_le (Nat.le_of_lt h)⟩ :=
      R.kernelAt_eq_recorded (Nat.le_of_lt h)
    _ = R.resolution.kernel (Fin.castSucc (⟨j, h⟩ : Fin R.resolution.length)) := by
      congr 1

private theorem MinimalFiniteRankProjectiveResolution.kernelAt_eq_last
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    R.kernelAt R.resolution.length =
      R.resolution.kernel (Fin.last R.resolution.length) := by
  calc
    R.kernelAt R.resolution.length =
        R.resolution.kernel ⟨R.resolution.length, Nat.lt_succ_of_le (Nat.le_refl _)⟩ :=
      R.kernelAt_eq_recorded (j := R.resolution.length) (Nat.le_refl _)
    _ = R.resolution.kernel (Fin.last R.resolution.length) := by
      congr 1

private noncomputable def MinimalFiniteRankProjectiveResolution.terminalTargetIso
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    (0 : PModule.{u,0,u} k P) ≅ R.kernelAt R.resolution.length :=
  R.resolution.terminal_iso.symm.trans
    (eqToIso (R.kernelAt_eq_last (M := M)).symm)

private noncomputable def MinimalFiniteRankProjectiveResolution.quotientAt
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    R.termAt j ⟶ R.kernelAt j := by
  classical
  by_cases h : j < R.resolution.length
  · let i : Fin R.resolution.length := ⟨j, h⟩
    let eT : R.resolution.term i ≅ R.termAt j :=
      (eqToIso (R.termAt_eq h)).symm
    let eK : R.resolution.kernel i.castSucc ≅ R.kernelAt j :=
      (eqToIso (R.kernelAt_eq_castSucc h)).symm
    exact eT.inv ≫ R.resolution.quotient i ≫ eK.hom
  · exact 0

private theorem MinimalFiniteRankProjectiveResolution.coverAt
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    IsRankProjectiveCover (R.quotientAt j) := by
  classical
  by_cases h : j < R.resolution.length
  · let i : Fin R.resolution.length := ⟨j, h⟩
    let eT : R.resolution.term i ≅ R.termAt j :=
      (eqToIso (R.termAt_eq h)).symm
    let eK : R.resolution.kernel i.castSucc ≅ R.kernelAt j :=
      (eqToIso (R.kernelAt_eq_castSucc h)).symm
    have hq : R.quotientAt j = eT.inv ≫ R.resolution.quotient i ≫ eK.hom := by
      unfold MinimalFiniteRankProjectiveResolution.quotientAt
      rw [dif_pos h]
    rw [hq]
    exact (R.quotient_is_cover i).ofIso eT eK
  · by_cases hj : j = R.resolution.length
    · subst j
      have hCover := (IsRankProjectiveCover.zero_identity (k := k) (P := P)).ofIso
        (Iso.refl (0 : PModule.{u,0,u} k P)) R.terminalTargetIso
      have hmap : (𝟙 (0 : PModule.{u,0,u} k P) ≫ R.terminalTargetIso.hom) =
          (0 : (0 : PModule.{u,0,u} k P) ⟶ R.kernelAt R.resolution.length) :=
        (isZero_zero _).eq_of_src _ _
      have hq : R.quotientAt R.resolution.length = 0 := by
        simp [MinimalFiniteRankProjectiveResolution.quotientAt]
      rw [hq]
      have hterm : R.termAt R.resolution.length = 0 :=
        R.termAt_eq_zero (Nat.le_refl _)
      rw [hterm]
      simpa [hmap] using hCover
    · have hlen : R.resolution.length < j := by omega
      have hq : R.quotientAt j = 0 := by
        simp [MinimalFiniteRankProjectiveResolution.quotientAt, h]
      rw [hq]
      have hterm : R.termAt j = 0 := R.termAt_eq_zero (Nat.le_of_lt hlen)
      have hkernel : R.kernelAt j = 0 := by
        simp [MinimalFiniteRankProjectiveResolution.kernelAt,
          Nat.not_le_of_gt hlen]
      rw [hterm, hkernel]
      exact IsRankProjectiveCover.zero_map (k := k) (P := P)

private theorem MinimalFiniteRankProjectiveResolution.quotientAt_eq_zero_of_length_le
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) {j : ℕ}
    (h : R.resolution.length ≤ j) : R.quotientAt j = 0 := by
  unfold MinimalFiniteRankProjectiveResolution.quotientAt
  rw [dif_neg (Nat.not_lt.mpr h)]

/-- A finite row's recorded kernel is identified with the categorical kernel
of its quotient by the actual short-exactness certificate. Beyond the final
row the zero padding uses the categorical kernel of its zero quotient. -/
private noncomputable def MinimalFiniteRankProjectiveResolution.nextKernelIso
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    R.kernelAt (j + 1) ≅ kernel (R.quotientAt j) := by
  classical
  by_cases h : j < R.resolution.length
  · let i : Fin R.resolution.length := ⟨j, h⟩
    have hnext : R.kernelAt (j + 1) = R.resolution.kernel i.succ := by
      have hle : j + 1 ≤ R.resolution.length := by omega
      have hidx : (⟨j + 1, Nat.lt_succ_of_le hle⟩ : Fin (R.resolution.length + 1)) = i.succ := by
        apply Fin.ext
        rfl
      simp [MinimalFiniteRankProjectiveResolution.kernelAt, hle, hidx]
    let eT : R.resolution.term i ≅ R.termAt j :=
      (eqToIso (R.termAt_eq h)).symm
    let eK : R.resolution.kernel i.castSucc ≅ R.kernelAt j :=
      (eqToIso (R.kernelAt_eq_castSucc h)).symm
    have hq : R.quotientAt j = eT.inv ≫ R.resolution.quotient i ≫ eK.hom := by
      unfold MinimalFiniteRankProjectiveResolution.quotientAt
      rw [dif_pos h]
    have hSquare : R.resolution.quotient i ≫ eK.hom =
        eT.hom ≫ R.quotientAt j := by
      rw [hq]
      simp
    let eMap := kernel.mapIso (R.resolution.quotient i) (R.quotientAt j) eT eK hSquare
    exact (eqToIso hnext).trans
      ((R.resolution.row_rank_exact i).toIsPointwiseShortExact.kernelIso.trans eMap)
  · have hsource : R.kernelAt (j + 1) = 0 := by
      simp [MinimalFiniteRankProjectiveResolution.kernelAt,
        Nat.not_le_of_gt (by omega : R.resolution.length < j + 1)]
    have hle : R.resolution.length ≤ j := by omega
    have hq := R.quotientAt_eq_zero_of_length_le hle
    have hterm : R.termAt j = 0 := R.termAt_eq_zero hle
    rw [hsource, hq]
    exact (eqToIso hterm).symm.trans
      (kernelZeroIsoSource (X := R.termAt j) (Y := R.kernelAt j)).symm

private structure MinimalFiniteRankProjectiveResolution.StageComparison
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) where
  termIso : R.termAt j ≅ S.termAt j
  nextKernelIso : R.kernelAt (j + 1) ≅ S.kernelAt (j + 1)

private noncomputable def MinimalFiniteRankProjectiveResolution.compareStage
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ)
    (eK : R.kernelAt j ≅ S.kernelAt j) :
    R.StageComparison S j := by
  classical
  let hR := R.coverAt j
  let hS := (S.coverAt j).postcomposeIso eK.symm
  let hExist := IsRankProjectiveCover.exists_iso_over_quotient hR hS
  let eT := Classical.choose hExist
  have hT := Classical.choose_spec hExist
  have hSquare : eT.hom ≫ S.quotientAt j = R.quotientAt j ≫ eK.hom := by
    apply (cancel_mono eK.symm.hom).1
    simpa [hS, Category.assoc] using hT
  let eKernel := kernel.mapIso (R.quotientAt j) (S.quotientAt j) eT eK hSquare.symm
  refine ⟨eT, ?_⟩
  exact (R.nextKernelIso j).trans (eKernel.trans (S.nextKernelIso j).symm)

private noncomputable def MinimalFiniteRankProjectiveResolution.kernelIsoAt
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    ∀ j : ℕ, R.kernelAt j ≅ S.kernelAt j := by
  let e0 : R.kernelAt 0 ≅ S.kernelAt 0 := by
    have hR : R.kernelAt 0 = R.resolution.kernel 0 := by
      simpa using R.kernelAt_eq_recorded (j := 0) (Nat.zero_le _)
    have hS : S.kernelAt 0 = S.resolution.kernel 0 := by
      simpa using S.kernelAt_eq_recorded (j := 0) (Nat.zero_le _)
    let eR := eqToIso hR
    let eS := eqToIso hS
    exact eR.trans ((R.resolution.initial_iso.trans S.resolution.initial_iso.symm).trans eS.symm)
  exact Nat.rec e0 (fun j e => (R.compareStage S j e).nextKernelIso)

/-- Any two minimal finite rank-projective resolutions of the same module
have isomorphic terms in every degree after zero padding. The result does not
assert equality of their raw lengths or choose a comparison isomorphism. -/
theorem MinimalFiniteRankProjectiveResolution.termAt_nonempty_iso
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    Nonempty (R.termAt j ≅ S.termAt j) := by
  exact ⟨(R.compareStage S j (R.kernelIsoAt S j)).termIso⟩

/-- The ranks of corresponding structure maps in zero-padded resolution terms
are independent of the chosen certified minimal resolution. -/
theorem MinimalFiniteRankProjectiveResolution.termAt_rank_eq
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ)
    {a b : P} (hab : a ≤ b) :
    rankOfStructureMap (R.termAt j) hab = rankOfStructureMap (S.termAt j) hab := by
  obtain ⟨e⟩ := R.termAt_nonempty_iso S j
  exact rankOfStructureMap_iso hab e

end TDA.Persistence
