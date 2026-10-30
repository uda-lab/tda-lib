import TDA.Persistence.RankProjective
import TDA.Persistence.RankExactIso
import TDA.Persistence.RealCoordinates
import Mathlib.Tactic

/-!
# Euler formula for finite rank-exact resolutions

For a supplied finite family of rank-exact short exact rows, the rank of each
structure map is the alternating sum of the corresponding ranks of the middle
terms. The proof uses the rank-additivity equation in every row and cancels the
successive kernel terms. Finite rank-exact projective resolutions are an
additional structured input for this row-only identity.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory
open scoped ZeroObject

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- The finrank of the image of a persistence-module structure map. On pointwise
finite-dimensional modules this is its usual rank. For an infinite-dimensional image,
Mathlib's `Module.finrank` convention gives zero, so the rank invariant interpretation
used below is in the finite-dimensional scope guaranteed by the rank-exact rows and
endpoint isomorphisms. -/
noncomputable def rankOfStructureMap (M : PModule.{u,v,u} k P) {a b : P}
    (hab : a ≤ b) : ℕ :=
  Module.finrank k (LinearMap.range (structureMapLinear M hab))

@[simp] theorem rankOfStructureMap_zero {a b : P} (hab : a ≤ b) :
    rankOfStructureMap (0 : PModule.{u,v,u} k P) hab = 0 := by
  unfold rankOfStructureMap
  have htarget : Subsingleton ((0 : PModule.{u,v,u} k P).obj b) :=
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj b)
  have hrange : Subsingleton
      (LinearMap.range (structureMapLinear (0 : PModule.{u,v,u} k P) hab)) :=
    ⟨fun x y => Subtype.ext (htarget.elim x.val y.val)⟩
  exact @Module.finrank_zero_of_subsingleton k _ _ _ _ _ hrange

/-- Natural isomorphisms preserve the ranks of corresponding structure maps. -/
theorem rankOfStructureMap_iso {M N : PModule.{u,v,u} k P} {a b : P}
    (hab : a ≤ b) (e : M ≅ N) :
    rankOfStructureMap M hab = rankOfStructureMap N hab := by
  let ea : M.obj a ≃ₗ[k] N.obj a := (e.app a).toLinearEquiv
  let eb : M.obj b ≃ₗ[k] N.obj b := (e.app b).toLinearEquiv
  have hnat : (structureMapLinear N hab).comp ea.toLinearMap =
      eb.toLinearMap.comp (structureMapLinear M hab) := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun f : M.obj a ⟶ N.obj b => f.hom x)
      (e.hom.naturality (homOfLE hab))
    change (e.app b).toLinearEquiv (structureMapLinear M hab x) =
      structureMapLinear N hab ((e.app a).toLinearEquiv x) at h
    exact h.symm
  have hrange := congrArg LinearMap.range hnat
  have hleft : LinearMap.range (eb.toLinearMap.comp (structureMapLinear M hab)) =
      Submodule.map eb.toLinearMap (LinearMap.range (structureMapLinear M hab)) :=
    LinearMap.range_comp _ _
  have hsurj : LinearMap.range ea.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr ea.surjective
  rw [LinearMap.range_comp_of_range_eq_top _ hsurj, hleft] at hrange
  calc
    rankOfStructureMap M hab =
        Module.finrank k (Submodule.map eb.toLinearMap
          (LinearMap.range (structureMapLinear M hab))) := by
      unfold rankOfStructureMap
      exact (LinearEquiv.finrank_map_eq eb _).symm
    _ = rankOfStructureMap N hab := by
      unfold rankOfStructureMap
      rw [← hrange]

/-- A finite family of actual rank-exact rows, retaining each indexed term as an occurrence.

For `i : Fin length`, the actual row is
`0 → kernel (i.succ) → term i → kernel (i.castSucc) → 0`.
The endpoint isomorphisms identify `kernel 0` with the resolved module and the
last kernel with zero. -/
structure FiniteRankExactResolution (M : PModule.{u,v,u} k P) where
  length : ℕ
  kernel : Fin (length + 1) → PModule.{u,v,u} k P
  term : Fin length → PModule.{u,v,u} k P
  inclusion : ∀ i, kernel i.succ ⟶ term i
  quotient : ∀ i, term i ⟶ kernel i.castSucc
  row_rank_exact : ∀ i, IsRankExact (inclusion i) (quotient i)
  initial_iso : kernel 0 ≅ M
  terminal_iso : kernel (Fin.last length) ≅ 0

/-! A projective resolution adds projectivity of each indexed middle term. The existing
`IsRankProjective` API is formulated for partial orders on a universe-zero index type. -/
structure FiniteRankProjectiveResolution {P : Type} [PartialOrder P]
    (M : PModule.{u,0,u} k P) extends FiniteRankExactResolution M where
  term_rank_projective : ∀ i, IsRankProjective (term i)

namespace FiniteRankExactResolution

variable {M : PModule.{u,v,u} k P}

private theorem alternatingRowSum :
    ∀ (m : ℕ) (r : Fin (m + 1) → ℤ) (q : Fin m → ℤ),
      (∀ i, q i = r i.succ + r i.castSucc) →
      (∑ i : Fin m, (-1 : ℤ) ^ i.val * q i) =
        r 0 - (-1 : ℤ) ^ m * r (Fin.last m) := by
  intro m
  induction m with
  | zero =>
      intro r q _
      simp
  | succ m ih =>
      intro r q hrow
      let r' : Fin (m + 1) → ℤ := fun i => r i.succ
      let q' : Fin m → ℤ := fun i => q i.succ
      have hrow' : ∀ i, q' i = r' i.succ + r' i.castSucc := by
        intro i
        dsimp [q', r']
        simpa using hrow i.succ
      have htail := ih r' q' hrow'
      have hsign :
          (∑ i : Fin m, (-1 : ℤ) ^ i.succ.val * q i.succ) =
            -(∑ i : Fin m, (-1 : ℤ) ^ i.val * q' i) := by
        calc
          _ = ∑ i : Fin m, -((-1 : ℤ) ^ i.val * q' i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [q', Fin.val_succ, pow_succ, mul_comm]
          _ = _ := by rw [Finset.sum_neg_distrib]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul]
      rw [hrow 0, hsign, htail]
      simp [r', Fin.castSucc_zero, Fin.succ_last, pow_succ, mul_comm]
      ring

/-- For every `a ≤ b`, the module rank is the integer alternating sum of the indexed
middle-term ranks. The equality follows by applying `IsRankExact.rank_add` to every actual
row and telescoping the kernel ranks. -/
theorem rank_eq_alternating_sum (R : FiniteRankExactResolution M)
    {a b : P} (hab : a ≤ b) :
    (rankOfStructureMap M hab : ℤ) =
      ∑ i : Fin R.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (R.term i) hab : ℤ) := by
  let r : Fin (R.length + 1) → ℤ := fun i =>
    (rankOfStructureMap (R.kernel i) hab : ℤ)
  let q : Fin R.length → ℤ := fun i =>
    (rankOfStructureMap (R.term i) hab : ℤ)
  have hrow : ∀ i, q i = r i.succ + r i.castSucc := by
    intro i
    dsimp [q, r, rankOfStructureMap]
    exact_mod_cast (R.row_rank_exact i).rank_add hab
  have hsum := alternatingRowSum R.length r q hrow
  have hstart : r 0 = (rankOfStructureMap M hab : ℤ) := by
    dsimp [r]
    exact_mod_cast rankOfStructureMap_iso hab R.initial_iso
  have hfinish : r (Fin.last R.length) = 0 := by
    dsimp [r]
    rw [rankOfStructureMap_iso hab R.terminal_iso]
    simp
  rw [hstart, hfinish] at hsum
  simp only [mul_zero, sub_zero] at hsum
  exact hsum.symm

end FiniteRankExactResolution

namespace FiniteRankProjectiveResolution

variable {P : Type} [PartialOrder P] {M : PModule.{u,0,u} k P}

/-- The Euler formula for a finite rank-exact projective resolution. -/
theorem rank_eq_alternating_sum (R : FiniteRankProjectiveResolution M)
    {a b : P} (hab : a ≤ b) :
    (rankOfStructureMap M hab : ℤ) =
      ∑ i : Fin R.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (R.term i) hab : ℤ) :=
  FiniteRankExactResolution.rank_eq_alternating_sum
    R.toFiniteRankExactResolution hab

end FiniteRankProjectiveResolution

section RealCoordinateOperations

open CategoryTheory.Limits
open scoped TDA.Persistence
variable {n : ℕ}

private theorem zero_isRankProjective :
    IsRankProjective (0 : PModule.{u,0,u} k (Fin n → ℝ)) := by
  intro L M N ι π hs α
  exact ⟨0, (isZero_zero _).eq_of_src _ _⟩

private theorem zeroTargetRow_rankExact {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (e : M ≅ 0) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ M) := by
  have hsub (p : Fin n → ℝ) : Subsingleton (M.obj p) := by
    refine ⟨fun x y => ?_⟩
    apply (ModuleCat.mono_iff_injective (e.hom.app p)).mp inferInstance
    exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
  refine {
    toIsPointwiseShortExact := {
      injective := fun p => by
        intro x y _
        letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
        exact Subsingleton.elim _ _
      surjective := fun p y => ⟨0, (hsub p).elim _ _⟩
      range_eq_ker := fun p => by
        letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
        ext x
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        simp
    }
    finiteDimensional := fun p => by
      letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
        ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
      letI : Finite ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) := Finite.of_subsingleton
      infer_instance
    rank_add := ?_
  }
  intro a b hab
  have hrange : Subsingleton
      (LinearMap.range (structureMapLinear M hab)) :=
    ⟨fun x y => Subtype.ext ((hsub b).elim x.val y.val)⟩
  letI := hrange
  have hrank : Module.finrank k (LinearMap.range (structureMapLinear M hab)) = 0 :=
    Module.finrank_zero_of_subsingleton
  change rankOfStructureMap (0 : PModule.{u,0,u} k (Fin n → ℝ)) hab =
    rankOfStructureMap (0 : PModule.{u,0,u} k (Fin n → ℝ)) hab +
      rankOfStructureMap M hab
  simp only [rankOfStructureMap_zero]
  change 0 = 0 + Module.finrank k (LinearMap.range (structureMapLinear M hab))
  rw [hrank]

private theorem projectiveIdentityRow
    (P : PModule.{u,0,u} k (Fin n → ℝ))
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ P) (𝟙 P) := by
  letI : ∀ p, FiniteDimensional k (P.obj p) := hfd
  have hs : IsPointwiseShortExact
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ P) (𝟙 P) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p y
      exact ⟨y, by simp⟩
    · intro p
      ext x
      simp
  exact hs.rankExact_of_section (𝟙 P) (by simp)

/-- The length-one identity resolution of a rank-projective module with
pointwise finite-dimensional fibers. -/
noncomputable def FiniteRankProjectiveResolution.identity
    (P : PModule.{u,0,u} k (Fin n → ℝ)) (hP : IsRankProjective P)
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) :
    FiniteRankProjectiveResolution P := by
  let kernel : Fin 2 → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun _ => P)
  have h0 : kernel (0 : Fin 2) = P := by
    change Fin.lastCases (0 : PModule.{u,0,u} k (Fin n → ℝ))
        (fun _ : Fin 1 => P) ((0 : Fin 1).castSucc) = P
    rw [Fin.lastCases_castSucc]
  have hlast : kernel (Fin.last 1) =
      (0 : PModule.{u,0,u} k (Fin n → ℝ)) := by
    change @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
        (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P) (Fin.last 1) = 0
    rw [Fin.lastCases_last]
  refine {
    toFiniteRankExactResolution := {
      length := 1
      kernel := kernel
      term := fun _ => P
      inclusion := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        change @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
            (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P) (Fin.last 1) ⟶ P
        rw [Fin.lastCases_last]
        exact 0
      quotient := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        change P ⟶ @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
            (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P)
            ((0 : Fin 1).castSucc)
        rw [Fin.lastCases_castSucc]
        exact 𝟙 P
      row_rank_exact := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        exact projectiveIdentityRow P hfd
      initial_iso := eqToIso h0
      terminal_iso := (eqToIso hlast) ≪≫ Iso.refl _
    }
    term_rank_projective := fun _ => hP
  }

/-- Append one zero projective term to an actual finite resolution.  The old
rows are transported along the canonical finite-index equalities, and the new
last row is rank exact because the old terminal kernel is zero. -/
noncomputable def FiniteRankProjectiveResolution.appendZero
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) : FiniteRankProjectiveResolution M := by
  let kernel : Fin (R.length + 2) → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun i => R.kernel i)
  let term : Fin (R.length + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun i => R.term i)
  let hL (i : Fin R.length) : R.kernel i.succ = kernel (i.castSucc).succ := by
    simp only [kernel, Fin.succ_castSucc, Fin.lastCases_castSucc]
  let hM (i : Fin R.length) : R.term i = term i.castSucc := by
    simp only [term, Fin.lastCases_castSucc]
  let hN (i : Fin R.length) : R.kernel i.castSucc = kernel i.castSucc.castSucc := by
    simp only [kernel, Fin.lastCases_castSucc]
  let inclusion : ∀ i, kernel i.succ ⟶ term i := fun i => Fin.lastCases
    (by simp only [kernel, term, Fin.lastCases_last, Fin.succ_last]; exact 0)
    (fun i => (eqToIso (hL i)).inv ≫ R.inclusion i ≫ (eqToIso (hM i)).hom)
    i
  let quotient : ∀ i, term i ⟶ kernel i.castSucc := fun i => Fin.lastCases
    (by
      simpa only [kernel, term, Fin.lastCases_last, Fin.lastCases_castSucc] using
        (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ R.kernel (Fin.last R.length)))
    (fun i => (eqToIso (hM i)).inv ≫ R.quotient i ≫ (eqToIso (hN i)).hom)
    i
  refine {
    toFiniteRankExactResolution := {
      length := R.length + 1
      kernel := kernel
      term := term
      inclusion := inclusion
      quotient := quotient
      row_rank_exact := ?_
      initial_iso := ?_
      terminal_iso := by simpa only [kernel, Fin.lastCases_last] using (Iso.refl 0)
    }
    term_rank_projective := ?_
  }
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · have hL : (0 : PModule.{u,0,u} k (Fin n → ℝ)) =
          kernel (Fin.last R.length).succ := by
        simp only [kernel, Fin.succ_last, Fin.lastCases_last]
      have hM : (0 : PModule.{u,0,u} k (Fin n → ℝ)) =
          term (Fin.last R.length) := by
        simp only [term, Fin.lastCases_last]
      have hN : R.kernel (Fin.last R.length) =
          kernel (Fin.last R.length).castSucc := by
        simp only [kernel, Fin.lastCases_castSucc]
      let eL := eqToIso hL
      let eM := eqToIso hM
      let eN := eqToIso hN
      have hs := (zeroTargetRow_rankExact R.terminal_iso).of_iso eL eM eN
      have hι : inclusion (Fin.last R.length) =
          eL.inv ≫ (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0) ≫ eM.hom := by
        have hsource : IsZero (kernel (Fin.last R.length).succ) :=
          IsZero.of_iso (isZero_zero _) eL.symm
        exact hsource.eq_of_src _ _
      have hπ : quotient (Fin.last R.length) =
          eM.inv ≫ (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶
            R.kernel (Fin.last R.length)) ≫ eN.hom := by
        have hsource : IsZero (term (Fin.last R.length)) :=
          IsZero.of_iso (isZero_zero _) eM.symm
        exact hsource.eq_of_src _ _
      rw [hι, hπ]
      exact hs
    · intro i
      simpa only [inclusion, quotient, Fin.lastCases_castSucc] using
        (R.row_rank_exact i).of_iso (eqToIso (hL i)) (eqToIso (hM i))
          (eqToIso (hN i))
  · have hzero : (0 : Fin (R.length + 2)) = (0 : Fin (R.length + 1)).castSucc := by
      ext
      rfl
    simpa only [kernel, hzero, Fin.lastCases_castSucc] using R.initial_iso
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · have hM : (0 : PModule.{u,0,u} k (Fin n → ℝ)) = term (Fin.last R.length) := by
        simp only [term, Fin.lastCases_last]
      exact zero_isRankProjective.of_iso (eqToIso hM)
    · intro i
      exact (R.term_rank_projective i).of_iso (eqToIso (hM i))

namespace FiniteRankProjectiveResolution

/-- Repeatedly append zero terms, preserving the resolved module and every
existing resolution row. -/
noncomputable def appendZeros {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) :
    (count : ℕ) → FiniteRankProjectiveResolution M
  | 0 => R
  | count + 1 => (appendZeros R count).appendZero

theorem appendZeros_length {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (count : ℕ) :
    (R.appendZeros count).length = R.length + count := by
  induction count with
  | zero => simp [appendZeros]
  | succ count ih =>
      simp [appendZeros, appendZero, ih, Nat.add_assoc]

/-- The degree-`j` term of a finite resolution, extended by zero after its
last indexed projective. -/
noncomputable def termAt {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (j : ℕ) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  if hj : j < R.length then R.term ⟨j, hj⟩ else 0

@[simp] theorem termAt_eq_term {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) {j : ℕ} (hj : j < R.length) :
    R.termAt j = R.term ⟨j, hj⟩ := by
  simp [termAt, hj]

@[simp] theorem termAt_eq_zero {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) {j : ℕ} (hj : R.length ≤ j) :
    R.termAt j = 0 := by
  simp [termAt, not_lt.mpr hj]

theorem termAt_appendZero {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (j : ℕ) :
    (R.appendZero).termAt j = R.termAt j := by
  by_cases hj : j < R.length
  · have hj' : j < (R.appendZero).length := by
      simp [FiniteRankProjectiveResolution.appendZero]
      omega
    rw [termAt_eq_term (R := R.appendZero) hj', termAt_eq_term (R := R) hj]
    change (Fin.lastCases (0 : PModule.{u,0,u} k (Fin n → ℝ))
      (fun i => R.term i) ⟨j, hj'⟩) = R.term ⟨j, hj⟩
    have hidx : (⟨j, hj'⟩ : Fin (R.length + 1)) = (⟨j, hj⟩ : Fin R.length).castSucc := by
      ext
      rfl
    rw [hidx, Fin.lastCases_castSucc]
  · rw [termAt_eq_zero (R := R) (Nat.le_of_not_gt hj)]
    by_cases hj' : j < (R.appendZero).length
    · have hlast : j = R.length := by
        simp [FiniteRankProjectiveResolution.appendZero] at hj'
        omega
      subst j
      rw [termAt_eq_term (R := R.appendZero) (by
        simp [FiniteRankProjectiveResolution.appendZero])]
      change @Fin.lastCases R.length
          (fun _ : Fin (R.length + 1) => PModule.{u,0,u} k (Fin n → ℝ))
          (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun i => R.term i)
          (Fin.last R.length) = 0
      simp
    · simp [termAt, hj']

theorem termAt_appendZeros {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (count j : ℕ) :
    (R.appendZeros count).termAt j = R.termAt j := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [appendZeros, termAt_appendZero, ih]

end FiniteRankProjectiveResolution


namespace FiniteRankProjectiveResolution

/-- The zero-padded terms of the selected identity resolution are the module in degree zero and zero thereafter. -/
theorem identity_termAt
    (P : PModule.{u,0,u} k (Fin n → ℝ)) (hP : IsRankProjective P)
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) (j : ℕ) :
    (FiniteRankProjectiveResolution.identity P hP hfd).termAt j =
      if j = 0 then P else 0 := by
  by_cases hj : j = 0
  · subst j
    rw [termAt_eq_term (R := FiniteRankProjectiveResolution.identity P hP hfd) (by
      simp [FiniteRankProjectiveResolution.identity])]
    rfl
  · have hjlen : (FiniteRankProjectiveResolution.identity P hP hfd).length ≤ j := by
      simp [FiniteRankProjectiveResolution.identity]
      omega
    rw [termAt_eq_zero (R := FiniteRankProjectiveResolution.identity P hP hfd) hjlen]
    simp [hj]

end FiniteRankProjectiveResolution

end RealCoordinateOperations

end TDA.Persistence
