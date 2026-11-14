import TDA.Persistence.RankSchanuel
import TDA.Persistence.FiniteRankProjectiveResolution
import TDA.Persistence.RankExactIso
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Persistent Schanuel for finite rank-projective resolutions

The shifted alternating-sum comparison is built from the actual rank-exact
rows in the given resolutions. Tail and coordinate-shift operations live with
the finite-resolution data; this file develops the comparison machinery.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject NNReal

variable {k : Type u} [Field k] {n : ℕ}

private noncomputable def schanuelLeftAt
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) {L : ℕ} (j : Fin L) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  (CoordinateShift.shift ((j.val : ℝ≥0) * ε)).obj
    (if Even j.val then R.termAt j.val else S.termAt j.val)

private noncomputable def schanuelRightAt
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) {L : ℕ} (j : Fin L) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  (CoordinateShift.shift ((j.val : ℝ≥0) * ε)).obj
    (if Even j.val then S.termAt j.val else R.termAt j.val)

namespace FiniteRankProjectiveResolution

/-- Degree-`j` summand in the shifted alternating resolution comparison:
even degrees use the first resolution, odd degrees the second. -/
noncomputable def schanuelLeftSummand
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (j : Fin (max R.length S.length)) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  schanuelLeftAt R S ε j

/-- Degree-`j` summand in the shifted alternating resolution comparison with
the two resolutions exchanged. -/
noncomputable def schanuelRightSummand
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (j : Fin (max R.length S.length)) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  schanuelRightAt R S ε j

/-- The finite biproduct of all shifted alternating summands, with every
resolution extended by its canonical zero terms to the common maximum length. -/
noncomputable def schanuelLeftBiproduct
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) : PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ schanuelLeftSummand R S ε

/-- The finite biproduct of the shifted alternating summands with the two
resolutions exchanged. -/
noncomputable def schanuelRightBiproduct
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) : PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ schanuelRightSummand R S ε

private noncomputable def biprodRightZeroIso
    (P : PModule.{u,0,u} k (Fin n → ℝ)) : P ⊞ 0 ≅ P where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp
    · exact (isZero_zero _).eq_of_src _ _
  inv_hom_id := by simp

private noncomputable def biprodLeftZeroIso
    (P : PModule.{u,0,u} k (Fin n → ℝ)) : 0 ⊞ P ≅ P where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · exact (isZero_zero _).eq_of_src _ _
    · simp
  inv_hom_id := by simp

/-- The one-projective-term case of persistent Schanuel.  The terminal kernels
are identified with zero by the supplied resolution structures, so the actual
one-step interleaving descends to the two degree-zero projectives. -/
noncomputable def interleaving_of_length_one
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hRlen : R.length = 1) (hSlen : S.length = 1)
    (ε : ℝ≥0) (i : CoordinateInterleaving ε M N) :
    CoordinateInterleaving ε (R.term ⟨0, by omega⟩) (S.term ⟨0, by omega⟩) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let iS : Fin S.length := ⟨0, by omega⟩
  have hRrow := (R.row_rank_exact iR).of_iso
    (Iso.refl _) (Iso.refl _) R.initial_iso
  have hSrow := (S.row_rank_exact iS).of_iso
    (Iso.refl _) (Iso.refl _) S.initial_iso
  let oneStep := RankSchanuel.interleavingOfSequences
    (α := R.quotient iR ≫ R.initial_iso.hom)
    (β := S.quotient iS ≫ S.initial_iso.hom) (i := i)
    hRrow hSrow (R.term_rank_projective iR) (S.term_rank_projective iS)
  have hRidx : iR.succ = Fin.last R.length := by
    apply Fin.ext
    simp [iR, hRlen]
  have hSidx : iS.succ = Fin.last S.length := by
    apply Fin.ext
    simp [iS, hSlen]
  let eR : R.kernel iR.succ ≅ 0 := (eqToIso (congrArg R.kernel hRidx)) ≪≫ R.terminal_iso
  let eS : S.kernel iS.succ ≅ 0 := (eqToIso (congrArg S.kernel hSidx)) ≪≫ S.terminal_iso
  let eR' : (CoordinateShift.shift ε).obj (R.kernel iR.succ) ≅ 0 :=
    (CoordinateShift.shift ε).mapIso eR ≪≫
      Functor.mapZeroObject (CoordinateShift.shift ε)
  let eS' : (CoordinateShift.shift ε).obj (S.kernel iS.succ) ≅ 0 :=
    (CoordinateShift.shift ε).mapIso eS ≪≫
      Functor.mapZeroObject (CoordinateShift.shift ε)
  have hRterm : R.term iR = R.term ⟨0, by omega⟩ := by
    apply congrArg R.term
    apply Fin.ext
    rfl
  have hSterm : S.term iS = S.term ⟨0, by omega⟩ := by
    apply congrArg S.term
    apply Fin.ext
    rfl
  exact oneStep.congr
    ((biprod.mapIso (eqToIso hRterm) eS').trans
      (biprodRightZeroIso (R.term ⟨0, by omega⟩)))
    ((biprod.mapIso eR' (eqToIso hSterm)).trans
      (biprodLeftZeroIso (S.term ⟨0, by omega⟩)))

end FiniteRankProjectiveResolution


private noncomputable def crossLeftResolution
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    FiniteRankProjectiveResolution
      ((CoordinateShift.shift ε).obj
        (R.kernel ⟨1, by omega⟩) ⊞ S.term ⟨0, by omega⟩) := by
  let iS : Fin S.length := ⟨0, by rw [← hlen]; omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idS := FiniteRankProjectiveResolution.identity (S.term iS)
    (S.term_rank_projective iS) (fun p => (S.row_rank_exact iS).finiteDimensional p)
  let paddedIdS := idS.appendZeros (R.length - 2)
  have hlen' : (tailR.shift ε).length = paddedIdS.length := by
    have htail : tailR.length = R.length - 1 :=
      FiniteRankProjectiveResolution.length_tail R (by omega)
    have hid : idS.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idS (R.length - 2)
    calc
      (tailR.shift ε).length = tailR.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idS.length + (R.length - 2) := by rw [hid]
      _ = paddedIdS.length := hpad.symm
  exact (tailR.shift ε).biprod paddedIdS hlen'

private noncomputable def crossRightResolution
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    FiniteRankProjectiveResolution
      ((CoordinateShift.shift ε).obj
        (S.kernel ⟨1, by rw [← hlen]; omega⟩) ⊞ R.term ⟨0, by omega⟩) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idR := FiniteRankProjectiveResolution.identity (R.term iR)
    (R.term_rank_projective iR) (fun p => (R.row_rank_exact iR).finiteDimensional p)
  let paddedIdR := idR.appendZeros (R.length - 2)
  have hlen' : (tailS.shift ε).length = paddedIdR.length := by
    have htail : tailS.length = R.length - 1 := by
      calc
        tailS.length = S.length - 1 :=
          FiniteRankProjectiveResolution.length_tail S (by rw [← hlen]; omega)
        _ = R.length - 1 := by rw [hlen]
    have hid : idR.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idR (R.length - 2)
    calc
      (tailS.shift ε).length = tailS.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idR.length + (R.length - 2) := by rw [hid]
      _ = paddedIdR.length := hpad.symm
  exact (tailS.shift ε).biprod paddedIdR hlen'

private noncomputable def crossLeftTermAtIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (j : ℕ) :
    (crossLeftResolution R S hlen hpos ε).termAt j ≅
      (CoordinateShift.shift ε).obj (R.termAt (j + 1)) ⊞
        (if j = 0 then S.termAt 0 else 0) := by
  let iS : Fin S.length := ⟨0, by rw [← hlen]; omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idS := FiniteRankProjectiveResolution.identity (S.term iS)
    (S.term_rank_projective iS) (fun p => (S.row_rank_exact iS).finiteDimensional p)
  let paddedIdS := idS.appendZeros (R.length - 2)
  have hlen' : (tailR.shift ε).length = paddedIdS.length := by
    have htail : tailR.length = R.length - 1 :=
      FiniteRankProjectiveResolution.length_tail R (by omega)
    have hid : idS.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idS (R.length - 2)
    calc
      (tailR.shift ε).length = tailR.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idS.length + (R.length - 2) := by rw [hid]
      _ = paddedIdS.length := hpad.symm
  have hP : S.term iS = S.termAt 0 := by
    rw [FiniteRankProjectiveResolution.termAt_eq_term (R := S) (by omega)]
  have htail : tailR.termAt j = R.termAt (j + 1) :=
    FiniteRankProjectiveResolution.termAt_tail R (by omega) j
  have hid : idS.termAt j = if j = 0 then S.term iS else 0 :=
    FiniteRankProjectiveResolution.identity_termAt (S.term iS)
      (S.term_rank_projective iS)
      (fun p => (S.row_rank_exact iS).finiteDimensional p) j
  have htarget : (if j = 0 then S.term iS else 0) =
      (if j = 0 then S.termAt 0 else 0) := by
    split_ifs <;> simp [hP]
  have hpadTerm : paddedIdS.termAt j = if j = 0 then S.termAt 0 else 0 :=
    (FiniteRankProjectiveResolution.termAt_appendZeros idS (R.length - 2) j).trans
      (hid.trans htarget)
  change ((tailR.shift ε).biprod paddedIdS hlen').termAt j ≅ _
  exact (FiniteRankProjectiveResolution.termAt_biprodIso
      (tailR.shift ε) paddedIdS hlen' j).trans
    (biprod.mapIso
      ((FiniteRankProjectiveResolution.termAt_shiftIso tailR ε j).trans
        (eqToIso (congrArg (fun X => (CoordinateShift.shift ε).obj X) htail)))
      (eqToIso hpadTerm))

private noncomputable def crossRightTermAtIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (j : ℕ) :
    (crossRightResolution R S hlen hpos ε).termAt j ≅
      (CoordinateShift.shift ε).obj (S.termAt (j + 1)) ⊞
        (if j = 0 then R.termAt 0 else 0) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let tailR := R.tail (by omega)
  let tailS := S.tail (by rw [← hlen]; omega)
  let idR := FiniteRankProjectiveResolution.identity (R.term iR)
    (R.term_rank_projective iR) (fun p => (R.row_rank_exact iR).finiteDimensional p)
  let paddedIdR := idR.appendZeros (R.length - 2)
  have hlen' : (tailS.shift ε).length = paddedIdR.length := by
    have htail : tailS.length = R.length - 1 := by
      calc
        tailS.length = S.length - 1 :=
          FiniteRankProjectiveResolution.length_tail S (by rw [← hlen]; omega)
        _ = R.length - 1 := by rw [hlen]
    have hid : idR.length = 1 := by rfl
    have hpad := FiniteRankProjectiveResolution.appendZeros_length idR (R.length - 2)
    calc
      (tailS.shift ε).length = tailS.length := rfl
      _ = R.length - 1 := htail
      _ = 1 + (R.length - 2) := by omega
      _ = idR.length + (R.length - 2) := by rw [hid]
      _ = paddedIdR.length := hpad.symm
  have hP : R.term iR = R.termAt 0 := by
    rw [FiniteRankProjectiveResolution.termAt_eq_term (R := R) (by omega)]
  have htail : tailS.termAt j = S.termAt (j + 1) :=
    FiniteRankProjectiveResolution.termAt_tail S (by rw [← hlen]; omega) j
  have hid : idR.termAt j = if j = 0 then R.term iR else 0 :=
    FiniteRankProjectiveResolution.identity_termAt (R.term iR)
      (R.term_rank_projective iR)
      (fun p => (R.row_rank_exact iR).finiteDimensional p) j
  have htarget : (if j = 0 then R.term iR else 0) =
      (if j = 0 then R.termAt 0 else 0) := by
    split_ifs <;> simp [hP]
  have hpadTerm : paddedIdR.termAt j = if j = 0 then R.termAt 0 else 0 :=
    (FiniteRankProjectiveResolution.termAt_appendZeros idR (R.length - 2) j).trans
      (hid.trans htarget)
  change ((tailS.shift ε).biprod paddedIdR hlen').termAt j ≅ _
  exact (FiniteRankProjectiveResolution.termAt_biprodIso
      (tailS.shift ε) paddedIdR hlen' j).trans
    (biprod.mapIso
      ((FiniteRankProjectiveResolution.termAt_shiftIso tailS ε j).trans
        (eqToIso (congrArg (fun X => (CoordinateShift.shift ε).obj X) htail)))
      (eqToIso hpadTerm))

private instance (δ : ℝ≥0) : (CoordinateShift.shift (R := k) (n := n) δ).Additive where
  map_add := by intros; rfl

private noncomputable def crossLeftTailTermIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0)
    (j : ℕ) (hj : 0 < j) :
    (CoordinateShift.shift ((j : ℝ≥0) * ε)).obj
        ((crossLeftResolution R S hlen hpos ε).termAt j) ≅
      (CoordinateShift.shift (((j + 1 : ℕ) : ℝ≥0) * ε)).obj
        (R.termAt (j + 1)) := by
  let θ : ℝ≥0 := (j : ℝ≥0) * ε
  let X := R.termAt (j + 1)
  have hscalar : θ + ε = (((j + 1 : ℕ) : ℝ≥0) * ε) := by
    dsimp [θ]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hterm := (CoordinateShift.shift θ).mapIso
    (crossLeftTermAtIso R S hlen hpos ε j)
  have hterm' : (CoordinateShift.shift θ).obj
      ((crossLeftResolution R S hlen hpos ε).termAt j) ≅
        (CoordinateShift.shift θ).obj ((CoordinateShift.shift ε).obj X ⊞ 0) := by
    simpa [X, Nat.ne_of_gt hj] using hterm
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct
    (CoordinateShift.shift (R := k) (n := n) θ)
    (X := (CoordinateShift.shift ε).obj X) (Y := (0 : PModule.{u,0,u} k (Fin n → ℝ)))
  exact hterm'.trans
    ((Functor.mapBiprod (CoordinateShift.shift θ) ((CoordinateShift.shift ε).obj X) 0).trans
      ((biprod.mapIso (CoordinateShift.compIso θ ε X)
        (Functor.mapZeroObject (CoordinateShift.shift θ))).trans
        ((FiniteRankProjectiveResolution.biprodRightZeroIso
          ((CoordinateShift.shift (θ + ε)).obj X)).trans
          (CoordinateShift.congrIso hscalar X))))

private noncomputable def crossRightTailTermIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0)
    (j : ℕ) (hj : 0 < j) :
    (CoordinateShift.shift ((j : ℝ≥0) * ε)).obj
        ((crossRightResolution R S hlen hpos ε).termAt j) ≅
      (CoordinateShift.shift (((j + 1 : ℕ) : ℝ≥0) * ε)).obj
        (S.termAt (j + 1)) := by
  let θ : ℝ≥0 := (j : ℝ≥0) * ε
  let X := S.termAt (j + 1)
  have hscalar : θ + ε = (((j + 1 : ℕ) : ℝ≥0) * ε) := by
    dsimp [θ]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hterm := (CoordinateShift.shift θ).mapIso
    (crossRightTermAtIso R S hlen hpos ε j)
  have hterm' : (CoordinateShift.shift θ).obj
      ((crossRightResolution R S hlen hpos ε).termAt j) ≅
        (CoordinateShift.shift θ).obj ((CoordinateShift.shift ε).obj X ⊞ 0) := by
    simpa [X, Nat.ne_of_gt hj] using hterm
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct
    (CoordinateShift.shift (R := k) (n := n) θ)
    (X := (CoordinateShift.shift ε).obj X) (Y := (0 : PModule.{u,0,u} k (Fin n → ℝ)))
  exact hterm'.trans
    ((Functor.mapBiprod (CoordinateShift.shift θ) ((CoordinateShift.shift ε).obj X) 0).trans
      ((biprod.mapIso (CoordinateShift.compIso θ ε X)
        (Functor.mapZeroObject (CoordinateShift.shift θ))).trans
        ((FiniteRankProjectiveResolution.biprodRightZeroIso
          ((CoordinateShift.shift (θ + ε)).obj X)).trans
          (CoordinateShift.congrIso hscalar X))))

private noncomputable def crossLeftHeadIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    (CoordinateShift.shift 0).obj
        ((crossLeftResolution R S hlen hpos ε).termAt 0) ≅
      (CoordinateShift.shift 0).obj (S.termAt 0) ⊞
        (CoordinateShift.shift ε).obj (R.termAt 1) := by
  exact (CoordinateShift.zeroIso _).trans
    ((crossLeftTermAtIso R S hlen hpos ε 0).trans
      ((biprod.braiding _ _).trans
        (biprod.mapIso (CoordinateShift.zeroIso (S.termAt 0)).symm (Iso.refl _))))

private noncomputable def crossRightHeadIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) :
    (CoordinateShift.shift 0).obj
        ((crossRightResolution R S hlen hpos ε).termAt 0) ≅
      (CoordinateShift.shift 0).obj (R.termAt 0) ⊞
        (CoordinateShift.shift ε).obj (S.termAt 1) := by
  exact (CoordinateShift.zeroIso _).trans
    ((crossRightTermAtIso R S hlen hpos ε 0).trans
      ((biprod.braiding _ _).trans
        (biprod.mapIso (CoordinateShift.zeroIso (R.termAt 0)).symm (Iso.refl _))))

private noncomputable def resolutionBiproductSplitFinSucc {m : ℕ}
    (F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ)) :
    F 0 ⊞ (⨁ fun j : Fin m => F j.succ) ≅ ⨁ F := by
  classical
  let tail : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let b : Bicone F := {
    pt := F 0 ⊞ ⨁ tail
    π := Fin.cases biprod.fst (fun j => biprod.snd ≫ biproduct.π tail j)
    ι := Fin.cases biprod.inl (fun j => biproduct.ι tail j ≫ biprod.inr)
    ι_π := by
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [Category.assoc]
        · simp [Category.assoc] <;> intro h <;> cases h
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [Category.assoc] <;> intro h <;> cases h
        · by_cases h : i = j
          · subst j
            simp [tail, Category.assoc, biproduct.ι_π]
          · simp [tail, Category.assoc, h, biproduct.ι_π]
  }
  have htotal : ∑ j : Fin (m + 1), b.π j ≫ b.ι j = 𝟙 b.pt := by
    rw [Fin.sum_univ_succ]
    change biprod.fst ≫ biprod.inl +
      ∑ j : Fin m, (biprod.snd ≫ biproduct.π tail j) ≫
        (biproduct.ι tail j ≫ biprod.inr) = 𝟙 _
    have hsum : ∑ j : Fin m, (biprod.snd ≫ biproduct.π tail j) ≫
          (biproduct.ι tail j ≫ biprod.inr (X := F 0) (Y := ⨁ tail)) =
        biprod.snd (X := F 0) (Y := ⨁ tail) ≫
          (∑ j : Fin m, biproduct.π tail j ≫ biproduct.ι tail j) ≫
            biprod.inr (X := F 0) (Y := ⨁ tail) := by
      symm
      rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Category.assoc]
    rw [hsum]
    rw [biproduct.total]
    change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr =
      𝟙 (F 0 ⊞ ⨁ tail)
    exact biprod.total
  exact biproduct.uniqueUpToIso F (isBilimitOfTotal b htotal)

private theorem resolutionBiproductSplitFinSucc_inl_hom {m : ℕ}
    (F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ)) :
    biprod.inl ≫ (resolutionBiproductSplitFinSucc F).hom = biproduct.ι F 0 := by
  apply biproduct.hom_ext
  intro j
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [resolutionBiproductSplitFinSucc, biproduct.uniqueUpToIso,
      Category.assoc, biproduct.lift_π,
      biproduct.ι_π_ne _ (Fin.succ_ne_zero _).symm]

private theorem resolutionBiproductSplitFinSucc_inv_fst {m : ℕ}
    (F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ)) :
    (resolutionBiproductSplitFinSucc F).inv ≫ biprod.fst = biproduct.π F 0 := by
  apply biproduct.hom_ext'
  intro j
  refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [resolutionBiproductSplitFinSucc, biproduct.uniqueUpToIso,
      Category.assoc, biproduct.ι_desc,
      biproduct.ι_π_ne _ (Fin.succ_ne_zero _).symm]

private noncomputable def resolutionBiproductPairIso {m : ℕ}
    (F G : Fin m → PModule.{u,0,u} k (Fin n → ℝ)) :
    (⨁ fun j => F j ⊞ G j) ≅ (⨁ F) ⊞ (⨁ G) := by
  classical
  let H : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j ⊞ G j
  let b : Bicone H := {
    pt := (⨁ F) ⊞ ⨁ G
    π := fun j => biprod.lift (biprod.fst ≫ biproduct.π F j)
      (biprod.snd ≫ biproduct.π G j)
    ι := fun j => biprod.desc (biproduct.ι F j ≫ biprod.inl)
      (biproduct.ι G j ≫ biprod.inr)
    ι_π := by
      intro i j
      by_cases h : i = j
      · subst j
        simp [H, Category.assoc, biprod.desc_eq, biprod.lift_eq,
          biproduct.ι_π]
      · simp [H, Category.assoc, biprod.desc_eq, biprod.lift_eq, h,
          biproduct.ι_π]
  }
  have htotal : ∑ j : Fin m, b.π j ≫ b.ι j = 𝟙 b.pt := by
    have hcomp (j : Fin m) : b.π j ≫ b.ι j =
        (biprod.fst ≫ biproduct.π F j ≫ biproduct.ι F j ≫ biprod.inl) +
          (biprod.snd ≫ biproduct.π G j ≫ biproduct.ι G j ≫ biprod.inr) := by
      simp [b, Category.assoc, biprod.lift_desc]
    calc
      _ = ∑ j : Fin m,
          ((biprod.fst ≫ biproduct.π F j ≫ biproduct.ι F j ≫ biprod.inl) +
            (biprod.snd ≫ biproduct.π G j ≫ biproduct.ι G j ≫ biprod.inr)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcomp j
      _ = (biprod.fst ≫ (∑ j : Fin m, biproduct.π F j ≫ biproduct.ι F j) ≫ biprod.inl) +
          (biprod.snd ≫ (∑ j : Fin m, biproduct.π G j ≫ biproduct.ι G j) ≫ biprod.inr) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · symm
            rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Category.assoc]
          · symm
            rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Category.assoc]
      _ = 𝟙 b.pt := by
          rw [biproduct.total, biproduct.total]
          change biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr =
            𝟙 ((⨁ F) ⊞ ⨁ G)
          exact biprod.total
  exact (biproduct.uniqueUpToIso H (isBilimitOfTotal b htotal)).symm

private theorem isZero_biproduct_of_isZero {ι : Type} [Finite ι]
    (F : ι → PModule.{u,0,u} k (Fin n → ℝ)) (hF : ∀ i, IsZero (F i)) :
    IsZero (⨁ F) := by
  refine ⟨?_, ?_⟩
  · intro Y
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply biproduct.hom_ext'
    intro i
    exact (hF i).eq_of_src _ _
  · intro Y
    refine ⟨{ default := 0, uniq := ?_ }⟩
    intro f
    apply biproduct.hom_ext
    intro i
    exact (hF i).eq_of_tgt _ _

private noncomputable def resolutionBiproductHeadZeroIsoOfPos {m : ℕ}
    (hm : 0 < m) (P : PModule.{u,0,u} k (Fin n → ℝ)) :
    (⨁ fun j : Fin m => if j = (⟨0, hm⟩ : Fin m) then P else 0) ≅ P := by
  classical
  let q : ℕ := m - 1
  have hq : q + 1 = m := by dsimp [q]; omega
  let e : Fin (q + 1) ≃ Fin m := finCongr hq
  let head : Fin m := ⟨0, hm⟩
  let G : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => if j = head then P else 0
  let F : Fin (q + 1) → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G (e j)
  have he0 : e (0 : Fin (q + 1)) = head := by
    apply Fin.ext
    rfl
  have hzero : F 0 = P := by simp [F, G, he0, head]
  have htail : ∀ j : Fin q, F j.succ = 0 := by
    intro j
    have he : e j.succ ≠ head := by
      intro h
      have heq : e j.succ = e (0 : Fin (q + 1)) := h.trans he0.symm
      have : j.succ = 0 := e.injective heq
      exact Fin.succ_ne_zero _ this
    change G (e j.succ) = 0
    simp only [G, if_neg he]
  have htailZero : ∀ j : Fin q, IsZero (F j.succ) := by
    intro j
    rw [htail j]
    exact isZero_zero _
  let tail : Fin q → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let eTail : (⨁ tail) ≅ (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    (isZero_biproduct_of_isZero tail htailZero).iso (isZero_zero _)
  have htailDef : tail = fun j : Fin q => F j.succ := rfl
  let reduce : P ⊞ (0 : PModule.{u,0,u} k (Fin n → ℝ)) ≅ P := {
    hom := biprod.fst
    inv := biprod.inl
    hom_inv_id := by
      apply biprod.hom_ext'
      · simp
      · exact (isZero_zero _).eq_of_src _ _
    inv_hom_id := by simp
  }
  simpa only [F, G, head, htailDef] using
    ((biproduct.reindex e G).symm ≪≫
      (resolutionBiproductSplitFinSucc F).symm ≪≫
      biprod.mapIso (eqToIso hzero) eTail ≪≫ reduce)

private noncomputable def crossResolutionInterleaving
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0)
    (i : CoordinateInterleaving ε M N) :
    CoordinateInterleaving ε
      ((CoordinateShift.shift ε).obj (R.kernel ⟨1, by omega⟩) ⊞
        S.term ⟨0, by omega⟩)
      ((CoordinateShift.shift ε).obj
        (S.kernel ⟨1, by rw [← hlen]; omega⟩) ⊞ R.term ⟨0, by omega⟩) := by
  let iR : Fin R.length := ⟨0, by omega⟩
  let iS : Fin S.length := ⟨0, by rw [← hlen]; omega⟩
  let hR := (R.row_rank_exact iR).of_iso
    (Iso.refl _) (Iso.refl _) R.initial_iso
  let hS := (S.row_rank_exact iS).of_iso
    (Iso.refl _) (Iso.refl _) S.initial_iso
  let oneStep := RankSchanuel.interleavingOfSequences
    (α := R.quotient iR ≫ R.initial_iso.hom)
    (β := S.quotient iS ≫ S.initial_iso.hom) (i := i)
    hR hS (R.term_rank_projective iR) (S.term_rank_projective iS)
  exact oneStep.symm.congr (Iso.refl _)
    (biprod.braiding (R.term iR)
      ((CoordinateShift.shift ε).obj (S.kernel iS.succ)))

private noncomputable def crossLeftResolutionBiproductIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (m : ℕ)
    (hR : R.length = m + 2) (hS : S.length = m + 2) :
    (⨁ schanuelLeftAt
      (crossLeftResolution R S hlen hpos ε)
      (crossRightResolution R S hlen hpos ε) ε (L := m + 1)) ≅
    (⨁ schanuelRightAt R S ε (L := m + 2)) := by
  classical
  let U := crossLeftResolution R S hlen hpos ε
  let V := crossRightResolution R S hlen hpos ε
  let F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelLeftAt U V ε j
  let G : Fin (m + 2) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelRightAt R S ε j
  have hhead : F 0 ≅ G 0 ⊞ G 1 := by
    simpa [F, G, U, schanuelLeftAt, schanuelRightAt] using
      (crossLeftHeadIso R S hlen hpos ε)
  let Ftail : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let Gtail1 : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ
  let Gtail2 : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ.succ
  have htail (q : Fin m) : Ftail q ≅ Gtail2 q := by
    let j : ℕ := q.val + 1
    have hj : 0 < j := by dsimp [j]; omega
    by_cases hEven : Even j
    · have hNotEvenNext : ¬ Even (j + 1) := by
        simp [Nat.even_add_one, hEven]
      simpa [Ftail, Gtail2, G, F, U, j, schanuelLeftAt,
        schanuelRightAt, hEven, hNotEvenNext] using
          (crossLeftTailTermIso R S hlen hpos ε j hj)
    · have hEvenNext : Even (j + 1) := by
        rw [Nat.even_add_one]
        exact hEven
      simpa [Ftail, Gtail2, G, F, V, j, schanuelLeftAt,
        schanuelRightAt, hEven, hEvenNext] using
          (crossRightTailTermIso R S hlen hpos ε j hj)
  let splitF := resolutionBiproductSplitFinSucc F
  let splitG := resolutionBiproductSplitFinSucc G
  let splitGtail := resolutionBiproductSplitFinSucc Gtail1
  exact splitF.symm ≪≫
    biprod.mapIso hhead (biproduct.mapIso htail) ≪≫
    biprod.associator (G 0) (G 1) (⨁ Gtail2) ≪≫
    biprod.mapIso (Iso.refl _) splitGtail ≪≫ splitG

private noncomputable def crossRightResolutionBiproductIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (hpos : 1 < R.length) (ε : ℝ≥0) (m : ℕ)
    (hR : R.length = m + 2) (hS : S.length = m + 2) :
    (⨁ schanuelRightAt
      (crossLeftResolution R S hlen hpos ε)
      (crossRightResolution R S hlen hpos ε) ε (L := m + 1)) ≅
    (⨁ schanuelLeftAt R S ε (L := m + 2)) := by
  classical
  let U := crossLeftResolution R S hlen hpos ε
  let V := crossRightResolution R S hlen hpos ε
  let F : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelRightAt U V ε j
  let G : Fin (m + 2) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => schanuelLeftAt R S ε j
  have hhead : F 0 ≅ G 0 ⊞ G 1 := by
    simpa [F, G, V, schanuelLeftAt, schanuelRightAt] using
      (crossRightHeadIso R S hlen hpos ε)
  let Ftail : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let Gtail1 : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ
  let Gtail2 : Fin m → PModule.{u,0,u} k (Fin n → ℝ) := fun j => G j.succ.succ
  have htail (q : Fin m) : Ftail q ≅ Gtail2 q := by
    let j : ℕ := q.val + 1
    have hj : 0 < j := by dsimp [j]; omega
    by_cases hEven : Even j
    · have hNotEvenNext : ¬ Even (j + 1) := by
        simp [Nat.even_add_one, hEven]
      simpa [Ftail, Gtail2, G, F, V, j, schanuelRightAt,
        schanuelLeftAt, hEven, hNotEvenNext] using
          (crossRightTailTermIso R S hlen hpos ε j hj)
    · have hEvenNext : Even (j + 1) := by
        rw [Nat.even_add_one]
        exact hEven
      simpa [Ftail, Gtail2, G, F, U, j, schanuelRightAt,
        schanuelLeftAt, hEven, hEvenNext] using
          (crossLeftTailTermIso R S hlen hpos ε j hj)
  let splitF := resolutionBiproductSplitFinSucc F
  let splitG := resolutionBiproductSplitFinSucc G
  let splitGtail := resolutionBiproductSplitFinSucc Gtail1
  exact splitF.symm ≪≫
    biprod.mapIso hhead (biproduct.mapIso htail) ≪≫
    biprod.associator (G 0) (G 1) (⨁ Gtail2) ≪≫
    biprod.mapIso (Iso.refl _) splitGtail ≪≫ splitG

private noncomputable def resolutionBiproductFinOneIso
    (P : PModule.{u,0,u} k (Fin n → ℝ)) :
    (⨁ fun _ : Fin 1 => P) ≅ P := by
  classical
  let F : Fin 1 → PModule.{u,0,u} k (Fin n → ℝ) := fun _ => P
  let tail : Fin 0 → PModule.{u,0,u} k (Fin n → ℝ) := fun j => F j.succ
  let eTail : (⨁ tail) ≅ (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    (isZero_biproduct_of_isZero tail (by intro j; exact Fin.elim0 j)).iso
      (isZero_zero _)
  exact (resolutionBiproductSplitFinSucc F).symm ≪≫
    biprod.mapIso (Iso.refl P) eTail ≪≫
      FiniteRankProjectiveResolution.biprodRightZeroIso P

private noncomputable def schanuelLeftFinOneIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (hR : R.length = 1) :
    (⨁ schanuelLeftAt R S ε (L := 1)) ≅ R.term ⟨0, by omega⟩ := by
  classical
  let F : Fin 1 → PModule.{u,0,u} k (Fin n → ℝ) := fun j => schanuelLeftAt R S ε j
  have hR0 : R.termAt 0 = R.term ⟨0, by omega⟩ :=
    FiniteRankProjectiveResolution.termAt_eq_term R (by omega)
  have hterm (j : Fin 1) : F j ≅ R.term ⟨0, by omega⟩ := by
    have hj : j = 0 := by apply Fin.ext; omega
    subst j
    simpa [F, schanuelLeftAt] using
      (CoordinateShift.zeroIso (R.termAt 0)).trans (eqToIso hR0)
  exact biproduct.mapIso hterm ≪≫ resolutionBiproductFinOneIso _

private noncomputable def schanuelRightFinOneIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (hS : S.length = 1) :
    (⨁ schanuelRightAt R S ε (L := 1)) ≅ S.term ⟨0, by omega⟩ := by
  classical
  let F : Fin 1 → PModule.{u,0,u} k (Fin n → ℝ) := fun j => schanuelRightAt R S ε j
  have hS0 : S.termAt 0 = S.term ⟨0, by omega⟩ :=
    FiniteRankProjectiveResolution.termAt_eq_term S (by omega)
  have hterm (j : Fin 1) : F j ≅ S.term ⟨0, by omega⟩ := by
    have hj : j = 0 := by apply Fin.ext; omega
    subst j
    simpa [F, schanuelRightAt] using
      (CoordinateShift.zeroIso (S.termAt 0)).trans (eqToIso hS0)
  exact biproduct.mapIso hterm ≪≫ resolutionBiproductFinOneIso _

private noncomputable def schanuelAtLength (L : ℕ) :
    ∀ {M N : PModule.{u,0,u} k (Fin n → ℝ)}
      (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
      (hR : R.length = L) (hS : S.length = L) (ε : ℝ≥0)
      (i : CoordinateInterleaving ε M N),
      CoordinateInterleaving ε
        (⨁ schanuelLeftAt R S ε (L := L))
        (⨁ schanuelRightAt R S ε (L := L)) := by
  induction L with
  | zero =>
    intro M N R S hR hS ε i
    have hA : IsZero (⨁ schanuelLeftAt R S ε (L := 0)) :=
      isZero_biproduct_of_isZero _ (by intro j; exact Fin.elim0 j)
    have hB : IsZero (⨁ schanuelRightAt R S ε (L := 0)) :=
      isZero_biproduct_of_isZero _ (by intro j; exact Fin.elim0 j)
    exact (CoordinateInterleaving.refl ε (0 : PModule.{u,0,u} k (Fin n → ℝ))).congr
      (hA.iso (isZero_zero _)).symm (hB.iso (isZero_zero _)).symm
  | succ L ih =>
    cases L with
    | zero =>
      intro M N R S hR hS ε i
      have hRlen : R.length = 1 := hR
      have hSlen : S.length = 1 := hS
      exact (FiniteRankProjectiveResolution.interleaving_of_length_one
          R S hRlen hSlen ε i).congr
        (schanuelLeftFinOneIso R S ε hRlen).symm
        (schanuelRightFinOneIso R S ε hSlen).symm
    | succ m =>
      intro M N R S hR hS ε i
      have hpos : 1 < R.length := by omega
      have hlen : R.length = S.length := hR.trans hS.symm
      let U := crossLeftResolution R S hlen hpos ε
      let V := crossRightResolution R S hlen hpos ε
      have hULen : U.length = m + 1 := by
        dsimp [U, crossLeftResolution, FiniteRankProjectiveResolution.biprod,
          FiniteRankProjectiveResolution.shift]
        simp [FiniteRankProjectiveResolution.length_tail, hR]
      have hVLen : V.length = m + 1 := by
        dsimp [V, crossRightResolution, FiniteRankProjectiveResolution.biprod,
          FiniteRankProjectiveResolution.shift]
        simp [FiniteRankProjectiveResolution.length_tail, hR, hS]
      have iUV := crossResolutionInterleaving R S hlen hpos ε i
      have ihUV := ih U V hULen hVLen ε iUV
      have hR' : R.length = m + 2 := by omega
      have hS' : S.length = m + 2 := by omega
      exact (ihUV.congr
        (crossLeftResolutionBiproductIso R S hlen hpos ε m hR' hS')
        (crossRightResolutionBiproductIso R S hlen hpos ε m hR' hS')).symm

/-- Persistent Schanuel comparison for arbitrary finite rank-projective
resolutions.  Each resolution is extended by zero terms to the larger length;
the alternating summands are shifted by their homological degree.  The proof
constructs the interleaving maps and both composite equations by induction on
that common length. -/
noncomputable def schanuelInterleavingOfResolutions
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (ε : ℝ≥0) (i : CoordinateInterleaving ε M N) :
    CoordinateInterleaving ε
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct R S ε)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct R S ε) := by
  classical
  let L := max R.length S.length
  let R' := FiniteRankProjectiveResolution.appendZeros R (L - R.length)
  let S' := FiniteRankProjectiveResolution.appendZeros S (L - S.length)
  have hR' : R'.length = L := by
    dsimp [R']
    rw [FiniteRankProjectiveResolution.appendZeros_length]
    dsimp [L]
    omega
  have hS' : S'.length = L := by
    dsimp [S']
    rw [FiniteRankProjectiveResolution.appendZeros_length]
    dsimp [L]
    omega
  have hmaxPad : max R'.length S'.length = L := by rw [hR', hS']; simp
  have hleft (j : Fin L) : schanuelLeftAt R' S' ε j = schanuelLeftAt R S ε j := by
    unfold schanuelLeftAt
    by_cases hEven : Even j.val <;>
      simp [hEven, R', S', FiniteRankProjectiveResolution.termAt_appendZeros]
  have hright (j : Fin L) : schanuelRightAt R' S' ε j = schanuelRightAt R S ε j := by
    unfold schanuelRightAt
    by_cases hEven : Even j.val <;>
      simp [hEven, R', S', FiniteRankProjectiveResolution.termAt_appendZeros]
  let eLeft0 : (⨁ schanuelLeftAt R' S' ε (L := L)) ≅
      (⨁ schanuelLeftAt R S ε (L := L)) :=
    biproduct.mapIso (fun j => eqToIso (hleft j))
  let eRight0 : (⨁ schanuelRightAt R' S' ε (L := L)) ≅
      (⨁ schanuelRightAt R S ε (L := L)) :=
    biproduct.mapIso (fun j => eqToIso (hright j))
  have eLeft :
      FiniteRankProjectiveResolution.schanuelLeftBiproduct R' S' ε ≅
        FiniteRankProjectiveResolution.schanuelLeftBiproduct R S ε := by
    change (⨁ schanuelLeftAt R' S' ε
      (L := max R'.length S'.length)) ≅
        (⨁ schanuelLeftAt R S ε (L := max R.length S.length))
    rw [hmaxPad]
    change (⨁ schanuelLeftAt R' S' ε (L := L)) ≅
      (⨁ schanuelLeftAt R S ε (L := L))
    exact eLeft0
  have eRight :
      FiniteRankProjectiveResolution.schanuelRightBiproduct R' S' ε ≅
        FiniteRankProjectiveResolution.schanuelRightBiproduct R S ε := by
    change (⨁ schanuelRightAt R' S' ε
      (L := max R'.length S'.length)) ≅
        (⨁ schanuelRightAt R S ε (L := max R.length S.length))
    rw [hmaxPad]
    change (⨁ schanuelRightAt R' S' ε (L := L)) ≅
      (⨁ schanuelRightAt R S ε (L := L))
    exact eRight0
  have ih0 := schanuelAtLength L R' S' hR' hS' ε i
  have ih : CoordinateInterleaving ε
      (FiniteRankProjectiveResolution.schanuelLeftBiproduct R' S' ε)
      (FiniteRankProjectiveResolution.schanuelRightBiproduct R' S' ε) := by
    change CoordinateInterleaving ε
      (⨁ schanuelLeftAt R' S' ε (L := max R'.length S'.length))
      (⨁ schanuelRightAt R' S' ε (L := max R'.length S'.length))
    rw [hmaxPad]
    exact ih0
  exact ih.congr eLeft eRight

end TDA.Persistence
