import TDA.Simplicial.Boundary
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Fin.Basic

/-!
# Oriented chains of vertex tuples

Repeated vertices give zero. Injective tuples are expressed in the increasing
actual-face basis with the sign of the sorting permutation.
-/

namespace TDA.Simplicial

open Equiv Finset
open scoped BigOperators

universe u v

noncomputable section

/-- The permutation induced after removing a position and its image. -/
def deletedPerm {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv i).trans
    ((p.subtypeEquiv (fun x => (show x ≠ i ↔ p x ≠ p i from p.injective.ne_iff.symm))).trans
      (finSuccAboveEquiv (p i)).symm)

/-- A permutation commutes with deletion after applying its induced permutation. -/
theorem deletedPerm_succAbove {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (j : Fin n) :
    (p i).succAbove (deletedPerm p i j) = p (i.succAbove j) := by
  have h := (finSuccAboveEquiv (p i)).apply_symm_apply
    ((p.subtypeEquiv (fun x => (show x ≠ i ↔ p x ≠ p i from p.injective.ne_iff.symm))) (finSuccAboveEquiv i j))
  exact congrArg Subtype.val h

/-- Removing one position changes the sign by the two removed-position signs. -/
theorem sign_deletedPerm {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    Equiv.Perm.sign (deletedPerm p i) =
      (-1 : ℤˣ) ^ (p i : ℕ) * Equiv.Perm.sign p * (-1 : ℤˣ) ^ (i : ℕ) := by
  let q : Equiv.Perm (Fin (n + 1)) :=
    (i.cycleRange.symm.trans p).trans (p i).cycleRange
  have hq : q = Equiv.Perm.decomposeFin.symm (0, deletedPerm p i) := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [q]
    · simp only [q, Equiv.trans_apply, Fin.cycleRange_symm_succ,
        Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
        Equiv.refl_apply]
      rw [← deletedPerm_succAbove p i k, Fin.cycleRange_succAbove]
  have hs := congrArg Equiv.Perm.sign hq
  simpa [q, Equiv.Perm.sign_trans, mul_assoc, mul_comm, mul_left_comm] using hs.symm

variable {V : Type u} [LinearOrder V]

private theorem tupleImage_perm {n : ℕ} (x : Fin n → V) (p : Equiv.Perm (Fin n)) :
    Finset.univ.image (x ∘ p) = Finset.univ.image x := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨p i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p.symm i, by simp⟩

/-- The actual image face of an injective vertex tuple. -/
def tupleFace (K : PreAbstractSimplicialComplex V) {n : ℕ} (x : Fin (n + 1) → V)
    (hx : Function.Injective x) (hk : Finset.univ.image x ∈ K) : Face K n :=
  ⟨Finset.univ.image x, hk, by simp [Finset.card_image_of_injective, hx]⟩

/-- The oriented actual-face chain of a tuple; repetitions and absent faces give zero. -/
def orientedTuple (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R]
    {n : ℕ} (x : Fin (n + 1) → V) : Chain K R n := by
  classical
  exact if hx : Function.Injective x then
    if hk : Finset.univ.image x ∈ K then
      ((Equiv.Perm.sign (Tuple.sort x) : ℤ)) •
        Finsupp.single (tupleFace K x hx hk) (1 : R)
    else 0
  else 0

@[simp] theorem orientedTuple_of_not_injective (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 1) → V)
    (hx : ¬Function.Injective x) : orientedTuple K R x = 0 := by
  simp [orientedTuple, hx]

/-- An injective tuple contributes its sorted face with its orientation sign. -/
theorem orientedTuple_of_injective (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 1) → V)
    (hx : Function.Injective x) (hk : Finset.univ.image x ∈ K) :
    orientedTuple K R x = ((Equiv.Perm.sign (Tuple.sort x) : ℤ)) •
      Finsupp.single (tupleFace K x hx hk) (1 : R) := by
  simp [orientedTuple, hx, hk]

private theorem sort_comp_of_injective {n : ℕ} (x : Fin n → V)
    (hx : Function.Injective x) (p : Equiv.Perm (Fin n)) :
    Tuple.sort (x ∘ p) = (Tuple.sort x).trans p.symm := by
  apply Equiv.ext
  intro i
  apply p.injective
  apply hx
  simpa using congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := x) (σ := p)) i

/-- Reordering any tuple multiplies its oriented chain by the permutation sign. -/
theorem orientedTuple_comp_perm (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 1) → V)
    (p : Equiv.Perm (Fin (n + 1))) :
    orientedTuple K R (x ∘ p) = (Equiv.Perm.sign p : ℤ) • orientedTuple K R x := by
  by_cases hx : Function.Injective x
  · have hxp : Function.Injective (x ∘ p) := hx.comp p.injective
    by_cases hk : Finset.univ.image x ∈ K
    · have hkp : Finset.univ.image (x ∘ p) ∈ K := by rwa [tupleImage_perm]
      have hf : tupleFace K (x ∘ p) hxp hkp = tupleFace K x hx hk :=
        Subtype.ext (tupleImage_perm x p)
      rw [orientedTuple_of_injective K R _ hxp hkp,
        orientedTuple_of_injective K R _ hx hk, hf, sort_comp_of_injective x hx]
      simp [Equiv.Perm.sign_trans, mul_smul]
    · have hkp : Finset.univ.image (x ∘ p) ∉ K := by rwa [tupleImage_perm]
      simp [orientedTuple, hx, hxp, hk, hkp]
  · have hxp : ¬Function.Injective (x ∘ p) := by
      intro h
      apply hx
      intro i j hij
      have h' := h (show (x ∘ p) (p.symm i) = (x ∘ p) (p.symm j) by simpa using hij)
      exact p.symm.injective h'
    simp [orientedTuple, hx, hxp]

private theorem signed_deletedPerm {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    (-1 : ℤ) ^ (i : ℕ) * (Equiv.Perm.sign (deletedPerm p i) : ℤ) =
      (Equiv.Perm.sign p : ℤ) * (-1 : ℤ) ^ (p i : ℕ) := by
  have h : (-1 : ℤˣ) ^ (i : ℕ) * Equiv.Perm.sign (deletedPerm p i) =
      Equiv.Perm.sign p * (-1 : ℤˣ) ^ (p i : ℕ) := by
    rw [sign_deletedPerm]
    calc
      _ = (Equiv.Perm.sign p * (-1 : ℤˣ) ^ (p i : ℕ)) *
          ((-1 : ℤˣ) ^ (i : ℕ) * (-1 : ℤˣ) ^ (i : ℕ)) := by ac_rfl
      _ = _ := by rw [Int.units_mul_self]; simp
  simpa using congrArg (fun z : ℤˣ => (z : ℤ)) h

/-- The alternating deletion sum of oriented vertex tuples. -/
def tupleBoundarySum (K : PreAbstractSimplicialComplex V) (R : Type v) [Ring R]
    {n : ℕ} (x : Fin (n + 2) → V) : Chain K R n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • orientedTuple K R (x ∘ i.succAbove)

/-- The alternating deletion sum also changes by the sign of a permutation. -/
theorem tupleBoundarySum_comp_perm (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 2) → V)
    (p : Equiv.Perm (Fin (n + 2))) :
    tupleBoundarySum K R (x ∘ p) =
      (Equiv.Perm.sign p : ℤ) • tupleBoundarySum K R x := by
  unfold tupleBoundarySum
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv p
  intro i
  have he : (x ∘ p) ∘ i.succAbove = (x ∘ (p i).succAbove) ∘ deletedPerm p i := by
    funext j
    simp only [Function.comp_apply]
    rw [deletedPerm_succAbove]
  rw [he, orientedTuple_comp_perm, smul_smul, smul_smul, signed_deletedPerm]

omit [LinearOrder V] in
private theorem delete_adjacent_eq {n : ℕ} (x : Fin (n + 2) → V)
    (r : Fin (n + 1)) (hr : x r.castSucc = x r.succ) :
    x ∘ r.castSucc.succAbove = x ∘ r.succ.succAbove := by
  funext j
  simp only [Function.comp_apply]
  rcases lt_trichotomy j r with hj | rfl | hj
  · have h1 : j.castSucc < r.castSucc := hj
    have h2 : j.castSucc < r.succ := lt_trans h1 Fin.castSucc_lt_succ
    rw [Fin.succAbove_of_castSucc_lt _ _ h1, Fin.succAbove_of_castSucc_lt _ _ h2]
  · rw [Fin.succAbove_of_le_castSucc _ _ le_rfl,
      Fin.succAbove_of_castSucc_lt _ _ Fin.castSucc_lt_succ]
    exact hr.symm
  · have h1 : r.castSucc ≤ j.castSucc := hj.le
    have h2 : r.succ ≤ j.castSucc := hj
    rw [Fin.succAbove_of_le_castSucc _ _ h1, Fin.succAbove_of_le_castSucc _ _ h2]

omit [LinearOrder V] in
private theorem delete_other_not_injective {n : ℕ} (x : Fin (n + 2) → V)
    (r : Fin (n + 1)) (hr : x r.castSucc = x r.succ)
    (i : Fin (n + 2)) (hia : i ≠ r.castSucc) (hib : i ≠ r.succ) :
    ¬Function.Injective (x ∘ i.succAbove) := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hia.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hib.symm
  intro hinj
  have hab : a = b := hinj (by simpa only [Function.comp_apply, ha, hb] using hr)
  have h : r.castSucc = r.succ := by rw [← ha, ← hb, hab]
  exact ((Fin.castSucc_lt_succ (i := r))).ne h

/-- If two adjacent entries agree, the entire alternating deletion sum cancels. -/
theorem tupleBoundarySum_eq_zero_of_adjacent (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 2) → V)
    (r : Fin (n + 1)) (hr : x r.castSucc = x r.succ) :
    tupleBoundarySum K R x = 0 := by
  classical
  have hne : r.castSucc ≠ r.succ := ((Fin.castSucc_lt_succ (i := r))).ne
  have hs : tupleBoundarySum K R x =
      (-1 : ℤ) ^ (r : ℕ) • orientedTuple K R (x ∘ r.castSucc.succAbove) +
      (-1 : ℤ) ^ ((r : ℕ) + 1) • orientedTuple K R (x ∘ r.succ.succAbove) := by
    unfold tupleBoundarySum
    have hz (i : Fin (n + 2)) (_ : i ∈ (Finset.univ : Finset (Fin (n + 2))))
        (hi : i ∉ ({r.castSucc, r.succ} : Finset (Fin (n + 2)))) :
        (-1 : ℤ) ^ (i : ℕ) • orientedTuple K R (x ∘ i.succAbove) = 0 := by
      have hia : i ≠ r.castSucc := by
        intro h
        exact hi (by simp [h])
      have hib : i ≠ r.succ := by
        intro h
        exact hi (by simp [h])
      rw [orientedTuple_of_not_injective K R _
        (delete_other_not_injective x r hr i hia hib), smul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ {r.castSucc, r.succ}) hz]
    simp [hne]
  rw [hs, delete_adjacent_eq x r hr, pow_succ]
  simp

/-- Repetitions force cancellation in the alternating deletion sum over every ring. -/
theorem tupleBoundarySum_eq_zero_of_not_injective (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 2) → V)
    (hx : ¬Function.Injective x) : tupleBoundarySum K R x = 0 := by
  let p := Tuple.sort x
  let y := x ∘ p
  have hm : Monotone y := Tuple.monotone_sort x
  have hns : ¬StrictMono y := by
    intro hs
    apply hx
    intro i j hij
    apply p.symm.injective
    apply hs.injective
    simpa [y] using hij
  have hex : ∃ r : Fin (n + 1), y r.castSucc = y r.succ := by
    by_contra h
    push Not at h
    apply hns
    apply Fin.strictMono_iff_lt_succ.mpr
    intro r
    exact lt_of_le_of_ne (hm (Fin.castSucc_le_succ r)) (h r)
  obtain ⟨r, hr⟩ := hex
  have hz : tupleBoundarySum K R y = 0 :=
    tupleBoundarySum_eq_zero_of_adjacent K R y r hr
  have he := tupleBoundarySum_comp_perm K R x p
  change tupleBoundarySum K R y = _ at he
  have hs : (Equiv.Perm.sign p : ℤ) * (Equiv.Perm.sign p : ℤ) = 1 := by
    simp
  have he' := congrArg (fun z : Chain K R n => (Equiv.Perm.sign p : ℤ) • z) he.symm
  simpa only [smul_smul, hs, one_smul, hz, smul_zero] using he'

private theorem tupleImage_delete {n : ℕ} (x : Fin (n + 2) → V)
    (hx : Function.Injective x) (i : Fin (n + 2)) :
    Finset.univ.image (x ∘ i.succAbove) = (Finset.univ.image x).erase (x i) := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase,
    Function.comp_apply]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => (Fin.succAbove_ne i j) (hx h), ⟨i.succAbove j, rfl⟩⟩
  · rintro ⟨hne, j, rfl⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (fun h : j = i => hne (congrArg x h))
    exact ⟨k, congrArg x hk⟩

theorem tupleImage_delete_mem (K : PreAbstractSimplicialComplex V)
    {n : ℕ} (x : Fin (n + 2) → V) (hk : Finset.univ.image x ∈ K)
    (i : Fin (n + 2)) : Finset.univ.image (x ∘ i.succAbove) ∈ K := by
  apply (K.isRelLowerSet_faces hk).2
  · intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨i.succAbove j, Finset.mem_univ _, rfl⟩
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty

/-- A monotone injective tuple has its increasing-face orientation. -/
theorem orientedTuple_of_monotone (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 1) → V)
    (hx : Function.Injective x) (hk : Finset.univ.image x ∈ K) (hm : Monotone x) :
    orientedTuple K R x = Finsupp.single (tupleFace K x hx hk) (1 : R) := by
  rw [orientedTuple_of_injective K R x hx hk,
    Tuple.sort_eq_refl_iff_monotone.mpr hm]
  simp

private theorem tupleFace_enumeration (K : PreAbstractSimplicialComplex V)
    {n : ℕ} (x : Fin (n + 1) → V) (hx : Function.Injective x)
    (hk : Finset.univ.image x ∈ K) (hm : Monotone x) :
    ⇑((tupleFace K x hx hk).1.orderEmbOfFin (tupleFace K x hx hk).2.2) = x := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · exact hm.strictMono_of_injective hx

private theorem tupleFace_delete (K : PreAbstractSimplicialComplex V)
    {n : ℕ} (x : Fin (n + 2) → V) (hx : Function.Injective x)
    (hk : Finset.univ.image x ∈ K) (hm : Monotone x) (i : Fin (n + 2)) :
    tupleFace K (x ∘ i.succAbove) (hx.comp (Fin.strictMono_succAbove i).injective)
        (tupleImage_delete_mem K x hk i) = deletedFace K n (tupleFace K x hx hk) i := by
  apply Subtype.ext
  change Finset.univ.image (x ∘ i.succAbove) =
    (Finset.univ.image x).erase
      ((tupleFace K x hx hk).1.orderEmbOfFin (tupleFace K x hx hk).2.2 i)
  rw [tupleFace_enumeration K x hx hk hm]
  exact tupleImage_delete x hx i

private theorem boundary_orientedTuple_of_monotone (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 2) → V)
    (hx : Function.Injective x) (hk : Finset.univ.image x ∈ K) (hm : Monotone x) :
    boundary K R n (orientedTuple K R x) = tupleBoundarySum K R x := by
  rw [orientedTuple_of_monotone K R x hx hk hm, boundary_single, one_smul]
  unfold tupleBoundarySum
  apply Finset.sum_congr rfl
  intro i _
  rw [orientedTuple_of_monotone K R _ (hx.comp (Fin.strictMono_succAbove i).injective)
    (tupleImage_delete_mem K x hk i) (hm.comp (Fin.strictMono_succAbove i).monotone),
    tupleFace_delete K x hx hk hm i]
  simp [Finsupp.smul_single]

/-- The actual signed boundary is the alternating deletion sum, including repeated vertices. -/
theorem boundary_orientedTuple (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (x : Fin (n + 2) → V)
    (hk : Finset.univ.image x ∈ K) :
    boundary K R n (orientedTuple K R x) = tupleBoundarySum K R x := by
  by_cases hx : Function.Injective x
  · let p := Tuple.sort x
    have hxp := hx.comp p.injective
    have hkp : Finset.univ.image (x ∘ p) ∈ K := by rwa [tupleImage_perm]
    have h := boundary_orientedTuple_of_monotone K R (x ∘ p) hxp hkp
      (Tuple.monotone_sort x)
    rw [orientedTuple_comp_perm, map_zsmul, tupleBoundarySum_comp_perm] at h
    have hs : (Equiv.Perm.sign p : ℤ) * (Equiv.Perm.sign p : ℤ) = 1 := by
      simp
    have h' := congrArg (fun z : Chain K R n => (Equiv.Perm.sign p : ℤ) • z) h
    simpa only [smul_smul, hs, one_smul] using h'
  · rw [orientedTuple_of_not_injective K R x hx, map_zero,
      tupleBoundarySum_eq_zero_of_not_injective K R x hx]

/-- The image-face enumeration is the sorted version of the original tuple. -/
theorem tupleFace_sorted_enumeration (K : PreAbstractSimplicialComplex V)
    {n : ℕ} (x : Fin (n + 1) → V) (hx : Function.Injective x)
    (hk : Finset.univ.image x ∈ K) :
    ⇑((tupleFace K x hx hk).1.orderEmbOfFin (tupleFace K x hx hk).2.2) =
      x ∘ Tuple.sort x := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image.mpr ⟨Tuple.sort x i, Finset.mem_univ _, rfl⟩
  · exact (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)

/-- The increasing enumeration of a present face is its unit oriented chain. -/
theorem orientedTuple_face (K : PreAbstractSimplicialComplex V)
    (R : Type v) [Ring R] {n : ℕ} (s : Face K n) :
    orientedTuple K R (s.1.orderEmbOfFin s.2.2) = Finsupp.single s (1 : R) := by
  have hk : Finset.univ.image (s.1.orderEmbOfFin s.2.2) ∈ K := by
    simpa only [Finset.image_orderEmbOfFin_univ] using s.2.1
  rw [orientedTuple_of_monotone K R _ (s.1.orderEmbOfFin s.2.2).injective hk
    (s.1.orderEmbOfFin s.2.2).monotone]
  congr 1
  exact Subtype.ext (Finset.image_orderEmbOfFin_univ s.1 s.2.2)

end
end TDA.Simplicial
