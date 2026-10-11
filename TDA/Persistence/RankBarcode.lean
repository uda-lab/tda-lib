import TDA.Persistence.RankReconstruction
import TDA.Persistence.FiniteBarcode

universe u
namespace TDA.Persistence
open scoped BigOperators
variable {N : ℕ} {k : Type u} [Field k]
variable (M : PModule.{u,0,u} k (Fin N))
variable [∀ i : Fin N, FiniteDimensional k (M.obj i)]

noncomputable def rankBarcode : Multiset (FiniteInterval N) := by
  classical
  exact ∑ b : Fin N, ∑ d : Fin (N + 1),
    if h : b.val < d.val then
      Multiset.replicate (moduleMultiplicityInteger M b.val d.val).toNat
        ⟨b.val, d.val, h, by omega⟩
    else 0

private theorem countP_finset_sum {α ι : Type*} (p : α → Prop) [DecidablePred p]
    (s : Finset ι) (f : ι → Multiset α) :
    (∑ x ∈ s, f x).countP p = ∑ x ∈ s, (f x).countP p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, Multiset.countP_add, ih]

private theorem countP_replicate_interval {N : ℕ} (I : FiniteInterval N) (n b d : ℕ) :
    (Multiset.replicate n I).countP (fun J => J.birth = b ∧ J.death = d) =
      if I.birth = b ∧ I.death = d then n else 0 := by
  classical
  induction n with
  | zero => simp
  | succ n ih => simp [Multiset.replicate_succ, Multiset.countP_cons, ih]; split_ifs <;> omega

private theorem rankBarcode_count (b d : ℕ) (hbd : b < d) (hd : d ≤ N) :
    barcodeMultiplicity (rankBarcode M) b d =
      (moduleMultiplicityInteger M b d).toNat := by
  classical
  let fb : Fin N := ⟨b, by omega⟩
  let fd : Fin (N + 1) := ⟨d, by omega⟩
  unfold barcodeMultiplicity rankBarcode
  rw [countP_finset_sum]
  rw [Finset.sum_eq_single fb]
  · rw [countP_finset_sum, Finset.sum_eq_single fd]
    · simpa [fb, fd, hbd] using
        (countP_replicate_interval
          (⟨b, d, hbd, hd⟩ : FiniteInterval N)
          (moduleMultiplicityInteger M b d).toNat b d)
    · intro y hy hne
      by_cases h : fb.val < y.val
      · simp [h, countP_replicate_interval]
        have : y.val ≠ d := by
          intro he
          apply hne
          exact Fin.ext he
        simp [this]
      · simp [h]
    · simp [fd]
  · intro x hx hne
    rw [countP_finset_sum]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases h : x.val < y.val
    · simp [h, countP_replicate_interval]
      have : x.val ≠ b := by
        intro he
        apply hne
        exact Fin.ext he
      simp [this]
    · simp [h]
  · simp [fb]

theorem barcodeMultiplicity_rankBarcode (b d : ℕ)
    (hbd : b < d) (hd : d ≤ N) :
    (barcodeMultiplicity (rankBarcode M) b d : ℤ) =
      moduleMultiplicityInteger M b d := by
  rw [rankBarcode_count M b d hbd hd]
  exact Int.toNat_of_nonneg (moduleMultiplicityInteger_nonneg M b d hbd hd)

private theorem moduleRankInteger_barcodeModule (B : Multiset (FiniteInterval N))
    (i j : ℤ) :
    moduleRankInteger (barcodeModule (k := k) B) i j =
      barcodeRankInteger (k := k) B i j := by
  classical
  unfold moduleRankInteger barcodeRankInteger
  split_ifs with h
  · rfl
  · rfl

private theorem moduleMultiplicityInteger_barcodeModule
    (B : Multiset (FiniteInterval N)) (b d : ℕ)
    (hbd : b < d) (hd : d ≤ N) :
    moduleMultiplicityInteger (barcodeModule (k := k) B) b d =
      (barcodeMultiplicity B b d : ℤ) := by
  rw [multiplicity_eq_rank_difference (k := k) B b d hbd hd]
  simp only [moduleMultiplicityInteger, moduleRankInteger_barcodeModule]

private theorem rankBarcode_count_eq (B C : Multiset (FiniteInterval N))
    (h : ∀ b d, b < d → d ≤ N → barcodeMultiplicity B b d = barcodeMultiplicity C b d) :
    B = C := by
  classical
  apply Multiset.ext'
  intro I
  have hpred (J : FiniteInterval N) :
      (J.birth = I.birth ∧ J.death = I.death) ↔ J = I := by
    constructor
    · rintro ⟨hb, hd⟩
      cases J with
      | mk jb jd hjb hjd =>
        cases I with
        | mk ib id hib hid => simp_all
    · intro h
      subst J
      exact ⟨rfl, rfl⟩
  have he := h I.birth I.death I.birth_lt_death I.death_le_size
  have hB : B.count I = barcodeMultiplicity B I.birth I.death := by
    simpa [barcodeMultiplicity, Multiset.count, eq_comm] using
      (Multiset.countP_congr (s := B) (s' := B) rfl
        (fun J _ => propext (hpred J)))
  have hC : C.count I = barcodeMultiplicity C I.birth I.death := by
    simpa [barcodeMultiplicity, Multiset.count, eq_comm] using
      (Multiset.countP_congr (s := C) (s' := C) rfl
        (fun J _ => propext (hpred J)))
  rw [hB, hC, he]

private theorem rankBarcode_integer_ranks (i j : Fin N) (hij : i ≤ j) :
    (structureMapRank (barcodeModule (k := k) (rankBarcode M)) i j hij : ℤ) =
      (structureMapRank M i j hij : ℤ) := by
  let B := rankBarcode M
  have hB := structureMapRank_eq_sum_moduleMultiplicityInteger
    (barcodeModule (k := k) B) i j hij
  have hM := structureMapRank_eq_sum_moduleMultiplicityInteger M i j hij
  rw [hB, hM]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  have hbd : b < d := by
    have hbi : b ≤ i.val := Finset.mem_range_succ_iff.mp hb
    have hjd : j.val < d := Finset.mem_Ioc.mp hd |>.1
    have hij' := Fin.le_iff_val_le_val.mp hij
    omega
  have hdN : d ≤ N := (Finset.mem_Ioc.mp hd).2
  rw [moduleMultiplicityInteger_barcodeModule B b d hbd hdN,
    barcodeMultiplicity_rankBarcode M b d hbd hdN]

theorem structureMapRank_rankBarcode (i j : Fin N) (hij : i ≤ j) :
    structureMapRank (barcodeModule (k := k) (rankBarcode M)) i j hij =
      structureMapRank M i j hij := by
  exact_mod_cast rankBarcode_integer_ranks M i j hij

theorem rankBarcode_barcodeModule (B : Multiset (FiniteInterval N)) :
    rankBarcode (barcodeModule (k := k) B) = B := by
  apply rankBarcode_count_eq
  intro b d hbd hd
  have hnew := barcodeMultiplicity_rankBarcode (barcodeModule (k := k) B) b d hbd hd
  rw [moduleMultiplicityInteger_barcodeModule B b d hbd hd] at hnew
  exact_mod_cast hnew

theorem rankBarcode_eq_iff
    (L : PModule.{u,0,u} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (L.obj i)] :
    rankBarcode M = rankBarcode L ↔
      ∀ (i j : Fin N) (hij : i ≤ j),
        structureMapRank M i j hij = structureMapRank L i j hij := by
  constructor
  · intro h i j hij
    calc
      structureMapRank M i j hij =
          structureMapRank (barcodeModule (k := k) (rankBarcode M)) i j hij :=
        (structureMapRank_rankBarcode M i j hij).symm
      _ = structureMapRank (barcodeModule (k := k) (rankBarcode L)) i j hij := by rw [h]
      _ = structureMapRank L i j hij := structureMapRank_rankBarcode L i j hij
  · intro h
    apply rankBarcode_count_eq
    intro b d hbd hd
    have heq : moduleMultiplicityInteger M b d = moduleMultiplicityInteger L b d := by
      have hrank : ∀ i j, moduleRankInteger M i j = moduleRankInteger L i j := by
        intro i j
        classical
        unfold moduleRankInteger
        split_ifs with hv
        · have hi := Int.toNat_of_nonneg hv.1
          have hj := Int.toNat_of_nonneg (hv.1.trans hv.2.1)
          have hle : i.toNat ≤ j.toNat := by omega
          have hr := h ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩
            (Fin.le_iff_val_le_val.mpr hle)
          simpa using congrArg (fun n : ℕ => (n : ℤ)) hr
        · rfl
      simp only [moduleMultiplicityInteger, hrank]
    have hm := barcodeMultiplicity_rankBarcode M b d hbd hd
    have hl := barcodeMultiplicity_rankBarcode L b d hbd hd
    exact_mod_cast hm.trans (heq.trans hl.symm)

end TDA.Persistence
