import TDA.Persistence.HookMultisetBottleneck
import TDA.Persistence.RankSchanuelUnshifted
import TDA.Persistence.FinitePresentationIndexLift

/-!
# Signed hook bottleneck stability

For two certified minimal resolutions, the actual unshifted Schanuel
biproducts have finite hook-sum presentations. Their tag multisets are the
cross-sign sums of the two parity-separated signed hook barcodes. The existing
finite hook matching theorem then gives the squared stability bound for the
actual signed multisets under the original finite-presentation hypotheses.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits CoordinateShift
open scoped TDA.Persistence NNReal ENNReal ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The signed bottleneck dissimilarity compares the two cross-sign sums and
keeps positive and negative hook occurrences separate. -/
noncomputable def signedHookBottleneckDissimilarity
    (C D : SignedHookBarcode n) : ℝ≥0∞ :=
  hookMultisetBottleneckDistance (k := k)
    (C.positive + D.negative) (D.positive + C.negative)

private theorem sum_fin_evenHookDegrees (L : ℕ)
    (f : ℕ → Multiset (RealHookTag (n := n))) :
    (∑ j : Fin L, if Even j.val then f j.val else 0) =
      ∑ j ∈ evenHookDegrees L, f j := by
  classical
  change (∑ j ∈ (Finset.univ : Finset (Fin L)),
      if Even j.val then f j.val else 0) = _
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, evenHookDegrees,
      Finset.mem_range] at hj ⊢
    exact ⟨j.isLt, hj⟩
  · intro j hj j' hj' heq
    exact Fin.ext heq
  · intro a ha
    simp only [evenHookDegrees, Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
    simp [evenHookDegrees, ha]
  · intro j hj
    rfl

private theorem sum_fin_oddHookDegrees (L : ℕ)
    (f : ℕ → Multiset (RealHookTag (n := n))) :
    (∑ j : Fin L, if Odd j.val then f j.val else 0) =
      ∑ j ∈ oddHookDegrees L, f j := by
  classical
  change (∑ j ∈ (Finset.univ : Finset (Fin L)),
      if Odd j.val then f j.val else 0) = _
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, oddHookDegrees,
      Finset.mem_range] at hj ⊢
    exact ⟨j.isLt, hj⟩
  · intro j hj j' hj' heq
    exact Fin.ext heq
  · intro a ha
    simp only [oddHookDegrees, Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
    simp [oddHookDegrees, ha]
  · intro j hj
    rfl

private theorem sum_fin_alternatingHookBetti (L : ℕ)
    (f g : ℕ → Multiset (RealHookTag (n := n))) :
    (∑ j : Fin L, if Even j.val then f j.val else g j.val) =
      (∑ j ∈ evenHookDegrees L, f j) +
        ∑ j ∈ oddHookDegrees L, g j := by
  classical
  have hsplit (j : Fin L) :
      (if Even j.val then f j.val else g j.val) =
        (if Even j.val then f j.val else 0) +
          (if Odd j.val then g j.val else 0) := by
    by_cases he : Even j.val
    · have ho : ¬ Odd j.val := by
        intro ho
        exact (Nat.not_even_iff_odd.mpr ho) he
      simp [he, ho]
    · have ho : Odd j.val := Nat.not_even_iff_odd.mp he
      simp [he, ho]
  calc
    (∑ j : Fin L, if Even j.val then f j.val else g j.val) =
        ∑ j : Fin L,
          ((if Even j.val then f j.val else 0) +
            (if Odd j.val then g j.val else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hsplit j
    _ = (∑ j : Fin L, if Even j.val then f j.val else 0) +
          ∑ j : Fin L, if Odd j.val then g j.val else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j ∈ evenHookDegrees L, f j) +
          ∑ j ∈ oddHookDegrees L, g j := by
      rw [sum_fin_evenHookDegrees, sum_fin_oddHookDegrees]

private theorem evenHookBetti_extend_to
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    {L : ℕ} (hL : R.resolution.length ≤ L) :
    (∑ j ∈ evenHookDegrees L,
      R.hookBettiMultiset (k := k) (n := n) M hM j) =
      R.evenHookBetti (k := k) (n := n) M hM := by
  classical
  unfold MinimalFiniteRankProjectiveResolution.evenHookBetti
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [evenHookDegrees, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 hL, hj.2⟩
  · intro j hj hjR
    simp only [evenHookDegrees, Finset.mem_filter, Finset.mem_range] at hj hjR
    have hnot : ¬ j < R.resolution.length := fun hlt => hjR ⟨hlt, hj.2⟩
    exact R.hookBettiMultiset_eq_zero_of_length_le M hM (Nat.le_of_not_gt hnot)

private theorem oddHookBetti_extend_to
    (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    {L : ℕ} (hL : R.resolution.length ≤ L) :
    (∑ j ∈ oddHookDegrees L,
      R.hookBettiMultiset (k := k) (n := n) M hM j) =
      R.oddHookBetti (k := k) (n := n) M hM := by
  classical
  unfold MinimalFiniteRankProjectiveResolution.oddHookBetti
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [oddHookDegrees, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 hL, hj.2⟩
  · intro j hj hjR
    simp only [oddHookDegrees, Finset.mem_filter, Finset.mem_range] at hj hjR
    have hnot : ¬ j < R.resolution.length := fun hlt => hjR ⟨hlt, hj.2⟩
    exact R.hookBettiMultiset_eq_zero_of_length_le M hM (Nat.le_of_not_gt hnot)

/-- A finite hook-sum presentation of the actual unshifted Schanuel left
biproduct. Its occurrences are flattened from the supplied minimal-resolution
term presentations. -/
noncomputable def unshiftedSchanuelLeftHookPresentation
    (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N)) :
    FiniteHookSumPresentation (k := k) (n := n)
      (unshiftedSchanuelLeftBiproduct R.resolution S.resolution) := by
  classical
  let L := max R.resolution.length S.resolution.length
  let X : Fin L → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => if Even j.val then R.termAt j.val else S.termAt j.val
  let P : ∀ j, FiniteHookSumPresentation (k := k) (n := n) (X j) := fun j =>
    if he : Even j.val then
      by
        simpa only [X, if_pos he] using
          (Classical.choice (R.exists_hook_sum_presentation (k := k) (n := n)
            M hM j.val))
    else
      by
        simpa only [X, if_neg he] using
          (Classical.choice (S.exists_hook_sum_presentation (k := k) (n := n)
            N hN j.val))
  let eTerm : ∀ j, X j ≅ unshiftedSchanuelLeftSummand R.resolution S.resolution j :=
    fun j => by
      by_cases he : Even j.val
      · simpa [X, unshiftedSchanuelLeftSummand, he] using
          (eqToIso (R.termAt_eq_resolution_termAt j.val))
      · simpa [X, unshiftedSchanuelLeftSummand, he] using
          (eqToIso (S.termAt_eq_resolution_termAt j.val))
  let eTotal : (⨁ X) ≅ unshiftedSchanuelLeftBiproduct R.resolution S.resolution :=
    biproduct.mapIso eTerm
  let flat := FiniteHookSumPresentation.biproduct (k := k) (n := n) X P
  exact ⟨flat.count, flat.tag, eTotal.symm.trans flat.iso⟩

/-- The left unshifted Schanuel presentation has exactly the positive hooks of
`R` together with the negative hooks of `S`, counted as a multiset. -/
theorem unshiftedSchanuelLeftHookPresentation_tagMultiset
    (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N)) :
    hookTagMultiset
        (unshiftedSchanuelLeftHookPresentation M N hM hN R S).tag =
      (R.signedHookBarcode (k := k) (n := n) M hM).positive +
        (S.signedHookBarcode (k := k) (n := n) N hN).negative := by
  classical
  let L := max R.resolution.length S.resolution.length
  let X : Fin L → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => if Even j.val then R.termAt j.val else S.termAt j.val
  let P : ∀ j, FiniteHookSumPresentation (k := k) (n := n) (X j) := fun j =>
    if he : Even j.val then
      by
        simpa only [X, if_pos he] using
          (Classical.choice (R.exists_hook_sum_presentation
            (k := k) (n := n) M hM j.val))
    else
      by
        simpa only [X, if_neg he] using
          (Classical.choice (S.exists_hook_sum_presentation
            (k := k) (n := n) N hN j.val))
  have hflat := FiniteHookSumPresentation.hookTagMultiset_biproduct
    (k := k) (n := n) X P
  have hterm (j : Fin L) :
      hookTagMultiset (P j).tag =
        if Even j.val then
          R.hookBettiMultiset (k := k) (n := n) M hM j.val
        else S.hookBettiMultiset (k := k) (n := n) N hN j.val := by
    by_cases he : Even j.val
    · simp only [if_pos he]
      have hX : X j = R.termAt j.val := by simp [X, he]
      let Q : FiniteHookSumPresentation (k := k) (n := n) (R.termAt j.val) :=
        ⟨(P j).count, (P j).tag, (eqToIso hX).symm.trans (P j).iso⟩
      exact (R.hookBettiMultiset_eq_tagMultiset M hM j.val Q).symm
    · simp only [if_neg he]
      have hX : X j = S.termAt j.val := by simp [X, he]
      let Q : FiniteHookSumPresentation (k := k) (n := n) (S.termAt j.val) :=
        ⟨(P j).count, (P j).tag, (eqToIso hX).symm.trans (P j).iso⟩
      exact (S.hookBettiMultiset_eq_tagMultiset N hN j.val Q).symm
  have hsum :
      (∑ j : Fin L, hookTagMultiset (P j).tag) =
        ∑ j : Fin L, if Even j.val then
          R.hookBettiMultiset (k := k) (n := n) M hM j.val
        else S.hookBettiMultiset (k := k) (n := n) N hN j.val := by
    apply Finset.sum_congr rfl
    intro j _
    exact hterm j
  change hookTagMultiset
    (FiniteHookSumPresentation.biproduct (k := k) (n := n) X P).tag = _
  let hLr : R.resolution.length ≤ L := Nat.le_max_left _ _
  let hLs : S.resolution.length ≤ L := Nat.le_max_right _ _
  calc
    hookTagMultiset (FiniteHookSumPresentation.biproduct (k := k) (n := n) X P).tag =
        ∑ j : Fin L, hookTagMultiset (P j).tag := hflat
    _ = ∑ j : Fin L, if Even j.val then
          R.hookBettiMultiset (k := k) (n := n) M hM j.val
        else S.hookBettiMultiset (k := k) (n := n) N hN j.val := hsum
    _ = R.evenHookBetti (k := k) (n := n) M hM +
          S.oddHookBetti (k := k) (n := n) N hN := by
      rw [sum_fin_alternatingHookBetti,
        evenHookBetti_extend_to M hM R hLr,
        oddHookBetti_extend_to N hN S hLs]

/-- A finite hook-sum presentation of the actual exchanged unshifted Schanuel
biproduct. -/
noncomputable def unshiftedSchanuelRightHookPresentation
    (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N)) :
    FiniteHookSumPresentation (k := k) (n := n)
      (unshiftedSchanuelRightBiproduct R.resolution S.resolution) := by
  classical
  let L := max R.resolution.length S.resolution.length
  let X : Fin L → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => if Even j.val then S.termAt j.val else R.termAt j.val
  let P : ∀ j, FiniteHookSumPresentation (k := k) (n := n) (X j) := fun j =>
    if he : Even j.val then
      by
        simpa only [X, if_pos he] using
          (Classical.choice (S.exists_hook_sum_presentation (k := k) (n := n)
            N hN j.val))
    else
      by
        simpa only [X, if_neg he] using
          (Classical.choice (R.exists_hook_sum_presentation (k := k) (n := n)
            M hM j.val))
  let eTerm : ∀ j, X j ≅ unshiftedSchanuelRightSummand R.resolution S.resolution j :=
    fun j => by
      by_cases he : Even j.val
      · simpa [X, unshiftedSchanuelRightSummand, he] using
          (eqToIso (S.termAt_eq_resolution_termAt j.val))
      · simpa [X, unshiftedSchanuelRightSummand, he] using
          (eqToIso (R.termAt_eq_resolution_termAt j.val))
  let eTotal : (⨁ X) ≅ unshiftedSchanuelRightBiproduct R.resolution S.resolution :=
    biproduct.mapIso eTerm
  let flat := FiniteHookSumPresentation.biproduct (k := k) (n := n) X P
  exact ⟨flat.count, flat.tag, eTotal.symm.trans flat.iso⟩

/-- The exchanged unshifted Schanuel presentation has exactly the positive
hooks of `S` and negative hooks of `R`, including every repeated occurrence. -/
theorem unshiftedSchanuelRightHookPresentation_tagMultiset
    (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N)) :
    hookTagMultiset
        (unshiftedSchanuelRightHookPresentation M N hM hN R S).tag =
      (S.signedHookBarcode (k := k) (n := n) N hN).positive +
        (R.signedHookBarcode (k := k) (n := n) M hM).negative := by
  classical
  let L := max R.resolution.length S.resolution.length
  let X : Fin L → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun j => if Even j.val then S.termAt j.val else R.termAt j.val
  let P : ∀ j, FiniteHookSumPresentation (k := k) (n := n) (X j) := fun j =>
    if he : Even j.val then
      by
        simpa only [X, if_pos he] using
          (Classical.choice (S.exists_hook_sum_presentation
            (k := k) (n := n) N hN j.val))
    else
      by
        simpa only [X, if_neg he] using
          (Classical.choice (R.exists_hook_sum_presentation
            (k := k) (n := n) M hM j.val))
  have hflat := FiniteHookSumPresentation.hookTagMultiset_biproduct
    (k := k) (n := n) X P
  have hterm (j : Fin L) :
      hookTagMultiset (P j).tag =
        if Even j.val then
          S.hookBettiMultiset (k := k) (n := n) N hN j.val
        else R.hookBettiMultiset (k := k) (n := n) M hM j.val := by
    by_cases he : Even j.val
    · simp only [if_pos he]
      have hX : X j = S.termAt j.val := by simp [X, he]
      let Q : FiniteHookSumPresentation (k := k) (n := n) (S.termAt j.val) :=
        ⟨(P j).count, (P j).tag, (eqToIso hX).symm.trans (P j).iso⟩
      exact (S.hookBettiMultiset_eq_tagMultiset N hN j.val Q).symm
    · simp only [if_neg he]
      have hX : X j = R.termAt j.val := by simp [X, he]
      let Q : FiniteHookSumPresentation (k := k) (n := n) (R.termAt j.val) :=
        ⟨(P j).count, (P j).tag, (eqToIso hX).symm.trans (P j).iso⟩
      exact (R.hookBettiMultiset_eq_tagMultiset M hM j.val Q).symm
  have hsum :
      (∑ j : Fin L, hookTagMultiset (P j).tag) =
        ∑ j : Fin L, if Even j.val then
          S.hookBettiMultiset (k := k) (n := n) N hN j.val
        else R.hookBettiMultiset (k := k) (n := n) M hM j.val := by
    apply Finset.sum_congr rfl
    intro j _
    exact hterm j
  have hsum' :
      (∑ j : Fin L, if Even j.val then
      S.hookBettiMultiset (k := k) (n := n) N hN j.val
      else R.hookBettiMultiset (k := k) (n := n) M hM j.val) =
        R.oddHookBetti (k := k) (n := n) M hM +
          S.evenHookBetti (k := k) (n := n) N hN := by
    rw [sum_fin_alternatingHookBetti]
    have hLr : R.resolution.length ≤ L := Nat.le_max_left _ _
    have hLs : S.resolution.length ≤ L := Nat.le_max_right _ _
    rw [oddHookBetti_extend_to M hM R hLr,
      evenHookBetti_extend_to N hN S hLs]
    ac_rfl
  change hookTagMultiset
    (FiniteHookSumPresentation.biproduct (k := k) (n := n) X P).tag = _
  calc
    hookTagMultiset (FiniteHookSumPresentation.biproduct (k := k) (n := n) X P).tag =
        ∑ j : Fin L, hookTagMultiset (P j).tag := hflat
    _ = ∑ j : Fin L, if Even j.val then
          S.hookBettiMultiset (k := k) (n := n) N hN j.val
        else R.hookBettiMultiset (k := k) (n := n) M hM j.val := hsum
    _ = R.oddHookBetti (k := k) (n := n) M hM +
          S.evenHookBetti (k := k) (n := n) N hN := hsum'
    _ = (S.signedHookBarcode (k := k) (n := n) N hN).positive +
          (R.signedHookBarcode (k := k) (n := n) M hM).negative := by
      simp [MinimalFiniteRankProjectiveResolution.signedHookBarcode]
      ac_rfl

/-- An actual interleaving of originally finitely presented modules induces
an actual occurrence matching of the signed hook multisets at radius
`(2*n-1)^2 * ε`. The presentations and occurrences are constructed inside the
proof; no decompositions or matching certificates are caller inputs. -/
theorem finitelyPresented_exists_signedHookMultisetMatching
    (hn : 1 ≤ n) (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N))
    (ε : ℝ≥0) (I : CoordinateInterleaving ε M N) :
    HasMultisetMatching (k := k)
      ((((2 * n - 1 : ℕ) : ℝ≥0) ^ 2) * ε)
      (((R.signedHookBarcode (k := k) (n := n) M hM).positive) +
        (S.signedHookBarcode (k := k) (n := n) N hN).negative)
      (((S.signedHookBarcode (k := k) (n := n) N hN).positive) +
        (R.signedHookBarcode (k := k) (n := n) M hM).negative) := by
  classical
  let P := unshiftedSchanuelLeftHookPresentation M N hM hN R S
  let Q := unshiftedSchanuelRightHookPresentation M N hM hN R S
  let hnn : 0 < n := by omega
  let iSum := finitelyPresented_unshiftedSchanuel_interleaving
    hn M N hM hN R S ε I
  let iHooks := iSum.congr P.iso Q.iso
  obtain ⟨U, hU⟩ := HookMatching.exists_matching hnn P.tag Q.tag
    (RectangleStabilityGeometry.stabilityRadius n ε) iHooks
  have hwidth :
      RectangleStabilityGeometry.stabilityRadius n
          (RectangleStabilityGeometry.stabilityRadius n ε) =
        (((2 * n - 1 : ℕ) : ℝ≥0) ^ 2) * ε := by
    simp [RectangleStabilityGeometry.stabilityRadius]
    ring
  have hMatch : HookMatching.IsMatching (k := k)
      ((((2 * n - 1 : ℕ) : ℝ≥0) ^ 2) * ε) P.tag Q.tag U := by
    rw [← hwidth]
    exact hU
  exact HasMultisetMatching.intro P.tag Q.tag
    (unshiftedSchanuelLeftHookPresentation_tagMultiset M N hM hN R S)
    (unshiftedSchanuelRightHookPresentation_tagMultiset M N hM hN R S)
    U hMatch

/-- For any fixed certified minimal resolutions, the signed bottleneck
dissimilarity is bounded by the squared coefficient times the original
extended interleaving distance, with no attainment or finiteness assumption. -/
theorem finitelyPresented_signedHookBottleneckDistance_le
    (hn : 1 ≤ n) (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M))
    (S : MinimalFiniteRankProjectiveResolution (k := k) (M := N)) :
    signedHookBottleneckDissimilarity (k := k)
        (R.signedHookBarcode (k := k) (n := n) M hM)
        (S.signedHookBarcode (k := k) (n := n) N hN) ≤
      (((2 * n - 1 : ℕ) : ℝ≥0∞) ^ 2) * coordinateInterleavingDistance M N := by
  have hc : (2 * n - 1 : ℕ) ≠ 0 := by omega
  have hc0 : (((2 * n - 1 : ℕ) : ℝ≥0∞) ^ 2) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 hc)
  have hct : (((2 * n - 1 : ℕ) : ℝ≥0∞) ^ 2) ≠ ⊤ := by
    exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  change hookMultisetBottleneckDistance (k := k)
      ((R.signedHookBarcode (k := k) (n := n) M hM).positive +
        (S.signedHookBarcode (k := k) (n := n) N hN).negative)
      ((S.signedHookBarcode (k := k) (n := n) N hN).positive +
        (R.signedHookBarcode (k := k) (n := n) M hM).negative) ≤
    (((2 * n - 1 : ℕ) : ℝ≥0∞) ^ 2) *
      (⨅ ε : ℝ≥0, ⨅ (_ : Nonempty (CoordinateInterleaving ε M N)),
        (ε : ℝ≥0∞))
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro ε
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  apply le_iInf
  intro hI
  obtain ⟨I⟩ := hI
  have hmatch := finitelyPresented_exists_signedHookMultisetMatching
    hn M N hM hN R S ε I
  have hdist := hookMultisetBottleneckDistance_le_of_matching hmatch
  simpa [ENNReal.coe_mul, ENNReal.coe_pow, pow_two, mul_assoc] using hdist

/-- The module-level signed hook barcode is obtained from the proved existence
of a minimal finite rank-projective resolution. -/
noncomputable def finitelyPresentedSignedHookBarcode
    (hn : 1 ≤ n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M) :
    SignedHookBarcode n :=
  (Classical.choice
    (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      hn M hM)).signedHookBarcode (k := k) (n := n) M hM

/-- The module barcode choice agrees with every supplied certified minimal
resolution, by the existing signed-hook choice-independence theorem. -/
theorem finitelyPresentedSignedHookBarcode_eq
    (hn : 1 ≤ n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    finitelyPresentedSignedHookBarcode hn M hM =
      R.signedHookBarcode (k := k) (n := n) M hM := by
  change (Classical.choice
      (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
        hn M hM)).signedHookBarcode (k := k) (n := n) M hM =
    R.signedHookBarcode (k := k) (n := n) M hM
  exact (R.signedHookBarcode_eq M hM
    (Classical.choice
      (FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
        hn M hM))).symm

/-- Original finite-presentation hypotheses suffice for the squared signed
stability bound, without caller-supplied resolutions or matching certificates. -/
theorem finitelyPresented_moduleSignedHookBottleneckDistance_le
    (hn : 1 ≤ n) (M N : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) M)
    (hN : GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin n → ℝ) N) :
    signedHookBottleneckDissimilarity (k := k)
        (finitelyPresentedSignedHookBarcode hn M hM)
        (finitelyPresentedSignedHookBarcode hn N hN) ≤
      (((2 * n - 1 : ℕ) : ℝ≥0∞) ^ 2) * coordinateInterleavingDistance M N := by
  obtain ⟨R⟩ :=
    FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      hn M hM
  obtain ⟨S⟩ :=
    FiniteRankProjectiveResolution.finitelyPresented_exists_minimalFiniteRankProjectiveResolution
      hn N hN
  have hfixed := finitelyPresented_signedHookBottleneckDistance_le hn M N hM hN R S
  simpa [finitelyPresentedSignedHookBarcode_eq hn M hM R,
    finitelyPresentedSignedHookBarcode_eq hn N hN S] using hfixed

end TDA.Persistence
