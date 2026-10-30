import TDA.Persistence.FinitePresentationRankProjectiveClassification
import TDA.Persistence.FiniteRankProjectiveResolutionUniqueness
import TDA.Persistence.CoordinateGridHook

/-!
# Hook multisets of minimal rank-projective resolutions

Finite-grid minimal resolutions are built from finite occurrence-indexed hook
sums. The actual grid Kan comparisons transport those occurrences to
real-coordinate hooks. Zero-padded termwise uniqueness and hook-sum
multiplicity uniqueness then make the degreewise multisets, and their separate
even and odd sums, independent of the chosen certified minimal resolution.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

/-- A finite-death endpoint pair or principal-upset birth in real coordinates. -/
abbrev RealHookTag :=
  FiniteRankProjectiveClassification.RankProjectiveHookTag (Fin n → ℝ)

/-- A finite hook-sum presentation records every summand occurrence. -/
structure FiniteHookSumPresentation
    (M : PModule.{u,0,u} k (Fin n → ℝ)) where
  count : ℕ
  tag : Fin count → RealHookTag (n := n)
  iso : M ≅ ⨁ fun i =>
    FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (tag i)

/-- The multiset of tags in a finite occurrence-indexed family. -/
def hookTagMultiset : ∀ {m : ℕ}, (Fin m → RealHookTag (n := n)) →
    Multiset (RealHookTag (n := n))
  | 0, _ => 0
  | m + 1, tag => {tag 0} + hookTagMultiset (fun i => tag i.succ)

/-- The recursive hook multiset is the multiset of the finite list of
occurrences. -/
theorem hookTagMultiset_eq_ofFn {m : ℕ}
    (tag : Fin m → RealHookTag (n := n)) :
    hookTagMultiset tag =
      (List.ofFn tag : Multiset (RealHookTag (n := n))) := by
  induction m with
  | zero => rfl
  | succ _ ih =>
      rw [hookTagMultiset, List.ofFn_succ, ih]
      rfl

/-- The recursive hook multiset is the image of the finite index multiset. -/
theorem hookTagMultiset_eq_map_univ {m : ℕ}
    (tag : Fin m → RealHookTag (n := n)) :
    hookTagMultiset tag = (Finset.univ : Finset (Fin m)).val.map tag := by
  rw [hookTagMultiset_eq_ofFn, List.ofFn_eq_map]
  rfl

@[simp] theorem hookTagMultiset_count {m : ℕ}
    (tag : Fin m → RealHookTag (n := n)) (c : RealHookTag (n := n)) :
    (hookTagMultiset tag).count c = Fintype.card {i : Fin m // tag i = c} := by
  classical
  induction m with
  | zero => simp [hookTagMultiset]
  | succ m ih =>
    have htail := ih (fun i : Fin m => tag i.succ)
    rw [hookTagMultiset, Multiset.count_add, Multiset.count_singleton,
      Fintype.card_subtype, Fin.card_filter_univ_succ']
    rw [Fintype.card_subtype] at htail
    rw [← htail]
    simp [eq_comm]

/-- The tag multiset depends only on the isomorphism class of its presented
module. Multiplicities are counted by occurrences, so repeated hooks are
retained. -/
theorem FiniteHookSumPresentation.tagMultiset_eq_of_iso
    {A B : PModule.{u,0,u} k (Fin n → ℝ)}
    (P : FiniteHookSumPresentation (k := k) (n := n) A)
    (Q : FiniteHookSumPresentation (k := k) (n := n) B) (e : A ≅ B) :
    hookTagMultiset P.tag = hookTagMultiset Q.tag := by
  ext c
  have hcount := GradedFree.rankProjectiveHookSum_multiplicity_unique_of_iso
    (k := k) (n := n) P.tag Q.tag
    ⟨P.iso.symm.trans (e.trans Q.iso)⟩ c
  simpa only [hookTagMultiset_count] using hcount

private def embedGridHookTag (G : CoordinateGrid n)
    (tag : FiniteRankProjectiveClassification.RankProjectiveHookTag G.Point) :
    RealHookTag (n := n) :=
  match tag with
  | .inl ab => .inl ⟨(G.embedding ab.val.1, G.embedding ab.val.2),
      G.embedding.strictMono ab.property⟩
  | .inr a => .inr (G.embedding a)

private noncomputable def embedGridHookTagLanIso (G : CoordinateGrid n)
    (tag : FiniteRankProjectiveClassification.RankProjectiveHookTag G.Point) :
    G.lan.obj (FiniteRankProjectiveClassification.rankProjectiveHookModule
      (k := k) tag) ≅
      FiniteRankProjectiveClassification.rankProjectiveHookModule
        (k := k) (embedGridHookTag G tag) := by
  cases tag with
  | inl ab => exact G.hookLanIso ab.val.1 ab.val.2
  | inr a => exact G.infinityLanIso a

namespace FiniteRankProjectiveResolution

/-- A finitely presented real-coordinate module has a certified minimal
resolution whose every zero-padded term is an actual finite sum of real hooks.
The witness is obtained from the constructed finite-grid resolution, carried
through its genuine Lan biproduct and hook isomorphisms, and then through the
presentation reconstruction. -/
theorem finitelyPresented_exists_minimal_resolution_with_hook_sum_terms
    (_hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M) :
    ∃ R : MinimalFiniteRankProjectiveResolution (k := k) (M := M),
      ∀ j, Nonempty (FiniteHookSumPresentation (k := k) (n := n) (R.termAt j)) := by
  classical
  obtain ⟨G, A, hA, ⟨e⟩⟩ := GradedFree.finitelyPresented_exists_pfd_finiteGridKan M hM
  obtain ⟨RGrid, hGrid⟩ :=
    FiniteRankProjectiveResolution.exists_minimalFiniteRankProjectiveResolution_with_hook_sum_terms_of_pfd_finitePoset
      A hA
  let RLan := G.lanMinimalFiniteRankProjectiveResolutionObj RGrid
  let R : MinimalFiniteRankProjectiveResolution (k := k) (M := M) := {
    resolution := RLan.resolution.ofIso e
    quotient_is_cover := RLan.quotient_is_cover
  }
  refine ⟨R, ?_⟩
  intro j
  by_cases hj : j < R.resolution.length
  · let i : Fin R.resolution.length := ⟨j, hj⟩
    obtain ⟨m, tagGrid, ⟨eGrid⟩⟩ := hGrid i
    let tagReal : Fin m → RealHookTag (n := n) :=
      fun r => embedGridHookTag G (tagGrid r)
    let eTerm : R.termAt j ≅ G.lan.obj (RGrid.resolution.term i) := by
      exact (eqToIso (R.termAt_eq hj)).trans
        (eqToIso (by rfl : R.resolution.term i = RLan.resolution.term i))
    let eHooks : G.lan.obj
          (⨁ fun r => FiniteRankProjectiveClassification.rankProjectiveHookModule
            (k := k) (tagGrid r)) ≅
        ⨁ fun r => FiniteRankProjectiveClassification.rankProjectiveHookModule
          (k := k) (tagReal r) :=
      (G.lanBiproductIso (fun r =>
        FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (tagGrid r))).trans
        (biproduct.mapIso (fun r => embedGridHookTagLanIso G (tagGrid r)))
    have eReal : R.termAt j ≅
        ⨁ fun r => FiniteRankProjectiveClassification.rankProjectiveHookModule
          (k := k) (tagReal r) := by
      calc
        R.termAt j ≅ G.lan.obj (RGrid.resolution.term i) := eTerm
        _ ≅ G.lan.obj (⨁ fun r =>
            FiniteRankProjectiveClassification.rankProjectiveHookModule
              (k := k) (tagGrid r)) := G.lan.mapIso eGrid
        _ ≅ ⨁ fun r => FiniteRankProjectiveClassification.rankProjectiveHookModule
            (k := k) (tagReal r) := eHooks
    exact ⟨⟨m, tagReal, eReal⟩⟩
  · have hle : R.resolution.length ≤ j := Nat.le_of_not_gt hj
    let emptyTag : Fin 0 → RealHookTag (n := n) := Fin.elim0
    have hEmpty : IsZero
        (⨁ fun i : Fin 0 =>
          FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (emptyTag i)) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply biproduct.hom_ext'
      intro i
      exact Fin.elim0 i
    have eEmpty : R.termAt j ≅
        ⨁ fun i : Fin 0 =>
          FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) (emptyTag i) := by
      rw [R.termAt_eq_zero hle]
      exact (isZero_zero _).isoZero.trans hEmpty.isoZero.symm
    exact ⟨⟨0, emptyTag, eEmpty⟩⟩

end FiniteRankProjectiveResolution

/-- Every zero-padded term of any certified minimal resolution of a finitely
presented real-coordinate module admits an actual finite hook-sum
presentation. The constructed resolution supplies the decomposition; the
termwise comparison theorem transports it to the given resolution. -/
theorem MinimalFiniteRankProjectiveResolution.exists_hook_sum_presentation
    (_hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    Nonempty (FiniteHookSumPresentation (k := k) (n := n) (R.termAt j)) := by
  obtain ⟨R₀, hR₀⟩ :=
    FiniteRankProjectiveResolution.finitelyPresented_exists_minimal_resolution_with_hook_sum_terms
      (k := k) (n := n) _hn M hM
  obtain ⟨e⟩ := R.termAt_nonempty_iso R₀ j
  obtain ⟨P⟩ := hR₀ j
  exact ⟨⟨P.count, P.tag, e.trans P.iso⟩⟩

/-- The degreewise finite hook multiset of a certified minimal resolution term.
Its construction uses choice, but the following theorem proves its value
independent of that choice and of the chosen resolution. -/
noncomputable def MinimalFiniteRankProjectiveResolution.hookBettiMultiset
    (_hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    Multiset (RealHookTag (n := n)) :=
  hookTagMultiset
    (Classical.choice (R.exists_hook_sum_presentation (k := k) (n := n) _hn M hM j)).tag

/-- Relate the chosen degreewise multiset to any supplied actual hook-sum
presentation, without unfolding the choice-based definition. -/
theorem MinimalFiniteRankProjectiveResolution.hookBettiMultiset_eq_tagMultiset
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ)
    (P : FiniteHookSumPresentation (k := k) (n := n) (R.termAt j)) :
    R.hookBettiMultiset (k := k) (n := n) hn M hM j =
      hookTagMultiset P.tag := by
  let Q := Classical.choice
    (R.exists_hook_sum_presentation (k := k) (n := n) hn M hM j)
  have h := Q.tagMultiset_eq_of_iso P (Iso.refl (R.termAt j))
  simpa [MinimalFiniteRankProjectiveResolution.hookBettiMultiset, Q] using h

/-- Degreewise hook multiplicities do not depend on the chosen minimal finite
resolution. This combines zero-padded term isomorphism with finite hook-sum
multiplicity uniqueness. -/
theorem MinimalFiniteRankProjectiveResolution.hookBettiMultiset_eq
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) (j : ℕ) :
    R.hookBettiMultiset (k := k) (n := n) hn M hM j =
      S.hookBettiMultiset (k := k) (n := n) hn M hM j := by
  let P := Classical.choice
    (R.exists_hook_sum_presentation (k := k) (n := n) hn M hM j)
  let Q := Classical.choice
    (S.exists_hook_sum_presentation (k := k) (n := n) hn M hM j)
  obtain ⟨e⟩ := R.termAt_nonempty_iso S j
  simpa [MinimalFiniteRankProjectiveResolution.hookBettiMultiset, P, Q] using
    P.tagMultiset_eq_of_iso Q e

/-- A zero-padded term beyond the actual resolution length has the empty hook
multiset. This makes the finite parity sums independent of raw resolution
length. -/
theorem MinimalFiniteRankProjectiveResolution.hookBettiMultiset_eq_zero_of_length_le
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) {j : ℕ}
    (hj : R.resolution.length ≤ j) :
    R.hookBettiMultiset (k := k) (n := n) hn M hM j = 0 := by
  let P := Classical.choice
    (R.exists_hook_sum_presentation (k := k) (n := n) hn M hM j)
  let emptyTag : Fin 0 → RealHookTag (n := n) := Fin.elim0
  have hEmpty : IsZero
      (⨁ fun i : Fin 0 =>
        FiniteRankProjectiveClassification.rankProjectiveHookModule
          (k := k) (emptyTag i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext'
    intro i
    exact Fin.elim0 i
  let Q : FiniteHookSumPresentation
      (k := k) (n := n) (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    ⟨0, emptyTag, (isZero_zero _).isoZero.trans hEmpty.isoZero.symm⟩
  have e : R.termAt j ≅ (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    eqToIso (R.termAt_eq_zero hj)
  have h := P.tagMultiset_eq_of_iso Q e
  simpa [MinimalFiniteRankProjectiveResolution.hookBettiMultiset,
    hookTagMultiset, P, Q] using h

/-- Any is-zero resolution term has no hook occurrences, including terms
vanishing because the module is already projective. -/
theorem MinimalFiniteRankProjectiveResolution.hookBettiMultiset_eq_zero_of_term_isZero
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) {j : ℕ}
    (hj : IsZero (R.termAt j)) :
    R.hookBettiMultiset (k := k) (n := n) hn M hM j = 0 := by
  let P := Classical.choice
    (R.exists_hook_sum_presentation (k := k) (n := n) hn M hM j)
  let emptyTag : Fin 0 → RealHookTag (n := n) := Fin.elim0
  have hEmpty : IsZero
      (⨁ fun i : Fin 0 =>
        FiniteRankProjectiveClassification.rankProjectiveHookModule
          (k := k) (emptyTag i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext'
    intro i
    exact Fin.elim0 i
  let Q : FiniteHookSumPresentation
      (k := k) (n := n) (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    ⟨0, emptyTag, (isZero_zero _).isoZero.trans hEmpty.isoZero.symm⟩
  have e : R.termAt j ≅ (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
    hj.isoZero
  have h := P.tagMultiset_eq_of_iso Q e
  simpa [MinimalFiniteRankProjectiveResolution.hookBettiMultiset,
    hookTagMultiset, P, Q] using h

/-- The even degree indices strictly below a finite resolution length. -/
def evenHookDegrees (L : ℕ) : Finset ℕ :=
  (Finset.range L).filter Even

/-- The odd degree indices strictly below a finite resolution length. -/
def oddHookDegrees (L : ℕ) : Finset ℕ :=
  (Finset.range L).filter Odd

/-- The sum of hook occurrences in even degrees of a zero-padded resolution. -/
noncomputable def MinimalFiniteRankProjectiveResolution.evenHookBetti
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    Multiset (RealHookTag (n := n)) :=
  ∑ j ∈ evenHookDegrees R.resolution.length,
    R.hookBettiMultiset (k := k) (n := n) hn M hM j

/-- The sum of hook occurrences in odd degrees of a zero-padded resolution. -/
noncomputable def MinimalFiniteRankProjectiveResolution.oddHookBetti
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    Multiset (RealHookTag (n := n)) :=
  ∑ j ∈ oddHookDegrees R.resolution.length,
    R.hookBettiMultiset (k := k) (n := n) hn M hM j

/-- The even-degree hook sum is independent of the chosen minimal resolution,
including when their raw lengths differ. -/
theorem MinimalFiniteRankProjectiveResolution.evenHookBetti_eq
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    R.evenHookBetti (k := k) (n := n) hn M hM =
      S.evenHookBetti (k := k) (n := n) hn M hM := by
  classical
  let L := max R.resolution.length S.resolution.length
  have hR : evenHookDegrees R.resolution.length ⊆ evenHookDegrees L := by
    intro j hj
    simp only [evenHookDegrees, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 (Nat.le_max_left _ _), hj.2⟩
  have hS : evenHookDegrees S.resolution.length ⊆ evenHookDegrees L := by
    intro j hj
    simp only [evenHookDegrees, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 (Nat.le_max_right _ _), hj.2⟩
  have hExtendR :
      (∑ j ∈ evenHookDegrees R.resolution.length,
        R.hookBettiMultiset (k := k) (n := n) hn M hM j) =
      ∑ j ∈ evenHookDegrees L,
        R.hookBettiMultiset (k := k) (n := n) hn M hM j := by
    apply Finset.sum_subset hR
    intro j hj hjR
    simp only [evenHookDegrees, Finset.mem_filter, Finset.mem_range] at hj hjR
    have hnot : ¬ j < R.resolution.length := fun hlt => hjR ⟨hlt, hj.2⟩
    exact R.hookBettiMultiset_eq_zero_of_length_le hn M hM (Nat.le_of_not_gt hnot)
  have hExtendS :
      (∑ j ∈ evenHookDegrees S.resolution.length,
        S.hookBettiMultiset (k := k) (n := n) hn M hM j) =
      ∑ j ∈ evenHookDegrees L,
        S.hookBettiMultiset (k := k) (n := n) hn M hM j := by
    apply Finset.sum_subset hS
    intro j hj hjS
    simp only [evenHookDegrees, Finset.mem_filter, Finset.mem_range] at hj hjS
    have hnot : ¬ j < S.resolution.length := fun hlt => hjS ⟨hlt, hj.2⟩
    exact S.hookBettiMultiset_eq_zero_of_length_le hn M hM (Nat.le_of_not_gt hnot)
  unfold MinimalFiniteRankProjectiveResolution.evenHookBetti
  rw [hExtendR]
  rw [hExtendS]
  apply Finset.sum_congr rfl
  intro j hj
  exact R.hookBettiMultiset_eq hn M hM S j

/-- The odd-degree hook sum is independent of the chosen minimal resolution,
including when their raw lengths differ. -/
theorem MinimalFiniteRankProjectiveResolution.oddHookBetti_eq
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    R.oddHookBetti (k := k) (n := n) hn M hM =
      S.oddHookBetti (k := k) (n := n) hn M hM := by
  classical
  let L := max R.resolution.length S.resolution.length
  have hR : oddHookDegrees R.resolution.length ⊆ oddHookDegrees L := by
    intro j hj
    simp only [oddHookDegrees, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 (Nat.le_max_left _ _), hj.2⟩
  have hS : oddHookDegrees S.resolution.length ⊆ oddHookDegrees L := by
    intro j hj
    simp only [oddHookDegrees, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 (Nat.le_max_right _ _), hj.2⟩
  have hExtendR :
      (∑ j ∈ oddHookDegrees R.resolution.length,
        R.hookBettiMultiset (k := k) (n := n) hn M hM j) =
      ∑ j ∈ oddHookDegrees L,
        R.hookBettiMultiset (k := k) (n := n) hn M hM j := by
    apply Finset.sum_subset hR
    intro j hj hjR
    simp only [oddHookDegrees, Finset.mem_filter, Finset.mem_range] at hj hjR
    have hnot : ¬ j < R.resolution.length := fun hlt => hjR ⟨hlt, hj.2⟩
    exact R.hookBettiMultiset_eq_zero_of_length_le hn M hM (Nat.le_of_not_gt hnot)
  have hExtendS :
      (∑ j ∈ oddHookDegrees S.resolution.length,
        S.hookBettiMultiset (k := k) (n := n) hn M hM j) =
      ∑ j ∈ oddHookDegrees L,
        S.hookBettiMultiset (k := k) (n := n) hn M hM j := by
    apply Finset.sum_subset hS
    intro j hj hjS
    simp only [oddHookDegrees, Finset.mem_filter, Finset.mem_range] at hj hjS
    have hnot : ¬ j < S.resolution.length := fun hlt => hjS ⟨hlt, hj.2⟩
    exact S.hookBettiMultiset_eq_zero_of_length_le hn M hM (Nat.le_of_not_gt hnot)
  unfold MinimalFiniteRankProjectiveResolution.oddHookBetti
  rw [hExtendR]
  rw [hExtendS]
  apply Finset.sum_congr rfl
  intro j hj
  exact R.hookBettiMultiset_eq hn M hM S j

/-- A parity-separated signed hook barcode stores positive and negative
occurrences as separate finite multisets. -/
structure SignedHookBarcode (n : ℕ) where
  positive : Multiset (RealHookTag (n := n))
  negative : Multiset (RealHookTag (n := n))

/-- The signed hook barcode attached to one certified minimal resolution. -/
noncomputable def MinimalFiniteRankProjectiveResolution.signedHookBarcode
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    SignedHookBarcode n :=
  ⟨R.evenHookBetti (k := k) (n := n) hn M hM,
    R.oddHookBetti (k := k) (n := n) hn M hM⟩

/-- The signed hook barcode of a finitely presented module is independent of
the chosen certified minimal finite rank-projective resolution. -/
theorem MinimalFiniteRankProjectiveResolution.signedHookBarcode_eq
    (hn : 0 < n) (M : PModule.{u,0,u} k (Fin n → ℝ))
    (hM : GradedFree.FinitelyPresented (R := k) (P := Fin n → ℝ) M)
    (R S : MinimalFiniteRankProjectiveResolution (k := k) (M := M)) :
    R.signedHookBarcode (k := k) (n := n) hn M hM =
      S.signedHookBarcode (k := k) (n := n) hn M hM := by
  change (⟨R.evenHookBetti hn M hM, R.oddHookBetti hn M hM⟩ : SignedHookBarcode n) = _
  exact congrArg₂ (fun p q => (⟨p, q⟩ : SignedHookBarcode n))
    (R.evenHookBetti_eq hn M hM S) (R.oddHookBetti_eq hn M hM S)

end TDA.Persistence
