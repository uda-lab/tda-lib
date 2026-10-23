import TDA.Filtration.SparseRips.UnionTailDeletion

/-!
# Homology of a complete finite deletion grid

Successively deleting its earliest stage identifies a finite union of closed
active complexes with the terminal closed-active complex on homology. The
forward map throughout is the inclusion of actual complexes.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial CategoryTheory

noncomputable section

variable {V : Type*} [MetricSpace V] [Fintype V] [LinearOrder V]

local instance unionGridDecidableEq : DecidableEq V := Classical.decEq V

private theorem isIso_homologyIncl_of_eq (R : Type*) [Ring R]
    {K L M : PreAbstractSimplicialComplex V} (hLM : L = M)
    (hKL : K ≤ L) (hKM : K ≤ M) (n : ℕ)
    (hIso : IsIso (simplicialHomologyIncl R hKL n)) :
    IsIso (simplicialHomologyIncl R hKM n) := by
  cases hLM
  exact hIso

/-- The terminal stage includes into a union containing its scale. -/
theorem terminal_le_activeUnion (seed : V) (η : ℝ) {F : Finset ℝ} {r : ℝ}
    (hr : r ∈ F) : closedActiveComplex seed η r ≤ activeUnion seed η F :=
  closedActiveComplex_le_activeUnion seed η hr

/-- A complete finite deletion grid has the homology of its last stage. -/
theorem isIso_terminal_activeUnion (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (r : ℝ) (n : ℕ)
    (F : Finset ℝ) (hrF : r ∈ F)
    (hbound : ∀ a ∈ F, 0 ≤ a ∧ a ≤ r)
    (hcomplete : DeletionComplete seed η F r) :
    IsIso (simplicialHomologyIncl R (terminal_le_activeUnion seed η hrF) n) := by
  classical
  have main : ∀ k : ℕ, ∀ F : Finset ℝ, F.card = k →
      (hrF : r ∈ F) →
      (∀ a ∈ F, 0 ≤ a ∧ a ≤ r) →
      DeletionComplete seed η F r →
      IsIso (simplicialHomologyIncl R (terminal_le_activeUnion seed η hrF) n) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro F hcard hrF hbound hcomplete
      let hF : F.Nonempty := ⟨r, hrF⟩
      let d := F.min' hF
      let H := F.erase d
      by_cases hH : H.Nonempty
      · let s := H.min' hH
        have hdF : d ∈ F := Finset.min'_mem F hF
        have hlt : H.card < k := hcard ▸ Finset.card_erase_lt_of_mem hdF
        have hrd : r ≠ d := by
          intro heq
          have hsH : s ∈ H := Finset.min'_mem H hH
          have hds : d < s := Finset.min'_lt_of_mem_erase_min' F hF hsH
          have hsr : s ≤ r := (hbound s (Finset.mem_of_mem_erase hsH)).2
          exact (not_lt_of_ge (heq ▸ hsr)) hds
        have hrH : r ∈ H := Finset.mem_erase.mpr ⟨hrd, hrF⟩
        have hHbound : ∀ a ∈ H, 0 ≤ a ∧ a ≤ r := by
          intro a ha
          exact hbound a (Finset.mem_of_mem_erase ha)
        have hHcomplete : DeletionComplete seed η H r :=
          deletionComplete_erase_min seed η hF hcomplete
        have hfirst : IsIso
            (simplicialHomologyIncl R (terminal_le_activeUnion seed η hrH) n) :=
          ih H.card hlt H rfl hrH hHbound hHcomplete
        let data := tailDeletionData_of_complete seed hF hbound hcomplete hH
        have hsecond : IsIso
            (simplicialHomologyIncl R (activeUnion_mono seed η data.tail_subset) n) := by
          have : IsIso (tailDeletionHomologyIso R seed hη hη' data n).hom := inferInstance
          simpa only [tailDeletionHomologyIso_hom] using this
        have hcomp : IsIso
            (simplicialHomologyIncl R
              ((terminal_le_activeUnion seed η hrH).trans
                (activeUnion_mono seed η data.tail_subset)) n) := by
          rw [simplicialHomologyIncl_comp R
            (terminal_le_activeUnion seed η hrH)
            (activeUnion_mono seed η data.tail_subset) n]
          letI := hfirst
          letI := hsecond
          exact IsIso.comp_isIso
        exact hcomp
      · have hsingle : F = {r} := by
          have he : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
          rcases (Finset.erase_eq_empty_iff F d).mp he with hempty | hsingleton
          · simp [hempty] at hrF
          · have hrd : r = d := by simpa [hsingleton] using hrF
            simpa [hrd] using hsingleton
        have hback : activeUnion seed η F ≤ closedActiveComplex seed η r := by
          intro σ hσ
          obtain ⟨a, ha, hσa⟩ := hσ
          have har : a = r := by simpa [hsingle] using ha
          subst a
          exact hσa
        let e : simplicialHomology (closedActiveComplex seed η r) R n ≅
            simplicialHomology (activeUnion seed η F) R n := {
          hom := simplicialHomologyIncl R (terminal_le_activeUnion seed η hrF) n
          inv := simplicialHomologyIncl R hback n
          hom_inv_id := by
            rw [← simplicialHomologyIncl_comp, simplicialHomologyIncl_id]
          inv_hom_id := by
            rw [← simplicialHomologyIncl_comp, simplicialHomologyIncl_id]
        }
        exact Iso.isIso_hom e
  exact main F.card F rfl hrF hbound hcomplete

/-- The closed active complex includes into the full sparse complex by a
homology isomorphism at each nonnegative scale. -/
theorem isIso_closedActive_sparse (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    IsIso (simplicialHomologyIncl R (closedActiveComplex_le_sparseComplex seed η hr) n) := by
  have hgrid : IsIso (simplicialHomologyIncl R
      (terminal_le_activeUnion seed η (show r ∈ deletionGrid seed η r from by simp)) n) :=
    isIso_terminal_activeUnion R seed hη hη' r n (deletionGrid seed η r)
      (by simp) (fun a ha => deletionGrid_nonneg_le seed hη hη' hr ha)
      (deletionGrid_complete seed η r)
  exact isIso_homologyIncl_of_eq R
    (sparseComplex_eq_activeUnion_deletionGrid seed hη hη' r).symm
    (terminal_le_activeUnion seed η (by simp))
    (closedActiveComplex_le_sparseComplex seed η hr) n hgrid

/-- The inclusion of the actual sparse complex into the relaxed complex is
an isomorphism on homology at every nonnegative scale. -/
theorem isIso_sparse_relaxed (R : Type*) [Ring R] (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    IsIso (simplicialHomologyIncl R (sparseComplex_le_relaxedComplex seed hη hη' r) n) := by
  let hfirst := closedActiveComplex_le_sparseComplex seed η hr
  let hsecond := sparseComplex_le_relaxedComplex seed hη hη' r
  let f := simplicialHomologyIncl R hfirst n
  let g := simplicialHomologyIncl R hsecond n
  letI : IsIso f := isIso_closedActive_sparse R seed hη hη' hr n
  have htotal : IsIso (simplicialHomologyIncl R (hfirst.trans hsecond) n) :=
    isIso_closedActiveHomologyIncl R seed hη hη' hr n
  letI : IsIso (f ≫ g) := by
    change IsIso (simplicialHomologyIncl R hfirst n ≫ simplicialHomologyIncl R hsecond n)
    rw [← simplicialHomologyIncl_comp R hfirst hsecond n]
    exact htotal
  exact IsIso.of_isIso_comp_left f g

end

end TDA.Filtration.SparseRips
