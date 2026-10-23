import TDA.Persistence.ConstructibleRefinement
import TDA.Persistence.ConstructibleBarcode

/-!
# Real endpoint diagrams are invariant under grid refinement

Refinement changes finite index intervals by monotone restriction of the
reconstructed coarse module. The endpoint cuts retain every positive-birth
occurrence and recover the same real finite endpoints and essential tails.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteConstructible

open CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {n m : ℕ} {c : Fin n ↪o ℝ} {d : Fin m ↪o ℝ}

private noncomputable def criticalSample (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ) :
    Fin m →o Fin (n + 1) := (cellIndex c).comp d.toOrderHom

private theorem cut_at_critical (h : Refines c d) (i : Fin n) :
    sampledEndpoint (criticalSample c d) (i.val + 1) = (h.embedding i).val := by
  have hs : Finset.univ.filter (fun j : Fin m =>
      (criticalSample c d j).val < i.val + 1) = Finset.Iio (h.embedding i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    change (cellIndex c (d j)).val < i.val + 1 ↔ j < h.embedding i
    calc
      _ ↔ ¬ i.val < (cellIndex c (d j)).val := by omega
      _ ↔ ¬ c i ≤ d j := not_congr (lt_cellIndex_iff c i (d j))
      _ ↔ d j < c i := not_le
      _ ↔ j < h.embedding i := by rw [← h.embedding_value i, d.lt_iff_lt]
  unfold sampledEndpoint
  rw [hs, Fin.card_Iio]

private theorem cut_positive (h : Refines c d) (e : ℕ) (he : 0 < e) (hen : e ≤ n) :
    sampledEndpoint (criticalSample c d) e =
      (h.embedding ⟨e - 1, by omega⟩).val := by
  simpa only [Fin.val_mk, show e - 1 + 1 = e by omega] using
    cut_at_critical h ⟨e - 1, by omega⟩

private theorem cut_terminal : sampledEndpoint (criticalSample c d) (n + 1) = m := by
  have hs : Finset.univ.filter (fun j : Fin m =>
      (criticalSample c d j).val < n + 1) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (criticalSample c d j).isLt
  unfold sampledEndpoint
  rw [hs, Finset.card_univ, Fintype.card_fin]

-- These are the interval restrictions used by rankBarcode_reindex. The
-- finite and terminal death cases have different endpoint interpretations.
private theorem restricted_real_endpoint (h : Refines c d)
    (I : FiniteInterval (n + 1)) (hb : 0 < I.birth) :
    Option.map (RealBarcode.endpoints d) (I.restrictAlong (criticalSample c d)) =
      some (RealBarcode.endpoints c (RealBarcode.dropZero I hb)) := by
  have hbd := I.birth_lt_death
  have hdn := I.death_le_size
  let b : Fin n := ⟨I.birth - 1, by omega⟩
  have hbcut := cut_positive h I.birth hb (by omega)
  change sampledEndpoint (criticalSample c d) I.birth = (h.embedding b).val at hbcut
  by_cases hd : I.death < n + 1
  · let e : Fin n := ⟨I.death - 1, by omega⟩
    have hdcut := cut_positive h I.death (by omega) (by omega)
    change sampledEndpoint (criticalSample c d) I.death = (h.embedding e).val at hdcut
    have hbe : b < e := by change I.birth - 1 < I.death - 1; omega
    have hlt : (h.embedding b).val < (h.embedding e).val := h.embedding.strictMono hbe
    simp only [FiniteInterval.restrictAlong, hbcut, hdcut, dif_pos hlt, Option.map_some]
    apply congrArg some
    apply Prod.ext
    · change d (h.embedding b) = c b
      exact h.embedding_value b
    · dsimp only [RealBarcode.endpoints, RealBarcode.dropZero]
      erw [dif_pos (h.embedding e).isLt, dif_pos (show I.death - 1 < n by omega)]
      exact congrArg (fun x : ℝ => (x : WithTop ℝ)) (h.embedding_value e)
  · have he : I.death = n + 1 := by omega
    have hdcut : sampledEndpoint (criticalSample c d) I.death = m := by
      rw [he]; exact cut_terminal
    have hlt := (h.embedding b).isLt
    simp only [FiniteInterval.restrictAlong, hbcut, hdcut, dif_pos hlt, Option.map_some]
    apply congrArg some
    apply Prod.ext
    · change d (h.embedding b) = c b
      exact h.embedding_value b
    · dsimp only [RealBarcode.endpoints, RealBarcode.dropZero]
      simp [he]

/-- Restricting a padded barcode to a finer critical grid preserves its real
endpoint multiset, with multiplicity and terminal essential bars retained. -/
private theorem ofIndexBars_refinement (h : Refines c d)
    (B : Multiset (FiniteInterval (n + 1))) (hb : ∀ I ∈ B, 0 < I.birth) :
    ofIndexBars d d.strictMono (reindexBarcode (criticalSample c d) B) =
      ofIndexBars c c.strictMono (reindexBarcode (Fin.succOrderEmb n).toOrderHom B) := by
  apply Diagram.ext
  rw [RealBarcode.ofIndexBars_points, RealBarcode.ofIndexBars_points]
  simp only [reindexBarcode, Multiset.map_filterMap]
  revert hb
  induction B using Multiset.induction_on with
  | empty => intro _; rfl
  | @cons I B ih =>
    intro hb
    have hi : 0 < I.birth := hb I (Multiset.mem_cons_self _ _)
    have ht : ∀ J ∈ B, 0 < J.birth := fun J hJ => hb J (Multiset.mem_cons_of_mem hJ)
    have he := restricted_real_endpoint h I hi
    simpa only [Multiset.filterMap_cons, he, RealBarcode.restrictAlong_succ I hi,
      Option.map_some, Option.getD_some] using
      congrArg (fun s => {RealBarcode.endpoints c (RealBarcode.dropZero I hi)} + s) (ih ht)

variable {k : Type u} [Field k]
variable (M : PModule.{u,0,u} k ℝ)

/-- Original critical-fiber finiteness determines every real fiber by reconstruction. -/
theorem finiteDimensional_of_isConstructible (hM : IsConstructible c M)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) (t : ℝ) :
    FiniteDimensional k (M.obj t) := by
  have : FiniteDimensional k ((reindex (cellIndex c) (sample c M)).obj t) := by
    change FiniteDimensional k ((sample c M).obj (cellIndex c t))
    exact finiteDimensional_sample c M hfd _
  exact ((reconstructionIso c M hM).app t).toLinearEquiv.finiteDimensional

/-- Adding critical values changes the finite index barcode but leaves the real endpoint diagram unchanged. Finiteness at new critical values is derived. -/
theorem moduleDiagram_refinement (h : Refines c d) (hM : IsConstructible c M)
    (hfd : ∀ i, FiniteDimensional k (M.obj (c i))) :
    moduleDiagram d M (fun j => finiteDimensional_of_isConstructible M hM hfd (d j)) =
      moduleDiagram c M hfd := by
  let A := sample c M
  have : ∀ i, FiniteDimensional k (A.obj i) := finiteDimensional_sample c M hfd
  have : ∀ j, FiniteDimensional k ((reindex d.toOrderHom M).obj j) := by
    intro j
    change FiniteDimensional k (M.obj (d j))
    exact finiteDimensional_of_isConstructible M hM hfd (d j)
  have : ∀ j, FiniteDimensional k ((reindex (criticalSample c d) A).obj j) := by
    intro j
    change FiniteDimensional k (A.obj (criticalSample c d j))
    infer_instance
  have : ∀ j, FiniteDimensional k ((reindex c.toOrderHom M).obj j) := by
    intro j
    change FiniteDimensional k (M.obj (c j))
    exact hfd j
  have e : reindex (criticalSample c d) A ≅ reindex d.toOrderHom M :=
    Functor.isoWhiskerLeft d.toOrderHom.toFunctor (reconstructionIso c M hM)
  unfold moduleDiagram
  rw [rankBarcode_eq_of_iso e.symm, rankBarcode_reindex A]
  change ofIndexBars d d.strictMono (reindexBarcode (criticalSample c d) (sampleBarcode c M hfd)) = _
  rw [ofIndexBars_refinement h _ (sampleBarcode_birth_pos c M hfd),
    ← moduleDiagram_eq_reindex_sample c M hfd]
  rfl

end TDA.Persistence.FiniteConstructible
