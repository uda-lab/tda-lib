import TDA.Mapper.GraphPLReebData

universe u

/-!
# MultiNerve Mapper of an adapted uniform cover as finite Reeb data

This module compares the MultiNerve Mapper of a height-separating uniform cover
with finite Reeb data for graph-PL input.  The comparison uses one member-adapted level per cover
member: an occupied member receives its unique vertex height, while an empty regular member
receives a midpoint.  Thus the list is not in general the canonical list of vertex heights; a
regular member can contribute a crossing-edge vertex cell and hence subdivide the data.

Faces over one label are the MultiNerve faces and are characterized by their face order.  The
adapted levels are separated from consecutive overlaps, and every height-separating cover has an
adapted list covering the vertex heights.  The cells are packaged as finite Reeb data, exhausted
under `2 * g ≤ r`, and the vertex and edge cells are identified with the graph-PL level and span
types, giving the finite-data isomorphism.

These are library results, in the context of Carrière--Oudot (CO16-v3, Definitions 3.2 and 3.3),
and are not attributed to that source.  No realization, 1-skeleton or graph packaging, refinement
to a canonical list, or ordinary Mapper claim is made here.
-/

namespace TDA.Mapper

open Finset Set
open TDA.Topology TDA.Topology.MultiNerveCell

namespace GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) {a r g : ℝ} {n : ℕ}

/-! ## Member-adapted level lists -/

/-- A critical-value list is adapted when its level for member `k` belongs to exactly that member. -/
def LevelsAdapted (T : CriticalValues n) (a r g : ℝ) : Prop :=
  ∀ k j : Fin (n + 1), T.value k ∈ uniformCover a r g (n + 1) j ↔ j = k

private theorem adapted_overlap_bounds {t : Fin (n + 1) → ℝ}
    (ht : ∀ k j : Fin (n + 1), t k ∈ uniformCover a r g (n + 1) j ↔ j = k)
    (hgr : g ≤ r) (e : Fin n) :
    t e.castSucc ≤ a + (e.succ : ℕ) * (r - g) ∧
      a + (e.succ : ℕ) * (r - g) + g ≤ t e.succ := by
  have hleft : t e.castSucc ≤ a + (e.succ : ℕ) * (r - g) := by
    by_contra hnot
    have hlt : a + (e.succ : ℕ) * (r - g) < t e.castSucc := lt_of_not_ge hnot
    have hown := (ht e.castSucc e.castSucc).2 rfl
    rw [uniformCover_apply, mem_uniformInterval] at hown
    have hmem : t e.castSucc ∈ uniformCover a r g (n + 1) e.succ := by
      rw [uniformCover_apply, mem_uniformInterval]
      constructor
      · exact hlt
      · simp only [Fin.val_succ, Fin.val_castSucc] at hown ⊢
        push_cast at hown ⊢
        nlinarith [hown.2, sub_nonneg.2 hgr]
    have heq := (ht e.castSucc e.succ).1 hmem
    exact (Fin.castSucc_lt_succ (i := e)).ne' heq
  have hright : a + (e.succ : ℕ) * (r - g) + g ≤ t e.succ := by
    by_contra hnot
    have hlt : t e.succ < a + (e.succ : ℕ) * (r - g) + g := lt_of_not_ge hnot
    have hown := (ht e.succ e.succ).2 rfl
    rw [uniformCover_apply, mem_uniformInterval] at hown
    have hmem : t e.succ ∈ uniformCover a r g (n + 1) e.castSucc := by
      rw [uniformCover_apply, mem_uniformInterval]
      constructor
      · simp only [Fin.val_succ, Fin.val_castSucc] at hown ⊢
        push_cast at hown ⊢
        nlinarith [hown.1, sub_nonneg.2 hgr]
      · simp only [Fin.val_succ, Fin.val_castSucc] at hlt ⊢
        push_cast at hlt ⊢
        nlinarith [hlt, hgr]
    have heq := (ht e.succ e.castSucc).1 hmem
    exact (Fin.castSucc_lt_succ (i := e)).ne heq
  exact ⟨hleft, hright⟩

/-- An adapted level for the lower member of a consecutive pair is no later than the overlap. -/
theorem LevelsAdapted.overlap_left_ge
    {T : CriticalValues n} (hT : LevelsAdapted T a r g) (hgr : g ≤ r) (e : Fin n) :
    T.value e.castSucc ≤ a + (e.succ : ℕ) * (r - g) :=
  (adapted_overlap_bounds (t := T.value) hT hgr e).1

/-- An adapted level for the upper member of a consecutive pair is no earlier than the overlap. -/
theorem LevelsAdapted.overlap_right_le
    {T : CriticalValues n} (hT : LevelsAdapted T a r g) (hgr : g ≤ r) (e : Fin n) :
    a + (e.succ : ℕ) * (r - g) + g ≤ T.value e.succ :=
  (adapted_overlap_bounds (t := T.value) hT hgr e).2

/-- Adapted levels and vertex-height coverage imply height separation of the uniform cover. -/
theorem LevelsAdapted.heightSeparating
    {V : Type u} {h : V → ℝ} {a r g : ℝ} {n : ℕ}
    {T : CriticalValues n} (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) :
    HeightSeparating h (uniformCover a r g (n + 1)) := by
  constructor
  · intro k v w hv hw
    obtain ⟨j, hj⟩ := hcov v
    obtain ⟨l, hl⟩ := hcov w
    have hkj : k = j := (hT j k).1 (by rw [hj]; exact hv)
    have hkl : k = l := (hT l k).1 (by rw [hl]; exact hw)
    calc
      h v = T.value j := hj.symm
      _ = T.value l := congrArg T.value (hkj.symm.trans hkl)
      _ = h w := hl
  · intro k l hkl v hv
    have hv' : h v ∈ (uniformCover a r g (n + 1) k : Set ℝ) ∩
        (uniformCover a r g (n + 1) l : Set ℝ) := by
      exact hv
    obtain ⟨j, hj⟩ := hcov v
    have hkj : k = j := (hT j k).1 (by rw [hj]; exact hv'.1)
    have hlj : l = j := (hT j l).1 (by rw [hj]; exact hv'.2)
    have : k = l := hkj.trans hlj.symm
    subst l
    omega

/-- Under adaptation and vertex-height coverage, the preimage of a member is its level set. -/
theorem LevelsAdapted.preimage_eq
    {V : Type u} {h : V → ℝ} {a r g : ℝ} {n : ℕ}
    {T : CriticalValues n} (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) (k : Fin (n + 1)) :
    h ⁻¹' (uniformCover a r g (n + 1) k : Set ℝ) = {v | h v = T.value k} := by
  ext v
  constructor
  · intro hv
    obtain ⟨j, hj⟩ := hcov v
    have hkj : k = j := (hT j k).1 (by rw [hj]; exact hv)
    exact hj.symm.trans (congrArg T.value hkj.symm)
  · intro hv
    change h v = T.value k at hv
    change h v ∈ (uniformCover a r g (n + 1) k : Set ℝ)
    rw [hv]
    exact (hT k k).2 rfl

private theorem midpoint_mem_uniformCover {k : Fin (n + 1)}
    (hg : 0 < g) (hgr : 2 * g ≤ r) :
    a + (k : ℕ) * (r - g) + r / 2 ∈
      uniformCover a r g (n + 1) k := by
  rw [uniformCover_apply, mem_uniformInterval]
  have hr : 0 < r := lt_of_lt_of_le (by linarith : 0 < 2 * g) hgr
  have hstep : 0 ≤ r - g := by linarith
  constructor <;> linarith

private theorem adapted_midpoint_not_mem_of_ne {k j : Fin (n + 1)}
    (_hk : ¬ ∃ v, h v ∈ uniformCover a r g (n + 1) k)
    (hg : 0 < g) (hgr : 2 * g ≤ r) (hkj : j ≠ k) :
    a + (k : ℕ) * (r - g) + r / 2 ∉
      uniformCover a r g (n + 1) j := by
  intro hmem
  have hmem' := hmem
  rw [uniformCover_apply, mem_uniformInterval] at hmem'
  have hmemk := midpoint_mem_uniformCover (a := a) (n := n) (k := k) hg hgr
  have hval_ne : (j : ℕ) ≠ (k : ℕ) := fun h => hkj (Fin.ext h)
  by_cases hfar : (k : ℕ) + 2 ≤ j
  · exact Set.disjoint_left.1 (uniformInterval_disjoint hgr hfar) hmemk hmem
  by_cases hfar' : (j : ℕ) + 2 ≤ k
  · exact Set.disjoint_left.1 (uniformInterval_disjoint hgr hfar') hmem hmemk
  by_cases hnext : (k : ℕ) + 1 = j
  ·
    have hnext' : ((k : ℕ) : ℝ) + 1 = ((j : ℕ) : ℝ) := by
      exact_mod_cast hnext
    have hbound : a + ((k : ℕ) : ℝ) * (r - g) + r / 2 ≤
        a + ((j : ℕ) : ℝ) * (r - g) := by
      rw [← hnext']
      nlinarith [hgr]
    linarith
  have hprev : (j : ℕ) + 1 = k := by omega
  have hprev' : ((j : ℕ) : ℝ) + 1 = ((k : ℕ) : ℝ) := by
    exact_mod_cast hprev
  have hbound : a + ((j : ℕ) : ℝ) * (r - g) + r ≤
      a + ((k : ℕ) : ℝ) * (r - g) + r / 2 := by
    rw [← hprev']
    nlinarith [hgr]
  linarith

private theorem adapted_of_member_chosen_level
    (hsep : HeightSeparating h (uniformCover a r g (n + 1)))
    (hgr : 2 * g ≤ r) (k : Fin (n + 1))
    (hk : ∃ v, h v ∈ uniformCover a r g (n + 1) k)
    (j : Fin (n + 1)) :
    (h hk.choose ∈ uniformCover a r g (n + 1) j) ↔ j = k := by
  constructor
  · intro hj
    by_cases hkj : j = k
    · exact hkj
    · have hval_ne : (j : ℕ) ≠ (k : ℕ) := fun h => hkj (Fin.ext h)
      by_cases hfar : (k : ℕ) + 2 ≤ j
      · exact (Set.disjoint_left.1 (uniformInterval_disjoint hgr hfar)
          (Classical.choose_spec hk) hj).elim
      by_cases hfar' : (j : ℕ) + 2 ≤ k
      · exact (Set.disjoint_left.1 (uniformInterval_disjoint hgr hfar') hj
          (Classical.choose_spec hk)).elim
      by_cases hnext : (k : ℕ) + 1 = j
      · exact ((hsep.2 k j hnext hk.choose) (by
          show h hk.choose ∈
            ((uniformCover a r g (n + 1) k ⊓ uniformCover a r g (n + 1) j :
              OpenInterval) : Set ℝ)
          exact ⟨Classical.choose_spec hk, hj⟩)).elim
      have hprev : (j : ℕ) + 1 = k := by omega
      exact ((hsep.2 j k hprev hk.choose) (by
        show h hk.choose ∈
          ((uniformCover a r g (n + 1) j ⊓ uniformCover a r g (n + 1) k :
            OpenInterval) : Set ℝ)
        exact ⟨hj, Classical.choose_spec hk⟩)).elim
  · intro hkj
    subst j
    exact Classical.choose_spec hk

/-! ## Existence of adapted lists -/

/-- A height-separating cover admits a member-adapted list covering all vertex heights. -/
theorem exists_levelsAdapted
    (hg : 0 < g) (hgr : 2 * g ≤ r)
    (hsep : HeightSeparating h (uniformCover a r g (n + 1)))
    (hcov : ∀ v, ∃ k, h v ∈ uniformCover a r g (n + 1) k) :
    ∃ T : CriticalValues n, LevelsAdapted T a r g ∧ CoversVertexHeights T h := by
  classical
  let t : Fin (n + 1) → ℝ := fun k =>
    if hk : ∃ v, h v ∈ uniformCover a r g (n + 1) k then h hk.choose
    else a + (k : ℕ) * (r - g) + r / 2
  have ht_mem : ∀ k, t k ∈ uniformCover a r g (n + 1) k := by
    intro k
    by_cases hk : ∃ v, h v ∈ uniformCover a r g (n + 1) k
    · have htk : t k = h hk.choose := by
        unfold t
        rw [dif_pos hk]
      rw [htk]
      exact Classical.choose_spec hk
    · have htk : t k = a + (k : ℕ) * (r - g) + r / 2 := by
        unfold t
        rw [dif_neg hk]
      rw [htk]
      exact midpoint_mem_uniformCover (a := a) (n := n) (k := k) hg hgr
  have ht_adapted : ∀ k j, t k ∈ uniformCover a r g (n + 1) j ↔ j = k := by
    intro k j
    by_cases hk : ∃ v, h v ∈ uniformCover a r g (n + 1) k
    · have htk : t k = h hk.choose := by
        unfold t
        rw [dif_pos hk]
      rw [htk]
      exact adapted_of_member_chosen_level (a := a) (r := r) (g := g)
        h hsep hgr k hk j
    · have htk : t k = a + (k : ℕ) * (r - g) + r / 2 := by
        unfold t
        rw [dif_neg hk]
      constructor
      · intro hj
        by_contra hne
        rw [htk] at hj
        exact (adapted_midpoint_not_mem_of_ne (a := a) (r := r) (g := g)
          (n := n) (k := k) (j := j) h hk hg hgr hne) hj
      · intro hkj
        subst j
        exact ht_mem k
  have ht_strict : StrictMono t := by
    apply (Fin.strictMono_iff_lt_succ (f := t)).2
    intro e
    have hb := adapted_overlap_bounds (a := a) (r := r) (g := g) (t := t) ht_adapted
      (by linarith [hg, hgr]) e
    linarith [hb.1, hb.2, hg]
  let T : CriticalValues n := ⟨t, ht_strict⟩
  refine ⟨T, ?_, ?_⟩
  · exact ht_adapted
  · intro v
    obtain ⟨k, hvk⟩ := hcov v
    have hk : ∃ w, h w ∈ uniformCover a r g (n + 1) k := ⟨v, hvk⟩
    refine ⟨k, ?_⟩
    have heq := hsep.1 k hk.choose v (Classical.choose_spec hk) hvk
    have htk : t k = h hk.choose := by
      unfold t
      rw [dif_pos hk]
    change t k = h v
    rw [htk]
    exact heq

end

end GraphPL

end TDA.Mapper

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) {a r g : ℝ} {n : ℕ}

/-! ## The finite Mapper data -/

/-- The finite incidence data whose vertices are the one-label MultiNerve Mapper cells and whose
edges are the consecutive two-label cells of the uniform cover.  The definition itself needs no
cover hypotheses; those hypotheses enter the exhaustion and comparison theorems below. -/
def uniformMapperData [Finite V] (a r g : ℝ) (n : ℕ) : FiniteReebData.{u} n where
  V k := {c : multiNerveMapper (plHeight G h)
      (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) //
      c.support.image Sigma.fst = {k}}
  E e := {c : multiNerveMapper (plHeight G h)
      (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) //
      c.support.image Sigma.fst = {e.castSucc, e.succ}}
  finiteV k := by
    have : Finite (ZerothHomotopy ↥(plHeight G h ⁻¹'
        (uniformCover a r g (n + 1) k : Set ℝ))) :=
      finite_zerothHomotopy G h (uniformCover a r g (n + 1) k)
    exact Finite.of_equiv _
      (vertexCellsEquiv (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) k).symm
  finiteE e := finite_edgeCells G h (uniformCover a r g (n + 1)) e.castSucc e.succ
  left e c := labelFace (plHeight G h)
    (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c e.castSucc
    (Finset.mem_insert_self _ _)
  right e c := labelFace (plHeight G h)
    (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c e.succ
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- The vertex types of `uniformMapperData` are the one-label MultiNerve Mapper cells. -/
@[simp] theorem uniformMapperData_V [Finite V] (k : Fin (n + 1)) :
    (uniformMapperData G h a r g n).V k =
      {c : multiNerveMapper (plHeight G h)
          (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) //
        c.support.image Sigma.fst = {k}} := rfl

/-- The edge types of `uniformMapperData` are the consecutive two-label cells. -/
@[simp] theorem uniformMapperData_E [Finite V] (e : Fin n) :
    (uniformMapperData G h a r g n).E e =
      {c : multiNerveMapper (plHeight G h)
          (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) //
        c.support.image Sigma.fst = {e.castSucc, e.succ}} := rfl

/-- The left endpoint of a Mapper edge is its MultiNerve face over the lower label. -/
@[simp] theorem uniformMapperData_left [Finite V] (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e) :
    (uniformMapperData G h a r g n).left e c =
      labelFace (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c e.castSucc
        (Finset.mem_insert_self _ _) := rfl

/-- The right endpoint of a Mapper edge is its MultiNerve face over the upper label. -/
@[simp] theorem uniformMapperData_right [Finite V] (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e) :
    (uniformMapperData G h a r g n).right e c =
      labelFace (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c e.succ
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) := rfl

private def uniformMapperCellsForget [Finite V] (a r g : ℝ) (n : ℕ) :
    (Σ k, (uniformMapperData G h a r g n).V k) ⊕
      (Σ e, (uniformMapperData G h a r g n).E e) →
      multiNerveMapper (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) :=
  Sum.elim (fun p => p.2.1) (fun p => p.2.1)

private theorem pair_castSucc_succ_injective {e e' : Fin n}
    (he : ({e.castSucc, e.succ} : Finset (Fin (n + 1))) =
      {e'.castSucc, e'.succ}) : e = e' := by
  have h₁ : e.castSucc ∈ ({e'.castSucc, e'.succ} : Finset (Fin (n + 1))) := by
    rw [← he]
    simp
  have h₂ : e'.castSucc ∈ ({e.castSucc, e.succ} : Finset (Fin (n + 1))) := by
    rw [he]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
  have hlt : e.castSucc < e.succ := Fin.castSucc_lt_succ
  have hlt' : e'.castSucc < e'.succ := Fin.castSucc_lt_succ
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Fin.ext (congrArg (fun z => z.val) h₁)
  · omega
  · omega
  · omega

private theorem uniformMapperCellsForget_injective [Finite V] :
    Function.Injective (uniformMapperCellsForget G h a r g n) := by
  rintro (⟨k, c⟩ | ⟨e, c⟩) (⟨k', c'⟩ | ⟨e', c'⟩) hc
  · change c.1 = c'.1 at hc
    have hcc : c.1 = c'.1 := hc
    have hlabels : ({k} : Finset (Fin (n + 1))) = {k'} :=
      c.2.symm.trans ((congrArg (fun z => z.support.image Sigma.fst) hcc).trans c'.2)
    have hkk : k = k' := Finset.singleton_inj.1 hlabels
    subst k'
    have hc' : c = c' := Subtype.ext hcc
    subst hc'
    rfl
  · change c.1 = c'.1 at hc
    have hcc : c.1 = c'.1 := hc
    have hlabels : ({k} : Finset (Fin (n + 1))) = {e'.castSucc, e'.succ} :=
      c.2.symm.trans ((congrArg (fun z => z.support.image Sigma.fst) hcc).trans c'.2)
    have hcard := congrArg Finset.card hlabels
    rw [Finset.card_singleton,
      Finset.card_pair (Fin.castSucc_lt_succ (i := e')).ne] at hcard
    omega
  · change c.1 = c'.1 at hc
    have hcc : c.1 = c'.1 := hc
    have hlabels : ({e.castSucc, e.succ} : Finset (Fin (n + 1))) = {k'} :=
      c.2.symm.trans ((congrArg (fun z => z.support.image Sigma.fst) hcc).trans c'.2)
    have hcard := congrArg Finset.card hlabels
    rw [Finset.card_pair (Fin.castSucc_lt_succ (i := e)).ne, Finset.card_singleton] at hcard
    omega
  · change c.1 = c'.1 at hc
    have hcc : c.1 = c'.1 := hc
    have hlabels : ({e.castSucc, e.succ} : Finset (Fin (n + 1))) =
        {e'.castSucc, e'.succ} :=
      c.2.symm.trans ((congrArg (fun z => z.support.image Sigma.fst) hcc).trans c'.2)
    have hee : e = e' := pair_castSucc_succ_injective hlabels
    subst e'
    have hc' : c = c' := Subtype.ext hcc
    subst hc'
    rfl

private theorem uniformMapperCells_pair_preimage [Finite V]
    (hgr : 2 * g ≤ r) (c : multiNerveMapper (plHeight G h)
      (fun i => (uniformCover a r g (n + 1) i : Set ℝ)))
    {k l : Fin (n + 1)} (hkl : k < l)
    (hc : c.support.image Sigma.fst = {k, l}) :
    ∃ p : (Σ e, (uniformMapperData G h a r g n).E e),
      uniformMapperCellsForget G h a r g n (Sum.inr p) = c := by
  by_cases hfar : (k : ℕ) + 2 ≤ l
  · exact ((isEmpty_uniformEdgeCells_of_far G h hgr hfar).false ⟨c, hc⟩).elim
  have hnext : (k : ℕ) + 1 = l := by omega
  let e : Fin n := ⟨k, by omega⟩
  have hecast : e.castSucc = k := Fin.ext rfl
  have hesucc : e.succ = l := by
    apply Fin.ext
    simpa [e] using hnext
  refine ⟨⟨e, ⟨c, hc.trans ?_⟩⟩, rfl⟩
  rw [hecast, hesucc]

private theorem uniformMapperCellsForget_surjective [Finite V]
    (hgr : 2 * g ≤ r) :
    Function.Surjective (uniformMapperCellsForget G h a r g n) := by
  intro c
  let L := c.support.image Sigma.fst
  have hLne : L.Nonempty := by
    obtain ⟨x, hx⟩ := c.support_nonempty
    exact ⟨x.1, Finset.mem_image.2 ⟨x, hx, rfl⟩⟩
  have hLcard : L.card ≤ 2 := by
    have hcard := multiNerveMapper_card_le_of_multiplicity
      (plHeight G h) (fun i => (uniformCover a r g (n + 1) i : Set ℝ))
      (coverMultiplicityAtMost_uniformCover hgr (plHeight G h)) c
    have himage : (c.support.image Sigma.fst).card ≤ c.support.card :=
      Finset.card_image_le
    exact himage.trans hcard
  have hpos : 0 < L.card := Finset.card_pos.2 hLne
  have hcases : L.card = 1 ∨ L.card = 2 := by omega
  rcases hcases with hcard_one | hcard_two
  · obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hcard_one
    refine ⟨Sum.inl ⟨k, ⟨c, show c.support.image Sigma.fst = {k} from hk⟩⟩, rfl⟩
  · obtain ⟨k, l, hkl, hL⟩ := Finset.card_eq_two.1 hcard_two
    rcases lt_or_gt_of_ne hkl with hkl' | hlk
    · obtain ⟨p, hp⟩ := uniformMapperCells_pair_preimage G h hgr c hkl'
        (show c.support.image Sigma.fst = {k, l} from hL)
      exact ⟨Sum.inr p, hp⟩
    · have hL' : L = {l, k} := hL.trans (Finset.pair_comm k l)
      obtain ⟨p, hp⟩ := uniformMapperCells_pair_preimage G h hgr c hlk
        (show c.support.image Sigma.fst = {l, k} from hL')
      exact ⟨Sum.inr p, hp⟩

/-- Under `2 * g ≤ r`, every MultiNerve Mapper cell is a one-label cell or a consecutive
two-label cell, with the corresponding finite-data index retained. -/
def uniformMapperCellsEquiv [Finite V] (hgr : 2 * g ≤ r) :
    multiNerveMapper (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) ≃
      (Σ k, (uniformMapperData G h a r g n).V k) ⊕
        (Σ e, (uniformMapperData G h a r g n).E e) :=
  (Equiv.ofBijective (uniformMapperCellsForget G h a r g n)
    ⟨uniformMapperCellsForget_injective G h,
      uniformMapperCellsForget_surjective G h hgr⟩).symm

/-! ## Vertex and edge identifications -/

/-- The one-label Mapper cells over an adapted member are the `LevelVertex` types at its level. -/
def uniformMapperVertexEquiv [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h) (k : Fin (n + 1)) :
    (uniformMapperData G h a r g n).V k ≃ LevelVertex G h (T.value k) :=
  let hmem : T.value k ∈ uniformCover a r g (n + 1) k := (hT k k).2 rfl
  let hlev : ∀ v, h v ∈ uniformCover a r g (n + 1) k → h v = T.value k :=
    fun v hv => (show v ∈ {v | h v = T.value k} from
      (hT.preimage_eq hcov k) ▸ hv)
  (vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) k).trans
    ((cellComponentsEquivSum G h (uniformCover a r g (n + 1) k)).trans
      (Equiv.sumCongr
        (induceComponentsEquivOfEq G (hT.preimage_eq hcov k))
        (uncoveredEdgeEquivCrossesOfLevel G h hmem hlev)))

private theorem uniformMapperVertexEquiv_apply [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h) (k : Fin (n + 1))
    (c : (uniformMapperData G h a r g n).V k) :
    uniformMapperVertexEquiv G h T hT hcov k c =
      (Equiv.sumCongr
        (induceComponentsEquivOfEq G (hT.preimage_eq hcov k))
        (uncoveredEdgeEquivCrossesOfLevel G h
          ((hT k k).2 rfl)
          (fun v hv => (show v ∈ {v | h v = T.value k} from
            (hT.preimage_eq hcov k) ▸ hv))))
        (cellComponentsEquivSum G h (uniformCover a r g (n + 1) k)
          ((vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) k) c)) := rfl

/-- Spanning an overlap with its geometric endpoints is equivalent to spanning the adapted levels.
The endpoint inequalities come from member adaptation, so no positivity assumption on `g` is
needed for this equivalence. -/
theorem spanEdge_overlap_iff (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hgr : g ≤ r) (e : Fin n) (x : G.edgeSet) :
    EdgeSpans G h (a + (e.succ : ℕ) * (r - g))
        (a + (e.succ : ℕ) * (r - g) + g) x ↔
      EdgeSpans G h (T.value e.castSucc) (T.value e.succ) x := by
  obtain ⟨d, rfl⟩ := exists_dartEdge_eq x
  rw [edgeSpans_dartEdge_iff, edgeSpans_dartEdge_iff]
  have hleft : a + (e.succ : ℕ) * (r - g) < T.value e.succ := by
    have hm := (hT e.succ e.succ).2 rfl
    rw [uniformCover_apply, mem_uniformInterval] at hm
    exact hm.1
  have hright : T.value e.castSucc <
      a + (e.succ : ℕ) * (r - g) + g := by
    have hm := (hT e.castSucc e.castSucc).2 rfl
    rw [uniformCover_apply, mem_uniformInterval] at hm
    simp only [Fin.val_succ, Fin.val_castSucc] at hm ⊢
    push_cast at hm ⊢
    nlinarith [hm.2]
  constructor
  · rintro ⟨hmin, hmax⟩
    constructor
    · rcases min_choice (h d.fst) (h d.snd) with hm | hm
      · obtain ⟨j, hj⟩ := hcov d.fst
        have hjlt : j < e.succ := T.strictMono.lt_iff_lt.1 (by
          rw [hj, ← hm]
          exact hmin.trans_lt hleft)
        have hjle : j ≤ e.castSucc := Fin.le_castSucc_iff.2 hjlt
        rw [hm, ← hj]
        exact T.strictMono.monotone hjle
      · obtain ⟨j, hj⟩ := hcov d.snd
        have hjlt : j < e.succ := T.strictMono.lt_iff_lt.1 (by
          rw [hj, ← hm]
          exact hmin.trans_lt hleft)
        have hjle : j ≤ e.castSucc := Fin.le_castSucc_iff.2 hjlt
        rw [hm, ← hj]
        exact T.strictMono.monotone hjle
    · rcases max_choice (h d.fst) (h d.snd) with hm | hm
      · obtain ⟨j, hj⟩ := hcov d.fst
        have hjlt : e.castSucc < j := T.strictMono.lt_iff_lt.1 (by
          rw [hj, ← hm]
          exact hright.trans_le hmax)
        have hle : e.succ ≤ j := Fin.castSucc_lt_iff_succ_le.1 hjlt
        rw [hm, ← hj]
        exact T.strictMono.monotone hle
      · obtain ⟨j, hj⟩ := hcov d.snd
        have hjlt : e.castSucc < j := T.strictMono.lt_iff_lt.1 (by
          rw [hj, ← hm]
          exact hright.trans_le hmax)
        have hle : e.succ ≤ j := Fin.castSucc_lt_iff_succ_le.1 hjlt
        rw [hm, ← hj]
        exact T.strictMono.monotone hle
  · rintro ⟨hmin, hmax⟩
    constructor
    · exact hmin.trans (hT.overlap_left_ge hgr e)
    · exact (hT.overlap_right_le hgr e).trans hmax

/-- Consecutive two-label Mapper cells are the spanning-edge types of the adapted levels. -/
def uniformMapperEdgeEquiv [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) (e : Fin n) :
    (uniformMapperData G h a r g n).E e ≃ SpanEdge G h (T.value e.castSucc) (T.value e.succ) :=
  (uniformEdgeCellsEquivSpans G h (hT.heightSeparating hcov) hgr hg
      (by simp : (e.castSucc : ℕ) + 1 = e.succ)).trans
    (Equiv.subtypeEquivRight (spanEdge_overlap_iff G h T hT hcov hgr e))

private theorem uniformMapper_cast_symm_apply {K L : OpenInterval}
    (hKL : K = L) (y : G.edgeSet) (hyK : EdgeActive G h K y)
    (hyL : EdgeActive G h L y) :
    (Equiv.cast (congrArg (fun K => (cellGraph G h K).ConnectedComponent) hKL)).symm
        ((cellGraph G h L).connectedComponentMk (Sum.inr ⟨y, hyL⟩)) =
      (cellGraph G h K).connectedComponentMk (Sum.inr ⟨y, hyK⟩) := by
  subst L
  rfl

/-- The inverse edge equivalence is the incidence component represented by the corresponding edge
node over the consecutive overlap. -/
theorem uniformMapperEdgeEquiv_symm_apply [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) (e : Fin n)
    (y : SpanEdge G h (T.value e.castSucc) (T.value e.succ))
    (hy : EdgeActive G h
      (uniformCover a r g (n + 1) e.castSucc ⊓
        uniformCover a r g (n + 1) e.succ) y.1) :
    edgeCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.castSucc e.succ
        ((uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y) =
      (cellGraph G h
        (uniformCover a r g (n + 1) e.castSucc ⊓
          uniformCover a r g (n + 1) e.succ)).connectedComponentMk
        (Sum.inr ⟨y.1, hy⟩) := by
  have hkl : (e.castSucc : ℕ) + 1 = e.succ := by simp
  let p : ℝ := a + (e.succ : ℕ) * (r - g)
  let q : ℝ := p + g
  have hK : ∀ v, h v ∉ ioo p q := by
    intro v hv
    apply (hT.heightSeparating hcov).2 e.castSucc e.succ hkl v
    rw [uniformCover_inf_of_succ hgr hkl]
    exact hv
  have hpq : p < q := by linarith
  have hyL : EdgeActive G h (ioo p q) y.1 := by
    rw [← uniformCover_inf_of_succ hgr hkl]
    exact hy
  have hyspan : EdgeSpans G h p q y.1 := by
    exact ((spanEdge_overlap_iff G h T hT hcov hgr e y.1).2 y.2)
  have hyactive : EdgeActive G h (ioo p q) y.1 :=
    ((activeEdgeEquivSpans (G := G) (h := h) hpq hK).symm
      ⟨y.1, hyspan⟩).2
  have hcancel :
      edgeCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.castSucc e.succ
          ((uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y) =
        (Equiv.cast (congrArg (fun K => (cellGraph G h K).ConnectedComponent)
          (uniformCover_inf_of_succ hgr hkl))).symm
          ((cellGraph G h (ioo p q)).connectedComponentMk
            (Sum.inr ⟨y.1, hyactive⟩)) := by
    unfold uniformMapperEdgeEquiv uniformEdgeCellsEquivSpans uniformEdgeCellsEquiv
    erw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_trans_apply,
      Equiv.apply_symm_apply]
    rfl
  rw [hcancel]
  exact uniformMapper_cast_symm_apply G h
    (uniformCover_inf_of_succ hgr hkl) y.1 hy hyL

end

end TDA.Mapper.GraphPL

namespace TDA.Mapper.GraphPL

open Set SimpleGraph CategoryTheory
open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL TDA.Reeb.GraphRealization

noncomputable section

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ) {a r g : ℝ} {n : ℕ}

/-! ## Faces and endpoint maps -/

private theorem uniformMapperEdgeEquiv_active [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) (e : Fin n)
    (y : SpanEdge G h (T.value e.castSucc) (T.value e.succ)) :
    EdgeActive G h
      (uniformCover a r g (n + 1) e.castSucc ⊓
        uniformCover a r g (n + 1) e.succ) y.1 := by
  have hkl : (e.castSucc : ℕ) + 1 = e.succ := by simp
  let p : ℝ := a + (e.succ : ℕ) * (r - g)
  let q : ℝ := p + g
  have hK : ∀ v, h v ∉ ioo p q := by
    intro v hv
    apply (hT.heightSeparating hcov).2 e.castSucc e.succ hkl v
    rw [uniformCover_inf_of_succ hgr hkl]
    exact hv
  have hpq : p < q := by linarith
  have hyspan : EdgeSpans G h p q y.1 :=
    ((spanEdge_overlap_iff G h T hT hcov hgr e y.1).2 y.2)
  have hyactive : EdgeActive G h (ioo p q) y.1 :=
    ((activeEdgeEquivSpans (G := G) (h := h) hpq hK).symm
      ⟨y.1, hyspan⟩).2
  rw [uniformCover_inf_of_succ hgr hkl]
  exact hyactive

/-- The vertex cell over member `k` generated by an active edge `x` is sent by
`uniformMapperVertexEquiv` to the level endpoint `levelEnd` of `x`. -/
theorem uniformMapperVertexEquiv_cell_inr [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (k : Fin (n + 1))
    (x : {e : G.edgeSet //
      EdgeActive G h (uniformCover a r g (n + 1) k) e})
    (hx : (∀ v ∈ (x.1 : Sym2 V), h v ≠ T.value k) →
      EdgeCrosses G h (T.value k) x.1) :
    uniformMapperVertexEquiv G h T hT hcov k
        ((vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) k).symm
          ((cellGraph G h (uniformCover a r g (n + 1) k)).connectedComponentMk
            (Sum.inr x))) =
      levelEnd G h (T.value k) x.1 hx := by
  refine (uniformMapperVertexEquiv_apply G h T hT hcov k _).trans ?_
  rw [Equiv.apply_symm_apply]
  by_cases hw : ∃ w ∈ (x.1 : Sym2 V), h w = T.value k
  · obtain ⟨w, hw, hwc⟩ := hw
    have hwK : h w ∈ uniformCover a r g (n + 1) k := by
      rw [hwc]
      exact (hT k k).2 rfl
    rw [cellComponentsEquivSum_inr_of_mem G h
      (uniformCover a r g (n + 1) k) x (w := ⟨w, hwK⟩) hw,
      levelEnd_of_mem G h hx hw hwc]
    rfl
  · replace hw : ∀ w ∈ (x.1 : Sym2 V), h w ≠ T.value k :=
      fun w hw' hwc => hw ⟨w, hw', hwc⟩
    have hunc : ∀ v ∈ (x.1 : Sym2 V),
        h v ∉ uniformCover a r g (n + 1) k := fun v hv hvK =>
      hw v hv (show v ∈ {v | h v = T.value k} from (hT.preimage_eq hcov k) ▸ hvK)
    rw [cellComponentsEquivSum_inr_uncovered G h
      (uniformCover a r g (n + 1) k) ⟨x.1, x.2, hunc⟩,
      levelEnd_of_forall_ne G h hx hw]
    rfl

private theorem uniformMapperVertexEquiv_face_component_left [Finite V]
    (T : CriticalValues n) (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) (hg : 0 < g) (hgr : g ≤ r) (e : Fin n)
    (y : SpanEdge G h (T.value e.castSucc) (T.value e.succ))
    (hy : EdgeActive G h
      (uniformCover a r g (n + 1) e.castSucc ⊓
        uniformCover a r g (n + 1) e.succ) y.1) :
    vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.castSucc
        (labelFace (plHeight G h)
          (fun i => (uniformCover a r g (n + 1) i : Set ℝ))
          ((uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y)
          e.castSucc (Finset.mem_insert_self _ _)) =
      (cellGraph G h (uniformCover a r g (n + 1) e.castSucc)).connectedComponentMk
        (Sum.inr ⟨y.1, hy.mono inf_le_left⟩) := by
  let c : (uniformMapperData G h a r g n).E e :=
    (uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y
  have hraw (z : ZerothHomotopy
      (plHeight G h ⁻¹'
        ((uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
          (uniformCover a r g (n + 1) e.succ : Set ℝ)))) :
      TDA.Topology.componentMap
          (TDA.Topology.preimageSetInclusion (ContinuousMap.id (Realization G))
            (Set.preimage_mono (f := plHeight G h) (Set.inter_subset_left :
              (uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
                (uniformCover a r g (n + 1) e.succ : Set ℝ) ⊆
              (uniformCover a r g (n + 1) e.castSucc : Set ℝ)))) z =
        TDA.Reeb.componentMap
          (preimageInclusion (plHeight G h)
            (toOpens_le_iff.2 (inf_le_left :
              uniformCover a r g (n + 1) e.castSucc ⊓
                uniformCover a r g (n + 1) e.succ ≤
              uniformCover a r g (n + 1) e.castSucc)))
          (zerothHomotopySetCongr
            (plHeight_preimage_inter G h
              (uniformCover a r g (n + 1) e.castSucc)
              (uniformCover a r g (n + 1) e.succ)) z) := by
    induction z using ZerothHomotopy.rec with
    | mk x => rfl
  have hcomponent (z : ZerothHomotopy
      (plHeight G h ⁻¹'
        ((uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
          (uniformCover a r g (n + 1) e.succ : Set ℝ)))) :
      preimageComponentsEquiv G h
          (uniformCover a r g (n + 1) e.castSucc)
          (TDA.Topology.componentMap
            (TDA.Topology.preimageSetInclusion (ContinuousMap.id (Realization G))
              (Set.preimage_mono (f := plHeight G h) (Set.inter_subset_left :
                (uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
                  (uniformCover a r g (n + 1) e.succ : Set ℝ) ⊆
                (uniformCover a r g (n + 1) e.castSucc : Set ℝ)))) z) =
        (preimageComponentsEquiv G h
          (uniformCover a r g (n + 1) e.castSucc ⊓
            uniformCover a r g (n + 1) e.succ)
          (zerothHomotopySetCongr
            (plHeight_preimage_inter G h
              (uniformCover a r g (n + 1) e.castSucc)
              (uniformCover a r g (n + 1) e.succ)) z)).map
          (cellInclusion G h (inf_le_left :
            uniformCover a r g (n + 1) e.castSucc ⊓
              uniformCover a r g (n + 1) e.succ ≤
            uniformCover a r g (n + 1) e.castSucc)) := by
    erw [hraw z]
    exact preimageComponentsEquiv_componentMap G h
      (inf_le_left :
        uniformCover a r g (n + 1) e.castSucc ⊓
          uniformCover a r g (n + 1) e.succ ≤
        uniformCover a r g (n + 1) e.castSucc) _
  have hedge :
      (preimageComponentsEquiv G h
        (uniformCover a r g (n + 1) e.castSucc ⊓
          uniformCover a r g (n + 1) e.succ)
        (zerothHomotopySetCongr
          (plHeight_preimage_inter G h
            (uniformCover a r g (n + 1) e.castSucc)
            (uniformCover a r g (n + 1) e.succ))
          (edgeCellsEquiv (plHeight G h)
            (fun i => (uniformCover a r g (n + 1) i : Set ℝ))
            e.castSucc e.succ c))) =
      edgeCellsCellGraphEquiv G h (uniformCover a r g (n + 1))
        e.castSucc e.succ c := rfl
  have hvertex :
      vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.castSucc
          (labelFace (plHeight G h)
            (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c
            e.castSucc (Finset.mem_insert_self _ _)) =
        (cellGraph G h (uniformCover a r g (n + 1) e.castSucc)).connectedComponentMk
          (Sum.inr ⟨y.1, hy.mono inf_le_left⟩) := by
    rw [vertexCellsCellGraphEquiv, Equiv.trans_apply,
      vertexCellsEquiv_labelFace_pair_left (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c]
    refine (hcomponent _).trans ?_
    rw [hedge, uniformMapperEdgeEquiv_symm_apply G h T hT hcov hg hgr e y hy]
    rfl
  exact hvertex

private theorem uniformMapperVertexEquiv_face_component_right [Finite V]
    (T : CriticalValues n) (hT : LevelsAdapted T a r g)
    (hcov : CoversVertexHeights T h) (hg : 0 < g) (hgr : g ≤ r) (e : Fin n)
    (y : SpanEdge G h (T.value e.castSucc) (T.value e.succ))
    (hy : EdgeActive G h
      (uniformCover a r g (n + 1) e.castSucc ⊓
        uniformCover a r g (n + 1) e.succ) y.1) :
    vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.succ
        (labelFace (plHeight G h)
          (fun i => (uniformCover a r g (n + 1) i : Set ℝ))
          ((uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y)
          e.succ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) =
      (cellGraph G h (uniformCover a r g (n + 1) e.succ)).connectedComponentMk
        (Sum.inr ⟨y.1, hy.mono inf_le_right⟩) := by
  let c : (uniformMapperData G h a r g n).E e :=
    (uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y
  have hraw (z : ZerothHomotopy
      (plHeight G h ⁻¹'
        ((uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
          (uniformCover a r g (n + 1) e.succ : Set ℝ)))) :
      TDA.Topology.componentMap
          (TDA.Topology.preimageSetInclusion (ContinuousMap.id (Realization G))
            (Set.preimage_mono (f := plHeight G h) (Set.inter_subset_right :
              (uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
                (uniformCover a r g (n + 1) e.succ : Set ℝ) ⊆
              (uniformCover a r g (n + 1) e.succ : Set ℝ)))) z =
        TDA.Reeb.componentMap
          (preimageInclusion (plHeight G h)
            (toOpens_le_iff.2 (inf_le_right :
              uniformCover a r g (n + 1) e.castSucc ⊓
                uniformCover a r g (n + 1) e.succ ≤
              uniformCover a r g (n + 1) e.succ)))
          (zerothHomotopySetCongr
            (plHeight_preimage_inter G h
              (uniformCover a r g (n + 1) e.castSucc)
              (uniformCover a r g (n + 1) e.succ)) z) := by
    induction z using ZerothHomotopy.rec with
    | mk x => rfl
  have hcomponent (z : ZerothHomotopy
      (plHeight G h ⁻¹'
        ((uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
          (uniformCover a r g (n + 1) e.succ : Set ℝ)))) :
      preimageComponentsEquiv G h
          (uniformCover a r g (n + 1) e.succ)
          (TDA.Topology.componentMap
            (TDA.Topology.preimageSetInclusion (ContinuousMap.id (Realization G))
              (Set.preimage_mono (f := plHeight G h) (Set.inter_subset_right :
                (uniformCover a r g (n + 1) e.castSucc : Set ℝ) ∩
                  (uniformCover a r g (n + 1) e.succ : Set ℝ) ⊆
                (uniformCover a r g (n + 1) e.succ : Set ℝ)))) z) =
        (preimageComponentsEquiv G h
          (uniformCover a r g (n + 1) e.castSucc ⊓
            uniformCover a r g (n + 1) e.succ)
          (zerothHomotopySetCongr
            (plHeight_preimage_inter G h
              (uniformCover a r g (n + 1) e.castSucc)
              (uniformCover a r g (n + 1) e.succ)) z)).map
          (cellInclusion G h (inf_le_right :
            uniformCover a r g (n + 1) e.castSucc ⊓
              uniformCover a r g (n + 1) e.succ ≤
            uniformCover a r g (n + 1) e.succ)) := by
    erw [hraw z]
    exact preimageComponentsEquiv_componentMap G h
      (inf_le_right :
        uniformCover a r g (n + 1) e.castSucc ⊓
          uniformCover a r g (n + 1) e.succ ≤
        uniformCover a r g (n + 1) e.succ) _
  have hedge :
      (preimageComponentsEquiv G h
        (uniformCover a r g (n + 1) e.castSucc ⊓
          uniformCover a r g (n + 1) e.succ)
        (zerothHomotopySetCongr
          (plHeight_preimage_inter G h
            (uniformCover a r g (n + 1) e.castSucc)
            (uniformCover a r g (n + 1) e.succ))
          (edgeCellsEquiv (plHeight G h)
            (fun i => (uniformCover a r g (n + 1) i : Set ℝ))
            e.castSucc e.succ c))) =
      edgeCellsCellGraphEquiv G h (uniformCover a r g (n + 1))
        e.castSucc e.succ c := rfl
  have hvertex :
      vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.succ
          (labelFace (plHeight G h)
            (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c e.succ
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) =
        (cellGraph G h (uniformCover a r g (n + 1) e.succ)).connectedComponentMk
          (Sum.inr ⟨y.1, hy.mono inf_le_right⟩) := by
    rw [vertexCellsCellGraphEquiv, Equiv.trans_apply,
      vertexCellsEquiv_labelFace_pair_right (plHeight G h)
        (fun i => (uniformCover a r g (n + 1) i : Set ℝ)) c]
    refine (hcomponent _).trans ?_
    rw [hedge, uniformMapperEdgeEquiv_symm_apply G h T hT hcov hg hgr e y hy]
    rfl
  exact hvertex

/-- The left MultiNerve face is the left endpoint of the adapted graph-PL edge. -/
theorem uniformMapperVertexEquiv_left [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e) :
    uniformMapperVertexEquiv G h T hT hcov e.castSucc
        ((uniformMapperData G h a r g n).left e c) =
      (graphPLReebData G h T).left e
        (uniformMapperEdgeEquiv G h T hT hcov hg hgr e c) := by
  obtain ⟨y, rfl⟩ :=
    (uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm.surjective c
  rw [Equiv.apply_symm_apply]
  have hy := uniformMapperEdgeEquiv_active G h T hT hcov hg hgr e y
  have hface :
      labelFace (plHeight G h)
          (fun i => (uniformCover a r g (n + 1) i : Set ℝ))
          ((uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y)
          e.castSucc (Finset.mem_insert_self _ _) =
        (vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.castSucc).symm
          ((cellGraph G h (uniformCover a r g (n + 1) e.castSucc)).connectedComponentMk
            (Sum.inr ⟨y.1, hy.mono inf_le_left⟩)) := by
    apply (vertexCellsCellGraphEquiv G h
      (uniformCover a r g (n + 1)) e.castSucc).injective
    rw [Equiv.apply_symm_apply]
    exact uniformMapperVertexEquiv_face_component_left G h T hT hcov hg hgr e y hy
  rw [uniformMapperData_left, hface,
    uniformMapperVertexEquiv_cell_inr G h T hT hcov e.castSucc
      ⟨y.1, hy.mono inf_le_left⟩
      (y.2.crosses_left (T.value_castSucc_lt_succ e))]
  rfl

/-- The right MultiNerve face is the right endpoint of the adapted graph-PL edge. -/
theorem uniformMapperVertexEquiv_right [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) (e : Fin n)
    (c : (uniformMapperData G h a r g n).E e) :
    uniformMapperVertexEquiv G h T hT hcov e.succ
        ((uniformMapperData G h a r g n).right e c) =
      (graphPLReebData G h T).right e
        (uniformMapperEdgeEquiv G h T hT hcov hg hgr e c) := by
  obtain ⟨y, rfl⟩ :=
    (uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm.surjective c
  rw [Equiv.apply_symm_apply]
  have hy := uniformMapperEdgeEquiv_active G h T hT hcov hg hgr e y
  have hface :
      labelFace (plHeight G h)
          (fun i => (uniformCover a r g (n + 1) i : Set ℝ))
          ((uniformMapperEdgeEquiv G h T hT hcov hg hgr e).symm y)
          e.succ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) =
        (vertexCellsCellGraphEquiv G h (uniformCover a r g (n + 1)) e.succ).symm
          ((cellGraph G h (uniformCover a r g (n + 1) e.succ)).connectedComponentMk
            (Sum.inr ⟨y.1, hy.mono inf_le_right⟩)) := by
    apply (vertexCellsCellGraphEquiv G h
      (uniformCover a r g (n + 1)) e.succ).injective
    rw [Equiv.apply_symm_apply]
    exact uniformMapperVertexEquiv_face_component_right G h T hT hcov hg hgr e y hy
  rw [uniformMapperData_right, hface,
    uniformMapperVertexEquiv_cell_inr G h T hT hcov e.succ
      ⟨y.1, hy.mono inf_le_right⟩
      (y.2.crosses_right (T.value_castSucc_lt_succ e))]
  rfl

/-! ## The finite-data homomorphism and isomorphism -/

/-- The adapted Mapper data map to the graph-PL finite Reeb data. -/
def uniformMapperHom [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) :
    (uniformMapperData G h a r g n).Hom (graphPLReebData G h T) where
  v i := uniformMapperVertexEquiv G h T hT hcov i
  e i := uniformMapperEdgeEquiv G h T hT hcov hg hgr i
  left_comm i x :=
    (uniformMapperVertexEquiv_left G h T hT hcov hg hgr i x).symm
  right_comm i x :=
    (uniformMapperVertexEquiv_right G h T hT hcov hg hgr i x).symm

/-- The vertex component of the finite-data homomorphism is the adapted vertex equivalence. -/
@[simp] theorem uniformMapperHom_v [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) (i : Fin (n + 1)) :
    (uniformMapperHom G h T hT hcov hg hgr).v i =
      uniformMapperVertexEquiv G h T hT hcov i := rfl

/-- The edge component of the finite-data homomorphism is the adapted edge equivalence. -/
@[simp] theorem uniformMapperHom_e [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) (e : Fin n) :
    (uniformMapperHom G h T hT hcov hg hgr).e e =
      uniformMapperEdgeEquiv G h T hT hcov hg hgr e := rfl

/-- The adapted Mapper finite data are isomorphic to the graph-PL finite Reeb data. -/
def uniformMapperIso [Finite V] (T : CriticalValues n)
    (hT : LevelsAdapted T a r g) (hcov : CoversVertexHeights T h)
    (hg : 0 < g) (hgr : g ≤ r) :
    uniformMapperData G h a r g n ≅ graphPLReebData G h T where
  hom := uniformMapperHom G h T hT hcov hg hgr
  inv := (uniformMapperHom G h T hT hcov hg hgr).inv
    (fun i => (uniformMapperVertexEquiv G h T hT hcov i).bijective)
    (fun e => (uniformMapperEdgeEquiv G h T hT hcov hg hgr e).bijective)
  hom_inv_id := (uniformMapperHom G h T hT hcov hg hgr).comp_inv _ _
  inv_hom_id := (uniformMapperHom G h T hT hcov hg hgr).inv_comp _ _

/-- Every bounded finite graph-PL height admits a member-adapted Mapper/Reeb isomorphism below
any positive resolution, with the uniform-cover separation bound. -/
theorem exists_uniformMapperIso [Finite V] {m M ρ : ℝ}
    (hh : ∀ v, h v ∈ Set.Icc m M) (hρ : 0 < ρ) :
    ∃ (a r g : ℝ) (n : ℕ) (T : CriticalValues n),
      0 < g ∧ 2 * g ≤ r ∧ r < ρ ∧ LevelsAdapted T a r g ∧
        CoversVertexHeights T h ∧
          Nonempty (uniformMapperData G h a r g n ≅ graphPLReebData G h T) := by
  obtain ⟨a, r, g, n', hg, hgr, hrρ, hn', ha₁, ha₂, hM, hsep, hcovers⟩ :=
    heightSeparating_covers_range h hh hρ
  obtain ⟨n, hn_eq⟩ := Nat.exists_eq_succ_of_ne_zero hn'.ne'
  subst hn_eq
  have hsep' : HeightSeparating h (uniformCover a r g (n + 1)) := by
    simpa [Nat.succ_eq_add_one] using hsep
  have hcov : ∀ v, ∃ k : Fin (n + 1),
      h v ∈ uniformCover a r g (n + 1) k := by
    intro v
    obtain ⟨k, hk⟩ := hcovers G (plHeight G h (vertex G v))
      ⟨vertex G v, rfl⟩
    refine ⟨k, ?_⟩
    exact hk
  obtain ⟨T, hT, hcovT⟩ := exists_levelsAdapted (a := a) (r := r) (g := g)
    h hg hgr hsep' hcov
  have hgr' : g ≤ r := by linarith
  refine ⟨a, r, g, n, T, hg, hgr, hrρ, hT, hcovT, ?_⟩
  exact ⟨uniformMapperIso G h T hT hcovT hg hgr'⟩

end

end TDA.Mapper.GraphPL
