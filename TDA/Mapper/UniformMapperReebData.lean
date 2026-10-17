import TDA.Mapper.GraphPLReebData

universe u v w

/-!
# MultiNerve Mapper of an adapted uniform cover as finite Reeb data

This module begins the comparison of the MultiNerve Mapper of a height-separating uniform cover
with finite Reeb data for graph-PL input.  The comparison uses one member-adapted level per cover
member: an occupied member receives its unique vertex height, while an empty regular member
receives a midpoint.  Thus the list is not in general the canonical list of vertex heights; a
regular member can contribute a crossing-edge vertex cell and hence subdivide the data.

Faces over one label are the MultiNerve faces and are characterized by their face order.  The
adapted levels are separated from consecutive overlaps, and every height-separating cover has an
adapted list covering the vertex heights.  Later parts of the comparison package the cells as
finite Reeb data, exhaust them under `2 * g ≤ r`, identify the vertex and edge cells with the
graph-PL level and span types, and prove the resulting finite-data isomorphism.

These are library results, in the context of Carrière--Oudot (CO16-v3, Definitions 3.2 and 3.3),
and are not attributed to that source.  No realization, 1-skeleton or graph packaging, refinement
to a canonical list, or ordinary Mapper claim is made here.
-/

namespace TDA.Mapper

open Finset Set
open TDA.Topology TDA.Topology.MultiNerveCell

noncomputable section

variable {X : Type u} {Y : Type v} {I : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

/-! ## Faces over one label -/

/-- The MultiNerve face of a cell over a single label `i`. -/
def labelFace (f : C(X, Y)) (U : I → Set Y) [DecidableEq I]
    {τ : Finset I}
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ})
    (i : I) (hi : i ∈ τ) :
    {c : multiNerveMapper f U // c.support.image Sigma.fst = {i}} := by
  have hi' : i ∈ c.1.support.image Sigma.fst := by
    rw [c.2]
    exact hi
  have hs : (c.1.support.filter (fun x => x.1 = i)).Nonempty := by
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.1 hi'
    exact ⟨x, Finset.mem_filter.2 ⟨hx, hxi⟩⟩
  have hlabels : (c.1.support.filter (fun x => x.1 = i)).image Sigma.fst = {i} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hs
      exact Finset.mem_image.2 ⟨x, hx, (Finset.mem_filter.1 hx).2⟩
    · intro j hj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hj
      exact Finset.mem_filter.1 hx |>.2
  exact ⟨c.1.face _ hs (Finset.filter_subset _ _), hlabels⟩

/-- The single-label face lies below its original MultiNerve cell. -/
theorem labelFace_le (f : C(X, Y)) (U : I → Set Y) [DecidableEq I]
    {τ : Finset I}
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ})
    (i : I) (hi : i ∈ τ) : (labelFace f U c i hi).1 ≤ c.1 := by
  unfold labelFace
  exact MultiNerveCell.face_le c.1 _ _ _

/-- A single-label face below a cell is the face selected by `labelFace`. -/
theorem eq_labelFace_of_le (f : C(X, Y)) (U : I → Set Y) [DecidableEq I]
    {τ : Finset I}
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ})
    (i : I) (hi : i ∈ τ)
    {b : {c : multiNerveMapper f U // c.support.image Sigma.fst = {i}}}
    (hb : b.1 ≤ c.1) : b = labelFace f U c i hi := by
  have hsub : b.1.support = c.1.support.filter (fun x => x.1 = i) := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hxc : x ∈ c.1.support := support_mono hb hx
      have hxi : x.1 = i := by
        have : x.1 ∈ b.1.support.image Sigma.fst :=
          Finset.mem_image.2 ⟨x, hx, rfl⟩
        rw [b.2] at this
        exact Finset.mem_singleton.1 this
      exact Finset.mem_filter.2 ⟨hxc, hxi⟩
    · intro x hx
      have hxc : x ∈ c.1.support := Finset.filter_subset _ _ hx
      have hxi : x.1 = i := Finset.mem_filter.1 hx |>.2
      obtain ⟨y, hy⟩ := b.1.support_nonempty
      have hyc : y ∈ c.1.support := support_mono hb hy
      have hyi : y.1 = i := by
        have : y.1 ∈ b.1.support.image Sigma.fst :=
          Finset.mem_image.2 ⟨y, hy, rfl⟩
        rw [b.2] at this
        exact Finset.mem_singleton.1 this
      have hxy : x = y :=
        componentLabel_injOn_face f U c.1.support_mem_nerve
          (show x ∈ (c.1.support : Set _) from hxc)
          (show y ∈ (c.1.support : Set _) from hyc) (hxi.trans hyi.symm)
      exact hxy ▸ hy
  refine Subtype.ext ((eq_face_of_le hb).trans ?_)
  have key : ∀ {σ σ' : Finset (ComponentIndex f U)} (hσσ' : σ = σ')
      (h₁ : σ.Nonempty) (h₂ : σ'.Nonempty) (s₁ : σ ⊆ c.1.support)
      (s₂ : σ' ⊆ c.1.support), c.1.face σ h₁ s₁ = c.1.face σ' h₂ s₂ := by
    intro σ σ' hσσ' _ _ _ _
    subst hσσ'
    rfl
  show c.1.face b.1.support _ _ =
    c.1.face (c.1.support.filter (fun x => x.1 = i)) _ _
  exact key hsub _ _ _ _

private theorem mem_carrier_labelFace
    (f : C(X, Y)) (U : I → Set Y) [DecidableEq I]
    {τ : Finset I}
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ})
    (i : I) (hi : i ∈ τ) {x : X} (hx : x ∈ c.1.carrier) :
    x ∈ (labelFace f U c i hi).1.carrier := by
  refine ⟨interMember_anti _ (Finset.filter_subset _ _) hx.1, ?_⟩
  show ZerothHomotopy.mk
      (⟨x, interMember_anti _ (Finset.filter_subset _ _) hx.1⟩ :
        interMember (componentCover f U)
          (c.1.support.filter (fun y => y.1 = i))) =
    faceMap (componentCover f U)
      (Finset.filter_subset (fun y => y.1 = i) _) c.1.component
  rw [← hx.2, faceMap_mk]

/-- The path-component map to the member containing a cell is the face map over that member. -/
theorem vertexCellsEquiv_labelFace
    (f : C(X, Y)) (U : I → Set Y) [DecidableEq I]
    {τ : Finset I}
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ})
    (i : I) (hi : i ∈ τ) (hτ : τ.Nonempty)
    (hτi : ⋂ j ∈ τ, U j ⊆ U i) :
    vertexCellsEquiv f U i (labelFace f U c i hi) =
      componentMap (preimageSetInclusion (ContinuousMap.id X) (Set.preimage_mono hτi))
        (cellsOverLabelsEquiv f U τ hτ c) := by
  obtain ⟨x, hx⟩ := c.1.carrier_nonempty
  rw [vertexCellsEquiv, Equiv.trans_apply]
  rw [cellsOverLabelsEquiv_apply_of_mem f U _ _ _
    (mem_carrier_labelFace f U c i hi hx)]
  rw [cellsOverLabelsEquiv_apply_of_mem f U _ _ _ hx]
  rfl

/-- The left face of a two-label cell is the component map from the binary intersection. -/
theorem vertexCellsEquiv_labelFace_pair_left
    (f : C(X, Y)) (U : I → Set Y) [DecidableEq I] {i j : I}
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = {i, j}}) :
    vertexCellsEquiv f U i (labelFace f U c i (Finset.mem_insert_self _ _)) =
      componentMap (preimageSetInclusion (ContinuousMap.id X) (Set.preimage_mono
        (Set.inter_subset_left : U i ∩ U j ⊆ U i))) (edgeCellsEquiv f U i j c) := by
  obtain ⟨x, hx⟩ := c.1.carrier_nonempty
  simp only [vertexCellsEquiv, edgeCellsEquiv, Equiv.trans_apply]
  rw [cellsOverLabelsEquiv_apply_of_mem f U _ _ _
    (mem_carrier_labelFace f U c i (Finset.mem_insert_self _ _) hx)]
  rw [cellsOverLabelsEquiv_apply_of_mem f U _ _ _ hx]
  rfl

/-- The right face of a two-label cell is the component map from the binary intersection. -/
theorem vertexCellsEquiv_labelFace_pair_right
    (f : C(X, Y)) (U : I → Set Y) [DecidableEq I] {i j : I}
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = {i, j}}) :
    vertexCellsEquiv f U j (labelFace f U c j
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) =
      componentMap (preimageSetInclusion (ContinuousMap.id X) (Set.preimage_mono
        (Set.inter_subset_right : U i ∩ U j ⊆ U j))) (edgeCellsEquiv f U i j c) := by
  obtain ⟨x, hx⟩ := c.1.carrier_nonempty
  simp only [vertexCellsEquiv, edgeCellsEquiv, Equiv.trans_apply]
  rw [cellsOverLabelsEquiv_apply_of_mem f U _ _ _
    (mem_carrier_labelFace f U c j
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hx)]
  rw [cellsOverLabelsEquiv_apply_of_mem f U _ _ _ hx]
  rfl

end

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
