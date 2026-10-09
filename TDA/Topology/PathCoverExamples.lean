import TDA.Topology.PathCover

/-!
# Path-local open-cover subdivision fixtures

Regression fixtures for `TDA.Topology.exists_subdivision` and its chain forms:

* the straight path `0 ⟶ 1` in `ℝ` crossing the two overlapping opens `(-∞, 2/3)` and
  `(1/3, ∞)`: every overlap chain for it is nonempty, starts in the first member and ends in
  the second;
* the constant path: every admissible subdivision has at least one segment, and every selected
  member contains the point;
* a cover with an empty member and two duplicate members: the empty member is never selected,
  and both duplicates are admissible;
* a non-open cover, the singletons of `[0, 1]`: they cover the identity path, but no finite
  monotone subdivision fits them, so the openness hypothesis cannot be dropped.

The universal fixtures quantify over every subdivision satisfying the segment inclusions; the
accompanying `example`s show that the subdivision theorem supplies such subdivisions.
-/

open Set unitInterval Fin

namespace TDA.Topology.Examples

variable {X : Type*} [TopologicalSpace X] {ι : Sort*} {x : X}

/-- The straight path `0 ⟶ 1` in `ℝ`. -/
def segment : Path (0 : ℝ) 1 where
  toFun s := (s : ℝ)
  continuous_toFun := continuous_subtype_val
  source' := rfl
  target' := rfl

/-- Two overlapping opens `(-∞, 2/3)` and `(1/3, ∞)`. -/
def twoOpens : Bool → Set ℝ
  | false => Iio (2 / 3)
  | true => Ioi (1 / 3)

theorem twoOpens_isOpen : ∀ b, IsOpen (twoOpens b)
  | false => isOpen_Iio
  | true => isOpen_Ioi

theorem twoOpens_cover : ∀ z : ℝ, z ∈ ⋃ b, twoOpens b := fun z => by
  rcases lt_or_ge z (2 / 3) with h | h
  · exact mem_iUnion.2 ⟨false, h⟩
  · exact mem_iUnion.2 ⟨true, show (1 / 3 : ℝ) < z by linarith⟩

/-- A chain exists for the path crossing both opens. -/
theorem segment_chain_exists :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ) (i : Fin n → Bool), p 0 = 0 ∧ p (last n) = 1 ∧
      (∀ k : Fin n, JoinedIn (twoOpens (i k)) (p k.castSucc) (p k.succ)) ∧
      ∀ (k : ℕ) (hk : k + 1 < n),
        p ⟨k + 1, by omega⟩ ∈ twoOpens (i ⟨k, by omega⟩) ∩ twoOpens (i ⟨k + 1, hk⟩) :=
  exists_overlap_chain segment twoOpens_isOpen (fun z _ => twoOpens_cover z)

/-- Every such chain is nonempty, starts in `(-∞, 2/3)` and ends in `(1/3, ∞)`: it genuinely
uses both members and crosses an overlap. -/
theorem segment_chain_uses_both (n : ℕ) (p : Fin (n + 1) → ℝ) (i : Fin n → Bool)
    (p0 : p 0 = 0) (pn : p (last n) = 1)
    (hJ : ∀ k : Fin n, JoinedIn (twoOpens (i k)) (p k.castSucc) (p k.succ)) :
    ∃ hn : 0 < n, i ⟨0, hn⟩ = false ∧ i ⟨n - 1, by omega⟩ = true := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : p (last 0) = p 0 := rfl
      rw [p0, pn] at this; norm_num at this
    · exact hn
  refine ⟨hn, ?_, ?_⟩
  · have h0 := (hJ ⟨0, hn⟩).source_mem
    have : p (castSucc ⟨0, hn⟩) = 0 := p0
    rw [this] at h0
    cases hi : i ⟨0, hn⟩
    · rfl
    · rw [hi] at h0; simp [twoOpens] at h0; norm_num at h0
  · have h1 := (hJ ⟨n - 1, by omega⟩).target_mem
    have : p (succ ⟨n - 1, by omega⟩) = 1 := by
      rw [← pn]; congr 1; ext; simp; omega
    rw [this] at h1
    cases hi : i ⟨n - 1, by omega⟩
    · rw [hi] at h1; simp [twoOpens] at h1; norm_num at h1
    · rfl

/-- Constant path: every subdivision satisfying the segment inclusions has at least one segment,
and every selected member contains the point. -/
theorem refl_subdivision_mem {U : ι → Set X} (n : ℕ) (t : Fin (n + 1) → I) (i : Fin n → ι)
    (t0 : t 0 = 0) (tn : t (last n) = 1) (tmono : Monotone t)
    (hsub : ∀ k : Fin n, Path.refl x '' Icc (t k.castSucc) (t k.succ) ⊆ U (i k)) :
    0 < n ∧ ∀ k, x ∈ U (i k) := by
  refine ⟨?_, fun k => hsub k ⟨t k.castSucc, ⟨le_rfl, tmono (castSucc_le_succ k)⟩, rfl⟩⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : t (last 0) = t 0 := rfl
    rw [t0, tn] at this; exact absurd this one_ne_zero
  · exact hn

/-- The hypotheses of `refl_subdivision_mem` are met by the subdivision theorem. -/
example {U : ι → Set X} (hU : ∀ i, IsOpen (U i)) (hx : x ∈ ⋃ i, U i) :
    ∃ (n : ℕ) (i : Fin n → ι), 0 < n ∧ ∀ k, x ∈ U (i k) := by
  obtain ⟨n, t, i, t0, tn, tmono, hsub⟩ :=
    exists_subdivision (Path.refl x) hU (by rintro _ ⟨s, rfl⟩; simpa using hx)
  exact ⟨n, i, refl_subdivision_mem n t i t0 tn tmono hsub⟩

/-- A cover with an empty member and two duplicate members. -/
def emptyDupCover : Fin 3 → Set ℝ := ![∅, univ, univ]

theorem emptyDupCover_isOpen : ∀ j, IsOpen (emptyDupCover j) := by
  intro j; fin_cases j <;> simp [emptyDupCover]

/-- The empty member is never selected: every monotone subdivision whose segments map into
the selected members of `emptyDupCover` avoids index `0`. -/
theorem emptyDupCover_never_empty (n : ℕ) (t : Fin (n + 1) → I) (i : Fin n → Fin 3)
    (tmono : Monotone t)
    (hsub : ∀ k : Fin n, segment '' Icc (t k.castSucc) (t k.succ) ⊆ emptyDupCover (i k)) :
    ∀ k, i k ≠ 0 := by
  intro k hk
  have := hsub k ⟨t k.castSucc, ⟨le_rfl, tmono (castSucc_le_succ k)⟩, rfl⟩
  rw [hk] at this
  simp [emptyDupCover] at this

/-- Both duplicate members are admissible for any segment. -/
theorem emptyDupCover_duplicates_admissible (s : Set I) :
    segment '' s ⊆ emptyDupCover 1 ∧ segment '' s ⊆ emptyDupCover 2 := by
  simp [emptyDupCover]

/-- The hypotheses of `emptyDupCover_never_empty` are met by the subdivision theorem. -/
example : ∃ (n : ℕ) (t : Fin (n + 1) → I) (i : Fin n → Fin 3), t 0 = 0 ∧ t (last n) = 1 ∧
    Monotone t ∧ ∀ k, i k ≠ 0 := by
  obtain ⟨n, t, i, t0, tn, tmono, hsub⟩ :=
    exists_subdivision segment emptyDupCover_isOpen
      (fun z _ => mem_iUnion.2 ⟨1, by simp [emptyDupCover]⟩)
  exact ⟨n, t, i, t0, tn, tmono, emptyDupCover_never_empty n t i tmono hsub⟩

/-- The identity path of `[0, 1]`. -/
def idPath : Path (0 : I) 1 where
  toFun := id
  continuous_toFun := continuous_id
  source' := rfl
  target' := rfl

/-- Non-open cover: the singletons of `[0, 1]` cover the identity path, but no finite
subdivision has every segment inside one singleton. The open hypothesis cannot be dropped. -/
theorem singletons_no_subdivision :
    ¬ ∃ (n : ℕ) (t : Fin (n + 1) → I) (i : Fin n → I), t 0 = 0 ∧ t (last n) = 1 ∧
      Monotone t ∧ ∀ k : Fin n, idPath '' Icc (t k.castSucc) (t k.succ) ⊆ {i k} := by
  rintro ⟨n, t, i, t0, tn, tmono, hsub⟩
  -- both endpoints of each segment equal `i k`, so `t` is constant along the chain
  have hconst : ∀ (m : ℕ) (hm : m < n + 1), t ⟨m, hm⟩ = t 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hle := tmono (castSucc_le_succ (⟨m, by omega⟩ : Fin n))
      have ha := hsub ⟨m, by omega⟩ ⟨_, ⟨le_rfl, hle⟩, rfl⟩
      have hb := hsub ⟨m, by omega⟩ ⟨_, ⟨hle, le_rfl⟩, rfl⟩
      rw [mem_singleton_iff] at ha hb
      rw [← ih (by omega)]
      exact hb.trans ha.symm
  have := hconst n (by omega)
  rw [show (⟨n, by omega⟩ : Fin (n + 1)) = last n from rfl, tn, t0] at this
  exact zero_ne_one this.symm

end TDA.Topology.Examples
