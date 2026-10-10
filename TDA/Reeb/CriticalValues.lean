import TDA.Reeb.Interval

/-!
# Critical levels, stars, gaps and envelopes

A critical-value list `S : CriticalValues n` is a strictly increasing `a : Fin (n + 1) → ℝ`;
`n` counts the internal regular gaps, so there are `n + 1` levels. This is the setting of
de Silva–Munch–Patel, Notation 3.11, for constructible cosheaves over `ℝ`. The list is a witness,
not a minimal critical set.

* Stars and gaps. The star of level `i` is `J i = (a (i-1), a (i+1))`, with `-∞` and `+∞` at
  the extremes (`lowerCut`, `upperCut`). The regular gap of edge `e : Fin n` is
  `K e = (a e, a (e+1))`, with endpoint levels `e.castSucc` and `e.succ`. The exterior tails are
  the rays `lowerTail = (-∞, a 0)` and `upperTail = (a n, ∞)`. For `n = 0` the single star is
  `ℝ` (`J_eq_top_of_zero`) and there are no gaps. The cut list `cut : Fin (n + 3) → EReal`
  (`-∞`, the levels, `+∞`) gives the same star bounds (`lowerCut_eq_cut`, `upperCut_eq_cut`).
* Overlaps. Adjacent stars meet in their common gap (`J_castSucc_inf_J_succ`), nonadjacent stars
  are disjoint (`J_inf_J_eq_bot`), a star contains exactly one level (`value_mem_J_iff`), and a
  gap lies in a star exactly when the star is incident to it (`K_le_J_iff`).
* Envelopes. `envelope I` is the greatest interval containing `I` that meets the same levels,
  for nonempty `I` (`le_envelope`, `value_mem_envelope_iff`, `le_envelope_of_le`). The
  envelope of an empty interval is `⊥` (`envelope_eq_bot`); no separate case is needed in the
  definition. The envelope is monotone (`envelope_mono`) and idempotent (`envelope_envelope`),
  and refining the levels shrinks it (`envelope_le_of_refines`). It does not preserve
  intersections (`exists_envelope_inf_ne`). `envelopeFunctor` and `envelopeUnit` package it as
  an endofunctor of the interval category with the inclusion unit.
* Pieces. `Piece n` indexes the stars, gaps and the two tails. Every piece is its own envelope
  (`envelope_piece`). Every interval that is its own envelope is the union of the pieces it
  contains (`iUnion_piece_eq`), and an envelope meeting a level is the union of the stars of the
  levels it meets (`iUnion_J_eq_envelope`). A gap inside such an interval either is the whole
  interval or lies in an incident star contained in it (`K_le_envelope_cases`).

See `docs/math/reeb-constructible-cosheaf.md`.
-/

open Set CategoryTheory

namespace TDA.Reeb

noncomputable section

namespace OpenInterval

theorem mem_ioo {a b x : ℝ} : x ∈ ioo a b ↔ a < x ∧ x < b := Iff.rfl
theorem mem_iio {b x : ℝ} : x ∈ iio b ↔ x < b := Iff.rfl
theorem mem_ioi {a x : ℝ} : x ∈ ioi a ↔ a < x := Iff.rfl

/-- An open interval contains every point between two of its points. -/
theorem mem_of_le_of_le {I : OpenInterval} {x y z : ℝ} (hx : x ∈ I) (hz : z ∈ I) (hxy : x ≤ y)
    (hyz : y ≤ z) : y ∈ I :=
  I.ordConnected.out hx hz ⟨hxy, hyz⟩

end OpenInterval

open OpenInterval

/-- A nonempty strictly increasing list of critical levels `a 0 < ⋯ < a n`. `n` counts the
internal regular gaps; there are `n + 1` levels and two exterior gaps. -/
structure CriticalValues (n : ℕ) where
  /-- The levels. -/
  value : Fin (n + 1) → ℝ
  /-- The levels are strictly increasing. -/
  strictMono : StrictMono value

namespace CriticalValues

variable {n : ℕ} (S : CriticalValues n)

/-! ### Stars, gaps and tails -/

/-- Lower end of the star of level `i`: `a (i - 1)`, or `-∞` for `i = 0`. -/
def lowerCut (i : Fin (n + 1)) : EReal :=
  Fin.cases (motive := fun _ => EReal) ⊥ (fun k : Fin n => ((S.value k.castSucc : ℝ) : EReal)) i

/-- Upper end of the star of level `i`: `a (i + 1)`, or `+∞` for `i = last`. -/
def upperCut (i : Fin (n + 1)) : EReal :=
  Fin.lastCases (motive := fun _ => EReal) ⊤ (fun k : Fin n => ((S.value k.succ : ℝ) : EReal)) i

/-- The open star `J i = (a (i-1), a (i+1))`, with infinite extremes. -/
def J (i : Fin (n + 1)) : OpenInterval := ofEReal (S.lowerCut i) (S.upperCut i)

/-- The regular gap `K e = (a e, a (e+1))` of edge `e`; its endpoint levels are `e.castSucc`
and `e.succ`. -/
def K (e : Fin n) : OpenInterval := ioo (S.value e.castSucc) (S.value e.succ)

/-- The lower exterior tail `(-∞, a 0)`. -/
def lowerTail : OpenInterval := iio (S.value 0)

/-- The upper exterior tail `(a n, ∞)`. -/
def upperTail : OpenInterval := ioi (S.value (Fin.last n))

@[simp] theorem lowerCut_zero : S.lowerCut 0 = ⊥ := Fin.cases_zero ..

@[simp] theorem lowerCut_succ (k : Fin n) : S.lowerCut k.succ = (S.value k.castSucc : EReal) :=
  Fin.cases_succ ..

@[simp] theorem upperCut_last : S.upperCut (Fin.last n) = ⊤ := Fin.lastCases_last ..

@[simp] theorem upperCut_castSucc (k : Fin n) :
    S.upperCut k.castSucc = (S.value k.succ : EReal) := Fin.lastCases_castSucc ..

theorem mem_J {i : Fin (n + 1)} {x : ℝ} :
    x ∈ S.J i ↔ S.lowerCut i < (x : EReal) ∧ (x : EReal) < S.upperCut i := Iff.rfl

theorem mem_K {e : Fin n} {x : ℝ} :
    x ∈ S.K e ↔ S.value e.castSucc < x ∧ x < S.value e.succ := Iff.rfl

theorem mem_lowerTail {x : ℝ} : x ∈ S.lowerTail ↔ x < S.value 0 := Iff.rfl

theorem mem_upperTail {x : ℝ} : x ∈ S.upperTail ↔ S.value (Fin.last n) < x := Iff.rfl

/-- The lower star bound in terms of the levels: `a (i-1) < x`, vacuous for `i = 0`. -/
theorem lowerCut_lt_iff {i : Fin (n + 1)} {x : ℝ} :
    S.lowerCut i < (x : EReal) ↔ ∀ k : Fin (n + 1), k.val + 1 = i.val → S.value k < x := by
  cases i using Fin.cases with
  | zero => simp
  | succ m =>
    rw [lowerCut_succ, EReal.coe_lt_coe_iff]
    refine ⟨fun h k hk => ?_, fun h => h _ (by simp)⟩
    rwa [show k = m.castSucc from Fin.ext (by simp at hk; simp; omega)]

/-- The upper star bound in terms of the levels: `x < a (i+1)`, vacuous for `i = last`. -/
theorem lt_upperCut_iff {i : Fin (n + 1)} {x : ℝ} :
    (x : EReal) < S.upperCut i ↔ ∀ k : Fin (n + 1), i.val + 1 = k.val → x < S.value k := by
  cases i using Fin.lastCases with
  | last => simp only [upperCut_last, EReal.coe_lt_top, Fin.val_last, true_iff]; omega
  | cast m =>
    rw [upperCut_castSucc, EReal.coe_lt_coe_iff]
    refine ⟨fun h k hk => ?_, fun h => h _ (by simp)⟩
    rwa [show k = m.succ from Fin.ext (by simp at hk; simp; omega)]

/-- Membership in a star in terms of the two neighbouring levels. -/
theorem mem_J_iff {i : Fin (n + 1)} {x : ℝ} :
    x ∈ S.J i ↔ (∀ k : Fin (n + 1), k.val + 1 = i.val → S.value k < x) ∧
      (∀ k : Fin (n + 1), i.val + 1 = k.val → x < S.value k) := by
  rw [mem_J, lowerCut_lt_iff, lt_upperCut_iff]

theorem lowerCut_lt_value (i : Fin (n + 1)) : S.lowerCut i < (S.value i : EReal) :=
  S.lowerCut_lt_iff.2 fun _ hk => S.strictMono (show _ < _ from by rw [Fin.lt_def]; omega)

theorem value_lt_upperCut (i : Fin (n + 1)) : (S.value i : EReal) < S.upperCut i :=
  S.lt_upperCut_iff.2 fun _ hk => S.strictMono (show _ < _ from by rw [Fin.lt_def]; omega)

/-- Every level lies in its own star. -/
theorem value_mem_J (i : Fin (n + 1)) : S.value i ∈ S.J i :=
  ⟨S.lowerCut_lt_value i, S.value_lt_upperCut i⟩

/-- A star contains exactly one level. -/
theorem value_mem_J_iff {i k : Fin (n + 1)} : S.value k ∈ S.J i ↔ k = i := by
  refine ⟨fun h => ?_, fun h => h ▸ S.value_mem_J i⟩
  obtain ⟨h₁, h₂⟩ := S.mem_J_iff.1 h
  refine Fin.ext (le_antisymm ?_ ?_)
  · by_contra hlt
    have := h₂ ⟨i.val + 1, by omega⟩ rfl
    exact absurd this (not_lt.2 (S.strictMono.monotone (show _ ≤ _ from by
      rw [Fin.le_def]; simp; omega)))
  · by_contra hlt
    have := h₁ ⟨i.val - 1, by omega⟩ (by simp; omega)
    exact absurd this (not_lt.2 (S.strictMono.monotone (show _ ≤ _ from by
      rw [Fin.le_def]; simp; omega)))

/-- Gap inclusion into the left incident star. -/
theorem K_le_J_castSucc (e : Fin n) : S.K e ≤ S.J e.castSucc :=
  OpenInterval.le_iff_subset.2 fun x hx => by
    obtain ⟨h₁, h₂⟩ := mem_ioo.1 hx
    refine ⟨(S.lowerCut_lt_value _).trans (EReal.coe_lt_coe_iff.2 h₁), ?_⟩
    rw [upperCut_castSucc]
    exact EReal.coe_lt_coe_iff.2 h₂

/-- Gap inclusion into the right incident star. -/
theorem K_le_J_succ (e : Fin n) : S.K e ≤ S.J e.succ :=
  OpenInterval.le_iff_subset.2 fun x hx => by
    obtain ⟨h₁, h₂⟩ := mem_ioo.1 hx
    refine ⟨?_, (EReal.coe_lt_coe_iff.2 h₂).trans (S.value_lt_upperCut _)⟩
    rw [lowerCut_succ]
    exact EReal.coe_lt_coe_iff.2 h₁

/-- Internal regular gaps are nonempty. -/
theorem K_nonempty (e : Fin n) : ((S.K e : OpenInterval) : Set ℝ).Nonempty :=
  nonempty_Ioo.2 (S.strictMono Fin.castSucc_lt_succ)

/-- Gaps avoid every level. -/
theorem value_notMem_K (e : Fin n) (i : Fin (n + 1)) : S.value i ∉ S.K e := by
  rintro ⟨h₁, h₂⟩
  rcases lt_or_ge i e.succ with h | h
  · have : i ≤ e.castSucc := Fin.le_castSucc_iff.2 h
    exact absurd h₁ (not_lt.2 (S.strictMono.monotone this))
  · exact absurd h₂ (not_lt.2 (S.strictMono.monotone h))

theorem value_notMem_lowerTail (i : Fin (n + 1)) : S.value i ∉ S.lowerTail := fun h =>
  absurd (S.mem_lowerTail.1 h) (not_lt.2 (S.strictMono.monotone (Fin.zero_le i)))

theorem value_notMem_upperTail (i : Fin (n + 1)) : S.value i ∉ S.upperTail := fun h =>
  absurd (S.mem_upperTail.1 h) (not_lt.2 (S.strictMono.monotone (Fin.le_last i)))

/-- Boundary `n = 0`: the single star is `ℝ`, and there are no edges. -/
theorem J_eq_top_of_zero (S : CriticalValues 0) : S.J 0 = ⊤ := by
  have h₂ : S.upperCut 0 = ⊤ := S.upperCut_last
  ext x
  rw [S.mem_J, lowerCut_zero, h₂]
  exact ⟨fun _ => trivial, fun _ => ⟨EReal.bot_lt_coe x, EReal.coe_lt_top x⟩⟩

/-- The lower tail lies in the first star. -/
theorem lowerTail_le_J_zero : S.lowerTail ≤ S.J 0 :=
  OpenInterval.le_iff_subset.2 fun x hx => S.mem_J_iff.2
    ⟨fun _ hk => by simp at hk, fun k hk => (S.mem_lowerTail.1 hx).trans_le
      (S.strictMono.monotone (Fin.zero_le k))⟩

/-- The upper tail lies in the last star. -/
theorem upperTail_le_J_last : S.upperTail ≤ S.J (Fin.last n) :=
  OpenInterval.le_iff_subset.2 fun x hx => S.mem_J_iff.2
    ⟨fun k _ => (S.strictMono.monotone (Fin.le_last k)).trans_lt (S.mem_upperTail.1 hx),
      fun k hk => by have := k.isLt; simp at hk; omega⟩

/-! ### The cut encoding -/

/-- Cut list `Fin (n + 3) → EReal`: index `0` is `-∞`, index `i.succ.castSucc` is `a i`, and
the last index is `+∞`. -/
def cut : Fin (n + 3) → EReal :=
  Fin.snoc (α := fun _ => EReal) (Fin.cons (α := fun _ => EReal) ⊥ fun j => (S.value j : EReal)) ⊤

theorem cut_vertex (i : Fin (n + 1)) : S.cut i.succ.castSucc = S.value i := by
  simp only [cut, Fin.snoc_castSucc, Fin.cons_succ]

theorem lowerCut_eq_cut (i : Fin (n + 1)) : S.lowerCut i = S.cut i.castSucc.castSucc := by
  cases i using Fin.cases with
  | zero => simp [cut]
  | succ k =>
    have hk : k.succ.castSucc = k.castSucc.succ := Fin.ext rfl
    simp only [lowerCut_succ, cut, Fin.snoc_castSucc, hk, Fin.cons_succ]

theorem upperCut_eq_cut (i : Fin (n + 1)) : S.upperCut i = S.cut i.succ.succ := by
  cases i using Fin.lastCases with
  | last => simp [cut]
  | cast k =>
    have hk : k.castSucc.succ.succ = k.succ.succ.castSucc := Fin.ext rfl
    simp only [upperCut_castSucc, cut, hk, Fin.snoc_castSucc, Fin.cons_succ]

/-! ### Overlaps of stars and gaps -/

/-- Adjacent stars meet in their common gap. -/
theorem J_castSucc_inf_J_succ (e : Fin n) : S.J e.castSucc ⊓ S.J e.succ = S.K e := by
  refine le_antisymm (OpenInterval.le_iff_subset.2 fun x hx => ?_)
    (le_inf (S.K_le_J_castSucc e) (S.K_le_J_succ e))
  obtain ⟨h₁, h₂⟩ := (show x ∈ S.J e.castSucc ∧ x ∈ S.J e.succ from hx)
  exact ⟨(S.mem_J_iff.1 h₂).1 _ (by simp), (S.mem_J_iff.1 h₁).2 _ (by simp)⟩

/-- Nonadjacent stars are disjoint. -/
theorem J_inf_J_eq_bot {i j : Fin (n + 1)} (h : i.val + 1 < j.val) : S.J i ⊓ S.J j = ⊥ := by
  refine le_antisymm (OpenInterval.le_iff_subset.2 fun x hx => ?_) bot_le
  obtain ⟨h₁, h₂⟩ := (show x ∈ S.J i ∧ x ∈ S.J j from hx)
  have hu := (S.mem_J_iff.1 h₁).2 ⟨i.val + 1, by omega⟩ rfl
  have hl := (S.mem_J_iff.1 h₂).1 ⟨j.val - 1, by omega⟩ (by simp; omega)
  exact absurd (hl.trans hu) (not_lt.2 (S.strictMono.monotone (show _ ≤ _ from by
    rw [Fin.le_def]; simp; omega)))

/-- If an interval contains a gap and meets some level, it contains an endpoint level of the
gap. -/
theorem value_mem_of_K_le {e : Fin n} {U : OpenInterval} (hK : S.K e ≤ U)
    (hU : ∃ k, S.value k ∈ U) : S.value e.castSucc ∈ U ∨ S.value e.succ ∈ U := by
  obtain ⟨k, hk⟩ := hU
  obtain ⟨y, hy⟩ := S.K_nonempty e
  have hyU : y ∈ U := hK hy
  obtain ⟨hy₁, hy₂⟩ := S.mem_K.1 hy
  rcases le_or_gt k e.castSucc with hke | hke
  · exact Or.inl (mem_of_le_of_le hk hyU (S.strictMono.monotone hke) hy₁.le)
  · exact Or.inr (mem_of_le_of_le hyU hk hy₂.le
      (S.strictMono.monotone (Fin.castSucc_lt_iff_succ_le.1 hke)))

/-- A gap lies in a star exactly when the star is incident to it. -/
theorem K_le_J_iff {e : Fin n} {j : Fin (n + 1)} :
    S.K e ≤ S.J j ↔ j = e.castSucc ∨ j = e.succ := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases S.value_mem_of_K_le h ⟨j, S.value_mem_J j⟩ with h' | h'
    · exact Or.inl (S.value_mem_J_iff.1 h').symm
    · exact Or.inr (S.value_mem_J_iff.1 h').symm
  · rintro (rfl | rfl)
    exacts [S.K_le_J_castSucc e, S.K_le_J_succ e]

/-- Distinct gaps are disjoint. -/
theorem eq_of_K_inf_K_nonempty {e e' : Fin n}
    (h : ((S.K e ⊓ S.K e' : OpenInterval) : Set ℝ).Nonempty) : e = e' := by
  obtain ⟨y, hy, hy'⟩ := h
  obtain ⟨h₁, h₂⟩ := S.mem_K.1 hy
  obtain ⟨h₁', h₂'⟩ := S.mem_K.1 hy'
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exact absurd (h₁'.trans h₂) (not_lt.2 (S.strictMono.monotone
      (Fin.succ_le_castSucc_iff.2 hlt)))
  · exact heq
  · exact absurd (h₁.trans h₂') (not_lt.2 (S.strictMono.monotone
      (Fin.succ_le_castSucc_iff.2 hgt)))

theorem eq_of_K_le_K {e e' : Fin n} (h : S.K e ≤ S.K e') : e = e' :=
  S.eq_of_K_inf_K_nonempty (by rw [inf_eq_left.2 h]; exact S.K_nonempty e)

theorem not_K_le_lowerTail (e : Fin n) : ¬ S.K e ≤ S.lowerTail := fun h => by
  obtain ⟨y, hy⟩ := S.K_nonempty e
  exact absurd ((S.mem_K.1 hy).1.trans (S.mem_lowerTail.1 (h hy)))
    (not_lt.2 (S.strictMono.monotone (Fin.zero_le _)))

theorem not_K_le_upperTail (e : Fin n) : ¬ S.K e ≤ S.upperTail := fun h => by
  obtain ⟨y, hy⟩ := S.K_nonempty e
  exact absurd ((S.mem_upperTail.1 (h hy)).trans (S.mem_K.1 hy).2)
    (not_lt.2 (S.strictMono.monotone (Fin.le_last _)))

/-! ### Envelopes -/

open Classical in
/-- Lower end of the envelope: the largest level lying strictly below every point of `I`, or
`-∞` if there is none. -/
noncomputable def envLower (I : OpenInterval) : EReal :=
  (Finset.univ.filter fun i => ∀ x ∈ I, S.value i < x).sup fun i => (S.value i : EReal)

open Classical in
/-- Upper end of the envelope: the smallest level lying strictly above every point of `I`, or
`+∞` if there is none. -/
noncomputable def envUpper (I : OpenInterval) : EReal :=
  (Finset.univ.filter fun i => ∀ x ∈ I, x < S.value i).inf fun i => (S.value i : EReal)

/-- The envelope of `I`: the open interval between the nearest levels outside `I`. For nonempty
`I` it is the greatest interval containing `I` that meets the same levels; for empty `I` it is
`⊥`. -/
noncomputable def envelope (I : OpenInterval) : OpenInterval :=
  ofEReal (S.envLower I) (S.envUpper I)

/-- Membership in the envelope: every level below all of `I` is below `x`, and every level above
all of `I` is above `x`. -/
theorem mem_envelope {I : OpenInterval} {x : ℝ} :
    x ∈ S.envelope I ↔ (∀ i, (∀ y ∈ I, S.value i < y) → S.value i < x) ∧
      (∀ i, (∀ y ∈ I, y < S.value i) → x < S.value i) := by
  classical
  rw [envelope, mem_ofEReal, envLower, envUpper, Finset.sup_lt_iff (EReal.bot_lt_coe x),
    Finset.lt_inf_iff (EReal.coe_lt_top x)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, EReal.coe_lt_coe_iff]

/-- Extensivity: `I ≤ envelope I`. -/
theorem le_envelope (I : OpenInterval) : I ≤ S.envelope I := fun x hx =>
  S.mem_envelope.2 ⟨fun _ hi => hi x hx, fun _ hi => hi x hx⟩

/-- Monotonicity of the envelope. -/
theorem envelope_mono {I I' : OpenInterval} (h : I ≤ I') : S.envelope I ≤ S.envelope I' :=
  fun x hx => by
    obtain ⟨h₁, h₂⟩ := S.mem_envelope.1 hx
    exact S.mem_envelope.2 ⟨fun i hi => h₁ i fun y hy => hi y (h hy),
      fun i hi => h₂ i fun y hy => hi y (h hy)⟩

theorem envelope_monotone : Monotone S.envelope := fun _ _ h => S.envelope_mono h

/-- The envelope of an empty interval is `⊥`. -/
theorem envelope_eq_bot {I : OpenInterval} (hI : ¬ (I : Set ℝ).Nonempty) : S.envelope I = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hI' : ∀ y, y ∉ I := fun y hy => hI ⟨y, hy⟩
  obtain ⟨h₁, h₂⟩ := S.mem_envelope.1 hx
  exact absurd ((h₁ 0 fun y hy => (hI' y hy).elim).trans (h₂ 0 fun y hy => (hI' y hy).elim))
    (lt_irrefl _)

@[simp] theorem envelope_bot : S.envelope ⊥ = ⊥ :=
  S.envelope_eq_bot fun ⟨_, h⟩ => h

/-- Key maximality step: an interval `P` meeting `I` whose levels all lie in `I` is contained in
the envelope of `I`. -/
theorem le_envelope_of_hits {P I : OpenInterval} (hP : ∀ i, S.value i ∈ P → S.value i ∈ I)
    (hPI : ∃ x ∈ P, x ∈ I) : P ≤ S.envelope I := fun y hy => by
  obtain ⟨x, hxP, hxI⟩ := hPI
  refine S.mem_envelope.2 ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hiP : S.value i ∉ P := fun h => lt_irrefl _ (hi _ (hP i h))
    by_contra hle
    exact hiP (mem_of_le_of_le hy hxP (not_lt.1 hle) (hi x hxI).le)
  · have hiP : S.value i ∉ P := fun h => lt_irrefl _ (hi _ (hP i h))
    by_contra hle
    exact hiP (mem_of_le_of_le hxP hy (hi x hxI).le (not_lt.1 hle))

/-- Maximality: an interval containing nonempty `I` and meeting the same levels lies in the
envelope of `I`. -/
theorem le_envelope_of_le {I J : OpenInterval} (hIJ : I ≤ J) (hI : (I : Set ℝ).Nonempty)
    (hhit : ∀ i, S.value i ∈ I ↔ S.value i ∈ J) : J ≤ S.envelope I := by
  obtain ⟨x, hx⟩ := hI
  exact S.le_envelope_of_hits (fun i h => (hhit i).2 h) ⟨x, hIJ hx, hx⟩

/-- Hit preservation: a nonempty interval and its envelope meet the same levels. -/
theorem value_mem_envelope_iff {I : OpenInterval} (hI : (I : Set ℝ).Nonempty) (i : Fin (n + 1)) :
    S.value i ∈ S.envelope I ↔ S.value i ∈ I := by
  refine ⟨fun h => ?_, fun h => S.le_envelope I h⟩
  obtain ⟨h₁, h₂⟩ := S.mem_envelope.1 h
  obtain ⟨y, hy⟩ := hI
  by_contra hiI
  rcases lt_or_gt_of_ne (show S.value i ≠ y from fun he => hiI (he ▸ hy)) with hlt | hgt
  · refine lt_irrefl _ (h₁ i fun z hz => ?_)
    by_contra hle
    exact hiI (mem_of_le_of_le hz hy (not_lt.1 hle) hlt.le)
  · refine lt_irrefl _ (h₂ i fun z hz => ?_)
    by_contra hle
    exact hiI (mem_of_le_of_le hy hz hgt.le (not_lt.1 hle))

/-- The envelope of a nonempty interval is nonempty, and conversely. -/
theorem envelope_nonempty_iff {I : OpenInterval} :
    ((S.envelope I : OpenInterval) : Set ℝ).Nonempty ↔ (I : Set ℝ).Nonempty := by
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ => ⟨x, S.le_envelope I hx⟩⟩
  by_contra hI
  rw [S.envelope_eq_bot hI] at h
  exact h.ne_empty rfl

/-- Idempotence of the envelope. -/
theorem envelope_envelope (I : OpenInterval) : S.envelope (S.envelope I) = S.envelope I := by
  by_cases hI : (I : Set ℝ).Nonempty
  · refine le_antisymm ?_ (S.le_envelope _)
    refine S.le_envelope_of_le ((S.le_envelope I).trans (S.le_envelope _)) hI fun i => ?_
    rw [S.value_mem_envelope_iff (S.envelope_nonempty_iff.2 hI),
      S.value_mem_envelope_iff hI]
  · rw [S.envelope_eq_bot hI, envelope_bot]

/-- The envelope of an intersection lies in the intersection of the envelopes. -/
theorem envelope_inf_le (I I' : OpenInterval) :
    S.envelope (I ⊓ I') ≤ S.envelope I ⊓ S.envelope I' :=
  le_inf (S.envelope_mono inf_le_left) (S.envelope_mono inf_le_right)

/-- An intersection of intervals that are their own envelopes is its own envelope. -/
theorem envelope_inf_of_eq {I I' : OpenInterval} (hI : S.envelope I = I)
    (hI' : S.envelope I' = I') : S.envelope (I ⊓ I') = I ⊓ I' := by
  refine le_antisymm ?_ (S.le_envelope _)
  have := S.envelope_inf_le I I'
  rwa [hI, hI'] at this

/-- The envelope does not preserve intersections: two disjoint nonempty subintervals of the lower
tail both have envelope containing the lower tail, while their intersection has envelope `⊥`.
Normalizing a cover therefore does not normalize its overlap diagram. -/
theorem exists_envelope_inf_ne :
    ∃ I I' : OpenInterval, S.envelope (I ⊓ I') ≠ S.envelope I ⊓ S.envelope I' := by
  set a := S.value 0
  have htail : ∀ {I : OpenInterval} (x : ℝ), x ∈ I → I ≤ S.lowerTail →
      S.lowerTail ≤ S.envelope I := fun x hx hI =>
    S.le_envelope_of_hits (fun i h => (S.value_notMem_lowerTail i h).elim) ⟨x, hI hx, hx⟩
  have hsub₁ : iio (a - 2) ≤ S.lowerTail := fun x (hx : x < a - 2) =>
    (S.mem_lowerTail).2 (by linarith)
  have hsub₂ : ioo (a - 1) a ≤ S.lowerTail := fun x hx => (S.mem_lowerTail).2 (mem_ioo.1 hx).2
  refine ⟨iio (a - 2), ioo (a - 1) a, fun h => ?_⟩
  have hdisj : iio (a - 2) ⊓ ioo (a - 1) a = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨h₁, h₂⟩ := (show x < a - 2 ∧ (a - 1 < x ∧ x < a) from hx)
    linarith
  rw [hdisj, envelope_bot] at h
  have hmem : a - 1 / 2 ∈ S.envelope (iio (a - 2)) ⊓ S.envelope (ioo (a - 1) a) :=
    ⟨htail (a - 3) (show a - 3 < a - 2 by linarith) hsub₁ ((S.mem_lowerTail).2 (by linarith)),
      htail (a - 1 / 2) (mem_ioo.2 ⟨by linarith, by linarith⟩) hsub₂
        ((S.mem_lowerTail).2 (by linarith))⟩
  rw [← h] at hmem
  exact hmem

/-- Refinement: if every level of `S` is a level of `T`, the `T`-envelope lies in the
`S`-envelope. -/
theorem envelope_le_of_refines {m : ℕ} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value) (I : OpenInterval) :
    T.envelope I ≤ S.envelope I := fun x hx => by
  obtain ⟨h₁, h₂⟩ := T.mem_envelope.1 hx
  refine S.mem_envelope.2 ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨j, hj⟩ := hST ⟨i, rfl⟩
    rw [← hj] at hi ⊢
    exact h₁ j hi
  · obtain ⟨j, hj⟩ := hST ⟨i, rfl⟩
    rw [← hj] at hi ⊢
    exact h₂ j hi

/-- Refinement moves the lower tail down. -/
theorem lowerTail_le_of_refines {m : ℕ} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value) : T.lowerTail ≤ S.lowerTail := fun x hx => by
  obtain ⟨j, hj⟩ := hST ⟨0, rfl⟩
  exact S.mem_lowerTail.2 (hj ▸ (T.mem_lowerTail.1 hx).trans_le
    (T.strictMono.monotone (Fin.zero_le j)))

/-- Refinement moves the upper tail up. -/
theorem upperTail_le_of_refines {m : ℕ} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value) : T.upperTail ≤ S.upperTail := fun x hx => by
  obtain ⟨j, hj⟩ := hST ⟨Fin.last n, rfl⟩
  exact S.mem_upperTail.2 (hj ▸ (T.strictMono.monotone (Fin.le_last j)).trans_lt
    (T.mem_upperTail.1 hx))

/-- The envelope as an endofunctor of the interval category. -/
noncomputable def envelopeFunctor : OpenInterval ⥤ OpenInterval := S.envelope_monotone.functor

@[simp] theorem envelopeFunctor_obj (I : OpenInterval) :
    S.envelopeFunctor.obj I = S.envelope I := rfl

/-- The unit `I ⟶ envelope I`. -/
noncomputable def envelopeUnit : 𝟭 OpenInterval ⟶ S.envelopeFunctor where
  app I := homOfLE (S.le_envelope I)

/-- An interval with bounds that are `±∞` or levels contains its envelope. -/
theorem envelope_ofEReal_le {lo hi : EReal} (hlo : lo = ⊥ ∨ ∃ k, lo = S.value k)
    (hhi : hi = ⊤ ∨ ∃ k, hi = S.value k) : S.envelope (ofEReal lo hi) ≤ ofEReal lo hi :=
  fun x hx => by
    obtain ⟨h₁, h₂⟩ := S.mem_envelope.1 hx
    refine ⟨?_, ?_⟩
    · rcases hlo with rfl | ⟨k, rfl⟩
      · exact EReal.bot_lt_coe x
      · exact EReal.coe_lt_coe_iff.2 (h₁ k fun y hy => EReal.coe_lt_coe_iff.1 hy.1)
    · rcases hhi with rfl | ⟨k, rfl⟩
      · exact EReal.coe_lt_top x
      · exact EReal.coe_lt_coe_iff.2 (h₂ k fun y hy => EReal.coe_lt_coe_iff.1 hy.2)

theorem K_eq_ofEReal (e : Fin n) :
    S.K e = ofEReal (S.value e.castSucc : EReal) (S.value e.succ : EReal) := by
  ext x; simp [mem_K]

theorem lowerTail_eq_ofEReal : S.lowerTail = ofEReal ⊥ (S.value 0 : EReal) := by
  ext x; simp [mem_lowerTail]

theorem upperTail_eq_ofEReal : S.upperTail = ofEReal (S.value (Fin.last n) : EReal) ⊤ := by
  ext x; simp [mem_upperTail]

theorem envelope_J (i : Fin (n + 1)) : S.envelope (S.J i) = S.J i := by
  refine le_antisymm (S.envelope_ofEReal_le ?_ ?_) (S.le_envelope _)
  · cases i using Fin.cases with
    | zero => exact Or.inl (S.lowerCut_zero)
    | succ k => exact Or.inr ⟨_, S.lowerCut_succ k⟩
  · cases i using Fin.lastCases with
    | last => exact Or.inl S.upperCut_last
    | cast k => exact Or.inr ⟨_, S.upperCut_castSucc k⟩

theorem envelope_K (e : Fin n) : S.envelope (S.K e) = S.K e := by
  refine le_antisymm ?_ (S.le_envelope _)
  rw [S.K_eq_ofEReal]
  exact S.envelope_ofEReal_le (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩)

theorem envelope_lowerTail : S.envelope S.lowerTail = S.lowerTail := by
  refine le_antisymm ?_ (S.le_envelope _)
  rw [S.lowerTail_eq_ofEReal]
  exact S.envelope_ofEReal_le (Or.inl rfl) (Or.inr ⟨_, rfl⟩)

theorem envelope_upperTail : S.envelope S.upperTail = S.upperTail := by
  refine le_antisymm ?_ (S.le_envelope _)
  rw [S.upperTail_eq_ofEReal]
  exact S.envelope_ofEReal_le (Or.inr ⟨_, rfl⟩) (Or.inl rfl)

/-- A star lies in the envelope of every interval containing its level. -/
theorem J_le_envelope {I : OpenInterval} {i : Fin (n + 1)} (h : S.value i ∈ I) :
    S.J i ≤ S.envelope I :=
  S.le_envelope_of_hits (fun _ hk => (S.value_mem_J_iff.1 hk) ▸ h) ⟨_, S.value_mem_J i, h⟩

/-- A subinterval of a star containing its level has the star as envelope. -/
theorem envelope_eq_J {I : OpenInterval} {i : Fin (n + 1)} (hI : I ≤ S.J i)
    (h : S.value i ∈ I) : S.envelope I = S.J i :=
  le_antisymm ((S.envelope_mono hI).trans_eq (S.envelope_J i)) (S.J_le_envelope h)

/-- A nonempty subinterval of a gap has the gap as envelope. -/
theorem envelope_eq_K {I : OpenInterval} {e : Fin n} (hI : I ≤ S.K e)
    (hne : (I : Set ℝ).Nonempty) : S.envelope I = S.K e :=
  le_antisymm ((S.envelope_mono hI).trans_eq (S.envelope_K e))
    (S.le_envelope_of_le hI hne fun i =>
      iff_of_false (fun h => S.value_notMem_K e i (hI h)) (S.value_notMem_K e i))

/-- A nonempty subinterval of the lower tail has the lower tail as envelope. -/
theorem envelope_eq_lowerTail {I : OpenInterval} (hI : I ≤ S.lowerTail)
    (hne : (I : Set ℝ).Nonempty) : S.envelope I = S.lowerTail :=
  le_antisymm ((S.envelope_mono hI).trans_eq S.envelope_lowerTail)
    (S.le_envelope_of_le hI hne fun i =>
      iff_of_false (fun h => S.value_notMem_lowerTail i (hI h)) (S.value_notMem_lowerTail i))

/-- A nonempty subinterval of the upper tail has the upper tail as envelope. -/
theorem envelope_eq_upperTail {I : OpenInterval} (hI : I ≤ S.upperTail)
    (hne : (I : Set ℝ).Nonempty) : S.envelope I = S.upperTail :=
  le_antisymm ((S.envelope_mono hI).trans_eq S.envelope_upperTail)
    (S.le_envelope_of_le hI hne fun i =>
      iff_of_false (fun h => S.value_notMem_upperTail i (hI h)) (S.value_notMem_upperTail i))

/-! ### Pieces: stars, gaps and tails -/

/-- Index of the pieces: the `n + 1` stars, the `n` gaps and the two exterior tails. -/
inductive Piece (n : ℕ) : Type
  /-- The star of a level. -/
  | star (i : Fin (n + 1))
  /-- The gap of an edge. -/
  | gap (e : Fin n)
  /-- The lower exterior tail. -/
  | lowerTail
  /-- The upper exterior tail. -/
  | upperTail

/-- The interval of a piece. -/
def piece : Piece n → OpenInterval
  | .star i => S.J i
  | .gap e => S.K e
  | .lowerTail => S.lowerTail
  | .upperTail => S.upperTail

/-- Every piece is its own envelope. -/
theorem envelope_piece (p : Piece n) : S.envelope (S.piece p) = S.piece p := by
  cases p
  exacts [S.envelope_J _, S.envelope_K _, S.envelope_lowerTail, S.envelope_upperTail]

/-- The only piece containing a level is the star of that level. -/
theorem value_mem_piece_iff {p : Piece n} {k : Fin (n + 1)} :
    S.value k ∈ S.piece p ↔ p = .star k := by
  cases p with
  | star i => exact S.value_mem_J_iff.trans ⟨fun h => h ▸ rfl, fun h => (Piece.star.inj h).symm⟩
  | gap e => exact iff_of_false (S.value_notMem_K e k) fun h => by cases h
  | lowerTail => exact iff_of_false (S.value_notMem_lowerTail k) fun h => by cases h
  | upperTail => exact iff_of_false (S.value_notMem_upperTail k) fun h => by cases h

/-- Every real number lies in a piece containing no other level. -/
theorem exists_piece (x : ℝ) :
    ∃ p : Piece n, x ∈ S.piece p ∧ ∀ i, S.value i ∈ S.piece p → S.value i = x := by
  by_cases hv : ∃ i, S.value i = x
  · obtain ⟨i, rfl⟩ := hv
    exact ⟨.star i, S.value_mem_J i, fun k hk => by rw [S.value_mem_J_iff.1 hk]⟩
  push Not at hv
  by_cases h0 : x < S.value 0
  · exact ⟨.lowerTail, h0, fun i hi => (S.value_notMem_lowerTail i hi).elim⟩
  have h0' : S.value 0 < x := lt_of_le_of_ne (not_lt.1 h0) (hv 0)
  by_cases hn : S.value (Fin.last n) < x
  · exact ⟨.upperTail, hn, fun i hi => (S.value_notMem_upperTail i hi).elim⟩
  classical
  set s := Finset.univ.filter fun i => S.value i < x
  have hs : s.Nonempty := ⟨0, by simp [s, h0']⟩
  set i := s.max' hs
  have hi : S.value i < x := by simpa [s] using s.max'_mem hs
  have hil : i ≠ Fin.last n := fun h => hn (h ▸ hi)
  obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.2 hil
  have hsucc : x < S.value e.succ := by
    refine lt_of_le_of_ne (not_lt.1 fun h => ?_) (fun h => hv _ h.symm)
    have : e.succ ≤ i := s.le_max' e.succ (by simp [s, h])
    rw [← he] at this
    exact absurd this (not_le.2 Fin.castSucc_lt_succ)
  exact ⟨.gap e, ⟨he ▸ hi, hsucc⟩, fun k hk => (S.value_notMem_K e k hk).elim⟩

/-- Every point of an envelope lies in a piece contained in that envelope. -/
theorem exists_piece_le_envelope {I : OpenInterval} {x : ℝ} (hx : x ∈ S.envelope I) :
    ∃ p : Piece n, x ∈ S.piece p ∧ S.piece p ≤ S.envelope I := by
  obtain ⟨p, hxp, hp⟩ := S.exists_piece x
  refine ⟨p, hxp, ?_⟩
  have := S.le_envelope_of_hits (I := S.envelope I) (fun i hi => (hp i hi) ▸ hx) ⟨x, hxp, hx⟩
  rwa [S.envelope_envelope] at this

/-- An interval that is its own envelope is the union of the pieces it contains. -/
theorem iUnion_piece_eq {U : OpenInterval} (hU : S.envelope U = U) :
    ⋃ p : {p : Piece n // S.piece p ≤ U}, (S.piece p.1 : Set ℝ) = U := by
  refine Subset.antisymm (iUnion_subset fun p => OpenInterval.le_iff_subset.1 p.2) fun x hx => ?_
  rw [← hU] at hx
  obtain ⟨p, hxp, hp⟩ := S.exists_piece_le_envelope hx
  exact mem_iUnion.2 ⟨⟨p, hU ▸ hp⟩, hxp⟩

/-- Fringe gaps: a gap inside an interval that is its own envelope is either the whole
interval, or lies in an incident star contained in the interval. -/
theorem K_le_envelope_cases {e : Fin n} {V : OpenInterval} (hV : S.envelope V = V)
    (hK : S.K e ≤ V) : V = S.K e ∨ S.J e.castSucc ≤ V ∨ S.J e.succ ≤ V := by
  by_cases hhit : ∃ k, S.value k ∈ V
  · rcases S.value_mem_of_K_le hK hhit with h | h
    · exact Or.inr (Or.inl (hV ▸ S.J_le_envelope h))
    · exact Or.inr (Or.inr (hV ▸ S.J_le_envelope h))
  · push Not at hhit
    refine Or.inl (le_antisymm ?_ hK)
    rw [← S.envelope_K e]
    exact S.le_envelope_of_le hK (S.K_nonempty e) fun i =>
      iff_of_false (S.value_notMem_K e i) (hhit i)

/-- Selected-star cover: an envelope meeting some level is the union of the stars of the levels
it meets. -/
theorem iUnion_J_eq_envelope {I : OpenInterval} (h : ∃ i, S.value i ∈ I) :
    ⋃ i : {i : Fin (n + 1) // S.value i ∈ I}, (S.J i.1 : Set ℝ) = S.envelope I := by
  have hI : (I : Set ℝ).Nonempty := let ⟨i, hi⟩ := h; ⟨_, hi⟩
  have hN := S.envelope_envelope I
  have hhitN : ∃ k, S.value k ∈ S.envelope I := let ⟨i, hi⟩ := h; ⟨i, S.le_envelope I hi⟩
  have hmem : ∀ {x : ℝ} (k : Fin (n + 1)), S.value k ∈ S.envelope I → x ∈ S.J k →
      x ∈ ⋃ i : {i : Fin (n + 1) // S.value i ∈ I}, (S.J i.1 : Set ℝ) := fun k hk hx =>
    mem_iUnion.2 ⟨⟨k, (S.value_mem_envelope_iff hI k).1 hk⟩, hx⟩
  refine Subset.antisymm (iUnion_subset fun i => OpenInterval.le_iff_subset.1
    (S.J_le_envelope i.2)) fun x hx => ?_
  obtain ⟨p, hxp, hp⟩ := S.exists_piece_le_envelope hx
  cases p with
  | star i => exact hmem i (hp (S.value_mem_J i)) hxp
  | gap e =>
    rcases S.value_mem_of_K_le hp hhitN with h' | h'
    · exact hmem _ h' (S.K_le_J_castSucc e hxp)
    · exact hmem _ h' (S.K_le_J_succ e hxp)
  | lowerTail =>
    obtain ⟨k, hk⟩ := hhitN
    refine hmem 0 (mem_of_le_of_le (hp hxp) hk (S.mem_lowerTail.1 hxp).le
      (S.strictMono.monotone (Fin.zero_le k))) (S.lowerTail_le_J_zero hxp)
  | upperTail =>
    obtain ⟨k, hk⟩ := hhitN
    refine hmem (Fin.last n) (mem_of_le_of_le hk (hp hxp)
      (S.strictMono.monotone (Fin.le_last k)) (S.mem_upperTail.1 hxp).le)
      (S.upperTail_le_J_last hxp)

end CriticalValues

end

end TDA.Reeb
