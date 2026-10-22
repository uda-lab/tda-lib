import TDA.Reeb.RGraphWindow
import TDA.Reeb.GeometricThickening
import TDA.Reeb.CriticalValuesShift

/-!
# Graph thickenings are constructible

The geometric thickening `T_ε` of a finite ℝ-graph is a constructible ℝ-space, for every `ε ≥ 0`
(de Silva–Munch–Patel, *Categorified Reeb Graphs*, Proposition 4.26), proved by the explicit
sliding-window construction of the proof of their Theorem 4.27 on graph input.

## Slabs of the shifted witness

The witness is the merged deduplicated shifted list `S.shifted ε` of `(S - ε) ∪ (S + ε)`, with
levels `b 0 < ⋯ < b m`. Every level lies weakly below or weakly above each closed gap
(`value_le_or_le`). `TransferOK S ε c u` records that `c` avoids every event `a i ± ε` and that the
lower and upper fragment branches persist from `c` to `u`; it holds from any height of an open gap
to any height of the closed gap (`transferOK_of_mem`). `mid S ε k` is the midpoint of gap `k`.

## Window transfer

`win S D ε c` is the window `[c - ε, c + ε]`. Under `TransferOK S ε c u`, the raw maps that fix
window vertices and move an edge parameter `s` to `fragAff a d ε c u s` respect the window gluing
and descend along the window quotient to `windowTransfer S D ε h : C(win c, win u)`. Included
vertices are fixed (`coe_windowTransfer_ofVertex`) and edge points move by `fragAff`
(`coe_windowTransfer_ofCylinder`). For `ε > 0` and mutual transfer hypotheses, for instance two
heights of one open gap, the transfers are mutually inverse (`windowTransfer_windowTransfer`,
`windowTransferHomeomorph`). At a slab end a transfer is an attaching map and need not be
injective.

## The presentation

`thickPresentation S D ε` over `S.shifted ε` has vertex piece `j` the window at `b j`, edge piece
`k` the window at `mid S ε k`, and endpoint maps the window transfers to `b k` and `b (k+1)`. All
pieces are compact, Hausdorff and locally path-connected. The joint cylinder map
`slabCylinder S D ε k : win (mid k) × [b k, b (k+1)] → BandSpace S D ε` descends along the
compact-to-Hausdorff product quotient, with first coordinate the window transfer at the height
(`coe_slabCylinder`). With the vertex maps `x ↦ (x, b j)` it forms compatible maps (`thickCompat`),
and the merged `CylinderPresentation.lift` gives the height-preserving `thickMap` into the band
`{(x, u) | u - ε ≤ f x ≤ u + ε}`.

For `ε > 0` the map is bijective (`thickMap_injective`, `thickMap_surjective`): a critical height is
covered by its vertex piece, and a regular height by the interior inverse transfer. A continuous
bijection from a compact space to a Hausdorff space is a homeomorphism (`thickHomeomorph`), and the
inverse of the merged `bandHomeomorph` gives `thickProdHomeomorph : realization ≃ₜ X × Band ε`,
which carries the presentation height to the thickened height (`height_thickProdHomeomorph`). A
vertex point `x` of level `b j` goes to `(x, b j - f x)` (`fst_thickProdHomeomorph_ofVertex`,
`snd_thickProdHomeomorph_ofVertex`), and a strip point `(x, t)` goes to `(y, t - f y)`, where `y`
is the window transfer of `x` to height `t` (`fst_thickProdHomeomorph_ofStrip`,
`snd_thickProdHomeomorph_ofStrip`).

## The real slice

`thickOverIso S D ε hε` is the isomorphism over `ℝ` from the thickening of the graph object
`toOver S D` to the realization of the presentation. With the merged `GeometricThickening.zeroIso`
at `ε = 0`, every graph object has a constructible thickening (`isConstructibleSpace_thickening`),
and `thickeningToConstructible ε : RGraphCat ⥤ ConstructibleSpaceCat` lifts the `GeometricThickening.functor ε` on all height-preserving maps. Followed by the merged
`quotientRGraphFunctor` and the graph inclusion, it is literally the Reeb quotient of the thickening (`thickeningToConstructible_comp_quotientRGraphFunctor`).

The unbundled construction holds at an arbitrary value universe `u`; the slice packaging is in
universe `0`, as `RGraphCat` and `ConstructibleSpaceCat` are. The raw descent maps are private.

See `docs/math/reeb-rgraph-thickening.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

universe u

namespace TDA.Reeb

noncomputable section

namespace RGraph

open CylinderPresentation

/-! ### Slabs of the shifted witness -/

section Slab

variable {n : ℕ} (S : CriticalValues n) (ε : ℝ≥0)

/-- Every level of a critical list lies weakly below or weakly above each closed gap. -/
theorem value_le_or_le {m : ℕ} (T : CriticalValues m) (j : Fin (m + 1)) (k : Fin m) :
    T.value j ≤ T.value k.castSucc ∨ T.value k.succ ≤ T.value j := by
  rcases le_or_gt j k.castSucc with h | h
  · exact .inl (T.strictMono.monotone h)
  · refine .inr (T.strictMono.monotone ?_)
    rw [Fin.le_def]
    rw [Fin.lt_def] at h
    simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
    omega

/-- **Window transfer hypotheses** from height `c` to height `u`: `c` avoids every event
`a i ± ε`, and the lower and upper fragment branches persist from `c` to `u`. -/
structure TransferOK (c u : ℝ) : Prop where
  ne_sub : ∀ i, c ≠ S.value i - ε
  ne_add : ∀ i, c ≠ S.value i + ε
  lo_le : ∀ i, c - ε ≤ S.value i → u - ε ≤ S.value i
  le_hi : ∀ i, S.value i ≤ c + ε → S.value i ≤ u + ε

/-- **Slab facts.** From a height in an open gap of the shifted witness to any height of the
closed gap, the transfer hypotheses hold: no event `a ± ε` lies in the open slab. -/
theorem transferOK_of_mem {k : Fin (S.shiftedCount ε)} {c u : ℝ}
    (hc : c ∈ ((S.shifted ε).K k : Set ℝ)) (hu : u ∈ Seg (S.shifted ε) k) :
    TransferOK S ε c u := by
  refine ⟨fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_⟩
  · obtain ⟨j, hj⟩ := S.exists_shifted_value_eq_sub ε i
    exact (S.shifted ε).value_notMem_K k j (by rw [hj, ← h]; exact hc)
  · obtain ⟨j, hj⟩ := S.exists_shifted_value_eq_add ε i
    exact (S.shifted ε).value_notMem_K k j (by rw [hj, ← h]; exact hc)
  · obtain ⟨j, hj⟩ := S.exists_shifted_value_eq_add ε i
    have hc1 := hc.1
    rcases value_le_or_le _ j k with h' | h'
    · exact absurd h' (not_le.2 (hc1.trans_le (by linarith)))
    · linarith [hu.2]
  · obtain ⟨j, hj⟩ := S.exists_shifted_value_eq_sub ε i
    have hc2 := hc.2
    rcases value_le_or_le _ j k with h' | h'
    · linarith [hu.1]
    · exact absurd h' (not_le.2 (lt_of_le_of_lt (by linarith) hc2))

/-- The midpoint of a gap of the shifted witness. -/
def mid (k : Fin (S.shiftedCount ε)) : ℝ :=
  ((S.shifted ε).value k.castSucc + (S.shifted ε).value k.succ) / 2

theorem mid_mem_K (k : Fin (S.shiftedCount ε)) : mid S ε k ∈ ((S.shifted ε).K k : Set ℝ) := by
  have := (S.shifted ε).value_castSucc_lt_succ k
  exact ⟨by unfold mid; linarith, by unfold mid; linarith⟩

end Slab

/-! ### Window transfer -/

section Transfer

variable {n : ℕ} (S : CriticalValues n) (D : FiniteReebData.{u} n) (ε : ℝ≥0)

/-- The window of half-width `ε` at height `c`. -/
abbrev win (c : ℝ) : Set ((ofFiniteData D).Realization S) := window S D (c - ε) (c + ε)

/-- The raw joint transfer on raw window points at `c`, as a function of the target height `u`:
vertices are fixed, and an edge parameter `s` goes to `fragAff a d ε c u s`, clamped to the
segment (the clamp is inactive under `TransferOK`). -/
private def transferRaw (c : ℝ) :
    C(WindowRaw S D (c - ε) (c + ε) × ℝ, (ofFiniteData D).Realization S) where
  toFun := Sum.elim (fun p => (ofFiniteData D).ofVertex S p.1.1.1 p.1.1.2)
      ((fun q : Σ c' : (Σ e, D.E e), frag S c'.1 (c - ε) (c + ε) × ℝ =>
        (ofFiniteData D).ofCylinder S q.1.1 (q.1.2, projIcc _ _ (S.value_castSucc_lt_succ q.1.1).le
          (fragAff (S.value q.1.1.castSucc) (S.value q.1.1.succ) ε c q.2.2 q.2.1))) ∘
        Homeomorph.sigmaProdDistrib) ∘ Homeomorph.sumProdDistrib
  continuous_toFun := by
    refine (Continuous.sumElim ?_ ?_).comp Homeomorph.sumProdDistrib.continuous
    · exact (continuous_of_discreteTopology
        (f := fun v : WindowV S D (c - ε) (c + ε) => (ofFiniteData D).ofVertex S v.1.1 v.1.2)).comp
        continuous_fst
    · refine Continuous.comp ?_ Homeomorph.sigmaProdDistrib.continuous
      refine continuous_sigma fun c' => ?_
      dsimp only
      have hf : Continuous fun q : frag S c'.1 (c - ε) (c + ε) × ℝ =>
          projIcc _ _ (S.value_castSucc_lt_succ c'.1).le
            (fragAff (S.value c'.1.castSucc) (S.value c'.1.succ) ε c q.2 q.1) :=
        continuous_projIcc.comp
          ((continuous_fragAff _ _ _ c).comp (continuous_subtype_val.prodMap continuous_id))
      exact ((ofFiniteData D).continuous_ofCylinder S c'.1).comp (continuous_const.prodMk hf)

private theorem transferRaw_inl (c u : ℝ) (v : WindowV S D (c - ε) (c + ε)) :
    transferRaw S D ε c (.inl v, u) = (ofFiniteData D).ofVertex S v.1.1 v.1.2 :=
  rfl

private theorem transferRaw_inr (c u : ℝ) (e : Fin n) (y : D.E e) (s : frag S e (c - ε) (c + ε)) :
    transferRaw S D ε c (.inr ⟨⟨e, y⟩, s⟩, u) =
      (ofFiniteData D).ofCylinder S e (y, projIcc _ _ (S.value_castSucc_lt_succ e).le
        (fragAff (S.value e.castSucc) (S.value e.succ) ε c u s)) :=
  rfl

variable {S ε}

namespace TransferOK

variable {c u : ℝ} (h : TransferOK S ε c u)
include h

theorem vertex_mem {i : Fin (n + 1)} (hi : S.value i ∈ Icc (c - ε) (c + ε)) :
    S.value i ∈ Icc (u - ε) (u + ε) :=
  ⟨h.lo_le i hi.1, h.le_hi i hi.2⟩

theorem frag_le {e : Fin n} {s : ℝ} (hs : s ∈ frag S e (c - ε) (c + ε)) :
    max (S.value e.castSucc) (u - ε) ≤ min (S.value e.succ) (u + ε) := by
  have h1 : S.value e.castSucc ≤ c + ε :=
    (le_max_left _ _).trans (hs.1.trans (hs.2.trans (min_le_right _ _)))
  have h2 : c - ε ≤ S.value e.succ :=
    (le_max_right _ _).trans (hs.1.trans (hs.2.trans (min_le_left _ _)))
  have had := S.value_castSucc_lt_succ e
  have hε := ε.coe_nonneg
  exact max_le (le_min had.le (h.le_hi _ h1)) (le_min (h.lo_le _ h2) (by linarith))

theorem fragAff_mem {e : Fin n} {s : ℝ} (hs : s ∈ frag S e (c - ε) (c + ε)) :
    fragAff (S.value e.castSucc) (S.value e.succ) ε c u s ∈ frag S e (u - ε) (u + ε) :=
  RGraph.fragAff_mem (h.frag_le hs) hs

/-- Positive fragment width at `c`, for `ε > 0`. -/
theorem frag_lt (hε : 0 < ε) {e : Fin n} {s : ℝ} (hs : s ∈ frag S e (c - ε) (c + ε)) :
    max (S.value e.castSucc) (c - ε) < min (S.value e.succ) (c + ε) :=
  fragLo_lt_fragHi (S.value_castSucc_lt_succ e) (NNReal.coe_pos.2 hε)
    ((le_max_left _ _).trans (hs.1.trans (hs.2.trans (min_le_right _ _)))) (h.ne_sub _)
    ((le_max_right _ _).trans (hs.1.trans (hs.2.trans (min_le_left _ _)))) (h.ne_add _)

/-- A fragment end at the lower vertex stays there. -/
theorem fragAff_eq_left {e : Fin n} {s : ℝ} (hs : s ∈ frag S e (c - ε) (c + ε))
    (hsa : s = S.value e.castSucc) :
    fragAff (S.value e.castSucc) (S.value e.succ) ε c u s = S.value e.castSucc := by
  have hca : c - ε ≤ S.value e.castSucc := by
    rw [← hsa]
    exact (le_max_right _ _).trans hs.1
  have hL : max (S.value e.castSucc) (c - ε) = S.value e.castSucc := max_eq_left hca
  calc fragAff (S.value e.castSucc) (S.value e.succ) ε c u s =
        fragAff (S.value e.castSucc) (S.value e.succ) ε c u (max (S.value e.castSucc) (c - ε)) := by
        rw [hL, hsa]
    _ = max (S.value e.castSucc) (u - ε) := fragAff_left _ _ _ _ _
    _ = S.value e.castSucc := max_eq_left (h.lo_le _ hca)

/-- A fragment end at the upper vertex stays there (uses only event avoidance, no `ε > 0`). -/
theorem fragAff_eq_right {e : Fin n} {s : ℝ} (hs : s ∈ frag S e (c - ε) (c + ε))
    (hsd : s = S.value e.succ) :
    fragAff (S.value e.castSucc) (S.value e.succ) ε c u s = S.value e.succ := by
  have hdc : S.value e.succ ≤ c + ε := by
    rw [← hsd]
    exact hs.2.trans (min_le_right _ _)
  have hR : min (S.value e.succ) (c + ε) = S.value e.succ := min_eq_left hdc
  have hlt : max (S.value e.castSucc) (c - ε) < min (S.value e.succ) (c + ε) := by
    rw [hR]
    refine lt_of_le_of_ne (by rw [← hsd]; exact hs.1) fun heq => ?_
    rcases max_choice (S.value e.castSucc) (c - ε) with hm | hm <;> rw [hm] at heq
    · exact (S.value_castSucc_lt_succ e).ne heq
    · exact h.ne_add e.succ (by linarith)
  calc fragAff (S.value e.castSucc) (S.value e.succ) ε c u s =
        fragAff (S.value e.castSucc) (S.value e.succ) ε c u (min (S.value e.succ) (c + ε)) := by
        rw [hR, hsd]
    _ = min (S.value e.succ) (u + ε) := fragAff_right hlt
    _ = S.value e.succ := min_eq_left (h.le_hi _ hdc)

end TransferOK

variable (S ε)

/-- The raw transfer of window points from `c` to `u`. -/
private def rawTransfer {c u : ℝ} (h : TransferOK S ε c u) :
    WindowRaw S D (c - ε) (c + ε) → WindowRaw S D (u - ε) (u + ε) :=
  Sum.map (fun v => ⟨v.1, h.vertex_mem v.2⟩) fun q =>
    ⟨q.1, ⟨fragAff (S.value q.1.1.castSucc) (S.value q.1.1.succ) ε c u q.2, h.fragAff_mem q.2.2⟩⟩

private theorem transferRaw_eq {c u : ℝ} (h : TransferOK S ε c u)
    (r : WindowRaw S D (c - ε) (c + ε)) :
    transferRaw S D ε c (r, u) =
      (windowCover S D (u - ε) (u + ε) (rawTransfer S D ε h r) :
        (ofFiniteData D).Realization S) := by
  rcases r with v | ⟨⟨e, y⟩, s⟩
  · rfl
  · rw [transferRaw_inr, projIcc_of_mem _ (frag_subset_seg (h.fragAff_mem s.2))]
    rfl

/-- The transfer extended to the whole raw sum, clamped to each segment; normal forms are compared
through it in `nf_windowIncl_rawTransfer`. -/
private def transferNf (c u : ℝ) : (ofFiniteData D).Raw S → (ofFiniteData D).Raw S :=
  Sum.elim Sum.inl fun q => .inr ⟨q.1, q.2.1, projIcc _ _ (S.value_castSucc_lt_succ q.1).le
    (fragAff (S.value q.1.castSucc) (S.value q.1.succ) ε c u q.2.2)⟩

/-- The raw transfer commutes with normal forms, so it respects the window gluing. -/
private theorem nf_windowIncl_rawTransfer {c u : ℝ} (h : TransferOK S ε c u)
    (r : WindowRaw S D (c - ε) (c + ε)) :
    (ofFiniteData D).nf S (windowIncl S D _ _ (rawTransfer S D ε h r)) =
      (ofFiniteData D).nf S (transferNf S D ε c u
        ((ofFiniteData D).nf S (windowIncl S D _ _ r))) := by
  rcases r with v | ⟨⟨e, y⟩, s⟩
  · rfl
  · have hmem : fragAff (S.value e.castSucc) (S.value e.succ) ε c u s ∈ frag S e (u - ε) (u + ε) :=
      h.fragAff_mem s.2
    by_cases hsa : (s : ℝ) = S.value e.castSucc
    · have h1 : (⟨s, frag_subset_seg s.2⟩ : Seg S e) = segBot S e := Subtype.ext hsa
      have h2 : (⟨_, frag_subset_seg hmem⟩ : Seg S e) = segBot S e :=
        Subtype.ext (h.fragAff_eq_left s.2 hsa)
      have hL : (ofFiniteData D).nf S (.inr ⟨e, y, ⟨_, frag_subset_seg hmem⟩⟩) =
          .inl ⟨e.castSucc, (ofFiniteData D).left e y⟩ := by
        rw [h2]
        exact (ofFiniteData D).nf_segBot S e y
      have hR : (ofFiniteData D).nf S (.inr ⟨e, y, ⟨s, frag_subset_seg s.2⟩⟩) =
          .inl ⟨e.castSucc, (ofFiniteData D).left e y⟩ := by
        rw [h1]
        exact (ofFiniteData D).nf_segBot S e y
      change (ofFiniteData D).nf S (.inr ⟨e, y, ⟨_, frag_subset_seg hmem⟩⟩) =
        (ofFiniteData D).nf S (transferNf S D ε c u
          ((ofFiniteData D).nf S (.inr ⟨e, y, ⟨s, frag_subset_seg s.2⟩⟩)))
      rw [hL, hR]
      rfl
    by_cases hsd : (s : ℝ) = S.value e.succ
    · have h1 : (⟨s, frag_subset_seg s.2⟩ : Seg S e) = segTop S e := Subtype.ext hsd
      have h2 : (⟨_, frag_subset_seg hmem⟩ : Seg S e) = segTop S e :=
        Subtype.ext (h.fragAff_eq_right s.2 hsd)
      have hL : (ofFiniteData D).nf S (.inr ⟨e, y, ⟨_, frag_subset_seg hmem⟩⟩) =
          .inl ⟨e.succ, (ofFiniteData D).right e y⟩ := by
        rw [h2]
        exact (ofFiniteData D).nf_segTop S e y
      have hR : (ofFiniteData D).nf S (.inr ⟨e, y, ⟨s, frag_subset_seg s.2⟩⟩) =
          .inl ⟨e.succ, (ofFiniteData D).right e y⟩ := by
        rw [h1]
        exact (ofFiniteData D).nf_segTop S e y
      change (ofFiniteData D).nf S (.inr ⟨e, y, ⟨_, frag_subset_seg hmem⟩⟩) =
        (ofFiniteData D).nf S (transferNf S D ε c u
          ((ofFiniteData D).nf S (.inr ⟨e, y, ⟨s, frag_subset_seg s.2⟩⟩)))
      rw [hL, hR]
      rfl
    · have hnf : (ofFiniteData D).nf S (.inr ⟨e, y, ⟨s, frag_subset_seg s.2⟩⟩) =
          .inr ⟨e, y, ⟨s, frag_subset_seg s.2⟩⟩ := by
        simp only [nf, nfCyl, Sum.elim_inr, hsa, hsd, ↓reduceIte]
      change (ofFiniteData D).nf S (.inr ⟨e, y, ⟨_, frag_subset_seg hmem⟩⟩) =
        (ofFiniteData D).nf S (transferNf S D ε c u
          ((ofFiniteData D).nf S (.inr ⟨e, y, ⟨s, frag_subset_seg s.2⟩⟩)))
      rw [hnf]
      simp only [transferNf, Sum.elim_inr]
      rw [projIcc_of_mem _ (frag_subset_seg hmem)]

private theorem windowCover_rawTransfer_eq {c u : ℝ} (h : TransferOK S ε c u)
    {r r' : WindowRaw S D (c - ε) (c + ε)}
    (hrr : windowCover S D _ _ r = windowCover S D _ _ r') :
    windowCover S D _ _ (rawTransfer S D ε h r) = windowCover S D _ _ (rawTransfer S D ε h r') := by
  rw [windowCover_eq_iff] at hrr ⊢
  rw [nf_windowIncl_rawTransfer, nf_windowIncl_rawTransfer, hrr]

private theorem transferRaw_mem {c u : ℝ} (h : TransferOK S ε c u)
    (r : WindowRaw S D (c - ε) (c + ε)) :
    transferRaw S D ε c (r, u) ∈ win S D ε u := by
  rw [transferRaw_eq S D ε h]
  exact (windowCover S D _ _ (rawTransfer S D ε h r)).2

/-- The raw transfer followed by the target cover, as a bundled continuous map. -/
private def transferCover {c u : ℝ} (h : TransferOK S ε c u) :
    C(WindowRaw S D (c - ε) (c + ε), win S D ε u) where
  toFun r := ⟨transferRaw S D ε c (r, u), transferRaw_mem S D ε h r⟩
  continuous_toFun :=
    ((transferRaw S D ε c).continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _

private theorem transferCover_eq {c u : ℝ} (h : TransferOK S ε c u)
    (r : WindowRaw S D (c - ε) (c + ε)) :
    transferCover S D ε h r = windowCover S D _ _ (rawTransfer S D ε h r) :=
  Subtype.ext (transferRaw_eq S D ε h r)

private theorem transferCover_factors {c u : ℝ} (h : TransferOK S ε c u) :
    Function.FactorsThrough (transferCover S D ε h) (windowCover S D (c - ε) (c + ε)) :=
  fun _ _ hrr => by
    rw [transferCover_eq, transferCover_eq, windowCover_rawTransfer_eq S D ε h hrr]

/-- **Window transfer** `W(c) → W(u)`, descended from the raw affine maps along the window
quotient. At a slab end it is DMP's attaching map `α^{b}`; it need not be injective. -/
def windowTransfer {c u : ℝ} (h : TransferOK S ε c u) : C(win S D ε c, win S D ε u) :=
  (isQuotientMap_windowCover S D (c - ε) (c + ε)).lift (transferCover S D ε h)
    (transferCover_factors S D ε h)

private theorem windowTransfer_windowCover {c u : ℝ} (h : TransferOK S ε c u)
    (r : WindowRaw S D (c - ε) (c + ε)) :
    windowTransfer S D ε h (windowCover S D _ _ r) =
      windowCover S D _ _ (rawTransfer S D ε h r) := by
  rw [← transferCover_eq]
  have := DFunLike.congr_fun (IsQuotientMap.lift_comp
    (isQuotientMap_windowCover S D (c - ε) (c + ε)) (transferCover S D ε h)
    (transferCover_factors S D ε h)) r
  rw [ContinuousMap.comp_apply] at this
  exact this

/-- Edge-point formula: an edge point at parameter `s` goes to parameter `fragAff … s`. -/
theorem coe_windowTransfer_ofCylinder {c u : ℝ} (h : TransferOK S ε c u) {e : Fin n} {s : ℝ}
    (hs : s ∈ frag S e (c - ε) (c + ε)) (x : win S D ε c) {y : D.E e}
    (hx : (x : (ofFiniteData D).Realization S) =
      (ofFiniteData D).ofCylinder S e (y, ⟨s, frag_subset_seg hs⟩)) :
    (windowTransfer S D ε h x : (ofFiniteData D).Realization S) =
      (ofFiniteData D).ofCylinder S e (y, ⟨fragAff (S.value e.castSucc) (S.value e.succ) ε c u s,
        frag_subset_seg (h.fragAff_mem hs)⟩) := by
  have hx' : x = windowCover S D _ _ (.inr ⟨⟨e, y⟩, ⟨s, hs⟩⟩) := Subtype.ext hx
  rw [hx', windowTransfer_windowCover]
  rfl

/-- Vertex formula: an included original vertex is fixed. -/
theorem coe_windowTransfer_ofVertex {c u : ℝ} (h : TransferOK S ε c u) (x : win S D ε c)
    {i : Fin (n + 1)} {v : D.V i}
    (hx : (x : (ofFiniteData D).Realization S) = (ofFiniteData D).ofVertex S i v) :
    (windowTransfer S D ε h x : (ofFiniteData D).Realization S) =
      (ofFiniteData D).ofVertex S i v := by
  have hi : S.value i ∈ Icc (c - ε) (c + ε) := by
    have hm := x.2
    rw [hx] at hm
    exact hm
  have hx' : x = windowCover S D _ _ (.inl ⟨⟨i, v⟩, hi⟩) := Subtype.ext hx
  rw [hx', windowTransfer_windowCover]
  rfl

private theorem rawTransfer_rawTransfer (hε : 0 < ε) {c u : ℝ} (h : TransferOK S ε c u)
    (h' : TransferOK S ε u c) (r : WindowRaw S D (c - ε) (c + ε)) :
    rawTransfer S D ε h' (rawTransfer S D ε h r) = r := by
  rcases r with v | ⟨⟨e, y⟩, s⟩
  · rfl
  · exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext
      (fragAff_fragAff (h.frag_lt hε s.2) (h'.frag_lt hε (h.fragAff_mem s.2)) s))))

/-- **Interior inverse.** For `ε > 0`, the transfers `c → u` and `u → c` are mutually inverse
whenever both satisfy the transfer hypotheses (for instance, `c` and `u` in one open gap). -/
theorem windowTransfer_windowTransfer (hε : 0 < ε) {c u : ℝ} (h : TransferOK S ε c u)
    (h' : TransferOK S ε u c) (x : win S D ε c) :
    windowTransfer S D ε h' (windowTransfer S D ε h x) = x := by
  obtain ⟨r, rfl⟩ := windowCover_surjective S D _ _ x
  rw [windowTransfer_windowCover, windowTransfer_windowCover, rawTransfer_rawTransfer S D ε hε h h']

/-- For `ε > 0`, the transfer between two heights with mutual transfer hypotheses (for instance,
two heights of one open gap of the shifted witness) is a homeomorphism `W(c) ≃ₜ W(u)`. -/
def windowTransferHomeomorph (hε : 0 < ε) {c u : ℝ} (h : TransferOK S ε c u)
    (h' : TransferOK S ε u c) : win S D ε c ≃ₜ win S D ε u where
  toFun := windowTransfer S D ε h
  invFun := windowTransfer S D ε h'
  left_inv := windowTransfer_windowTransfer S D ε hε h h'
  right_inv := windowTransfer_windowTransfer S D ε hε h' h
  continuous_toFun := (windowTransfer S D ε h).continuous
  continuous_invFun := (windowTransfer S D ε h').continuous

end Transfer

/-! ### The cylinder presentation of the thickening -/

section Presentation

variable {n : ℕ} (S : CriticalValues n) (D : FiniteReebData.{u} n) (ε : ℝ≥0)

/-- The band `{(x, u) | u - ε ≤ f x ≤ u + ε}` of the realization: the codomain of the merged
`GeometricThickening.bandHomeomorph`. -/
abbrev BandSpace :=
  {p : (ofFiniteData D).Realization S × ℝ //
    p.2 - ε ≤ (ofFiniteData D).height S p.1 ∧ (ofFiniteData D).height S p.1 ≤ p.2 + ε}

/-- The product cover of a slab: raw window points at the midpoint, times the closed gap. -/
private def slabCover (k : Fin (S.shiftedCount ε)) :
    C(WindowRaw S D (mid S ε k - ε) (mid S ε k + ε) × Seg (S.shifted ε) k,
      win S D ε (mid S ε k) × Seg (S.shifted ε) k) :=
  (windowCover S D _ _).prodMap (ContinuousMap.id _)

/-- The product cover is a quotient map (compact source, Hausdorff target). -/
private theorem isQuotientMap_slabCover (k : Fin (S.shiftedCount ε)) :
    IsQuotientMap (slabCover S D ε k) :=
  IsQuotientMap.of_surjective_continuous
    ((windowCover_surjective S D _ _).prodMap Function.surjective_id) (slabCover S D ε k).continuous

/-- The raw joint cylinder map of a slab into the band. -/
private def slabRaw (k : Fin (S.shiftedCount ε)) :
    C(WindowRaw S D (mid S ε k - ε) (mid S ε k + ε) × Seg (S.shifted ε) k, BandSpace S D ε) where
  toFun p := ⟨(transferRaw S D ε (mid S ε k) (p.1, (p.2 : ℝ)), (p.2 : ℝ)),
    (transferRaw_mem S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) p.2.2) p.1).1,
    (transferRaw_mem S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) p.2.2) p.1).2⟩
  continuous_toFun := (((transferRaw S D ε (mid S ε k)).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private theorem slabRaw_factors (k : Fin (S.shiftedCount ε)) :
    Function.FactorsThrough (slabRaw S D ε k) (slabCover S D ε k) := by
  rintro ⟨r, t⟩ ⟨r', t'⟩ hpp'
  obtain ⟨h1, h2⟩ := Prod.mk.inj hpp'
  change t = t' at h2
  subst h2
  have hok := transferOK_of_mem S ε (mid_mem_K S ε k) t.2
  refine Subtype.ext (Prod.ext ?_ rfl)
  change transferRaw S D ε (mid S ε k) (r, (t : ℝ)) = transferRaw S D ε (mid S ε k) (r', (t : ℝ))
  rw [transferRaw_eq S D ε hok, transferRaw_eq S D ε hok, windowCover_rawTransfer_eq S D ε hok h1]

/-- **The joint cylinder map** `E'ₖ × [b k, b (k+1)] → B`, descended along the product quotient:
DMP's `α_k (ξ, u) = (α_k^u ξ, u)`. -/
def slabCylinder (k : Fin (S.shiftedCount ε)) :
    C(win S D ε (mid S ε k) × Seg (S.shifted ε) k, BandSpace S D ε) :=
  (isQuotientMap_slabCover S D ε k).lift (slabRaw S D ε k) (slabRaw_factors S D ε k)

private theorem slabCylinder_slabCover (k : Fin (S.shiftedCount ε))
    (p : WindowRaw S D (mid S ε k - ε) (mid S ε k + ε) × Seg (S.shifted ε) k) :
    slabCylinder S D ε k (slabCover S D ε k p) = slabRaw S D ε k p := by
  have := DFunLike.congr_fun (IsQuotientMap.lift_comp (isQuotientMap_slabCover S D ε k)
    (slabRaw S D ε k) (slabRaw_factors S D ε k)) p
  rw [ContinuousMap.comp_apply] at this
  exact this

theorem coe_slabCylinder (k : Fin (S.shiftedCount ε)) (x : win S D ε (mid S ε k))
    (t : Seg (S.shifted ε) k) :
    (slabCylinder S D ε k (x, t) : (ofFiniteData D).Realization S × ℝ) =
      ((windowTransfer S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) t.2) x :
        (ofFiniteData D).Realization S), (t : ℝ)) := by
  obtain ⟨r, rfl⟩ := windowCover_surjective S D _ _ x
  have h := congrArg Subtype.val (slabCylinder_slabCover S D ε k (r, t))
  refine h.trans (Prod.ext ?_ rfl)
  change transferRaw S D ε (mid S ε k) (r, (t : ℝ)) = _
  rw [transferRaw_eq S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) t.2),
    windowTransfer_windowCover]

theorem snd_slabCylinder (k : Fin (S.shiftedCount ε)) (x : win S D ε (mid S ε k))
    (t : Seg (S.shifted ε) k) : (slabCylinder S D ε k (x, t)).1.2 = t :=
  congrArg Prod.snd (coe_slabCylinder S D ε k x t)

/-- **The thickening presentation** over the shifted witness `S.shifted ε`: vertex piece
`j` is the window at `b j`, edge piece `k` the window at the midpoint of gap `k`, and the endpoint
maps are the window transfers to the two ends of the gap. -/
def thickPresentation : CylinderPresentation.{u} (S.shiftedCount ε) where
  V j := ↥(win S D ε ((S.shifted ε).value j))
  E k := ↥(win S D ε (mid S ε k))
  topV _ := inferInstance
  topE _ := inferInstance
  left k := windowTransfer S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) (segBot _ k).2)
  right k := windowTransfer S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) (segTop _ k).2)

instance instCompactSpaceThickV (j : Fin (S.shiftedCount ε + 1)) :
    CompactSpace ((thickPresentation S D ε).V j) :=
  inferInstanceAs (CompactSpace (win S D ε ((S.shifted ε).value j)))
instance instLocallyPathConnectedSpaceThickV (j : Fin (S.shiftedCount ε + 1)) :
    LocallyPathConnectedSpace ((thickPresentation S D ε).V j) :=
  inferInstanceAs (LocallyPathConnectedSpace (win S D ε ((S.shifted ε).value j)))
instance instT2SpaceThickV (j : Fin (S.shiftedCount ε + 1)) :
    T2Space ((thickPresentation S D ε).V j) :=
  inferInstanceAs (T2Space (win S D ε ((S.shifted ε).value j)))
instance instCompactSpaceThickE (k : Fin (S.shiftedCount ε)) :
    CompactSpace ((thickPresentation S D ε).E k) :=
  inferInstanceAs (CompactSpace (win S D ε (mid S ε k)))
instance instLocallyPathConnectedSpaceThickE (k : Fin (S.shiftedCount ε)) :
    LocallyPathConnectedSpace ((thickPresentation S D ε).E k) :=
  inferInstanceAs (LocallyPathConnectedSpace (win S D ε (mid S ε k)))
instance instT2SpaceThickE (k : Fin (S.shiftedCount ε)) :
    T2Space ((thickPresentation S D ε).E k) :=
  inferInstanceAs (T2Space (win S D ε (mid S ε k)))

/-- The compatible maps into the band: vertex pieces at their level, cylinders by
`slabCylinder`. The two endpoint equations hold because the attaching maps are the slab ends. -/
def thickCompat :
    (thickPresentation S D ε).CompatibleMaps (S.shifted ε) (BandSpace S D ε) where
  vertex j := ⟨fun x => ⟨(x.1, (S.shifted ε).value j), x.2.1, x.2.2⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩
  cylinder k := slabCylinder S D ε k
  segBot_eq k x := Subtype.ext (coe_slabCylinder S D ε k x _)
  segTop_eq k x := Subtype.ext (coe_slabCylinder S D ε k x _)

/-- The comparison map from the realization to the band, by the merged
`CylinderPresentation.lift`. -/
def thickMap : C((thickPresentation S D ε).Realization (S.shifted ε), BandSpace S D ε) :=
  lift (thickCompat S D ε)

theorem thickMap_ofVertex (j : Fin (S.shiftedCount ε + 1)) (x : (thickPresentation S D ε).V j) :
    thickMap S D ε ((thickPresentation S D ε).ofVertex (S.shifted ε) j x) =
      ⟨(x.1, (S.shifted ε).value j), x.2.1, x.2.2⟩ :=
  rfl

theorem coe_thickMap_ofStrip (k : Fin (S.shiftedCount ε)) (x : (thickPresentation S D ε).E k)
    (t : ((S.shifted ε).K k : Set ℝ)) :
    (thickMap S D ε ((thickPresentation S D ε).ofStrip (S.shifted ε) k (x, t))).1 =
      ((windowTransfer S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) (Ioo_subset_Icc_self t.2))
        x : (ofFiniteData D).Realization S), (t : ℝ)) :=
  coe_slabCylinder S D ε k x (gapIncl _ k t)

/-- The comparison map preserves height. -/
theorem thickMap_snd (q : (thickPresentation S D ε).Realization (S.shifted ε)) :
    (thickMap S D ε q).1.2 = (thickPresentation S D ε).height (S.shifted ε) q := by
  obtain ⟨x, rfl⟩ := (thickPresentation S D ε).quotMk_surjective _ q
  rcases x with ⟨j, v⟩ | ⟨k, v, t⟩
  · rfl
  · exact snd_slabCylinder S D ε k v t

theorem thickMap_injective (hε : 0 < ε) : Function.Injective (thickMap S D ε) := by
  intro q q' hqq'
  have hh := (thickMap_snd S D ε q).symm.trans
    ((congrArg (fun p : BandSpace S D ε => p.1.2) hqq').trans (thickMap_snd S D ε q'))
  rcases (thickPresentation S D ε).exists_rep _ q with ⟨j, x, rfl⟩ | ⟨k, ⟨x, t⟩, rfl⟩ <;>
    rcases (thickPresentation S D ε).exists_rep _ q' with ⟨j', x', rfl⟩ | ⟨k', ⟨x', t'⟩, rfl⟩
  · rw [height_ofVertex, height_ofVertex] at hh
    obtain rfl : j = j' := (S.shifted ε).strictMono.injective hh
    have h1 := congrArg (fun p : BandSpace S D ε => p.1.1) hqq'
    exact congrArg _ (Subtype.ext h1)
  · rw [height_ofVertex, height_ofStrip] at hh
    exact ((S.shifted ε).value_notMem_K k' j (by rw [hh]; exact t'.2)).elim
  · rw [height_ofStrip, height_ofVertex] at hh
    exact ((S.shifted ε).value_notMem_K k j' (by rw [← hh]; exact t.2)).elim
  · rw [height_ofStrip, height_ofStrip] at hh
    obtain rfl : k = k' :=
      (S.shifted ε).eq_of_mem_K_of_mem_Icc t.2 (by rw [hh]; exact Ioo_subset_Icc_self t'.2)
    obtain rfl : t = t' := Subtype.ext hh
    have h1 := congrArg (fun p : BandSpace S D ε => p.1.1) hqq'
    simp only [coe_thickMap_ofStrip] at h1
    have hok := transferOK_of_mem S ε (mid_mem_K S ε k) (Ioo_subset_Icc_self t.2)
    have hok' := transferOK_of_mem S ε t.2 (Ioo_subset_Icc_self (mid_mem_K S ε k))
    have hx := congrArg (windowTransfer S D ε hok') (Subtype.ext h1 :
      windowTransfer S D ε hok x = windowTransfer S D ε hok x')
    have hxx : x = x' := (windowTransfer_windowTransfer S D ε hε hok hok' x).symm.trans
      (hx.trans (windowTransfer_windowTransfer S D ε hε hok hok' x'))
    rw [hxx]

theorem thickMap_surjective (hε : 0 < ε) : Function.Surjective (thickMap S D ε) := by
  rintro ⟨⟨y, u⟩, hy⟩
  by_cases hlev : ∃ j, (S.shifted ε).value j = u
  · obtain ⟨j, rfl⟩ := hlev
    exact ⟨(thickPresentation S D ε).ofVertex _ j ⟨y, hy.1, hy.2⟩, rfl⟩
  · simp only [not_exists] at hlev
    have hu : u ∈ Icc ((S.shifted ε).value 0) ((S.shifted ε).value (Fin.last _)) := by
      rw [S.shifted_value_zero, S.shifted_value_last]
      have := (ofFiniteData D).height_mem_Icc S y
      exact ⟨by linarith [hy.1, hy.2, this.1, this.2], by linarith [hy.1, hy.2, this.1, this.2]⟩
    obtain ⟨k, hk⟩ := (S.shifted ε).exists_mem_K_of_mem_Icc hu hlev
    have hok' : TransferOK S ε u (mid S ε k) :=
      transferOK_of_mem S ε hk (Ioo_subset_Icc_self (mid_mem_K S ε k))
    have hok := transferOK_of_mem S ε (mid_mem_K S ε k) (Ioo_subset_Icc_self hk)
    refine ⟨(thickPresentation S D ε).ofStrip _ k
      (windowTransfer S D ε hok' ⟨y, hy.1, hy.2⟩, ⟨u, hk⟩), Subtype.ext
        ((coe_thickMap_ofStrip S D ε k (windowTransfer S D ε hok' ⟨y, hy.1, hy.2⟩) ⟨u, hk⟩).trans
          (Prod.ext ?_ rfl))⟩
    exact congrArg Subtype.val (windowTransfer_windowTransfer S D ε hε hok' hok ⟨y, hy.1, hy.2⟩)

/-- **The realization is the band** (DMP Theorem 4.27, Step 6, on graph input): a continuous
bijection from a compact space to a Hausdorff space. -/
def thickHomeomorph (hε : 0 < ε) :
    (thickPresentation S D ε).Realization (S.shifted ε) ≃ₜ BandSpace S D ε :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨thickMap_injective S D ε hε, thickMap_surjective S D ε hε⟩)
    (thickMap S D ε).continuous

/-- The realization is the product thickening `X × Band ε`. -/
def thickProdHomeomorph (hε : 0 < ε) :
    (thickPresentation S D ε).Realization (S.shifted ε) ≃ₜ
      (ofFiniteData D).Realization S × GeometricThickening.Band ε :=
  (thickHomeomorph S D ε hε).trans
    (GeometricThickening.bandHomeomorph ((ofFiniteData D).height S) ε).symm

/-- Height preservation into the thickened height. -/
theorem height_thickProdHomeomorph (hε : 0 < ε)
    (q : (thickPresentation S D ε).Realization (S.shifted ε)) :
    GeometricThickening.height ((ofFiniteData D).height S) ε (thickProdHomeomorph S D ε hε q) =
      (thickPresentation S D ε).height (S.shifted ε) q := by
  rw [← GeometricThickening.snd_bandHomeomorph]
  simp only [thickProdHomeomorph, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  exact thickMap_snd S D ε q

/-- Critical-fiber coordinate: a vertex point `x` of level `b j` has first coordinate `x`; by
`height_thickProdHomeomorph` its band coordinate is `b j - f x`. -/
theorem fst_thickProdHomeomorph_ofVertex (hε : 0 < ε) (j : Fin (S.shiftedCount ε + 1))
    (x : (thickPresentation S D ε).V j) :
    (thickProdHomeomorph S D ε hε ((thickPresentation S D ε).ofVertex _ j x)).1 = x.1 :=
  rfl

/-- Noncritical cylinder coordinate: a strip point `(x, t)` has first coordinate the window
transfer of `x` to height `t`. -/
theorem fst_thickProdHomeomorph_ofStrip (hε : 0 < ε) (k : Fin (S.shiftedCount ε))
    (x : (thickPresentation S D ε).E k) (t : ((S.shifted ε).K k : Set ℝ)) :
    (thickProdHomeomorph S D ε hε ((thickPresentation S D ε).ofStrip _ k (x, t))).1 =
      (windowTransfer S D ε (transferOK_of_mem S ε (mid_mem_K S ε k) (Ioo_subset_Icc_self t.2)) x :
        (ofFiniteData D).Realization S) :=
  congrArg Prod.fst (coe_thickMap_ofStrip S D ε k x t)

/-- Critical-fiber band coordinate: a vertex point `x` of level `b j` has band coordinate
`b j - f x`. -/
theorem snd_thickProdHomeomorph_ofVertex (hε : 0 < ε) (j : Fin (S.shiftedCount ε + 1))
    (x : (thickPresentation S D ε).V j) :
    ((thickProdHomeomorph S D ε hε ((thickPresentation S D ε).ofVertex _ j x)).2 : ℝ) =
      (S.shifted ε).value j - (ofFiniteData D).height S x.1 :=
  rfl

/-- Noncritical band coordinate: a strip point `(x, t)` has band coordinate `t - f y`, where `y` is
the window transfer of `x` to height `t`. -/
theorem snd_thickProdHomeomorph_ofStrip (hε : 0 < ε) (k : Fin (S.shiftedCount ε))
    (x : (thickPresentation S D ε).E k) (t : ((S.shifted ε).K k : Set ℝ)) :
    ((thickProdHomeomorph S D ε hε ((thickPresentation S D ε).ofStrip _ k (x, t))).2 : ℝ) =
      t - (ofFiniteData D).height S (windowTransfer S D ε
        (transferOK_of_mem S ε (mid_mem_K S ε k) (Ioo_subset_Icc_self t.2)) x :
          (ofFiniteData D).Realization S) := by
  have h := height_thickProdHomeomorph S D ε hε ((thickPresentation S D ε).ofStrip _ k (x, t))
  rw [GeometricThickening.height_apply, fst_thickProdHomeomorph_ofStrip, height_ofStrip] at h
  linarith

end Presentation

/-! ### Packaging on the real slice (universe `0`) -/

section Over

variable {n : ℕ} (S : CriticalValues n) (D : FiniteReebData.{0} n) (ε : ℝ≥0)

/-- The thickening of a graph realization is isomorphic over `ℝ` to the realization of the
thickening presentation, for `ε > 0`. -/
def thickOverIso (hε : 0 < ε) :
    (GeometricThickening.functor ε).obj (toOver S D) ≅
      Over.mk (TopCat.ofHom ((thickPresentation S D ε).height (S.shifted ε))) :=
  Over.isoMk (TopCat.isoOfHomeo (X := ((GeometricThickening.functor ε).obj (toOver S D)).left)
      (Y := TopCat.of ((thickPresentation S D ε).Realization (S.shifted ε)))
      (thickProdHomeomorph S D ε hε).symm) (by
    ext z
    change (thickPresentation S D ε).height (S.shifted ε) ((thickProdHomeomorph S D ε hε).symm z) =
      GeometricThickening.height ((ofFiniteData D).height S) ε z
    exact (height_thickProdHomeomorph S D ε hε ((thickProdHomeomorph S D ε hε).symm z)).symm.trans
      (congrArg (GeometricThickening.height ((ofFiniteData D).height S) ε)
        ((thickProdHomeomorph S D ε hε).apply_symm_apply z)))

/-- **Graph thickenings are constructible**, at a presentation; `ε = 0` by the merged `zeroIso`. -/
theorem isConstructibleSpace_thickening_toOver :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj (toOver S D)) := by
  rcases eq_zero_or_pos ε with rfl | hε
  · obtain ⟨m, T, P, h1, h2, h3, h4, ⟨i⟩⟩ :=
      isConstructibleSpace_of_isRGraph (A := toOver S D) ⟨n, S, D, ⟨Iso.refl _⟩⟩
    exact ⟨m, T, P, h1, h2, h3, h4, ⟨GeometricThickening.zeroIso.app (toOver S D) ≪≫ i⟩⟩
  · exact ⟨_, S.shifted ε, thickPresentation S D ε, fun _ => inferInstance,
      fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
      ⟨thickOverIso S D ε hε⟩⟩

/-- **DMP Proposition 4.26.** The thickening of every graph object is a constructible
ℝ-space, for every `ε ≥ 0`. -/
theorem isConstructibleSpace_thickening {A : Over (TopCat.of ℝ)} (hA : IsRGraph A) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj A) := by
  obtain ⟨n, S, D, ⟨i⟩⟩ := hA
  obtain ⟨m, T, P, h1, h2, h3, h4, ⟨j⟩⟩ := isConstructibleSpace_thickening_toOver S D ε
  exact ⟨m, T, P, h1, h2, h3, h4, ⟨(GeometricThickening.functor ε).mapIso i ≪≫ j⟩⟩

/-- The thickening functor restricted to graph objects, with values in constructible
ℝ-spaces, on all height-preserving maps. -/
def thickeningToConstructible (ε : ℝ≥0) : RGraphCat ⥤ ConstructibleSpaceCat :=
  IsConstructibleSpace.lift (IsRGraph.ι ⋙ GeometricThickening.functor ε)
    fun A => isConstructibleSpace_thickening A.property ε

theorem thickeningToConstructible_comp_ι (ε : ℝ≥0) :
    thickeningToConstructible ε ⋙ IsConstructibleSpace.ι =
      IsRGraph.ι ⋙ GeometricThickening.functor ε :=
  rfl

theorem thickeningToConstructible_obj_obj (ε : ℝ≥0) (A : RGraphCat) :
    ((thickeningToConstructible ε).obj A).obj = (GeometricThickening.functor ε).obj A.obj :=
  rfl

theorem thickeningToConstructible_map_hom (ε : ℝ≥0) {A B : RGraphCat} (φ : A ⟶ B) :
    ((thickeningToConstructible ε).map φ).hom = (GeometricThickening.functor ε).map φ.hom :=
  rfl

/-- The Reeb-quotient form of the lift: followed by the merged `quotientRGraphFunctor` and the graph
inclusion, the lift is literally the Reeb quotient of the product thickening. -/
theorem thickeningToConstructible_comp_quotientRGraphFunctor (ε : ℝ≥0) :
    thickeningToConstructible ε ⋙ quotientRGraphFunctor ⋙ IsRGraph.ι =
      IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ :=
  rfl

end Over

end RGraph

end

end TDA.Reeb
