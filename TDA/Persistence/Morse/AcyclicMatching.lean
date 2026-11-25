import TDA.Filtration.FilterFunction
import Mathlib.Data.Finset.Grade
import Mathlib.Logic.Relation

/-!
# Acyclic matchings for discrete Morse reduction

A matching on the faces of a preabstract simplicial complex `K` is a relation `M σ τ`, read as
"`σ` is matched with its codimension-one coface `τ`", subject to the four conditions of
`IsMatching`. The modified Hasse diagram `arrow M` covers every face: an unmatched cover pair
`σ ⋖ τ` gives the arrow `τ → σ` (coface to face), and a matched pair gives `σ → τ` (face to
coface). `IsAcyclic M` says that this diagram has no directed cycle.

## Source and convention digest

The source is Mischaikow and Nanda, *Morse Theory for Filtrations and Efficient Computation of
Persistent Homology*, Discrete Comput. Geom. 50 (2013), DOI 10.1007/s00454-013-9529-6 (register
card `MN13` in `docs/math/references.md`). Def. 2.2 there defines a partial matching
`(A, w : Q → K)` and calls it acyclic when the transitive closure of
`Q' ◁ Q :⇔ Q' ≠ Q ∧ Q' ≺ w(Q)` on `Q` is a partial order. For a simplicial complex with the
standard incidence, both `≺` and the unit-incidence condition become the cover relation `⋖`;
`mnRel` and `IsMNAcyclic` state this form, and `isAcyclic_iff_isMNAcyclic` proves it equivalent
to `IsAcyclic` for a matching. Def. 4.1 (filtered acyclic matchings) is stated for the sublevel
frames of one `FilterFunction` as `IsFilteredAcyclicMatching`, and
`isFilteredAcyclicMatching_iff` proves it equivalent to an acyclic matching whose pairs have
equal grades. The topological-rank characterization `isAcyclic_iff_exists_rank` is a library
derivation, not a numbered result of the source. No chain contraction, Morse complex or
persistence statement is made here.
-/

set_option autoImplicit false

namespace TDA.Simplicial

/-- The cover relation of finite sets is "subset with exactly one more element". A general
`Finset` fact, used for the face-size bookkeeping of discrete Morse matchings. -/
theorem covBy_iff_subset_card {V : Type*} {s t : Finset V} :
    s ⋖ t ↔ s ⊆ t ∧ t.card = s.card + 1 := by
  classical
  rw [Finset.covBy_iff_card_sdiff_eq_one]
  constructor
  · rintro ⟨hst, hcard⟩
    refine ⟨hst, ?_⟩
    have := Finset.card_sdiff_add_card_eq_card hst
    omega
  · rintro ⟨hst, hcard⟩
    refine ⟨hst, ?_⟩
    have := Finset.card_sdiff_add_card_eq_card hst
    omega

end TDA.Simplicial

namespace TDA.Persistence.Morse

open TDA.Simplicial TDA.Filtration

universe u w

variable {V : Type u} {K : PreAbstractSimplicialComplex V}

/-- A partial matching of the faces of `K`: `M σ τ` pairs a face with a codimension-one
coface; every face lies in at most one pair, in either role. -/
structure IsMatching (M : TotalFace K → TotalFace K → Prop) : Prop where
  /-- Each pair is a face together with a codimension-one coface. -/
  covBy : ∀ {σ τ : TotalFace K}, M σ τ → σ.val ⋖ τ.val
  /-- A face is the lower cell of at most one pair. -/
  lower_unique : ∀ {σ τ τ' : TotalFace K}, M σ τ → M σ τ' → τ = τ'
  /-- A face is the upper cell of at most one pair. -/
  upper_unique : ∀ {σ σ' τ : TotalFace K}, M σ τ → M σ' τ → σ = σ'
  /-- An upper cell is never also a lower cell. -/
  disjoint : ∀ {σ τ ρ : TotalFace K}, M σ τ → ¬ M τ ρ

/-- Modified Hasse diagram. Unmatched cover arrows go from coface to face; a matched pair
`M u v` is reversed, from face to coface. -/
def arrow (M : TotalFace K → TotalFace K → Prop) (u v : TotalFace K) : Prop :=
  (v.val ⋖ u.val ∧ ¬ M v u) ∨ M u v

/-- No directed cycle in the modified Hasse diagram of all faces. For an infinite `K` this still
allows an infinite directed path; the Morse reduction modules apply the predicate to the finite
complex of a simplex list. -/
def IsAcyclic (M : TotalFace K → TotalFace K → Prop) : Prop :=
  ∀ x : TotalFace K, ¬ Relation.TransGen (arrow M) x x

/-- An acyclic matching: a matching whose modified Hasse diagram has no directed cycle. -/
def IsAcyclicMatching (M : TotalFace K → TotalFace K → Prop) : Prop :=
  IsMatching M ∧ IsAcyclic M

/-- The empty matching is an acyclic matching: every arrow lowers the face size. -/
theorem isAcyclicMatching_empty :
    IsAcyclicMatching (fun _ _ : TotalFace K => False) := by
  refine ⟨⟨fun h => h.elim, fun h => h.elim, fun h => h.elim, fun h => h.elim⟩, ?_⟩
  have step : ∀ x y : TotalFace K, Relation.TransGen (arrow fun _ _ => False) x y →
      y.val.card < x.val.card := by
    intro x y h
    induction h with
    | single h =>
      rcases h with ⟨hc, -⟩ | h
      · exact Finset.card_lt_card hc.lt
      · exact h.elim
    | tail _ h ih =>
      rcases h with ⟨hc, -⟩ | h
      · exact (Finset.card_lt_card hc.lt).trans ih
      · exact h.elim
  intro x hx
  exact lt_irrefl _ (step x x hx)

/-- MN Def. 2.2, generating relation on matched lower cells: `Q' ◁ Q` for distinct
lower cells with `Q' ≺ w(Q)`, where `≺` is the cover relation. -/
def mnRel (M : TotalFace K → TotalFace K → Prop) (Q' Q : TotalFace K) : Prop :=
  (∃ τ', M Q' τ') ∧ Q' ≠ Q ∧ ∃ τ, M Q τ ∧ Q'.val ⋖ τ.val

/-- MN Def. 2.2 acyclicity: the order generated by `mnRel` is a partial order, i.e. its
reflexive-transitive closure is antisymmetric. -/
def IsMNAcyclic (M : TotalFace K → TotalFace K → Prop) : Prop :=
  ∀ a b : TotalFace K, Relation.ReflTransGen (mnRel M) a b →
    Relation.ReflTransGen (mnRel M) b a → a = b

/-- MN acyclicity is equivalent to the absence of a cycle of the generating relation, since
`mnRel` is irreflexive. -/
theorem isMNAcyclic_iff_irrefl {M : TotalFace K → TotalFace K → Prop} :
    IsMNAcyclic M ↔ ∀ x : TotalFace K, ¬ Relation.TransGen (mnRel M) x x := by
  constructor
  · intro h x hx
    obtain ⟨y, hxy, hyx⟩ := Relation.TransGen.head'_iff.mp hx
    have hxy' : x = y := h x y (Relation.ReflTransGen.single hxy) hyx
    subst hxy'
    exact hxy.2.1 rfl
  · intro h a b hab hba
    by_contra hne
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with hab | hab
    · exact hne hab.symm
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hba with hba | hba
    · exact hne hba
    exact h a (hab.trans hba)

section Alternation

variable {M : TotalFace K → TotalFace K → Prop}

/-- An arrow either lowers the face size by one (unmatched) or raises it by one (matched). -/
private theorem arrow_cases (hM : IsMatching M) {u v : TotalFace K} (h : arrow M u v) :
    (v.val ⋖ u.val ∧ ¬ M v u ∧ u.val.card = v.val.card + 1) ∨
      (M u v ∧ v.val.card = u.val.card + 1) := by
  rcases h with ⟨hc, hn⟩ | h
  · exact Or.inl ⟨hc, hn, (covBy_iff_subset_card.mp hc).2⟩
  · exact Or.inr ⟨h, (covBy_iff_subset_card.mp (hM.covBy h)).2⟩

/-- Along a path the face size rises by at most one, and only at a matched upper cell. -/
private theorem card_le_of_transGen (hM : IsMatching M) {z w : TotalFace K}
    (h : Relation.TransGen (arrow M) z w) :
    w.val.card ≤ z.val.card + 1 ∧
      (w.val.card = z.val.card + 1 → ∃ σ, M σ w) := by
  induction h with
  | single h =>
    rcases arrow_cases hM h with ⟨-, -, hc⟩ | ⟨hm, hc⟩
    · exact ⟨by omega, fun h' => by omega⟩
    · exact ⟨by omega, fun _ => ⟨_, hm⟩⟩
  | @tail a b _ hab ih =>
    rcases arrow_cases hM hab with ⟨-, -, hc⟩ | ⟨hm, hc⟩
    · exact ⟨by omega, fun h' => by omega⟩
    · have hne : a.val.card ≠ z.val.card + 1 := by
        intro he
        obtain ⟨σ, hσ⟩ := ih.2 he
        exact hM.disjoint hσ hm
      exact ⟨by omega, fun _ => ⟨_, hm⟩⟩

/-- A path either strictly lowers the face size or passes through a matched arrow. -/
private theorem transGen_card_lt_or_matched {z w : TotalFace K}
    (h : Relation.TransGen (arrow M) z w) :
    w.val.card < z.val.card ∨
      ∃ Q τ, M Q τ ∧ Relation.ReflTransGen (arrow M) z Q ∧
        Relation.ReflTransGen (arrow M) τ w := by
  induction h with
  | single h =>
    rcases h with ⟨hc, -⟩ | hm
    · exact Or.inl (Finset.card_lt_card hc.lt)
    · exact Or.inr ⟨_, _, hm, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail a b hza hab ih =>
    rcases hab with ⟨hc, hn⟩ | hm
    · rcases ih with ih | ⟨Q, τ, hQ, hzQ, hτa⟩
      · exact Or.inl ((Finset.card_lt_card hc.lt).trans ih)
      · exact Or.inr ⟨Q, τ, hQ, hzQ, hτa.tail (Or.inl ⟨hc, hn⟩)⟩
    · exact Or.inr ⟨_, _, hm, hza.to_reflTransGen, Relation.ReflTransGen.refl⟩

/-- On a cycle through a matched lower cell `u`, every face has size `#u` or `#u + 1`. -/
private theorem card_bounds_of_cycle (hM : IsMatching M) {u v : TotalFace K} {τ₀ : TotalFace K}
    (hu : M u τ₀) (huv : Relation.ReflTransGen (arrow M) u v)
    (hvu : Relation.ReflTransGen (arrow M) v u) :
    u.val.card ≤ v.val.card ∧ v.val.card ≤ u.val.card + 1 := by
  constructor
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hvu with h | h
    · rw [h]
    · obtain ⟨h1, h2⟩ := card_le_of_transGen hM h
      by_contra hlt
      obtain ⟨σ, hσ⟩ := h2 (by omega)
      exact hM.disjoint hσ hu
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp huv with h | h
    · rw [← h]; omega
    · exact (card_le_of_transGen hM h).1

/-- The alternating-path invariant along a cycle through a matched lower cell `u`: a face of
size `#u + 1` is the partner of a lower cell reachable from `u` backwards along `mnRel`, and a
face of size `#u` is `u` or an unmatched facet of such a partner. -/
private theorem cycle_invariant (hM : IsMatching M) {u : TotalFace K} {τ₀ : TotalFace K}
    (hu : M u τ₀) {v : TotalFace K} (huv : Relation.ReflTransGen (arrow M) u v)
    (hvu : Relation.ReflTransGen (arrow M) v u) :
    (v.val.card = u.val.card + 1 →
        ∃ Q, M Q v ∧ Relation.ReflTransGen (mnRel M) Q u) ∧
      (v.val.card = u.val.card →
        v = u ∨ ∃ Q τ, Relation.ReflTransGen (mnRel M) Q u ∧ M Q τ ∧
          v.val ⋖ τ.val ∧ ¬ M v τ) := by
  induction huv with
  | refl => exact ⟨fun h => by omega, fun _ => Or.inl rfl⟩
  | @tail a b hua hab ih =>
    have hau : Relation.ReflTransGen (arrow M) a u := Relation.ReflTransGen.head hab hvu
    have ⟨ha1, ha2⟩ := card_bounds_of_cycle hM hu hua hau
    have ⟨hb1, hb2⟩ := card_bounds_of_cycle hM hu (hua.tail hab) hvu
    obtain ⟨ih1, ih2⟩ := ih hau
    rcases arrow_cases hM hab with ⟨hc, hn, hcard⟩ | ⟨hm, hcard⟩
    · obtain ⟨Q, hQ, hQu⟩ := ih1 (by omega)
      exact ⟨fun h => by omega, fun _ => Or.inr ⟨Q, a, hQu, hQ, hc, hn⟩⟩
    · refine ⟨fun _ => ?_, fun h => by omega⟩
      rcases ih2 (by omega) with rfl | ⟨Q, τ, hQu, hQ, hc, hn⟩
      · exact ⟨a, hm, Relation.ReflTransGen.refl⟩
      · have hrel : mnRel M a Q :=
          ⟨⟨b, hm⟩, fun he => hn (he ▸ hQ), ⟨τ, hQ, hc⟩⟩
        exact ⟨a, hm, Relation.ReflTransGen.head hrel hQu⟩

/-- An arrow cycle yields an `mnRel` cycle. -/
private theorem mn_cycle_of_cycle (hM : IsMatching M) {x : TotalFace K}
    (hx : Relation.TransGen (arrow M) x x) :
    ∃ y, Relation.TransGen (mnRel M) y y := by
  rcases transGen_card_lt_or_matched hx with h | ⟨u, τ₀, hu, hxu, hτx⟩
  · exact (lt_irrefl _ h).elim
  -- The cycle `u → τ₀ → ⋯ → x → ⋯ → u` starts with a matched arrow.
  have hcyc : Relation.TransGen (arrow M) u u :=
    Relation.TransGen.head' (Or.inr hu) (hτx.trans hxu)
  obtain ⟨a, hua, hau⟩ := Relation.TransGen.tail'_iff.mp hcyc
  have ⟨ha1, ha2⟩ := card_bounds_of_cycle hM hu hua (Relation.ReflTransGen.single hau)
  obtain ⟨ih1, -⟩ := cycle_invariant hM hu hua (Relation.ReflTransGen.single hau)
  rcases arrow_cases hM hau with ⟨hc, hn, hcard⟩ | ⟨hm, -⟩
  · obtain ⟨Q, hQ, hQu⟩ := ih1 (by omega)
    have hrel : mnRel M u Q := ⟨⟨τ₀, hu⟩, fun he => hn (he ▸ hQ), ⟨a, hQ, hc⟩⟩
    exact ⟨u, Relation.TransGen.head' hrel hQu⟩
  · exact (hM.disjoint hm hu).elim

/-- An `mnRel` step `Q' ◁ Q` is the two-arrow path `Q → w(Q) → Q'`. -/
private theorem transGen_arrow_of_mnRel (hM : IsMatching M) {Q' Q : TotalFace K}
    (h : mnRel M Q' Q) : Relation.TransGen (arrow M) Q Q' := by
  obtain ⟨-, hne, τ, hQ, hc⟩ := h
  have hn : ¬ M Q' τ := fun h' => hne (hM.upper_unique h' hQ)
  exact Relation.TransGen.head (Or.inr hQ) (Relation.TransGen.single (Or.inl ⟨hc, hn⟩))

private theorem transGen_arrow_of_transGen_mnRel (hM : IsMatching M) {a b : TotalFace K}
    (h : Relation.TransGen (mnRel M) a b) : Relation.TransGen (arrow M) b a := by
  induction h with
  | single h => exact transGen_arrow_of_mnRel hM h
  | tail _ h ih => exact (transGen_arrow_of_mnRel hM h).trans ih

end Alternation

/-- Whole-diagram acyclicity agrees with MN Def. 2.2 for a matching. -/
theorem isAcyclic_iff_isMNAcyclic {M : TotalFace K → TotalFace K → Prop}
    (hM : IsMatching M) : IsAcyclic M ↔ IsMNAcyclic M := by
  rw [isMNAcyclic_iff_irrefl]
  constructor
  · intro h x hx
    exact h x (transGen_arrow_of_transGen_mnRel hM hx)
  · intro h x hx
    obtain ⟨y, hy⟩ := mn_cycle_of_cycle hM hx
    exact h y hy

/-- A rank strictly increasing along every arrow (coface → face unmatched,
face → coface matched). -/
def IsTopologicalRank (M : TotalFace K → TotalFace K → Prop)
    (rank : TotalFace K → ℕ) : Prop :=
  ∀ u v : TotalFace K, arrow M u v → rank u < rank v

/-- A topological rank rules out directed cycles. -/
theorem IsTopologicalRank.isAcyclic {M : TotalFace K → TotalFace K → Prop}
    {rank : TotalFace K → ℕ} (h : IsTopologicalRank M rank) : IsAcyclic M := by
  have step : ∀ x y : TotalFace K, Relation.TransGen (arrow M) x y → rank x < rank y := by
    intro x y hxy
    induction hxy with
    | single hab => exact h _ _ hab
    | tail _ hab ih => exact ih.trans (h _ _ hab)
  intro x hx
  exact lt_irrefl _ (step x x hx)

/-- With finitely many faces, acyclicity is equivalent to the existence of a topological
rank. The rank in the forward direction counts the faces with a path to the given face. -/
theorem isAcyclic_iff_exists_rank [Finite (TotalFace K)]
    {M : TotalFace K → TotalFace K → Prop} :
    IsAcyclic M ↔ ∃ rank : TotalFace K → ℕ, IsTopologicalRank M rank := by
  classical
  have := Fintype.ofFinite (TotalFace K)
  constructor
  · intro hM
    refine ⟨fun v => (Finset.univ.filter fun u => Relation.TransGen (arrow M) u v).card, ?_⟩
    intro u v huv
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨u, ?_, ?_⟩
      · simpa using Relation.TransGen.single huv
      · simpa using hM u
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw.tail huv
  · rintro ⟨rank, h⟩
    exact h.isAcyclic

variable {α : Type w} [LinearOrder α]

/-- Both faces of every pair have the same filtration grade. -/
def IsGradePreserving (f : FilterFunction K α) (M : TotalFace K → TotalFace K → Prop) :
    Prop :=
  ∀ {σ τ : TotalFace K}, M σ τ → f.value σ = f.value τ

/-- A face of a sublevel, as a face of `K`. -/
def sublevelIncl (f : FilterFunction K α) (r : α) :
    TotalFace (f.sublevel r) → TotalFace K :=
  fun s => ⟨s.val, f.sublevel_le r s.property⟩

/-- Distinct faces of a sublevel stay distinct in `K`. -/
theorem sublevelIncl_injective (f : FilterFunction K α) (r : α) :
    Function.Injective (sublevelIncl f r) := by
  intro s t h
  have hval : (sublevelIncl f r s).val = (sublevelIncl f r t).val := congrArg Subtype.val h
  exact Subtype.ext hval

/-- The pairs of `M` with both faces in the sublevel at `r`. -/
def restrictSublevel (f : FilterFunction K α) (r : α)
    (M : TotalFace K → TotalFace K → Prop) :
    TotalFace (f.sublevel r) → TotalFace (f.sublevel r) → Prop :=
  fun σ τ => M (sublevelIncl f r σ) (sublevelIncl f r τ)

/-- An equal-grade pair lies entirely inside or entirely outside every sublevel. -/
theorem IsGradePreserving.mem_sublevel_iff {f : FilterFunction K α}
    {M : TotalFace K → TotalFace K → Prop} (hf : IsGradePreserving f M)
    {σ τ : TotalFace K} (h : M σ τ) (r : α) :
    σ.val ∈ f.sublevel r ↔ τ.val ∈ f.sublevel r := by
  rw [f.mem_sublevel_iff_of_mem, f.mem_sublevel_iff_of_mem, hf h]

/-- The restricted arrow relation is the arrow relation between included faces. -/
private theorem arrow_restrictSublevel {f : FilterFunction K α} {r : α}
    {M : TotalFace K → TotalFace K → Prop} {σ τ : TotalFace (f.sublevel r)} :
    arrow (restrictSublevel f r M) σ τ ↔ arrow M (sublevelIncl f r σ) (sublevelIncl f r τ) :=
  Iff.rfl

/-- The restriction to a sublevel is again an acyclic matching. -/
theorem IsAcyclicMatching.restrictSublevel {f : FilterFunction K α}
    {M : TotalFace K → TotalFace K → Prop} (hM : IsAcyclicMatching M) (r : α) :
    IsAcyclicMatching (restrictSublevel f r M) := by
  obtain ⟨hm, ha⟩ := hM
  refine ⟨⟨fun h => hm.covBy h, fun h h' => sublevelIncl_injective f r (hm.lower_unique h h'),
    fun h h' => sublevelIncl_injective f r (hm.upper_unique h h'),
    fun h h' => hm.disjoint h h'⟩, ?_⟩
  intro x hx
  exact ha _ (Relation.TransGen.lift (sublevelIncl f r)
    (fun _ _ h => arrow_restrictSublevel.mp h) x x hx)

/-- MN Def. 4.1 for the sublevel frames of `f`: one matching whose pairs never straddle a
frame and whose restriction to every frame is acyclic. -/
def IsFilteredAcyclicMatching (f : FilterFunction K α)
    (M : TotalFace K → TotalFace K → Prop) : Prop :=
  IsMatching M ∧ ∀ r : α,
    (∀ {σ τ : TotalFace K}, M σ τ → (σ.val ∈ f.sublevel r ↔ τ.val ∈ f.sublevel r)) ∧
    IsAcyclic (restrictSublevel f r M)

/-- With equal grades, the grade never increases along an arrow, hence along a path. -/
private theorem value_le_of_transGen {f : FilterFunction K α}
    {M : TotalFace K → TotalFace K → Prop} (hf : IsGradePreserving f M) {x y : TotalFace K}
    (h : Relation.TransGen (arrow M) x y) : f.value y ≤ f.value x := by
  have step : ∀ a b : TotalFace K, arrow M a b → f.value b ≤ f.value a := by
    intro a b hab
    rcases hab with ⟨hc, -⟩ | hm
    · exact f.mono hc.le
    · exact (hf hm).ge
  induction h with
  | single hab => exact step _ _ hab
  | tail _ hab ih => exact (step _ _ hab).trans ih

/-- MN Def. 4.1 for sublevel frames is exactly an acyclic matching with equal grades. -/
theorem isFilteredAcyclicMatching_iff (f : FilterFunction K α)
    (M : TotalFace K → TotalFace K → Prop) :
    IsFilteredAcyclicMatching f M ↔ IsAcyclicMatching M ∧ IsGradePreserving f M := by
  constructor
  · rintro ⟨hm, hr⟩
    have hf : IsGradePreserving f M := by
      intro σ τ h
      have hle : f.value σ ≤ f.value τ := f.mono (hm.covBy h).le
      have hσ : σ.val ∈ f.sublevel (f.value σ) := (f.mem_sublevel_iff_of_mem _ σ).mpr le_rfl
      have hτ := ((hr (f.value σ)).1 h).mp hσ
      exact le_antisymm hle ((f.mem_sublevel_iff_of_mem _ τ).mp hτ)
    refine ⟨⟨hm, ?_⟩, hf⟩
    intro x hx
    -- Every face on the cycle has grade at most `f.value x`, so the cycle lies in that
    -- sublevel and lifts to it.
    have hmem : ∀ y : TotalFace K, Relation.TransGen (arrow M) x y →
        y.val ∈ f.sublevel (f.value x) := fun y hy =>
      (f.mem_sublevel_iff_of_mem _ y).mpr (value_le_of_transGen hf hy)
    have hx' := hmem x hx
    have lift : ∀ y : TotalFace K, ∀ hy : Relation.TransGen (arrow M) x y,
        Relation.TransGen (arrow (restrictSublevel f (f.value x) M))
          ⟨x.val, hx'⟩ ⟨y.val, hmem y hy⟩ := by
      intro y hy
      induction hy with
      | single hab => exact Relation.TransGen.single hab
      | @tail a b hxa hab ih =>
        refine ih.tail ?_
        exact hab
    exact (hr (f.value x)).2 _ (lift x hx)
  · rintro ⟨hM, hf⟩
    exact ⟨hM.1, fun r => ⟨fun h => hf.mem_sublevel_iff h r, (hM.restrictSublevel r).2⟩⟩

end TDA.Persistence.Morse
