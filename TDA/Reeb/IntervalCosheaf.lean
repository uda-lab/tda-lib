import TDA.Topology.Cosheaf
import TDA.Reeb.ComponentsGluing
import TDA.Reeb.Smoothing
import TDA.Reeb.IntervalComponents

/-!
# Smoothing preserves the interval cosheaf condition

`IsIntervalCosheaf.{w} F` states the cosheaf condition for a `Type`-valued interval
precosheaf `F : OpenInterval ⥤ Type wF`: for every cover `I : κ → OpenInterval` of an interval
`J` with `⋃ k, I k = J` and `κ : Type w`, `F` sends the pairwise-intersection cocone
`coverCocone I _` to a colimit. Covers of `⊥`, rays and `ℝ` are included, and so are `⊥`
members; the empty cover of `⊥` forces `F ⊥` to be empty (`IsIntervalCosheaf.isEmpty_obj_bot`).

* Interval facts: a cover thickens to a cover of the thickened interval
  (`iUnion_thicken_eq`), and thickening preserves the intersection of two intervals that meet
  (`thicken_inf`). It does not preserve intersections in general.
* Interval-chain lemma: for members `I i`, `I j` of a cover and
  `W = T_ε (I i) ⊓ T_ε (I j)`, there is a finite chain from `i` to `j` with
  `W ≤ T_ε (I k ⊓ I l)` at every step (`reflTransGen_thicken_inf`). For empty `W` the chain is a
  single step. For nonempty `W` consecutive members intersect
  (`reflTransGen_thicken_inf_of_nonempty`).
* Restriction: a pairwise cosheaf on all opens of `ℝ` restricts to an interval cosheaf
  (`isIntervalCosheaf_of_isPairwiseCosheaf`), so the interval component functor is one
  (`intervalComponents_isIntervalCosheaf`).
* Main theorem (de Silva–Munch–Patel, Proposition 4.20): smoothing preserves the interval
  cosheaf condition (`isIntervalCosheaf_smoothing`), with no extra hypothesis.

The statements are `Type`-valued and specific to open intervals of `ℝ`; nothing here is claimed
for arbitrary open sets or metric spaces. See `docs/math/reeb-interval-cosheaf.md`.
-/

open Set CategoryTheory Limits TDA.Topology
open scoped NNReal

universe u w

namespace TDA.Reeb

namespace OpenInterval

/-- A member of an interval cover lies in the covered interval. -/
theorem le_of_iUnion_eq {κ : Sort*} {I : κ → OpenInterval} {J : OpenInterval}
    (hJ : ⋃ k, (I k : Set ℝ) = J) (k : κ) : I k ≤ J :=
  le_iff_subset.2 (hJ ▸ subset_iUnion (fun k => (I k : Set ℝ)) k)

/-- Thickening a cover of `J` gives a cover of `T_ε J`. -/
theorem iUnion_thicken_eq {κ : Sort*} {I : κ → OpenInterval} {J : OpenInterval}
    (hJ : ⋃ k, (I k : Set ℝ) = J) (ε : ℝ≥0) :
    ⋃ k, (thicken ε (I k) : Set ℝ) = thicken ε J := by
  ext x
  simp only [mem_iUnion, SetLike.mem_coe, mem_thicken]
  constructor
  · rintro ⟨k, y, hy, hxy⟩
    exact ⟨y, le_iff_subset.1 (le_of_iUnion_eq hJ k) hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    have hy' : y ∈ ⋃ k, (I k : Set ℝ) := by rw [hJ]; exact hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy'
    exact ⟨k, y, hk, hxy⟩

/-- Thickening preserves an intersection of two intervals that meet. Without the hypothesis it
fails: disjoint intervals can have overlapping thickenings (see the examples). -/
theorem thicken_inf {I I' : OpenInterval} (h : ((I ⊓ I' : OpenInterval) : Set ℝ).Nonempty)
    (ε : ℝ≥0) : thicken ε (I ⊓ I') = thicken ε I ⊓ thicken ε I' := by
  refine le_antisymm (le_inf (thicken_mono inf_le_left) (thicken_mono inf_le_right)) ?_
  refine le_iff_subset.2 fun x hx => ?_
  have hx' : x ∈ (thicken ε I : Set ℝ) ∩ thicken ε I' := hx
  obtain ⟨y₁, hy₁, h₁⟩ := mem_thicken.1 hx'.1
  obtain ⟨y₂, hy₂, h₂⟩ := mem_thicken.1 hx'.2
  obtain ⟨z, hz⟩ := h
  rw [coe_inf] at hz
  obtain ⟨hzI, hzI'⟩ := hz
  have hy₁' : y₁ ∈ (I : Set ℝ) := hy₁
  have hy₂' : y₂ ∈ (I' : Set ℝ) := hy₂
  rw [abs_le] at h₁ h₂
  have key : ∃ y, y ∈ (I : Set ℝ) ∧ y ∈ (I' : Set ℝ) ∧ |x - y| ≤ ε := by
    rcases le_total y₁ y₂ with h12 | h21
    · rcases le_total z y₁ with hz1 | h1z
      · exact ⟨y₁, hy₁', I'.ordConnected.out hzI' hy₂' ⟨hz1, h12⟩, abs_le.2 h₁⟩
      · rcases le_total z y₂ with hz2 | h2z
        · exact ⟨z, hzI, hzI', abs_le.2 ⟨by linarith, by linarith⟩⟩
        · exact ⟨y₂, I.ordConnected.out hy₁' hzI ⟨h12, h2z⟩, hy₂', abs_le.2 h₂⟩
    · rcases le_total z y₂ with hz2 | h2z
      · exact ⟨y₂, I.ordConnected.out hzI hy₁' ⟨hz2, h21⟩, hy₂', abs_le.2 h₂⟩
      · rcases le_total z y₁ with hz1 | h1z
        · exact ⟨z, hzI, hzI', abs_le.2 ⟨by linarith, by linarith⟩⟩
        · exact ⟨y₁, hy₁', I'.ordConnected.out hy₂' hzI' ⟨h21, h1z⟩, abs_le.2 h₁⟩
  obtain ⟨y, hy, hy', hxy⟩ := key
  exact mem_thicken.2 ⟨y, (show y ∈ (I : Set ℝ) ∩ I' from ⟨hy, hy'⟩), hxy⟩

/-- Interval-chain lemma. For members `I i`, `I j` of a cover of
an interval `J`, with `W = T_ε (I i) ⊓ T_ε (I j)`, there is a finite chain `i = k₀, …, kₙ = j`
with `W ≤ T_ε (I kᵣ ⊓ I kᵣ₊₁)` for every step. (`ReflTransGen` is a finite chain.) For empty
`W` one step suffices. Otherwise the convex hull of `I i ∪ I j` lies in `J` and each of its points
outside `I i ∪ I j` is within `ε` of all of `W`, so the members through it contain `W` after
thickening; overlapping such members are related by `thicken_inf`, and connectedness of the hull
closes the chain. -/
theorem reflTransGen_thicken_inf {κ : Type*} {I : κ → OpenInterval} {J : OpenInterval}
    (hJ : ⋃ k, (I k : Set ℝ) = J) (ε : ℝ≥0) (i j : κ) :
    Relation.ReflTransGen
      (fun k l => thicken ε (I i) ⊓ thicken ε (I j) ≤ thicken ε (I k ⊓ I l)) i j := by
  set W := thicken ε (I i) ⊓ thicken ε (I j) with hW
  by_cases hne : (W : Set ℝ).Nonempty
  swap
  · refine Relation.ReflTransGen.single (le_iff_subset.2 ?_)
    rw [not_nonempty_iff_eq_empty.1 hne]
    exact empty_subset _
  have hstep : ∀ k l, W ≤ thicken ε (I k) → W ≤ thicken ε (I l) →
      ((I k : Set ℝ) ∩ I l).Nonempty → W ≤ thicken ε (I k ⊓ I l) := fun k l hk hl hkl => by
    rw [thicken_inf (by rw [coe_inf]; exact hkl) ε]
    exact le_inf hk hl
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀' : x₀ ∈ (thicken ε (I i) : Set ℝ) ∩ thicken ε (I j) := hx₀
  obtain ⟨p, hp, -⟩ := mem_thicken.1 hx₀'.1
  obtain ⟨q, hq, -⟩ := mem_thicken.1 hx₀'.2
  have hsub : (I i : Set ℝ) ∪ I j ⊆ J :=
    union_subset (le_iff_subset.1 (le_of_iUnion_eq hJ i)) (le_iff_subset.1 (le_of_iUnion_eq hJ j))
  -- the convex hull of `I i ∪ I j`
  let S : Set ℝ := {y | ∃ u ∈ (I i : Set ℝ) ∪ I j, ∃ v ∈ (I i : Set ℝ) ∪ I j, u ≤ y ∧ y ≤ v}
  have hS : S.OrdConnected := ⟨fun a ha b hb y hy => by
    obtain ⟨u, hu, -, -, hua, -⟩ := ha
    obtain ⟨-, -, v, hv, -, hbv⟩ := hb
    exact ⟨u, hu, v, hv, hua.trans hy.1, hy.2.trans hbv⟩⟩
  -- every point of the hull lies in a member whose thickening contains `W`
  have hcov : ∀ y ∈ S, ∃ k, y ∈ (I k : Set ℝ) ∧ W ≤ thicken ε (I k) := by
    rintro y ⟨u, hu, v, hv, huy, hyv⟩
    by_cases hyi : y ∈ (I i : Set ℝ)
    · exact ⟨i, hyi, inf_le_left⟩
    by_cases hyj : y ∈ (I j : Set ℝ)
    · exact ⟨j, hyj, inf_le_right⟩
    have hyJ : y ∈ (J : Set ℝ) := J.ordConnected.out (hsub hu) (hsub hv) ⟨huy, hyv⟩
    rw [← hJ] at hyJ
    obtain ⟨k, hk⟩ := mem_iUnion.1 hyJ
    refine ⟨k, hk, le_iff_subset.2 fun x hx => mem_thicken.2 ⟨y, hk, ?_⟩⟩
    have hx' : x ∈ (thicken ε (I i) : Set ℝ) ∩ thicken ε (I j) := hx
    obtain ⟨y₁, hy₁, h₁⟩ := mem_thicken.1 hx'.1
    obtain ⟨y₂, hy₂, h₂⟩ := mem_thicken.1 hx'.2
    have hy₁' : y₁ ∈ (I i : Set ℝ) := hy₁
    have hy₂' : y₂ ∈ (I j : Set ℝ) := hy₂
    rw [abs_le] at h₁ h₂ ⊢
    rcases le_total y y₁ with hy1 | h1y <;> rcases le_total y y₂ with hy2 | h2y
    · exfalso
      rcases hu with hu | hu
      · exact hyi ((I i).ordConnected.out hu hy₁' ⟨huy, hy1⟩)
      · exact hyj ((I j).ordConnected.out hu hy₂' ⟨huy, hy2⟩)
    · constructor <;> linarith
    · constructor <;> linarith
    · exfalso
      rcases hv with hv | hv
      · exact hyi ((I i).ordConnected.out hy₁' hv ⟨h1y, hyv⟩)
      · exact hyj ((I j).ordConnected.out hy₂' hv ⟨h2y, hyv⟩)
  -- split the members containing `W` by reachability from `i`
  let P : κ → κ → Prop := fun k l => W ≤ thicken ε (I k ⊓ I l)
  let O₁ : Set ℝ := ⋃ (k) (_ : W ≤ thicken ε (I k) ∧ Relation.ReflTransGen P i k), (I k : Set ℝ)
  let O₂ : Set ℝ := ⋃ (k) (_ : W ≤ thicken ε (I k) ∧ ¬ Relation.ReflTransGen P i k),
    (I k : Set ℝ)
  have hO₁ : IsOpen O₁ := isOpen_iUnion fun k => isOpen_iUnion fun _ => (I k).isOpen
  have hO₂ : IsOpen O₂ := isOpen_iUnion fun k => isOpen_iUnion fun _ => (I k).isOpen
  have hdisj : Disjoint O₁ O₂ := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨k, ⟨hkW, hk⟩, hyk⟩ := mem_iUnion₂.1 hy₁
    obtain ⟨l, ⟨hlW, hl⟩, hyl⟩ := mem_iUnion₂.1 hy₂
    exact hl (hk.tail (hstep k l hkW hlW ⟨y, hyk, hyl⟩))
  have hSO : S ⊆ O₁ ∪ O₂ := by
    intro y hy
    obtain ⟨k, hyk, hkW⟩ := hcov y hy
    by_cases hk : Relation.ReflTransGen P i k
    · exact Or.inl (mem_iUnion₂.2 ⟨k, ⟨hkW, hk⟩, hyk⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨k, ⟨hkW, hk⟩, hyk⟩)
  have hp' : p ∈ (I i : Set ℝ) := hp
  have hq' : q ∈ (I j : Set ℝ) := hq
  have hpS : p ∈ S := ⟨p, Or.inl hp', p, Or.inl hp', le_rfl, le_rfl⟩
  have hqS : q ∈ S := ⟨q, Or.inr hq', q, Or.inr hq', le_rfl, le_rfl⟩
  have hSO₁ : S ⊆ O₁ := hS.isPreconnected.subset_left_of_subset_union hO₁ hO₂ hdisj hSO
    ⟨p, hpS, mem_iUnion₂.2 ⟨i, ⟨inf_le_left, .refl⟩, hp'⟩⟩
  obtain ⟨k, ⟨hkW, hk⟩, hqk⟩ := mem_iUnion₂.1 (hSO₁ hqS)
  exact hk.tail (hstep k j hkW inf_le_right ⟨q, hqk, hq'⟩)

/-- The interval-chain lemma in the body's literal form: for nonempty
`W = T_ε (I i) ⊓ T_ε (I j)` there is a finite chain `i = k₀, …, kₙ = j` whose consecutive original
members intersect and with `W ≤ T_ε (I kᵣ ⊓ I kᵣ₊₁)` for every step. -/
theorem reflTransGen_thicken_inf_of_nonempty {κ : Type*} {I : κ → OpenInterval} {J : OpenInterval}
    (hJ : ⋃ k, (I k : Set ℝ) = J) (ε : ℝ≥0) (i j : κ)
    (hW : ((thicken ε (I i) ⊓ thicken ε (I j) : OpenInterval) : Set ℝ).Nonempty) :
    Relation.ReflTransGen (fun k l => ((I k ⊓ I l : OpenInterval) : Set ℝ).Nonempty ∧
      thicken ε (I i) ⊓ thicken ε (I j) ≤ thicken ε (I k ⊓ I l)) i j := by
  refine Relation.ReflTransGen.mono ?_ i j (reflTransGen_thicken_inf hJ ε i j)
  intro k l hkl
  refine ⟨?_, hkl⟩
  by_contra hne
  have hbot : I k ⊓ I l = ⊥ :=
    SetLike.coe_injective (by rw [not_nonempty_iff_eq_empty.1 hne, coe_bot])
  obtain ⟨x, hx⟩ := hW
  have hx' := le_iff_subset.1 hkl hx
  rw [hbot, thicken_bot, coe_bot] at hx'
  exact hx'

end OpenInterval

open OpenInterval

/-- The interval cosheaf condition (DMP §3, pairwise-intersection form): for every cover
`I : κ → OpenInterval` of an interval `J` (`⋃ k, I k = J`, `κ : Type wκ`), `F` sends the
pairwise-intersection cocone with apex `J` to a colimit. The empty cover of `⊥` is included. -/
def IsIntervalCosheaf.{wκ, wF} (F : OpenInterval ⥤ Type wF) : Prop :=
  ∀ ⦃κ : Type wκ⦄ (I : κ → OpenInterval) (J : OpenInterval) (hJ : ⋃ k, (I k : Set ℝ) = J),
    Nonempty (IsColimit (F.mapCocone (coverCocone I (le_of_iUnion_eq hJ))))

section

variable {F : OpenInterval ⥤ Type u}

/-- Empty-value condition: an interval cosheaf is empty over `⊥` (the empty cover). -/
theorem IsIntervalCosheaf.isEmpty_obj_bot (hF : IsIntervalCosheaf.{w} F) : IsEmpty (F.obj ⊥) := by
  obtain ⟨hsurj, -⟩ := (nonempty_isColimit_mapCocone_iff _ _ _).1
    (hF (PEmpty.elim : PEmpty.{w + 1} → OpenInterval) ⊥ (by simp))
  exact ⟨fun x => (hsurj x).elim fun i _ => i.elim⟩

/-- Raw compatible-family universal property of an interval cosheaf, test object in any `Sort`. -/
theorem IsIntervalCosheaf.existsUnique_glue (hF : IsIntervalCosheaf.{w} F) {κ : Type w}
    (I : κ → OpenInterval) {J : OpenInterval} (hJ : ⋃ k, (I k : Set ℝ) = J) {A : Sort*}
    (a : ∀ k, F.obj (I k) → A)
    (ha : ∀ k l (c : F.obj (I k ⊓ I l)),
      a k (F.map (homOfLE inf_le_left) c) = a l (F.map (homOfLE inf_le_right) c)) :
    ∃! g : F.obj J → A, ∀ k (e : F.obj (I k)), g (F.map (homOfLE (le_of_iUnion_eq hJ k)) e) = a k e := by
  obtain ⟨hsurj, hker⟩ := (nonempty_isColimit_mapCocone_iff _ _ _).1 (hF I J hJ)
  exact existsUnique_glue_of_surjective_of_eqvGen F I _ hsurj hker a ha

/-- Invariance under natural isomorphism. -/
theorem IsIntervalCosheaf.of_iso {G : OpenInterval ⥤ Type u} (e : F ≅ G)
    (hF : IsIntervalCosheaf.{w} F) : IsIntervalCosheaf.{w} G :=
  fun _ I J hJ => (hF I J hJ).map fun h => IsColimit.mapCoconeEquiv e h

end

/-- Restriction along `toOpensFunctor`: a pairwise cosheaf on all opens of `ℝ`
restricts to an interval cosheaf. Inputs: `iSup_toOpens_eq` (union equation) and `toOpens_inf`
(definitional here: interval overlaps map to opens overlaps). -/
theorem isIntervalCosheaf_of_isPairwiseCosheaf {G : TopologicalSpace.Opens ℝ ⥤ Type u}
    (hG : IsPairwiseCosheaf.{w} G) : IsIntervalCosheaf.{w} (toOpensFunctor ⋙ G) := by
  intro κ I J hJ
  have hV := hG (fun k => toOpens (I k))
  rw [nonempty_isColimit_mapCocone_iff] at hV ⊢
  obtain ⟨hsurj, hker⟩ := hV
  have hsup : ⨆ k, toOpens (I k) = toOpens J := iSup_toOpens_eq I J hJ
  let a : (⨆ k, toOpens (I k)) ⟶ toOpens J := homOfLE hsup.le
  let b : toOpens J ⟶ ⨆ k, toOpens (I k) := homOfLE hsup.ge
  refine ⟨fun x => ?_, fun i j e e' h => ?_⟩
  · obtain ⟨i, e, he⟩ := hsurj (G.map b x)
    refine ⟨i, e, ?_⟩
    refine (map_map_apply_of_thin G ((Pairwise.cocone fun k => toOpens (I k)).ι.app (.single i))
      a _ e).symm.trans ?_
    rw [he]
    exact (map_map_apply_of_thin G b a (𝟙 _) x).trans (G.map_id_apply _ x)
  · refine hker i j e e' ?_
    have h' := congrArg (fun y => G.map b y) h
    exact (map_map_apply_of_thin G _ b _ e).symm.trans (h'.trans (map_map_apply_of_thin G _ b _ e'))

/-- The interval component functor `C_f|Int` of `f : X → ℝ` (`intervalComponents`) is an
interval cosheaf. -/
theorem intervalComponents_isIntervalCosheaf {X : Type u} [TopologicalSpace X] (f : C(X, ℝ)) :
    IsIntervalCosheaf.{w} (intervalComponents f) :=
  isIntervalCosheaf_of_isPairwiseCosheaf (componentFunctor_isPairwiseCosheaf f)

section smoothing

variable {F : OpenInterval ⥤ Type u}

/-- An overlap step of `F` on the thickened cover is a chain of overlap steps of `S_ε F` on the
original cover (uses the interval-chain lemma). -/
theorem eqvGen_overlapRel_smoothing (F : OpenInterval ⥤ Type u) (ε : ℝ≥0) {κ : Type w}
    {I : κ → OpenInterval} {J : OpenInterval} (hJ : ⋃ k, (I k : Set ℝ) = J)
    {p q : Σ k, F.obj (thicken ε (I k))}
    (h : Relation.EqvGen (overlapRel F (fun k => thicken ε (I k))) p q) :
    Relation.EqvGen (overlapRel ((smoothing ε).obj F) I) p q := by
  have step : ∀ p q, overlapRel F (fun k => thicken ε (I k)) p q →
      Relation.EqvGen (overlapRel ((smoothing ε).obj F) I) p q := by
    rintro ⟨i, e⟩ ⟨j, e'⟩ ⟨c, hc, hc'⟩
    have key : ∀ k, Relation.ReflTransGen
        (fun k l => thicken ε (I i) ⊓ thicken ε (I j) ≤ thicken ε (I k ⊓ I l)) i k →
        ∃ hk : thicken ε (I i) ⊓ thicken ε (I j) ≤ thicken ε (I k),
          Relation.EqvGen (overlapRel ((smoothing ε).obj F) I) ⟨i, e⟩ ⟨k, F.map (homOfLE hk) c⟩ := by
      intro k hk
      induction hk with
      | refl => exact ⟨inf_le_left, by rw [hc]; exact .refl _⟩
      | tail _ hkl ih =>
        obtain ⟨hk, ih⟩ := ih
        refine ⟨hkl.trans (thicken_mono inf_le_right), ih.trans _ _ _ (.rel _ _ ?_)⟩
        refine ⟨F.map (homOfLE hkl) c, ?_, ?_⟩
        · exact map_map_apply_of_thin F _ _ _ c
        · exact map_map_apply_of_thin F _ _ _ c
    obtain ⟨hj, hrel⟩ := key j (reflTransGen_thicken_inf hJ ε i j)
    have : F.map (homOfLE hj) c = e' := (map_apply_eq_of_thin F _ _ c).trans hc'
    rw [← this]
    exact hrel
  induction h with
  | rel p q hpq => exact step p q hpq
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Cover-wise form: if `F` satisfies the cosheaf condition on the thickened cover of `T_ε J`,
then `S_ε F` satisfies it on the cover of `J`. -/
theorem smoothing_isColimit_coverCocone (ε : ℝ≥0) {κ : Type w} (I : κ → OpenInterval)
    {J : OpenInterval} (hJ : ⋃ k, (I k : Set ℝ) = J)
    (hF : Nonempty (IsColimit (F.mapCocone
      (coverCocone (fun k => thicken ε (I k)) (le_of_iUnion_eq (iUnion_thicken_eq hJ ε)))))) :
    Nonempty (IsColimit (((smoothing ε).obj F).mapCocone (coverCocone I (le_of_iUnion_eq hJ)))) := by
  rw [nonempty_isColimit_mapCocone_iff] at hF ⊢
  obtain ⟨hsurj, hker⟩ := hF
  refine ⟨fun x => ?_, fun i j e e' h => ?_⟩
  · obtain ⟨i, e, he⟩ := hsurj x
    exact ⟨i, e, (map_apply_eq_of_thin F _ _ e).trans he⟩
  · refine eqvGen_overlapRel_smoothing F ε hJ (hker i j e e' ?_)
    exact (map_apply_eq_of_thin F _ _ e).trans (h.trans (map_apply_eq_of_thin F _ _ e'))

/-- DMP Proposition 4.20 for `Type`-valued interval precosheaves: smoothing preserves the
interval cosheaf condition. -/
theorem isIntervalCosheaf_smoothing (hF : IsIntervalCosheaf.{w} F) (ε : ℝ≥0) :
    IsIntervalCosheaf.{w} ((smoothing ε).obj F) :=
  fun _ I _ hJ => smoothing_isColimit_coverCocone ε I hJ (hF _ _ (iUnion_thicken_eq hJ ε))

/-- At `ε = 0` the statement reduces to the hypothesis. -/
theorem isIntervalCosheaf_smoothing_zero_iff :
    IsIntervalCosheaf.{w} ((smoothing 0).obj F) ↔ IsIntervalCosheaf.{w} F :=
  ⟨fun h => h.of_iso (smoothingZeroIso.app F), fun h => isIntervalCosheaf_smoothing h 0⟩

end smoothing

end TDA.Reeb
