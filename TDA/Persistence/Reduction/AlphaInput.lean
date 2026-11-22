import TDA.Filtration.RationalAlpha
import TDA.Persistence.Reduction.RipsInput
import TDA.Persistence.Reduction.FiniteInputVertexMap
import TDA.Persistence.SublevelDiagramVertexMap
import Mathlib.Order.Interval.Finset.Fin

/-!
# Certified barcodes of rational planar α filtrations

The input is a finite family of rational planar sites. Distinct sites are accepted,
including the empty family. The squared entrance grades are ordered exactly and
assigned zero-based integer ranks for the finite F₂ reducer. The returned list
keeps repeated occurrences and records essential deaths separately.
-/

set_option autoImplicit false

namespace TDA.Persistence.Reduction.AlphaInput

open TDA.Filtration TDA.Simplicial TDA.Persistence CategoryTheory
open scoped Finset

variable {n : ℕ}

abbrev Point := RationalAlpha.Point

private def grades (p : Fin n ↪ Point) : Finset ℚ :=
  (RationalAlpha.gradedFaces p).image Prod.snd

private def rank (G : Finset ℚ) (q : ℚ) : ℤ :=
  ((G.filter (· < q)).card : ℤ)

private theorem rank_strictMonoOn (G : Finset ℚ) : StrictMonoOn (rank G) (↑G : Set ℚ) := by
  intro a ha b _ hab
  have he : G.filter (· < a) ≠ G.filter (· < b) := by
    intro h
    have hm : a ∈ G.filter (· < b) := Finset.mem_filter.2 ⟨ha,hab⟩
    rw [← h] at hm
    exact (lt_irrefl _) (Finset.mem_filter.1 hm).2
  have hs : G.filter (· < a) ⊂ G.filter (· < b) :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.monotone_filter_right G
      (fun _ _ ht => ht.trans hab), he⟩
  unfold rank
  exact_mod_cast Finset.card_lt_card hs

private theorem rank_le_rank (G : Finset ℚ) {a b : ℚ} (h : a ≤ b) :
    rank G a ≤ rank G b := by
  have hs : G.filter (· < a) ⊆ G.filter (· < b) :=
    Finset.monotone_filter_right G (fun _ _ ht => ht.trans_le h)
  unfold rank
  exact_mod_cast Finset.card_le_card hs

private def decodeGrade (G : Finset ℚ) (z : ℤ) : ℚ :=
  G.sort[z.toNat]?.getD 0

private theorem rank_of_index (G : Finset ℚ) (i : Fin G.card) :
    rank G (G.orderEmbOfFin rfl i) = (i.val : ℤ) := by
  let e := G.orderEmbOfFin rfl
  have h : (Finset.Iio i).map e.toEmbedding = G.filter (· < e i) := by
    ext q
    simp only [Finset.mem_map, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem G rfl j, e.strictMono hj⟩
    · rintro ⟨hq, hlt⟩
      let j := (G.orderIsoOfFin rfl).symm ⟨q, hq⟩
      have hej : e j = q := congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨q, hq⟩)
      exact ⟨j, e.lt_iff_lt.mp (hej ▸ hlt), hej⟩
  change ((G.filter (· < e i)).card : ℤ) = _
  rw [← h, Finset.card_map, Fin.card_Iio]

private theorem decode_rank (G : Finset ℚ) {q : ℚ} (hq : q ∈ G) :
    decodeGrade G (rank G q) = q := by
  let i := (G.orderIsoOfFin rfl).symm ⟨q, hq⟩
  have he : G.orderEmbOfFin rfl i = q :=
    congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨q, hq⟩)
  have hr := rank_of_index G i
  rw [he] at hr
  unfold decodeGrade
  rw [hr, Int.toNat_natCast, ← he, Finset.orderEmbOfFin_apply]
  rw [List.getElem?_eq_getElem (by simp)]
  rfl

private def atGrade (rows : Finset (Finset (Fin n) × ℚ)) (G : Finset ℚ) (q : ℚ) :
    List FiniteInput.Entry :=
  (DistanceTable.faceLists n).filterMap fun l =>
    if (l.toFinset, q) ∈ rows then some (l.toFinset.map Fin.valEmbedding, rank G q) else none

/-- The α faces, ordered by grade and then by cardinality and vertex labels. -/
def simplexInput (p : Fin n ↪ Point) : FiniteInput.Input :=
  let rows := RationalAlpha.gradedFaces p
  let G := rows.image Prod.snd
  G.sort.flatMap (atGrade rows G)

private theorem count_mem_grades {p : Fin n ↪ Point} {s : Finset (Fin n)} {q : ℚ}
    (h : (s,q) ∈ RationalAlpha.gradedFaces p) : q ∈ grades p :=
  Finset.mem_image_of_mem Prod.snd h

private theorem row_filter {p : Fin n ↪ Point} {s : Finset (Fin n)} {q : ℚ}
    (h : (s,q) ∈ RationalAlpha.gradedFaces p) :
    ∃ hs : s ∈ (RationalAlpha.finiteComplex p).toPre,
      (RationalAlpha.filter p).value ⟨s,hs⟩ = q := by
  obtain ⟨r, hr, rfl⟩ := (RationalAlpha.mem_gradedFaces_iff p q).1 h
  exact ⟨(RationalAlpha.mem_faces_iff p).2 ⟨r,hr⟩, RationalAlpha.filter_value p _ hr⟩

private theorem mem_atGrade {rows : Finset (Finset (Fin n) × ℚ)} {G : Finset ℚ}
    {q : ℚ} {e : FiniteInput.Entry} :
    e ∈ atGrade rows G q ↔ ∃ s : Finset (Fin n), s.Nonempty ∧ (s,q) ∈ rows ∧
      e = (s.map Fin.valEmbedding, rank G q) := by
  unfold atGrade
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, hp⟩
    split at hp
    · exact ⟨_, (List.toFinset_nonempty_iff l).2 (DistanceTable.mem_faceLists.1 hl).1, ‹_›,
        (Option.some.inj hp).symm⟩
    · simp at hp
  · rintro ⟨s, hs, hrow, rfl⟩
    refine ⟨s.sort, DistanceTable.mem_faceLists.2 ⟨?_, (Finset.sortedLT_sort s).pairwise⟩, ?_⟩
    · rw [← List.toFinset_nonempty_iff, Finset.sort_toFinset]
      exact hs
    · simp [hrow]

private theorem mem_simplexInput {p : Fin n ↪ Point} {e : FiniteInput.Entry} :
    e ∈ simplexInput p ↔ ∃ s q, (s,q) ∈ RationalAlpha.gradedFaces p ∧
      e = (s.map Fin.valEmbedding, rank (grades p) q) := by
  unfold simplexInput
  simp only [List.mem_flatMap, Finset.mem_sort, mem_atGrade]
  constructor
  · rintro ⟨q, -, s, -, h, he⟩
    exact ⟨s,q,h,he⟩
  · rintro ⟨s,q,h,he⟩
    obtain ⟨hs, -⟩ := row_filter h
    exact ⟨q, count_mem_grades h, s,
      ((RationalAlpha.finiteComplex p).toPre.isRelLowerSet_faces hs).1, h, he⟩

private def EntryLT (a b : FiniteInput.Entry) : Prop :=
  a.2 < b.2 ∨ a.2 = b.2 ∧ a.1.card ≤ b.1.card ∧ a.1 ≠ b.1

private theorem faceLists_pairwise_length :
    (DistanceTable.faceLists n).Pairwise (fun a b => a.length ≤ b.length) := by
  unfold DistanceTable.faceLists
  rw [List.pairwise_flatMap]
  refine ⟨fun k _ => List.pairwise_iff_get.2 (fun i j _ => ?_), ?_⟩
  · have hi := List.mem_sublistsLen.1 (List.mem_reverse.1 (List.get_mem _ i))
    have hj := List.mem_sublistsLen.1 (List.mem_reverse.1 (List.get_mem _ j))
    rw [hi.2, hj.2]
  · refine List.pairwise_lt_range.imp ?_
    intro i j hij a ha b hb
    have ha' := (List.mem_sublistsLen.1 (List.mem_reverse.1 ha)).2
    have hb' := (List.mem_sublistsLen.1 (List.mem_reverse.1 hb)).2
    omega

private theorem pairwise_atGrade (rows : Finset (Finset (Fin n) × ℚ)) (G : Finset ℚ)
    (q : ℚ) : (atGrade rows G q).Pairwise EntryLT := by
  unfold atGrade
  rw [List.pairwise_filterMap]
  refine ((faceLists_pairwise_length (n := n)).and DistanceTable.nodup_faceLists).imp_of_mem ?_
  intro a b ha hb hab x hx y hy
  split at hx <;> try simp at hx
  split at hy <;> try simp at hy
  cases hx
  cases hy
  have ha' := (DistanceTable.mem_faceLists.1 ha).2
  have hb' := (DistanceTable.mem_faceLists.1 hb).2
  refine Or.inr ⟨rfl, ?_, ?_⟩
  · simpa only [Finset.card_map, List.toFinset_card_of_nodup (ha'.imp ne_of_lt),
      List.toFinset_card_of_nodup (hb'.imp ne_of_lt)] using hab.1
  · intro h
    apply hab.2
    have he := Finset.map_injective _ h
    exact ((List.toFinset_sort (· ≤ ·) (ha'.imp ne_of_lt)).2 (ha'.imp le_of_lt)).symm.trans
      (he ▸ (List.toFinset_sort (· ≤ ·) (hb'.imp ne_of_lt)).2 (hb'.imp le_of_lt))

private theorem simplexInput_pairwise (p : Fin n ↪ Point) :
    (simplexInput p).Pairwise EntryLT := by
  change ((grades p).sort.flatMap _).Pairwise _
  rw [List.pairwise_flatMap]
  refine ⟨fun q _ => pairwise_atGrade _ _ q, ?_⟩
  refine ((Finset.sortedLT_sort (grades p)).pairwise.imp_of_mem ?_)
  intro a b ha hb hab x hx y hy
  obtain ⟨s, -, -, rfl⟩ := mem_atGrade.1 hx
  obtain ⟨t, -, -, rfl⟩ := mem_atGrade.1 hy
  exact Or.inl (rank_strictMonoOn _ ((Finset.mem_sort (· ≤ ·)).1 ha) ((Finset.mem_sort (· ≤ ·)).1 hb) hab)

/-- Every generated simplex list meets all the reducer's validity conditions. -/
theorem simplexInput_valid (p : Fin n ↪ Point) : FiniteInput.Valid (simplexInput p) := by
  let xs := simplexInput p
  have hget (i : Fin xs.length) := mem_simplexInput.1 (List.get_mem xs i)
  have hpw := List.pairwise_iff_get.1 (simplexInput_pairwise p)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨s, q, hs, he⟩ := hget i
    obtain ⟨hs', -⟩ := row_filter hs
    rw [he]
    exact (((RationalAlpha.finiteComplex p).toPre.isRelLowerSet_faces hs').1).map
  · unfold FiniteInput.faces List.Nodup
    rw [List.pairwise_map]
    refine (simplexInput_pairwise p).imp_of_mem ?_
    intro x y hx hy h hxy
    obtain ⟨s, a, ha, rfl⟩ := mem_simplexInput.1 hx
    obtain ⟨t, b, hb, rfl⟩ := mem_simplexInput.1 hy
    have hst : s = t := Finset.map_injective _ hxy
    subst t
    obtain ⟨_, ha'⟩ := row_filter ha
    obtain ⟨_, hb'⟩ := row_filter hb
    have hab := ha'.symm.trans hb'
    rw [← hab] at h
    exact h.elim (lt_irrefl _) (fun h => h.2.2 rfl)
  · intro i t ht htne
    obtain ⟨s, q, hs, hi⟩ := hget i
    obtain ⟨hs', -⟩ := row_filter hs
    rw [hi, Finset.mem_powerset] at ht
    obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 ht
    have hu' : u ∈ (RationalAlpha.finiteComplex p).toPre :=
      ((RationalAlpha.finiteComplex p).toPre.isRelLowerSet_faces hs').2 hu
        (Finset.map_nonempty.1 htne)
    obtain ⟨r, hr⟩ := (RationalAlpha.mem_faces_iff p).1 hu'
    have hm := (RationalAlpha.mem_gradedFaces_iff p r.grade).2 ⟨r,hr,rfl⟩
    exact List.mem_map.2 ⟨_, mem_simplexInput.2 ⟨u,r.grade,hm,rfl⟩, rfl⟩
  · intro i j hij
    by_contra h
    rcases lt_or_eq_of_le (not_lt.1 h) with hji | rfl
    · obtain ⟨s,a,ha,hi⟩ := hget i
      obtain ⟨t,b,hb,hj⟩ := hget j
      rw [hi,hj] at hij
      obtain ⟨hs, ha'⟩ := row_filter ha
      obtain ⟨ht, hb'⟩ := row_filter hb
      have hle := (RationalAlpha.filter p).mono
        (show (⟨s,hs⟩ : TotalFace (RationalAlpha.finiteComplex p).toPre) ≤ ⟨t,ht⟩ from
          Finset.map_subset_map.1 hij.subset)
      rw [ha', hb'] at hle
      have hg := rank_le_rank (grades p) hle
      have hc := Finset.card_lt_card hij
      have ho := hpw j i hji
      rw [hi,hj] at ho
      rcases ho with ho | ⟨-, ho, -⟩
      · exact (not_lt_of_ge hg) ho
      · exact (not_le_of_gt hc) ho
    · exact (ssubset_irrefl _ hij)
  · intro i j hij
    rcases lt_or_eq_of_le hij with h | rfl
    · exact (hpw i j h).elim le_of_lt (fun h => h.1.le)
    · exact le_rfl

/-- The reducer stage that represents the actual squared-radius threshold.
Before the first cut, including for an empty cloud, the stage is `-1`. -/
noncomputable def stage (p : Fin n ↪ Point) : ℝ →o ℤ where
  toFun t := (((grades p).filter fun (q : ℚ) => (q : ℝ) ≤ t).card : ℤ) - 1
  monotone' s t h := by
    have hsub : (grades p).filter (fun (q : ℚ) => (q : ℝ) ≤ s) ⊆
        (grades p).filter (fun (q : ℚ) => (q : ℝ) ≤ t) :=
      Finset.monotone_filter_right _ (fun _ _ hq => hq.trans h)
    have hc := Finset.card_le_card hsub
    dsimp only
    omega

private theorem rank_le_stage {p : Fin n ↪ Point} {q : ℚ} (hq : q ∈ grades p) (t : ℝ) :
    rank (grades p) q ≤ stage p t ↔ (q : ℝ) ≤ t := by
  let S := (grades p).filter (· < q)
  let T := (grades p).filter (fun (g : ℚ) => (g : ℝ) ≤ t)
  change (S.card : ℤ) ≤ (T.card : ℤ) - 1 ↔ _
  by_cases h : (q : ℝ) ≤ t
  · have hsubset : S ⊆ T := by
      intro g hg
      have hg' := Finset.mem_filter.mp hg
      exact Finset.mem_filter.mpr ⟨hg'.1, (Rat.cast_le.mpr hg'.2.le).trans h⟩
    have hne : S ≠ T := by
      intro he
      have hm : q ∈ T := Finset.mem_filter.mpr ⟨hq, h⟩
      rw [← he] at hm
      exact (lt_irrefl q) (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩)
    simp only [h, iff_true]
    omega
  · have hsubset : T ⊆ S := by
      intro g hg
      have hg' := Finset.mem_filter.mp hg
      exact Finset.mem_filter.mpr ⟨hg'.1, Rat.cast_lt.mp (hg'.2.trans_lt (lt_of_not_ge h))⟩
    have hcard := Finset.card_le_card hsubset
    simp only [h, iff_false]
    omega

/-- At every real threshold the reducer presents precisely the α sublevel faces on
the corresponding natural-number labels. -/
theorem mem_sublevel (p : Fin n ↪ Point) (t : ℝ) (u : Finset ℕ) :
    u ∈ (FiniteInput.gradeFilter (simplexInput p) (simplexInput_valid p)).sublevel (stage p t) ↔
      ∃ s ∈ Alpha.complex (RationalAlpha.realSites p) t, u = s.map Fin.valEmbedding := by
  rw [FiniteInput.mem_sublevel_iff_list]
  constructor
  · rintro ⟨i, hi, hr⟩
    obtain ⟨s,q,hrow,he⟩ := mem_simplexInput.1 (List.get_mem (simplexInput p) i)
    obtain ⟨r, hp, rfl⟩ := (RationalAlpha.mem_gradedFaces_iff p q).1 hrow
    refine ⟨s, (RationalAlpha.mem_complex_iff p t).2 ⟨r,hp, ?_⟩, ?_⟩
    · apply (rank_le_stage (count_mem_grades hrow) t).1
      simpa only [he] using hr
    · exact hi.symm.trans (congrArg Prod.fst he)
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨r, hr, ht⟩ := (RationalAlpha.mem_complex_iff p t).1 hs
    have hrow := (RationalAlpha.mem_gradedFaces_iff p r.grade).2 ⟨r,hr,rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 (mem_simplexInput.2 ⟨s,r.grade,hrow,rfl⟩)
    exact ⟨i, congrArg Prod.fst hi,
      (congrArg Prod.snd hi).le.trans ((rank_le_stage (count_mem_grades hrow) t).2 ht)⟩

/-- The integer filtration represented by the executable simplex list. -/
abbrev inputFilter (p : Fin n ↪ Point) :=
  FiniteInput.gradeFilter (simplexInput p) (simplexInput_valid p)

/-- Relabel the actual α sublevel by natural-number vertex labels. -/
def labelMap (p : Fin n ↪ Point) (t : ℝ) :
    VertexMap ((Alpha.filter (RationalAlpha.realSites p)).sublevel t)
      ((inputFilter p).sublevel (stage p t)) where
  toFun := Fin.val
  map_face s hs := by
    rw [Alpha.sublevel_eq_complex] at hs
    have h := (mem_sublevel p t (s.map Fin.valEmbedding)).2 ⟨s,hs,rfl⟩
    rw [Finset.map_eq_image] at h
    convert h using 1
    ext v
    simp

private def clamp (hn : 0 < n) (x : ℕ) : Fin n :=
  if h : x < n then ⟨x,h⟩ else ⟨0,hn⟩

private theorem clamp_val (hn : 0 < n) (i : Fin n) : clamp hn i.val = i := by
  simp [clamp]

private def inverseLabelMap (p : Fin n ↪ Point) (hn : 0 < n) (t : ℝ) :
    VertexMap ((inputFilter p).sublevel (stage p t))
      ((Alpha.filter (RationalAlpha.realSites p)).sublevel t) where
  toFun := clamp hn
  map_face u hu := by
    rw [Alpha.sublevel_eq_complex]
    obtain ⟨s,hs,rfl⟩ := (mem_sublevel p t u).1 hu
    have he : @Finset.image ℕ (Fin n) (Classical.decEq _) (clamp hn)
        (s.map Fin.valEmbedding) = s := by
      ext i
      simp only [Finset.mem_image, Finset.mem_map, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨_, ⟨j,hj,rfl⟩, rfl⟩
        simpa only [clamp_val] using hj
      · intro hi
        exact ⟨i.val, ⟨i,hi,rfl⟩, clamp_val hn i⟩
    rw [he]
    exact hs

/-- The relabeling induces an isomorphism in each degree, including for the empty cloud. -/
theorem labelMap_isIso (p : Fin n ↪ Point) (t : ℝ) (k : ℕ) :
    IsIso (simplicialHomologyMap (ZMod 2) (labelMap p t) k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have ha : (Alpha.filter (RationalAlpha.realSites p)).sublevel t = ⊥ := by
      rw [Alpha.sublevel_eq_complex]
      exact le_antisymm (fun s hs => by
        obtain ⟨i, -⟩ := (Alpha.complex (RationalAlpha.realSites p) t).isRelLowerSet_faces hs |>.1
        exact i.elim0) bot_le
    have hb : (inputFilter p).sublevel (stage p t) = ⊥ :=
      le_antisymm (fun u hu => by
        obtain ⟨s,hs,-⟩ := (mem_sublevel p t u).1 hu
        rw [← Alpha.sublevel_eq_complex, ha] at hs
        exact (TDA.Filtration.mem_bot_iff s).1 hs) bot_le
    have hx : Limits.IsZero (simplicialHomology
        ((Alpha.filter (RationalAlpha.realSites p)).sublevel t) (ZMod 2) k) := by
      rw [ha]
      exact TDA.Simplicial.isZero_simplicialHomology_bot (ZMod 2) k
    have hy : Limits.IsZero (simplicialHomology
        ((inputFilter p).sublevel (stage p t)) (ZMod 2) k) := by
      rw [hb]
      exact TDA.Simplicial.isZero_simplicialHomology_bot (ZMod 2) k
    exact ⟨⟨0, hx.eq_of_src _ _, hy.eq_of_src _ _⟩⟩
  · refine ⟨⟨simplicialHomologyMap (ZMod 2) (inverseLabelMap p hn t) k, ?_, ?_⟩⟩
    · exact simplicialHomologyMap_comp_eq_id (ZMod 2) _ _ (fun _ _ i _ => clamp_val hn i) k
    · refine simplicialHomologyMap_comp_eq_id (ZMod 2) _ _ (fun u hu x hx => ?_) k
      obtain ⟨s,-,rfl⟩ := (mem_sublevel p t u).1 hu
      obtain ⟨i,-,rfl⟩ := Finset.mem_map.1 hx
      exact congrArg Fin.val (clamp_val hn i)

/-- Relabeling commutes with α inclusions at all ordered pairs of real thresholds. -/
theorem labelMap_naturality (p : Fin n ↪ Point) {s t : ℝ} (hst : s ≤ t) (k : ℕ) :
    simplicialHomologyIncl (ZMod 2) ((Alpha.filter
        (RationalAlpha.realSites p)).sublevel_mono hst) k ≫
      simplicialHomologyMap (ZMod 2) (labelMap p t) k =
    simplicialHomologyMap (ZMod 2) (labelMap p s) k ≫
      simplicialHomologyIncl (ZMod 2) ((inputFilter p).sublevel_mono
        ((stage p).monotone hst)) k := by
  rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_inclusion,
    ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
  rfl

inductive Death where
  | finite (grade : ℚ)
  | essential
  deriving DecidableEq, Repr

structure Occurrence where
  degree : ℕ
  birth : ℚ
  death : Death
  deriving DecidableEq, Repr

/-- Read exact rational endpoints on the real squared-radius parameter line. -/
def Occurrence.point (o : Occurrence) : ℝ × WithTop ℝ :=
  (o.birth, match o.death with
    | .finite d => ((d : ℝ) : WithTop ℝ)
    | .essential => ⊤)

private def decode (G : Finset ℚ) (o : FiniteInput.Occurrence) : Occurrence where
  degree := o.degree
  birth := decodeGrade G o.birth
  death := match o.death with
    | .finite d => .finite (decodeGrade G d)
    | .essential => .essential

private def decoded (p : Fin n ↪ Point) : List Occurrence :=
  (FiniteInput.occurrences (simplexInput p)).map (decode (grades p))

/-- Compute the F₂ barcode of a finite family of exact rational planar sites.
Repeated coordinates are rejected. -/
def run (sites : Fin n → Point) : Option (List Occurrence) :=
  if h : Function.Injective sites then
    (FiniteInput.run (simplexInput ⟨sites,h⟩)).map (List.map (decode (grades ⟨sites,h⟩)))
  else none

private theorem run_eq_some_iff (sites : Fin n → Point) (out : List Occurrence) :
    run sites = some out ↔ ∃ h : Function.Injective sites, out = decoded ⟨sites,h⟩ := by
  by_cases h : Function.Injective sites
  · have he := (FiniteInput.run_eq_some_iff _ _).2 ⟨simplexInput_valid ⟨sites,h⟩, rfl⟩
    simp [run, h, he, decoded, eq_comm]
  · simp [run, h]

/-- Rejection occurs exactly for repeated sites. The empty family is accepted. -/
theorem run_eq_none_iff (sites : Fin n → Point) :
    run sites = none ↔ ¬ Function.Injective sites := by
  by_cases h : Function.Injective sites
  · have he := (run_eq_some_iff sites _).2 ⟨h,rfl⟩
    simp [he,h]
  · simp [run,h]

private theorem index_grade (p : Fin n ↪ Point) (i : Fin (simplexInput p).length) :
    ∃ q ∈ grades p, ((simplexInput p).get i).2 = rank (grades p) q := by
  obtain ⟨s,q,h,he⟩ := mem_simplexInput.1 (List.get_mem _ i)
  exact ⟨q, count_mem_grades h, congrArg Prod.snd he⟩

private theorem occurrence_ranks (p : Fin n ↪ Point) (o : FiniteInput.Occurrence)
    (ho : o ∈ FiniteInput.occurrences (simplexInput p)) :
    (∃ q ∈ grades p, o.birth = rank (grades p) q) ∧
    (∀ d, o.death = .finite d → ∃ q ∈ grades p, d = rank (grades p) q) := by
  rcases List.mem_append.1 ho with hf | he
  · obtain ⟨⟨i,j⟩,-,h⟩ := List.mem_filterMap.1 hf
    dsimp [FiniteInput.pairOccurrence] at h
    split at h
    · cases h
    · cases h
      exact ⟨index_grade p i, fun _ h => by cases h; exact index_grade p j⟩
  · obtain ⟨i,-,rfl⟩ := List.mem_map.1 he
    exact ⟨index_grade p i, fun _ h => by cases h⟩

private theorem decode_positive (p : Fin n ↪ Point) (o : FiniteInput.Occurrence)
    (ho : o ∈ FiniteInput.occurrences (simplexInput p)) :
    ((decode (grades p) o).point.1 : WithTop ℝ) < (decode (grades p) o).point.2 := by
  obtain ⟨⟨b,hb,hob⟩, hd⟩ := occurrence_ranks p o ho
  cases h : o.death with
  | essential => simp [decode, Occurrence.point, h]
  | finite d =>
    obtain ⟨q,hq,hdq⟩ := hd d h
    have hlt := FiniteInput.finite_birth_lt_death _ (simplexInput_valid p) o ho d h
    rw [hob,hdq] at hlt
    have hbq : b < q := lt_of_not_ge fun h => (not_lt_of_ge (rank_le_rank _ h)) hlt
    simpa [decode, Occurrence.point, h, hob, hdq, decode_rank _ hb, decode_rank _ hq] using hbq

private theorem decode_count (p : Fin n ↪ Point) (o : FiniteInput.Occurrence)
    (ho : o ∈ FiniteInput.occurrences (simplexInput p)) (s t : ℝ) :
    ((decode (grades p) o).point.1 ≤ s ∧ (t : WithTop ℝ) < (decode (grades p) o).point.2) ↔
      (o.point.1 ≤ stage p s ∧ (stage p t : WithTop ℤ) < o.point.2) := by
  obtain ⟨⟨b,hb,hob⟩, hd⟩ := occurrence_ranks p o ho
  cases h : o.death with
  | essential =>
    simp [decode, Occurrence.point, FiniteInput.Occurrence.point, h,
      hob, decode_rank _ hb, rank_le_stage hb s]
  | finite d =>
    obtain ⟨q,hq,hdq⟩ := hd d h
    have hdeath : stage p t < rank (grades p) q ↔ t < (q : ℝ) := by
      simpa only [not_le] using not_congr (rank_le_stage hq t)
    simp [decode, Occurrence.point, FiniteInput.Occurrence.point, h,
      hob, hdq, decode_rank _ hb, decode_rank _ hq, rank_le_stage hb s, hdeath]

/-- The degreewise real barcode of a successful run, including multiplicities. -/
def points (out : List Occurrence) (k : ℕ) : Multiset (ℝ × WithTop ℝ) :=
  ((out.filter fun o => o.degree = k : List Occurrence) : Multiset Occurrence).map Occurrence.point

private theorem points_eq_dgm (p : Fin n ↪ Point) (k : ℕ) :
    letI := Fintype.ofFinite (TotalFace (Alpha.carrier (RationalAlpha.realSites p)))
    points (decoded p) k = (dgm (ZMod 2) (Alpha.filter (RationalAlpha.realSites p)) k).points := by
  classical
  letI := Fintype.ofFinite (TotalFace (Alpha.carrier (RationalAlpha.realSites p)))
  letI := FiniteInput.faceFintype (simplexInput p) (simplexInput_valid p)
  have hpoints : points (decoded p) k =
      (((FiniteInput.occurrences (simplexInput p)).filter (fun o => o.degree = k) :
        List FiniteInput.Occurrence) : Multiset FiniteInput.Occurrence).map
        (Occurrence.point ∘ decode (grades p)) := by
    simp only [points, decoded, List.filter_map, Multiset.map_coe, List.map_map]
    rfl
  rw [hpoints]
  apply RealBarcode.multiset_eq_of_rankCounts_eq
  · intro x hx
    obtain ⟨o,ho,rfl⟩ := Multiset.mem_map.1 hx
    exact decode_positive p o (List.mem_filter.1 ho).1
  · exact dgm_isPositive (ZMod 2) _ k
  · intro s t hst
    rw [← rank_sublevelHomologyMap (ZMod 2) _ k s t hst]
    letI := labelMap_isIso p s k
    letI := labelMap_isIso p t k
    have hr := finrank_range_eq_of_iso_square _ _
      (asIso (simplicialHomologyMap (ZMod 2) (labelMap p s) k))
      (asIso (simplicialHomologyMap (ZMod 2) (labelMap p t) k))
      (labelMap_naturality p hst k)
    rw [hr, rank_sublevelHomologyMap (ZMod 2) (inputFilter p) k
      (stage p s) (stage p t) ((stage p).monotone hst),
      ← FiniteInput.outputDiagram_eq_dgm _ (simplexInput_valid p) k]
    change _ = (Multiset.map FiniteInput.Occurrence.point
      (((FiniteInput.occurrences (simplexInput p)).filter (fun o => o.degree = k) :
        List FiniteInput.Occurrence) : Multiset FiniteInput.Occurrence)).countP _
    rw [Multiset.countP_map, Multiset.countP_map]
    congr 1
    apply Multiset.filter_congr
    intro o ho
    exact decode_count p o (List.mem_filter.1 ho).1 s t

/-- The executable barcode agrees in every degree with actual closed α persistence. -/
theorem run_correct {sites : Fin n → Point} {out : List Occurrence}
    (hr : run sites = some out) (h : Function.Injective sites) (k : ℕ) :
    letI := Fintype.ofFinite (TotalFace (Alpha.carrier (RationalAlpha.realSites ⟨sites,h⟩)))
    points out k =
      (dgm (ZMod 2) (Alpha.filter (RationalAlpha.realSites ⟨sites,h⟩)) k).points := by
  obtain ⟨h', rfl⟩ := (run_eq_some_iff sites out).1 hr
  exact points_eq_dgm ⟨sites,h⟩ k

end TDA.Persistence.Reduction.AlphaInput
