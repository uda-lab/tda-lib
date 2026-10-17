import TDA.Mapper.MultiNerveGraphPL
import TDA.Mapper.MultiNerveExamples
import TDA.Reeb.GraphPLComponentsExamples

/-!
# Uniform-cover fixtures

Acceptance fixtures for `TDA.Mapper.UniformCover` and `TDA.Mapper.MultiNerveGraphPL`, on the
merged graph-PL objects. Every cover is an instance of `uniformCover`; coverage of the attained
range comes from `uniformCover_covers_range` and the multiplicity bound from
`coverMultiplicityAtMost_uniformCover`.

* **4-cycle, two members.** `uniformCover (-5/4) 2 (1/2) 2` has the members `(-5/4, 3/4)` and
  `(1/4, 9/4)` and the overlap `(1/4, 3/4)`. Each member preimage of the 4-cycle with heights
  `0, 1, 2, 1` has one path component. The overlap contains no vertex height, its active edges are
  `0 — 1` and `0 — 3`, so there are exactly two edge cells: the MultiNerve Mapper is a 2-cycle,
  while ordinary Mapper has one edge. The projection is surjective and not injective.
* **4-cycle, three members.** `uniformCover (-1/8) 1 (3/8) 3` has the members `(-1/8, 7/8)`,
  `(1/2, 3/2)` and `(9/8, 17/8)`. The component counts per label are `1, 2, 1`; each consecutive
  label pair carries two edge cells and the far pair none. The two edge cells over each pair have
  distinct supports, so the projection is a bijection from the cells with two-element support onto
  the four Mapper edges: both constructions are 4-cycles.
* **Single edge, same covers.** For one edge of heights `0` and `2`, every member preimage has one
  component, and every consecutive label pair carries one edge cell and one Mapper face.
* **One member.** `uniformCover (-1/2) 3 g 1` has the single member `(-1/2, 5/2)` for every `g`; the
  Mapper of the 4-cycle has one vertex, the number of graph components. On two disjoint edges,
  `uniformCover (-1) 4 g 1` gives two vertices. No cell has two-element support.
* **Negative control, `2g > r`.** For `uniformCover (-1/2) 1 (3/4) 3` the attained value `1/4` lies
  in all three members: the multiplicity bound fails and ordinary Mapper has a face of size three.
* **Boundary, `2g = r`.** For `uniformCover 0 2 1 3` the outer members are disjoint and every point
  lies in at most two members, although the part of the middle member outside the others is the
  single point `2`.
-/

namespace TDA.Mapper.UniformCoverExamples

open Finset Set SimpleGraph
open TDA.Topology TDA.Topology.MultiNerveCell
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval
open TDA.Reeb.Examples.GraphPL
open TDA.Reeb.Examples.GraphRealization (edgeGraph d₀)
open TDA.Mapper.GraphPL (uniformEdgeCellsEquiv isEmpty_uniformEdgeCells_of_far
  cellGraphComponentsEquivActiveEdges edgeActive_ioo_iff_of_endpoints finite_edgeCells
  nat_card_mapperEdges_le)
open scoped Classical

noncomputable section

/-! ## General helpers -/

section helpers

variable {X : Type*} [TopologicalSpace X] {I : Type*}

/-- The `k`-th member as a bounded interval with computed endpoints. -/
private theorem uniformCover_eq_ioo {a r g p q : ℝ} {n : ℕ} (k : Fin n)
    (hp : a + ((k : ℕ) : ℝ) * (r - g) = p) (hq : a + ((k : ℕ) : ℝ) * (r - g) + r = q) :
    uniformCover a r g n k = ioo p q := by
  subst hp hq
  rfl

private theorem fin3_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k, P k := by
  intro k
  fin_cases k <;> assumption

private theorem fin3_pairs (L : Finset (Fin 3)) (hL : L.card = 2) :
    L = {0, 1} ∨ L = {1, 2} ∨ L = {0, 2} := by
  revert L
  decide

/-- Two component indices with one label are equal when that label has one path component. -/
private theorem componentIndex_eq_of_fst_eq {f : C(X, ℝ)} {U : I → Set ℝ}
    {a b : ComponentIndex f U} (h : a.1 = b.1)
    (hsub : Subsingleton (ZerothHomotopy (PullbackSpace f U a.1))) : a = b := by
  rcases a with ⟨i, c⟩
  rcases b with ⟨j, d⟩
  change i = j at h
  subst h
  exact Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ hsub c d))

/-- A face with two distinct labels consists of one index over each label. -/
private theorem exists_pair_of_labels [DecidableEq I] {f : C(X, ℝ)} {U : I → Set ℝ}
    {s : Finset (ComponentIndex f U)} (hs : s ∈ mapper f U) {i j : I} (hij : i ≠ j)
    (hlab : s.image Sigma.fst = {i, j}) : ∃ a b, a.1 = i ∧ b.1 = j ∧ s = {a, b} := by
  have hi : i ∈ s.image Sigma.fst := hlab ▸ Finset.mem_insert_self i {j}
  have hj : j ∈ s.image Sigma.fst := hlab ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hj
  have hcard : s.card = 2 :=
    (Finset.card_image_of_injOn (componentLabel_injOn_face f U hs)).symm.trans
      ((congrArg Finset.card hlab).trans (Finset.card_pair hij))
  refine ⟨a, b, rfl, rfl, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton.1 hx]
      exact hb
  · rw [hcard, Finset.card_pair (α := ComponentIndex f U) fun h => hij (congrArg Sigma.fst h)]

/-- The labels of a pair of indices. -/
private theorem image_pair [DecidableEq I] {f : C(X, ℝ)} {U : I → Set ℝ}
    (a b : ComponentIndex f U) :
    ({a, b} : Finset (ComponentIndex f U)).image Sigma.fst = {a.1, b.1} := by
  ext i
  constructor
  · intro hi
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hi
    rcases (Finset.mem_insert (α := ComponentIndex f U)).1 hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · rw [(Finset.mem_singleton (α := ComponentIndex f U)).1 hc]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · intro hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact Finset.mem_image.2 ⟨a, Finset.mem_insert_self (α := ComponentIndex f U) _ _, rfl⟩
    · rw [Finset.mem_singleton.1 hi]
      exact Finset.mem_image.2 ⟨b, Finset.mem_insert_of_mem (α := ComponentIndex f U)
        (Finset.mem_singleton_self _), rfl⟩

/-- A pair of indices with a common point is a Mapper face. -/
private theorem pair_mem_mapper {f : C(X, ℝ)} {U : I → Set ℝ} {a b : ComponentIndex f U} (x : X)
    (ha : x ∈ componentCover f U a) (hb : x ∈ componentCover f U b) :
    ({a, b} : Finset (ComponentIndex f U)) ∈ mapper f U :=
  (mem_mapper_iff _ _ _).2 ⟨Finset.insert_nonempty _ _, x, fun c hc => by
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact ha
    · rw [Finset.mem_singleton.1 hc]
      exact hb⟩

/-- With finitely many edge cells, exactly one edge cell gives exactly one Mapper face over the
same labels. -/
private theorem faces_card_one [DecidableEq I] {f : C(X, ℝ)} {U : I → Set ℝ} {τ : Finset I}
    [Finite {c : multiNerveMapper f U // c.support.image Sigma.fst = τ}]
    (hcells : Nat.card {c : multiNerveMapper f U // c.support.image Sigma.fst = τ} = 1) :
    Nat.card {s // s ∈ mapper f U ∧ s.image Sigma.fst = τ} = 1 := by
  have hsurj := mapperFacesOverLabels_surjective f U τ
  have : Finite {s // s ∈ mapper f U ∧ s.image Sigma.fst = τ} := Finite.of_surjective _ hsurj
  obtain ⟨c⟩ := (Nat.card_pos_iff.1 (by omega : 0 < Nat.card
    {c : multiNerveMapper f U // c.support.image Sigma.fst = τ})).1
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have hpos : 0 < Nat.card {s // s ∈ mapper f U ∧ s.image Sigma.fst = τ} :=
    Nat.card_pos_iff.2 ⟨⟨⟨c.1.support, c.1.support_mem_nerve, c.2⟩⟩, inferInstance⟩
  omega

/-- No edge cell over a label set gives no Mapper face over it. -/
private theorem faces_isEmpty [DecidableEq I] {f : C(X, ℝ)} {U : I → Set ℝ} {τ : Finset I}
    (hcells : IsEmpty {c : multiNerveMapper f U // c.support.image Sigma.fst = τ}) :
    IsEmpty {s // s ∈ mapper f U ∧ s.image Sigma.fst = τ} :=
  ⟨fun s => by
    obtain ⟨c, -⟩ := mapperFacesOverLabels_surjective f U τ s
    exact hcells.false c⟩

/-- Path components of a subtype with an everywhere-true predicate are those of the space. -/
private def zerothHomotopyEquivOfForall {P : X → Prop} (hP : ∀ x, P x) :
    ZerothHomotopy {x // P x} ≃ ZerothHomotopy X where
  toFun := TDA.Topology.componentMap ⟨Subtype.val, continuous_subtype_val⟩
  invFun := TDA.Topology.componentMap ⟨fun x => ⟨x, hP x⟩, continuous_id.subtype_mk _⟩
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  right_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

end helpers

section graphHelpers

variable {V : Type*} {G : SimpleGraph V} {h : V → ℝ}

/-- One preimage path component, through endpoint coverage and a connected induced graph. -/
private theorem card_preimage_eq_one {K : OpenInterval} (hcov : EndpointCoverage G h K)
    (v₀ : V) (hv₀ : h v₀ ∈ K)
    (hconn : ∀ (v : V) (hv : h v ∈ K),
      (G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk ⟨v, hv⟩ =
        (G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk ⟨v₀, hv₀⟩) :
    Nat.card (ZerothHomotopy {p : Realization G // plHeight G h p ∈ K}) = 1 := by
  rw [Nat.card_congr (preimageInducedEquiv G h K hcov)]
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨ConnectedComponent.ind₂ fun x y =>
    (hconn x.1 x.2).trans (hconn y.1 y.2).symm⟩,
    ⟨(G.induce (h ⁻¹' (K : Set ℝ))).connectedComponentMk ⟨v₀, hv₀⟩⟩⟩

/-- Without a vertex height in `K`, the preimage path components are the active edges. -/
private theorem card_preimage_eq_card_active {K : OpenInterval} (hK : ∀ v, h v ∉ K) :
    Nat.card (ZerothHomotopy {p : Realization G // plHeight G h p ∈ K}) =
      Nat.card {e : G.edgeSet // EdgeActive G h K e} :=
  Nat.card_congr ((preimageComponentsEquiv G h K).trans (cellGraphComponentsEquivActiveEdges hK))

/-- The component indices of a finite graph-PL height over `n` intervals. -/
private theorem card_componentIndex [Finite V] {n : ℕ} (U : Fin n → OpenInterval) :
    Nat.card (ComponentIndex (plHeight G h) (fun k => (U k : Set ℝ))) =
      ∑ k, Nat.card (ZerothHomotopy {p : Realization G // plHeight G h p ∈ U k}) := by
  have : ∀ k, Finite (ZerothHomotopy {p : Realization G // plHeight G h p ∈ U k}) :=
    fun k => finite_zerothHomotopy G h (U k)
  exact Nat.card_sigma (β := fun k => ZerothHomotopy {p : Realization G // plHeight G h p ∈ U k})

/-- For a finite graph, the edge cells over a label set of a vertex-free overlap are counted by
the active edges. -/
private theorem card_edgeCells_eq {n : ℕ} {a r g : ℝ} (hgr : g ≤ r) {k l : Fin n}
    (hkl : (k : ℕ) + 1 = l) {p q : ℝ}
    (hp : a + ((l : ℕ) : ℝ) * (r - g) = p) (hq : p + g = q) (hK : ∀ v, h v ∉ ioo p q) :
    Nat.card {c : multiNerveMapper (plHeight G h) (fun i => (uniformCover a r g n i : Set ℝ)) //
        c.support.image Sigma.fst = {k, l}} =
      Nat.card {e : G.edgeSet // EdgeActive G h (ioo p q) e} := by
  rw [Nat.card_congr (uniformEdgeCellsEquiv G h hgr hkl), hp, hq]
  exact Nat.card_congr (cellGraphComponentsEquivActiveEdges hK)

end graphHelpers

/-! ## The 4-cycle -/

section Cycle

/-- The dart `1 → 2`. -/
def d12 : C4.Dart := ⟨(1, 2), by decide⟩

/-- The dart `2 → 1`. -/
def d21 : C4.Dart := ⟨(2, 1), by decide⟩

/-- The dart `0 → 3`. -/
def d03 : C4.Dart := ⟨(0, 3), by decide⟩

/-- The four edges of the 4-cycle. -/
theorem c4_edge_cases (e : C4.edgeSet) :
    e = dartEdge d01 ∨ e = dartEdge d12 ∨ e = dartEdge d23 ∨ e = dartEdge d03 := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ := exists_dartEdge_eq e
  have hab' : C4.Adj a b := hab
  fin_cases a <;> fin_cases b <;> first
    | exact absurd hab' (by decide)
    | exact Or.inl rfl
    | exact Or.inl (Subtype.ext Sym2.eq_swap)
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inl (Subtype.ext Sym2.eq_swap))
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inl (Subtype.ext Sym2.eq_swap)))
    | exact Or.inr (Or.inr (Or.inr rfl))
    | exact Or.inr (Or.inr (Or.inr (Subtype.ext Sym2.eq_swap)))

private theorem c4_dartEdge_ne {d d' : C4.Dart} (v : Fin 4) (hv : v = d.fst ∨ v = d.snd)
    (hv' : v ≠ d'.fst ∧ v ≠ d'.snd) : dartEdge d ≠ dartEdge d' := fun h => by
  have hmem : v ∈ (dartEdge d' : Sym2 (Fin 4)) := h ▸ mem_dartEdge.2 hv
  rcases mem_dartEdge.1 hmem with h' | h'
  · exact hv'.1 h'
  · exact hv'.2 h'

private theorem h4_cases (v : Fin 4) : h4 v = 0 ∨ h4 v = 1 ∨ h4 v = 2 := by
  fin_cases v <;> norm_num [h4]

theorem h4_mem_Icc (v : Fin 4) : h4 v ∈ Set.Icc (0 : ℝ) 2 := by
  rcases h4_cases v with h | h | h <;> rw [h] <;> norm_num

private theorem h4_not_mem_low {p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ 1) (v : Fin 4) :
    h4 v ∉ ioo p q := fun hv => by
  rw [mem_ioo] at hv
  rcases h4_cases v with h | h | h <;> rw [h] at hv <;> linarith [hv.1, hv.2]

private theorem h4_not_mem_high {p q : ℝ} (hp : 1 ≤ p) (hq : q ≤ 2) (v : Fin 4) :
    h4 v ∉ ioo p q := fun hv => by
  rw [mem_ioo] at hv
  rcases h4_cases v with h | h | h <;> rw [h] at hv <;> linarith [hv.1, hv.2]

/-- Over a vertex-free interval inside `[0, 1]`, the active edges are `0 — 1` and `0 — 3`. -/
theorem c4_active_low {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) (e : C4.edgeSet) :
    EdgeActive C4 h4 (ioo p q) e ↔ e = dartEdge d01 ∨ e = dartEdge d03 := by
  have key := fun d : C4.Dart => edgeActive_ioo_iff_of_endpoints hpq d
    (h4_not_mem_low hp hq d.fst) (h4_not_mem_low hp hq d.snd)
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · refine iff_of_true ((key d01).2 ?_) (Or.inl rfl)
    change min (h4 0) (h4 1) ≤ p ∧ q ≤ max (h4 0) (h4 1)
    rw [h4_zero, h4_one, min_eq_left zero_le_one, max_eq_right zero_le_one]
    exact ⟨hp, hq⟩
  · refine iff_of_false (fun hact => ?_) ?_
    · have h1 := (key d12).1 hact
      change min (h4 1) (h4 2) ≤ p ∧ q ≤ max (h4 1) (h4 2) at h1
      rw [h4_one, h4_two, min_eq_left one_le_two] at h1
      linarith [h1.1]
    · rintro (h | h)
      · exact c4_dartEdge_ne (d := d12) (d' := d01) 2 (by decide) (by decide) h
      · exact c4_dartEdge_ne (d := d12) (d' := d03) 1 (by decide) (by decide) h
  · refine iff_of_false (fun hact => ?_) ?_
    · have h1 := (key d23).1 hact
      change min (h4 2) (h4 3) ≤ p ∧ q ≤ max (h4 2) (h4 3) at h1
      rw [h4_two, h4_three, min_eq_right one_le_two] at h1
      linarith [h1.1]
    · rintro (h | h)
      · exact c4_dartEdge_ne (d := d23) (d' := d01) 2 (by decide) (by decide) h
      · exact c4_dartEdge_ne (d := d23) (d' := d03) 2 (by decide) (by decide) h
  · refine iff_of_true ((key d03).2 ?_) (Or.inr rfl)
    change min (h4 0) (h4 3) ≤ p ∧ q ≤ max (h4 0) (h4 3)
    rw [h4_zero, h4_three, min_eq_left zero_le_one, max_eq_right zero_le_one]
    exact ⟨hp, hq⟩

/-- Over a vertex-free interval inside `[1, 2]`, the active edges are `1 — 2` and `2 — 3`. -/
theorem c4_active_high {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q) (hq : q ≤ 2) (e : C4.edgeSet) :
    EdgeActive C4 h4 (ioo p q) e ↔ e = dartEdge d12 ∨ e = dartEdge d23 := by
  have key := fun d : C4.Dart => edgeActive_ioo_iff_of_endpoints hpq d
    (h4_not_mem_high hp hq d.fst) (h4_not_mem_high hp hq d.snd)
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · refine iff_of_false (fun hact => ?_) ?_
    · have h1 := (key d01).1 hact
      change min (h4 0) (h4 1) ≤ p ∧ q ≤ max (h4 0) (h4 1) at h1
      rw [h4_zero, h4_one, max_eq_right zero_le_one] at h1
      linarith [h1.2]
    · rintro (h | h)
      · exact c4_dartEdge_ne (d := d01) (d' := d12) 0 (by decide) (by decide) h
      · exact c4_dartEdge_ne (d := d01) (d' := d23) 0 (by decide) (by decide) h
  · refine iff_of_true ((key d12).2 ?_) (Or.inl rfl)
    change min (h4 1) (h4 2) ≤ p ∧ q ≤ max (h4 1) (h4 2)
    rw [h4_one, h4_two, min_eq_left one_le_two, max_eq_right one_le_two]
    exact ⟨hp, hq⟩
  · refine iff_of_true ((key d23).2 ?_) (Or.inr rfl)
    change min (h4 2) (h4 3) ≤ p ∧ q ≤ max (h4 2) (h4 3)
    rw [h4_two, h4_three, min_eq_right one_le_two, max_eq_left one_le_two]
    exact ⟨hp, hq⟩
  · refine iff_of_false (fun hact => ?_) ?_
    · have h1 := (key d03).1 hact
      change min (h4 0) (h4 3) ≤ p ∧ q ≤ max (h4 0) (h4 3) at h1
      rw [h4_zero, h4_three, max_eq_right zero_le_one] at h1
      linarith [h1.2]
    · rintro (h | h)
      · exact c4_dartEdge_ne (d := d03) (d' := d12) 0 (by decide) (by decide) h
      · exact c4_dartEdge_ne (d := d03) (d' := d23) 0 (by decide) (by decide) h

private theorem card_active_two {K : OpenInterval} {e₁ e₂ : C4.edgeSet} (hne : e₁ ≠ e₂)
    (h : ∀ e, EdgeActive C4 h4 K e ↔ e = e₁ ∨ e = e₂) :
    Nat.card {e : C4.edgeSet // EdgeActive C4 h4 K e} = 2 :=
  Nat.card_eq_two_iff.2 ⟨⟨e₁, (h e₁).2 (Or.inl rfl)⟩, ⟨e₂, (h e₂).2 (Or.inr rfl)⟩,
    fun h' => hne (congrArg Subtype.val h'), Set.eq_univ_of_forall fun e => by
      rcases (h e.1).1 e.2 with he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Subtype.ext he)⟩

private theorem c4_card_active_low {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    Nat.card {e : C4.edgeSet // EdgeActive C4 h4 (ioo p q) e} = 2 :=
  card_active_two (c4_dartEdge_ne (d := d01) (d' := d03) 1 (by decide) (by decide))
    (c4_active_low hp hpq hq)

private theorem c4_card_active_high {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q) (hq : q ≤ 2) :
    Nat.card {e : C4.edgeSet // EdgeActive C4 h4 (ioo p q) e} = 2 :=
  card_active_two (c4_dartEdge_ne (d := d12) (d' := d23) 1 (by decide) (by decide))
    (c4_active_high hp hpq hq)

/-- A member around height `0` only: one path component. -/
private theorem c4_card_low {p q : ℝ} (hp : p < 0) (hq0 : 0 < q) (hq : q ≤ 1) :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ ioo p q}) = 1 := by
  have h0 : h4 0 ∈ ioo p q := by
    rw [h4_zero]
    exact ⟨hp, hq0⟩
  have honly : ∀ v, h4 v ∈ ioo p q → v = 0 := by
    intro v hv
    rw [mem_ioo] at hv
    rcases h4_cases v with h | h | h
    · fin_cases v
      · rfl
      all_goals norm_num [h4] at h
    all_goals (rw [h] at hv; linarith [hv.2])
  refine card_preimage_eq_one ?_ 0 h0 fun v hv => by
    obtain rfl := honly v hv
    rfl
  intro e he
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · exact ⟨0, fst_mem_dartEdge d01, h0⟩
  · exfalso
    obtain ⟨t, -, -, ht⟩ := (edgeActive_dartEdge_iff d12).1 he
    change p < (1 - (t : ℝ)) * h4 1 + (t : ℝ) * h4 2 ∧ (1 - (t : ℝ)) * h4 1 + (t : ℝ) * h4 2 < q
      at ht
    rw [h4_one, h4_two] at ht
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    linarith [ht.2]
  · exfalso
    obtain ⟨t, -, -, ht⟩ := (edgeActive_dartEdge_iff d23).1 he
    change p < (1 - (t : ℝ)) * h4 2 + (t : ℝ) * h4 3 ∧ (1 - (t : ℝ)) * h4 2 + (t : ℝ) * h4 3 < q
      at ht
    rw [h4_two, h4_three] at ht
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    linarith [ht.2]
  · exact ⟨0, fst_mem_dartEdge d03, h0⟩

/-- A member around height `2` only: one path component. -/
private theorem c4_card_high {p q : ℝ} (hp1 : 1 ≤ p) (hp : p < 2) (hq : 2 < q) :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ ioo p q}) = 1 := by
  have h2 : h4 2 ∈ ioo p q := by
    rw [h4_two]
    exact ⟨hp, hq⟩
  have honly : ∀ v, h4 v ∈ ioo p q → v = 2 := by
    intro v hv
    rw [mem_ioo] at hv
    rcases h4_cases v with h | h | h
    · rw [h] at hv; linarith [hv.1]
    · rw [h] at hv; linarith [hv.1]
    · fin_cases v
      all_goals first | rfl | (norm_num [h4] at h)
  refine card_preimage_eq_one ?_ 2 h2 fun v hv => by
    obtain rfl := honly v hv
    rfl
  intro e he
  rcases c4_edge_cases e with rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨t, -, -, ht⟩ := (edgeActive_dartEdge_iff d01).1 he
    change p < (1 - (t : ℝ)) * h4 0 + (t : ℝ) * h4 1 ∧ (1 - (t : ℝ)) * h4 0 + (t : ℝ) * h4 1 < q
      at ht
    rw [h4_zero, h4_one] at ht
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    linarith [ht.1]
  · exact ⟨2, snd_mem_dartEdge d12, h2⟩
  · exact ⟨2, fst_mem_dartEdge d23, h2⟩
  · exfalso
    obtain ⟨t, -, -, ht⟩ := (edgeActive_dartEdge_iff d03).1 he
    change p < (1 - (t : ℝ)) * h4 0 + (t : ℝ) * h4 3 ∧ (1 - (t : ℝ)) * h4 0 + (t : ℝ) * h4 3 < q
      at ht
    rw [h4_zero, h4_three] at ht
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    linarith [ht.1]

/-- A member containing the heights `1` and `2` but not `0`: one path component. -/
private theorem c4_card_upper {p q : ℝ} (hp0 : 0 ≤ p) (hp : p < 1) (hq : 2 < q) :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ ioo p q}) = 1 := by
  have h2 : h4 2 ∈ ioo p q := by
    rw [h4_two]
    exact ⟨by linarith, hq⟩
  have h13 : ∀ w : Fin 4, w = 1 ∨ w = 3 → h4 w ∈ ioo p q := by
    rintro w (rfl | rfl)
    · rw [h4_one]; exact ⟨hp, by linarith⟩
    · rw [h4_three]; exact ⟨hp, by linarith⟩
  refine card_preimage_eq_one ?_ 2 h2 fun v hv => ?_
  · intro e _
    obtain ⟨d, rfl⟩ := exists_dartEdge_eq e
    obtain ⟨w, hw, hw13⟩ := C4_edge_endpoint d
    exact ⟨w, hw, h13 w hw13⟩
  · fin_cases v
    · exfalso
      norm_num [h4, mem_ioo] at hv
      linarith [hv.1]
    · exact ConnectedComponent.connectedComponentMk_eq_of_adj (show C4.Adj 1 2 by decide)
    · rfl
    · exact ConnectedComponent.connectedComponentMk_eq_of_adj (show C4.Adj 3 2 by decide)

/-! ### Two members -/

/-- The two-member uniform family on the 4-cycle. -/
local notation "U₂" => uniformCover (-5 / 4 : ℝ) 2 (1 / 2) 2

/-- The two-member family as real sets. -/
local notation "F₂" => fun k : Fin 2 => ((U₂ k : OpenInterval) : Set ℝ)

theorem twoMember_zero : U₂ 0 = ioo (-5 / 4) (3 / 4) :=
  uniformCover_eq_ioo 0 (by norm_num) (by norm_num)

theorem twoMember_one : U₂ 1 = ioo (1 / 4) (9 / 4) :=
  uniformCover_eq_ioo 1 (by norm_num) (by norm_num)

/-- The two-member family covers the attained range of the 4-cycle height (item 6). -/
theorem twoMember_covers_cycle : Covers F₂ (Set.range (plHeight C4 h4)) :=
  uniformCover_covers_range h4_mem_Icc (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The two-member family has multiplicity at most two (item 8). -/
theorem twoMember_multiplicity_cycle : CoverMultiplicityAtMost (plHeight C4 h4) F₂ 2 :=
  coverMultiplicityAtMost_uniformCover (by norm_num) _

/-- Each member preimage has exactly one path component. -/
theorem twoMember_cycle_preimage_card (k : Fin 2) :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₂ k}) = 1 := by
  fin_cases k
  · show Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₂ 0}) = 1
    rw [twoMember_zero]
    exact c4_card_low (by norm_num) (by norm_num) (by norm_num)
  · show Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₂ 1}) = 1
    rw [twoMember_one]
    exact c4_card_upper (by norm_num) (by norm_num) (by norm_num)

private theorem twoMember_sub (k : Fin 2) :
    Subsingleton (ZerothHomotopy (PullbackSpace (plHeight C4 h4) F₂ k)) :=
  (Nat.card_eq_one_iff_unique.1 (twoMember_cycle_preimage_card k)).1

/-- Ordinary Mapper has two vertices. -/
theorem twoMember_componentIndex_card : Nat.card (ComponentIndex (plHeight C4 h4) F₂) = 2 := by
  rw [card_componentIndex, Fin.sum_univ_two, twoMember_cycle_preimage_card,
    twoMember_cycle_preimage_card]

/-- The active edges over the overlap `(1/4, 3/4)` are `0 — 1` and `0 — 3`. -/
theorem twoMember_overlap_active (e : C4.edgeSet) :
    EdgeActive C4 h4 (ioo (1 / 4) (3 / 4)) e ↔ e = dartEdge d01 ∨ e = dartEdge d03 :=
  c4_active_low (by norm_num) (by norm_num) (by norm_num) e

/-- Exactly two MultiNerve Mapper edge cells lie over the labels `{0, 1}`. -/
theorem twoMember_edgeCells_card :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₂ // c.support.image Sigma.fst = {0, 1}} =
      2 :=
  Eq.trans (card_edgeCells_eq (k := 0) (l := 1) (by norm_num) (by rfl) (p := 1 / 4) (q := 3 / 4)
    (by norm_num) (by norm_num) (h4_not_mem_low (by norm_num) (by norm_num)))
    (c4_card_active_low (by norm_num) (by norm_num) (by norm_num))

private theorem twoMember_support_subset {s s' : Finset (ComponentIndex (plHeight C4 h4) F₂)}
    (h : s.image Sigma.fst = s'.image Sigma.fst) : s ⊆ s' := fun a ha => by
  have : a.1 ∈ s'.image Sigma.fst := h ▸ Finset.mem_image_of_mem Sigma.fst ha
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 this
  rw [componentIndex_eq_of_fst_eq hba.symm (twoMember_sub a.1)]
  exact hb

private theorem twoMember_labels_of_card {s : Finset (ComponentIndex (plHeight C4 h4) F₂)}
    (hs : s ∈ mapper (plHeight C4 h4) F₂) (hcard : s.card = 2) : s.image Sigma.fst = {0, 1} := by
  have h1 : (s.image Sigma.fst).card = 2 :=
    (Finset.card_image_of_injOn (componentLabel_injOn_face _ _ hs)).trans hcard
  have h2 : s.image Sigma.fst = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [h1, Fintype.card_fin])
  rw [h2]
  decide

/-- Ordinary Mapper has exactly one face of size two. -/
theorem twoMember_mapper_edge_card :
    Nat.card {s // s ∈ mapper (plHeight C4 h4) F₂ ∧ s.card = 2} = 1 := by
  obtain ⟨c⟩ := (Nat.card_pos_iff.1 (by rw [twoMember_edgeCells_card]; norm_num :
    0 < Nat.card {c : multiNerveMapper (plHeight C4 h4) F₂ //
      c.support.image Sigma.fst = {0, 1}})).1
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun s s' => Subtype.ext ?_⟩,
    ⟨⟨c.1.support, c.1.support_mem_nerve,
      card_support_of_labels_pair _ _ (by decide) c.2⟩⟩⟩
  have hs := twoMember_labels_of_card s.2.1 s.2.2
  have hs' := twoMember_labels_of_card s'.2.1 s'.2.2
  exact Finset.Subset.antisymm (twoMember_support_subset (hs.trans hs'.symm))
    (twoMember_support_subset (hs'.trans hs.symm))

/-- **Fixture 1.** On the 4-cycle with two uniform members, every member preimage has one path
component, ordinary Mapper has two vertices and one edge, and the MultiNerve Mapper has two vertex
cells and two edge cells over that edge, a 2-cycle. The projection is surjective and not
injective, and `IntersectionsPathSubsingleton` fails. -/
theorem twoMember_cycle :
    (∀ k, Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₂ k}) = 1) ∧
    Nat.card (ComponentIndex (plHeight C4 h4) F₂) = 2 ∧
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₂ // c.support.card = 1} = 2 ∧
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₂ // c.support.image Sigma.fst = {0, 1}} =
      2 ∧
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₂ // c.support.card = 2} = 2 ∧
    Nat.card {s // s ∈ mapper (plHeight C4 h4) F₂ ∧ s.card = 2} = 1 ∧
    Function.Surjective (multiNerveMapper_projection (plHeight C4 h4) F₂) ∧
    ¬ Function.Injective (multiNerveMapper_projection (plHeight C4 h4) F₂) ∧
    ¬ IntersectionsPathSubsingleton (componentCover (plHeight C4 h4) F₂) := by
  have hnotinj : ¬ Function.Injective (multiNerveMapper_projection (plHeight C4 h4) F₂) := by
    intro hinj
    obtain ⟨c, c', hne, -⟩ := Nat.card_eq_two_iff.1 twoMember_edgeCells_card
    apply hne
    apply Subtype.ext
    apply hinj
    apply Subtype.ext
    exact Finset.Subset.antisymm (twoMember_support_subset (c.2.trans c'.2.symm))
      (twoMember_support_subset (c'.2.trans c.2.symm))
  refine ⟨twoMember_cycle_preimage_card, twoMember_componentIndex_card,
    (Nat.card_congr (vertexCellEquiv _ _)).trans twoMember_componentIndex_card,
    twoMember_edgeCells_card, ?_, twoMember_mapper_edge_card,
    multiNerveMapper_projection_surjective _ _, hnotinj,
    fun h => hnotinj ((projection_injective_iff _).2 h)⟩
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun c =>
    ⟨fun hc => twoMember_labels_of_card c.support_mem_nerve hc,
      fun hc => card_support_of_labels_pair _ _ (by decide) hc⟩)).trans twoMember_edgeCells_card

/-! ### Three members -/

/-- The three-member uniform family on the 4-cycle. -/
local notation "U₃" => uniformCover (-1 / 8 : ℝ) 1 (3 / 8) 3

/-- The three-member family as real sets. -/
local notation "F₃" => fun k : Fin 3 => ((U₃ k : OpenInterval) : Set ℝ)

theorem threeMember_zero : U₃ 0 = ioo (-1 / 8) (7 / 8) :=
  uniformCover_eq_ioo 0 (by norm_num) (by norm_num)

theorem threeMember_one : U₃ 1 = I4 :=
  uniformCover_eq_ioo 1 (by norm_num) (by norm_num)

theorem threeMember_two : U₃ 2 = ioo (9 / 8) (17 / 8) :=
  uniformCover_eq_ioo 2 (by norm_num) (by norm_num)

/-- The three-member family covers the attained range of the 4-cycle height (item 6). -/
theorem threeMember_covers_cycle : Covers F₃ (Set.range (plHeight C4 h4)) :=
  uniformCover_covers_range h4_mem_Icc (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The three-member family has multiplicity at most two (item 8). -/
theorem threeMember_multiplicity_cycle : CoverMultiplicityAtMost (plHeight C4 h4) F₃ 2 :=
  coverMultiplicityAtMost_uniformCover (by norm_num) _

theorem threeMember_card_zero :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 0}) = 1 := by
  rw [threeMember_zero]
  exact c4_card_low (by norm_num) (by norm_num) (by norm_num)

theorem threeMember_card_one :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 1}) = 2 := by
  rw [threeMember_one]
  exact c4_card_preimage

theorem threeMember_card_two :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 2}) = 1 := by
  rw [threeMember_two]
  exact c4_card_high (by norm_num) (by norm_num) (by norm_num)

/-- Ordinary Mapper has four vertices. -/
theorem threeMember_componentIndex_card : Nat.card (ComponentIndex (plHeight C4 h4) F₃) = 4 := by
  rw [card_componentIndex, Fin.sum_univ_three, threeMember_card_zero, threeMember_card_one,
    threeMember_card_two]

theorem threeMember_edgeCells01_card :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 1}} =
      2 :=
  Eq.trans (card_edgeCells_eq (k := 0) (l := 1) (by norm_num) (by rfl) (p := 1 / 2) (q := 7 / 8)
    (by norm_num) (by norm_num) (h4_not_mem_low (by norm_num) (by norm_num)))
    (c4_card_active_low (by norm_num) (by norm_num) (by norm_num))

theorem threeMember_edgeCells12_card :
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1, 2}} =
      2 :=
  Eq.trans (card_edgeCells_eq (k := 1) (l := 2) (by norm_num) (by rfl) (p := 9 / 8) (q := 3 / 2)
    (by norm_num) (by norm_num) (h4_not_mem_high (by norm_num) (by norm_num)))
    (c4_card_active_high (by norm_num) (by norm_num) (by norm_num))

theorem threeMember_edgeCells02_isEmpty :
    IsEmpty {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 2}} :=
  isEmpty_uniformEdgeCells_of_far C4 h4 (k := 0) (l := 2) (by norm_num) (by decide)

/-! The four component indices and the transport of the middle label to `I4`. -/

/-- The component index of the class of a point at a label. -/
def threeIndex (k : Fin 3) (p : Realization C4) (hp : plHeight C4 h4 p ∈ U₃ k) :
    ComponentIndex (plHeight C4 h4) F₃ :=
  ⟨k, ZerothHomotopy.mk ⟨p, hp⟩⟩

private theorem v0_mem : plHeight C4 h4 (vertex C4 0) ∈ U₃ 0 := by
  rw [threeMember_zero, plHeight_vertex, h4_zero, mem_ioo]
  norm_num

private theorem v1_mem : plHeight C4 h4 (vertex C4 1) ∈ U₃ 1 := by
  rw [threeMember_one]
  exact one_mem_I4

private theorem v3_mem : plHeight C4 h4 (vertex C4 3) ∈ U₃ 1 := by
  rw [threeMember_one]
  exact three_mem_I4

private theorem v2_mem : plHeight C4 h4 (vertex C4 2) ∈ U₃ 2 := by
  rw [threeMember_two, plHeight_vertex, h4_two, mem_ioo]
  norm_num

/-- The vertex at label `0`. -/
def threeLow : ComponentIndex (plHeight C4 h4) F₃ := threeIndex 0 (vertex C4 0) v0_mem

/-- The vertex at label `1` represented by the vertex `1` (the class `x1`). -/
def threeMidOne : ComponentIndex (plHeight C4 h4) F₃ := threeIndex 1 (vertex C4 1) v1_mem

/-- The vertex at label `1` represented by the vertex `3` (the class `x3`). -/
def threeMidThree : ComponentIndex (plHeight C4 h4) F₃ := threeIndex 1 (vertex C4 3) v3_mem

/-- The vertex at label `2`. -/
def threeHigh : ComponentIndex (plHeight C4 h4) F₃ := threeIndex 2 (vertex C4 2) v2_mem

private def midTransport : ZerothHomotopy (PullbackSpace (plHeight C4 h4) F₃ 1) ≃
    ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4} :=
  zerothHomotopySetCongr (A := plHeight C4 h4 ⁻¹' (U₃ 1 : Set ℝ))
    (B := plHeight C4 h4 ⁻¹' (I4 : Set ℝ)) (by rw [threeMember_one])

private theorem three_sub0 : Subsingleton (ZerothHomotopy (PullbackSpace (plHeight C4 h4) F₃ 0)) :=
  (Nat.card_eq_one_iff_unique.1 threeMember_card_zero).1

private theorem three_sub2 : Subsingleton (ZerothHomotopy (PullbackSpace (plHeight C4 h4) F₃ 2)) :=
  (Nat.card_eq_one_iff_unique.1 threeMember_card_two).1

private theorem eq_threeLow {a : ComponentIndex (plHeight C4 h4) F₃} (ha : a.1 = 0) :
    a = threeLow := by
  rcases a with ⟨k, c⟩
  change k = 0 at ha
  subst ha
  exact Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ three_sub0 _ _))

private theorem eq_threeHigh {a : ComponentIndex (plHeight C4 h4) F₃} (ha : a.1 = 2) :
    a = threeHigh := by
  rcases a with ⟨k, c⟩
  change k = 2 at ha
  subst ha
  exact Sigma.ext rfl (heq_of_eq (@Subsingleton.elim _ three_sub2 _ _))

private theorem eq_threeMid {a : ComponentIndex (plHeight C4 h4) F₃} (ha : a.1 = 1) :
    a = threeMidOne ∨ a = threeMidThree := by
  rcases a with ⟨k, c⟩
  change k = 1 at ha
  subst ha
  rcases c4_preimage_classification (midTransport c) with h | h
  · exact Or.inl (Sigma.ext rfl (heq_of_eq (midTransport.injective (h.trans rfl))))
  · exact Or.inr (Sigma.ext rfl (heq_of_eq (midTransport.injective (h.trans rfl))))

theorem threeMidOne_ne_threeMidThree : threeMidOne ≠ threeMidThree := fun h => by
  have hc := eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact c4_x1_ne_x3 (congrArg midTransport hc)

/-! The four edges of the three-member Mapper and their witnesses. -/

theorem d03_mem : dartHeight h4 d03 threeQuarter ∈ I4 := by
  show (1 / 2 : ℝ) < (1 - 3 / 4) * h4 0 + 3 / 4 * h4 3 ∧ (1 - 3 / 4) * h4 0 + 3 / 4 * h4 3 < 3 / 2
  norm_num [h4_zero, h4_three]

theorem d21_mem : dartHeight h4 d21 threeQuarter ∈ I4 := by
  show (1 / 2 : ℝ) < (1 - 3 / 4) * h4 2 + 3 / 4 * h4 1 ∧ (1 - 3 / 4) * h4 2 + 3 / 4 * h4 1 < 3 / 2
  norm_num [h4_two, h4_one]

/-- An interior point of the edge `0 — 3` lies in the class `x3`. -/
theorem c4_d03_class :
    (ZerothHomotopy.mk ⟨edgePoint C4 d03 threeQuarter, d03_mem⟩ :
      ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4}) = x3 :=
  (preimageComponentsEquiv C4 h4 I4).injective
    ((preimageComponentsEquiv_mk_edgePoint_of_snd_mem C4 h4 I4 d03_mem three_mem_I4).trans
      c4_equiv_x3.symm)

/-- An interior point of the edge `2 — 1` lies in the class `x1`. -/
theorem c4_d21_class :
    (ZerothHomotopy.mk ⟨edgePoint C4 d21 threeQuarter, d21_mem⟩ :
      ZerothHomotopy {p : Realization C4 // plHeight C4 h4 p ∈ I4}) = x1 :=
  (preimageComponentsEquiv C4 h4 I4).injective
    ((preimageComponentsEquiv_mk_edgePoint_of_snd_mem C4 h4 I4 d21_mem one_mem_I4).trans
      c4_equiv_x1.symm)

private theorem height_lowEdge {d : C4.Dart} (hd : h4 d.fst = 0) (hd' : h4 d.snd = 1) :
    plHeight C4 h4 (edgePoint C4 d threeQuarter) = 3 / 4 := by
  show (1 - (3 / 4 : ℝ)) * h4 d.fst + 3 / 4 * h4 d.snd = 3 / 4
  rw [hd, hd']
  norm_num

private theorem height_highEdge {d : C4.Dart} (hd : h4 d.fst = 2) (hd' : h4 d.snd = 1) :
    plHeight C4 h4 (edgePoint C4 d threeQuarter) = 5 / 4 := by
  show (1 - (3 / 4 : ℝ)) * h4 d.fst + 3 / 4 * h4 d.snd = 5 / 4
  rw [hd, hd']
  norm_num

private theorem mem_low_of_height {p : Realization C4} (hp : plHeight C4 h4 p = 3 / 4) :
    plHeight C4 h4 p ∈ U₃ 0 := by
  rw [threeMember_zero, hp, mem_ioo]
  norm_num

private theorem mem_mid_of_height {p : Realization C4} {y : ℝ} (hp : plHeight C4 h4 p = y)
    (hy : 1 / 2 < y ∧ y < 3 / 2) : plHeight C4 h4 p ∈ U₃ 1 := by
  rw [threeMember_one, hp]
  exact hy

private theorem mem_high_of_height {p : Realization C4} (hp : plHeight C4 h4 p = 5 / 4) :
    plHeight C4 h4 p ∈ U₃ 2 := by
  rw [threeMember_two, hp, mem_ioo]
  norm_num

private theorem mem_threeLow {p : Realization C4} (hp : plHeight C4 h4 p ∈ U₃ 0) :
    p ∈ componentCover (plHeight C4 h4) F₃ threeLow :=
  ⟨hp, @Subsingleton.elim _ three_sub0 _ _⟩

private theorem mem_threeHigh {p : Realization C4} (hp : plHeight C4 h4 p ∈ U₃ 2) :
    p ∈ componentCover (plHeight C4 h4) F₃ threeHigh :=
  ⟨hp, @Subsingleton.elim _ three_sub2 _ _⟩

private theorem mem_threeMid {p q : Realization C4} (hp : plHeight C4 h4 p ∈ U₃ 1)
    (hq : plHeight C4 h4 q ∈ U₃ 1)
    (h : midTransport (ZerothHomotopy.mk ⟨p, hp⟩) = midTransport (ZerothHomotopy.mk ⟨q, hq⟩)) :
    p ∈ componentCover (plHeight C4 h4) F₃ (threeIndex 1 q hq) :=
  ⟨hp, midTransport.injective h⟩

/-- The face `{low, x1}`, witnessed by the edge point of `0 → 1` at height `3/4`. -/
theorem threeFace_low_one : ({threeLow, threeMidOne} : Finset _) ∈ mapper (plHeight C4 h4) F₃ := by
  have hh := height_lowEdge (d := d01) h4_zero h4_one
  have hmid := mem_mid_of_height hh (by norm_num)
  exact pair_mem_mapper (edgePoint C4 d01 threeQuarter) (mem_threeLow (mem_low_of_height hh))
    (mem_threeMid hmid v1_mem c4_d01_class)

/-- The face `{low, x3}`, witnessed by the edge point of `0 → 3` at height `3/4`. -/
theorem threeFace_low_three :
    ({threeLow, threeMidThree} : Finset _) ∈ mapper (plHeight C4 h4) F₃ := by
  have hh := height_lowEdge (d := d03) h4_zero h4_three
  have hmid := mem_mid_of_height hh (by norm_num)
  exact pair_mem_mapper (edgePoint C4 d03 threeQuarter) (mem_threeLow (mem_low_of_height hh))
    (mem_threeMid hmid v3_mem c4_d03_class)

/-- The face `{x1, high}`, witnessed by the edge point of `2 → 1` at height `5/4`. -/
theorem threeFace_one_high :
    ({threeMidOne, threeHigh} : Finset _) ∈ mapper (plHeight C4 h4) F₃ := by
  have hh := height_highEdge (d := d21) h4_two h4_one
  have hmid := mem_mid_of_height hh (by norm_num)
  exact pair_mem_mapper (edgePoint C4 d21 threeQuarter)
    (mem_threeMid hmid v1_mem c4_d21_class) (mem_threeHigh (mem_high_of_height hh))

/-- The face `{x3, high}`, witnessed by the edge point of `2 → 3` at height `5/4`. -/
theorem threeFace_three_high :
    ({threeMidThree, threeHigh} : Finset _) ∈ mapper (plHeight C4 h4) F₃ := by
  have hh := height_highEdge (d := d23) h4_two h4_three
  have hmid := mem_mid_of_height hh (by norm_num)
  exact pair_mem_mapper (edgePoint C4 d23 threeQuarter)
    (mem_threeMid hmid v3_mem c4_d23_class) (mem_threeHigh (mem_high_of_height hh))

/-- Faces with labels `{0, 1}` are `{low, x1}` or `{low, x3}`. -/
theorem threeMember_faces01 {s : Finset (ComponentIndex (plHeight C4 h4) F₃)}
    (hs : s ∈ mapper (plHeight C4 h4) F₃) (hlab : s.image Sigma.fst = {0, 1}) :
    s = {threeLow, threeMidOne} ∨ s = {threeLow, threeMidThree} := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_pair_of_labels hs (by decide) hlab
  rw [eq_threeLow ha]
  rcases eq_threeMid hb with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Faces with labels `{1, 2}` are `{x1, high}` or `{x3, high}`. -/
theorem threeMember_faces12 {s : Finset (ComponentIndex (plHeight C4 h4) F₃)}
    (hs : s ∈ mapper (plHeight C4 h4) F₃) (hlab : s.image Sigma.fst = {1, 2}) :
    s = {threeMidOne, threeHigh} ∨ s = {threeMidThree, threeHigh} := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_pair_of_labels hs (by decide) hlab
  rw [eq_threeHigh hb]
  rcases eq_threeMid ha with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem threeLow_fst : threeLow.1 = 0 := rfl
private theorem threeMidOne_fst : threeMidOne.1 = 1 := rfl
private theorem threeMidThree_fst : threeMidThree.1 = 1 := rfl
private theorem threeHigh_fst : threeHigh.1 = 2 := rfl

private theorem threeMidOne_not_mem_low_three :
    threeMidOne ∉ ({threeLow, threeMidThree} : Finset (ComponentIndex (plHeight C4 h4) F₃)) := by
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · exact absurd (congrArg Sigma.fst h) (by decide)
  · exact threeMidOne_ne_threeMidThree (Finset.mem_singleton.1 h)

private theorem threeMidOne_not_mem_three_high :
    threeMidOne ∉ ({threeMidThree, threeHigh} : Finset (ComponentIndex (plHeight C4 h4) F₃)) := by
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · exact threeMidOne_ne_threeMidThree h
  · exact absurd (congrArg Sigma.fst (Finset.mem_singleton.1 h)) (by decide)

/-- With two cells and two faces over one label pair, the projection is a bijection there. -/
private theorem cells_faces_bijective {τ : Finset (Fin 3)}
    [Finite {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = τ}]
    (hcells : Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ //
      c.support.image Sigma.fst = τ} = 2)
    (s₁ s₂ : Finset (ComponentIndex (plHeight C4 h4) F₃)) (hne : s₁ ≠ s₂)
    (h₁ : s₁ ∈ mapper (plHeight C4 h4) F₃ ∧ s₁.image Sigma.fst = τ)
    (h₂ : s₂ ∈ mapper (plHeight C4 h4) F₃ ∧ s₂.image Sigma.fst = τ)
    (hcases : ∀ s, s ∈ mapper (plHeight C4 h4) F₃ → s.image Sigma.fst = τ → s = s₁ ∨ s = s₂) :
    Function.Bijective
      (fun c : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = τ} =>
        (⟨c.1.support, c.1.support_mem_nerve, c.2⟩ :
          {s // s ∈ mapper (plHeight C4 h4) F₃ ∧ s.image Sigma.fst = τ})) := by
  refine (mapperFacesOverLabels_surjective _ _ τ).bijective_of_nat_card_le ?_
  rw [hcells]
  refine le_of_eq (Nat.card_eq_two_iff.2 ⟨⟨s₁, h₁⟩, ⟨s₂, h₂⟩,
    fun h => hne (congrArg Subtype.val h), Set.eq_univ_of_forall fun s => ?_⟩).symm
  rcases hcases s.1 s.2.1 s.2.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private theorem cells01_bijective :
    Function.Bijective
      (fun c : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 1}} =>
        (⟨c.1.support, c.1.support_mem_nerve, c.2⟩ :
          {s // s ∈ mapper (plHeight C4 h4) F₃ ∧ s.image Sigma.fst = {0, 1}})) := by
  have := finite_edgeCells C4 h4 U₃ 0 1
  refine cells_faces_bijective threeMember_edgeCells01_card _ _ ?_
    ⟨threeFace_low_one, image_pair _ _⟩ ⟨threeFace_low_three, image_pair _ _⟩
    fun s hs hl => threeMember_faces01 hs hl
  intro h
  have hmem : threeMidOne ∈ ({threeLow, threeMidOne} : Finset _) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [h] at hmem
  exact threeMidOne_not_mem_low_three hmem

private theorem cells12_bijective :
    Function.Bijective
      (fun c : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1, 2}} =>
        (⟨c.1.support, c.1.support_mem_nerve, c.2⟩ :
          {s // s ∈ mapper (plHeight C4 h4) F₃ ∧ s.image Sigma.fst = {1, 2}})) := by
  have := finite_edgeCells C4 h4 U₃ 1 2
  refine cells_faces_bijective threeMember_edgeCells12_card _ _ ?_
    ⟨threeFace_one_high, image_pair _ _⟩ ⟨threeFace_three_high, image_pair _ _⟩
    fun s hs hl => threeMember_faces12 hs hl
  intro h
  have hmem : threeMidOne ∈ ({threeMidOne, threeHigh} : Finset _) := Finset.mem_insert_self _ _
  rw [h] at hmem
  exact threeMidOne_not_mem_three_high hmem

private theorem three_labels {c : multiNerveMapper (plHeight C4 h4) F₃}
    (hc : c.support.card = 2) :
    c.support.image Sigma.fst = {0, 1} ∨ c.support.image Sigma.fst = {1, 2} := by
  have hcard : (c.support.image Sigma.fst).card = 2 :=
    (Finset.card_image_of_injOn (componentLabel_injOn_face _ _ c.support_mem_nerve)).trans hc
  rcases fin3_pairs _ hcard with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (threeMember_edgeCells02_isEmpty.false ⟨c, h⟩).elim

/-- **Fixture 2.** On the 4-cycle with three uniform members, the component counts per label are
`1, 2, 1`. The consecutive label pairs carry two edge cells each and the far pair none; the two
cells over each pair have the distinct supports `{low, x1}`, `{low, x3}`, respectively `{x1, high}`,
`{x3, high}`. Ordinary Mapper has four vertices and exactly four faces of size two, and the
projection from the cells with two-element support onto them is a bijection: both are
4-cycles. -/
theorem threeMember_cycle :
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 0}) = 1 ∧
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 1}) = 2 ∧
    Nat.card (ZerothHomotopy {x : Realization C4 // plHeight C4 h4 x ∈ U₃ 2}) = 1 ∧
    Nat.card (ComponentIndex (plHeight C4 h4) F₃) = 4 ∧
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 1}} =
      2 ∧
    Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1, 2}} =
      2 ∧
    IsEmpty {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 2}} ∧
    (∀ c : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 1}},
      c.1.support = {threeLow, threeMidOne} ∨ c.1.support = {threeLow, threeMidThree}) ∧
    (∀ c : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1, 2}},
      c.1.support = {threeMidOne, threeHigh} ∨ c.1.support = {threeMidThree, threeHigh}) ∧
    threeMidOne ≠ threeMidThree ∧
    (∀ c c' : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 1}},
      c.1.support = c'.1.support → c = c') ∧
    (∀ c c' : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1, 2}},
      c.1.support = c'.1.support → c = c') ∧
    Nat.card {s // s ∈ mapper (plHeight C4 h4) F₃ ∧ s.card = 2} = 4 ∧
    Function.Bijective
      (fun c : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.card = 2} =>
        (⟨c.1.support, c.1.support_mem_nerve, c.2⟩ :
          {s // s ∈ mapper (plHeight C4 h4) F₃ ∧ s.card = 2})) := by
  have inj01 : ∀ c c' : {c : multiNerveMapper (plHeight C4 h4) F₃ //
      c.support.image Sigma.fst = {0, 1}}, c.1.support = c'.1.support → c = c' :=
    fun c c' h => cells01_bijective.1 (Subtype.ext h)
  have inj12 : ∀ c c' : {c : multiNerveMapper (plHeight C4 h4) F₃ //
      c.support.image Sigma.fst = {1, 2}}, c.1.support = c'.1.support → c = c' :=
    fun c c' h => cells12_bijective.1 (Subtype.ext h)
  have hbij : Function.Bijective
      (fun c : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.card = 2} =>
        (⟨c.1.support, c.1.support_mem_nerve, c.2⟩ :
          {s // s ∈ mapper (plHeight C4 h4) F₃ ∧ s.card = 2})) := by
    refine ⟨fun c c' h => ?_, fun s => ?_⟩
    · have hs : c.1.support = c'.1.support := by
        have h' := congrArg Subtype.val h
        exact h'
      apply Subtype.ext
      rcases three_labels c.2 with hc | hc
      · have h2 := congrArg Subtype.val (inj01 ⟨c.1, hc⟩ ⟨c'.1, hs ▸ hc⟩ hs)
        exact h2
      · have h2 := congrArg Subtype.val (inj12 ⟨c.1, hc⟩ ⟨c'.1, hs ▸ hc⟩ hs)
        exact h2
    · obtain ⟨c, hc⟩ := exists_cell_of_mem_nerve s.2.1
      exact ⟨⟨c, hc ▸ s.2.2⟩, Subtype.ext hc⟩
  have hcells2 : Nat.card {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.card = 2} = 4 := by
    have := finite_edgeCells C4 h4 U₃ 0 1
    have := finite_edgeCells C4 h4 U₃ 1 2
    let e : {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {0, 1}} ⊕
        {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.image Sigma.fst = {1, 2}} →
        {c : multiNerveMapper (plHeight C4 h4) F₃ // c.support.card = 2} :=
      Sum.elim (fun c => ⟨c.1, card_support_of_labels_pair _ _ (by decide) c.2⟩)
        (fun c => ⟨c.1, card_support_of_labels_pair _ _ (by decide) c.2⟩)
    have he : Function.Bijective e := by
      refine ⟨?_, fun c => ?_⟩
      · rintro (c | c) (c' | c') h <;> have h' := congrArg Subtype.val h
        · exact congrArg Sum.inl (Subtype.ext h')
        · have : ({0, 1} : Finset (Fin 3)) = {1, 2} := by
            rw [← c.2, ← c'.2]
            exact congrArg (fun d : multiNerveMapper (plHeight C4 h4) F₃ =>
              d.support.image Sigma.fst) h'
          exact absurd this (by decide)
        · have : ({1, 2} : Finset (Fin 3)) = {0, 1} := by
            rw [← c.2, ← c'.2]
            exact congrArg (fun d : multiNerveMapper (plHeight C4 h4) F₃ =>
              d.support.image Sigma.fst) h'
          exact absurd this (by decide)
        · exact congrArg Sum.inr (Subtype.ext h')
      · rcases three_labels c.2 with hc | hc
        · exact ⟨Sum.inl ⟨c.1, hc⟩, rfl⟩
        · exact ⟨Sum.inr ⟨c.1, hc⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective e he), Nat.card_sum, threeMember_edgeCells01_card,
      threeMember_edgeCells12_card]
  refine ⟨threeMember_card_zero, threeMember_card_one, threeMember_card_two,
    threeMember_componentIndex_card, threeMember_edgeCells01_card, threeMember_edgeCells12_card,
    threeMember_edgeCells02_isEmpty, fun c => threeMember_faces01 c.1.support_mem_nerve c.2,
    fun c => threeMember_faces12 c.1.support_mem_nerve c.2, threeMidOne_ne_threeMidThree,
    inj01, inj12, ?_, hbij⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hcells2]

end Cycle

/-! ## The boundary case `2g = r` -/

section Boundary

/-- The uniform family `(0, 2)`, `(1, 3)`, `(2, 4)`. -/
local notation "U₆" => uniformCover (0 : ℝ) 2 1 3

theorem boundary_zero : U₆ 0 = ioo 0 2 := uniformCover_eq_ioo 0 (by norm_num) (by norm_num)

theorem boundary_one : U₆ 1 = ioo 1 3 := uniformCover_eq_ioo 1 (by norm_num) (by norm_num)

theorem boundary_two : U₆ 2 = ioo 2 4 := uniformCover_eq_ioo 2 (by norm_num) (by norm_num)

/-- **Fixture 6.** At `2g = r` the outer members are disjoint and every real number lies in at
most two members, although the part of the middle member outside the others is the single point
`2`; the family is not generic in the sense of CO16-v3 §2.4. -/
theorem boundary_uniformCover :
    (U₆ 0 : Set ℝ) ∩ (U₆ 2 : Set ℝ) = ∅ ∧
    (∀ y (t : Finset (Fin 3)), (∀ k ∈ t, y ∈ U₆ k) → t.card ≤ 2) ∧
    (U₆ 1 : Set ℝ) \ ((U₆ 0 : Set ℝ) ∪ (U₆ 2 : Set ℝ)) = {2} := by
  refine ⟨(uniformInterval_disjoint (by norm_num) (by decide)).inter_eq,
    uniformCover_card_le_two (by norm_num), ?_⟩
  rw [boundary_zero, boundary_one, boundary_two]
  ext y
  simp only [coe_ioo, Set.mem_sdiff, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h₁, h₃⟩, hn⟩
    have h₂ : 2 ≤ y := by
      by_contra hy
      exact hn (Or.inl ⟨by linarith, by linarith⟩)
    by_contra hy
    exact hn (Or.inr ⟨lt_of_le_of_ne h₂ (Ne.symm hy), by linarith⟩)
  · rintro rfl
    norm_num

end Boundary

end

end TDA.Mapper.UniformCoverExamples
