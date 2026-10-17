import TDA.Mapper.GraphPL
import TDA.Mapper.MultiNerveRefinement
import TDA.Mapper.UniformCover

/-!
# MultiNerve Mapper cells over a label set and graph-PL edge cells

For `f : C(X, Y)`, a target family `U : I → Set Y` and a nonempty finite label set `τ`, the
MultiNerve Mapper cells whose support has label set `τ` are in bijection with the path
components of the preimage `f ⁻¹' ⋂ i ∈ τ, U i` (`cellsOverLabelsEquiv`). A cell goes to the
class of any point of its carrier. Injectivity is the merged
`interMemberPreimageMap_injective`, together with the observation that two points joined inside
the preimage of the label intersection determine the same component member over every label. For
two labels this counts the edge cells over `U i ∩ U j` (`edgeCellsEquiv`), and the ordinary
Mapper faces with label set `{i, j}` are the images of these cells under the projection
(`mapperFacesOverLabels_surjective`, `nat_card_mapperFacesOverLabels_le`).

For a graph-PL height `plHeight G h` and an interval family, the edge cells with labels `{i, j}`
are the connected components of the incidence graph `cellGraph G h (U i ⊓ U j)`
(`edgeCellsCellGraphEquiv`). If no vertex height lies in an open interval `K`, these components
are the active edges of `K` (`cellGraphComponentsEquivActiveEdges`), and for a bounded `K = (p, q)`
an edge whose endpoint heights avoid `(p, q)` is active exactly when its height interval contains
`[p, q]` (`edgeActive_ioo_iff_of_endpoints`). For the uniform family, consecutive labels carry the
components over the overlap of length `g`, and labels at distance at least two carry no edge cell
(`uniformEdgeCellsEquiv`, `isEmpty_uniformEdgeCells_of_far`).

These are elementary library results, not attributed to a source; the context is Carrière–Oudot
(CO16-v3, Corollary 3.5 and the paragraph after it). No geometric realization of the Mapper or of
the MultiNerve Mapper as a graph or multigraph is constructed. See `docs/math/mapper.md`.
-/

namespace TDA.Mapper

open Finset Set
open TDA.Topology TDA.Topology.MultiNerveCell

noncomputable section

universe u v w

variable {X : Type u} {Y : Type v} {I : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

/-! ## Path components of equal sets -/

/-- Path components of equal subsets of one space, through the two inclusions. -/
def zerothHomotopySetCongr {A B : Set X} (hAB : A = B) : ZerothHomotopy A ≃ ZerothHomotopy B where
  toFun := componentMap (preimageSetInclusion (ContinuousMap.id X) hAB.subset)
  invFun := componentMap (preimageSetInclusion (ContinuousMap.id X) hAB.symm.subset)
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  right_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl

@[simp] theorem zerothHomotopySetCongr_mk {A B : Set X} (hAB : A = B) (x : A) :
    zerothHomotopySetCongr hAB (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk ⟨x.1, hAB ▸ x.2⟩ := rfl

/-! ## Cells over a label set -/

section labels

variable (f : C(X, Y)) (U : I → Set Y)

/-- The intersection over a set of component indices with label set `τ` lies in the preimage of
the intersection of the target members over `τ`. -/
theorem interMember_subset_preimage_of_labels [DecidableEq I] {s : Finset (ComponentIndex f U)}
    {τ : Finset I} (hs : s.image Sigma.fst = τ) :
    interMember (componentCover f U) s ⊆ f ⁻¹' ⋂ i ∈ τ, U i := by
  intro x hx
  rw [Set.mem_preimage, Set.mem_iInter₂]
  intro i hi
  rw [← hs] at hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
  exact ((mem_interMember_iff _).1 hx a ha).1

/-- Two points of component members with one label, joined inside the preimage of that label's
target member, determine the same component index. -/
private theorem componentIndex_eq_of_joinedIn {a b : ComponentIndex f U} {x y : X}
    (hx : x ∈ componentCover f U a) (hy : y ∈ componentCover f U b) (hab : a.1 = b.1)
    (hxy : JoinedIn (f ⁻¹' U a.1) x y) : a = b := by
  rcases a with ⟨i, c⟩
  rcases b with ⟨j, d⟩
  change i = j at hab
  subst hab
  obtain ⟨hxi, hc⟩ := hx
  obtain ⟨hyi, hd⟩ := hy
  exact Sigma.ext rfl (heq_of_eq (hc.symm.trans
    ((mk_eq_of_joinedIn f (U i) hxy hxi hyi).trans hd)))

/-- Membership in the preimage of the intersection over the labels of `s`, for any decidable
equality on the labels. -/
private theorem mem_preimage_biInter_image {inst : DecidableEq I}
    {s : Finset (ComponentIndex f U)} {τ : Finset I} (hs : ∀ a ∈ s, a.1 ∈ τ) {z : X}
    (hz : z ∈ f ⁻¹' ⋂ i ∈ τ, U i) : z ∈ f ⁻¹' ⋂ i ∈ @Finset.image _ _ inst Sigma.fst s, U i :=
  show f z ∈ ⋂ i ∈ @Finset.image _ _ inst Sigma.fst s, U i from
    Set.mem_iInter₂.2 fun i hi => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      exact Set.mem_iInter₂.1 hz a.1 (hs a ha)

variable {f U} [DecidableEq I]

/-- The forward map of `cellsOverLabelsEquiv`: the image of the cell component under the inclusion
into the preimage of the label intersection. -/
private def cellLabelsMap (τ : Finset I)
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ}) :
    ZerothHomotopy (f ⁻¹' ⋂ i ∈ τ, U i) :=
  componentMap (preimageSetInclusion (ContinuousMap.id X)
    (interMember_subset_preimage_of_labels f U c.2)) c.1.component

private theorem cellLabelsMap_of_mem (τ : Finset I)
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ}) {x : X}
    (hx : x ∈ c.1.carrier) :
    cellLabelsMap τ c = ZerothHomotopy.mk
      ⟨x, interMember_subset_preimage_of_labels f U c.2 (c.1.carrier_subset hx)⟩ := by
  obtain ⟨hx', hcls⟩ := hx
  exact (congrArg (componentMap (preimageSetInclusion (ContinuousMap.id X)
    (interMember_subset_preimage_of_labels f U c.2))) hcls).symm

private theorem cellLabelsMap_injective (τ : Finset I) :
    Function.Injective (cellLabelsMap (f := f) (U := U) τ) := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
  obtain ⟨x, hx⟩ := c.carrier_nonempty
  obtain ⟨y, hy⟩ := d.carrier_nonempty
  rw [cellLabelsMap_of_mem τ ⟨c, hc⟩ hx, cellLabelsMap_of_mem τ ⟨d, hd⟩ hy] at hcd
  set P : Set X := f ⁻¹' ⋂ i ∈ τ, U i
  have hxP : x ∈ P := interMember_subset_preimage_of_labels f U hc (c.carrier_subset hx)
  have hyP : y ∈ P := interMember_subset_preimage_of_labels f U hd (d.carrier_subset hy)
  have hxy : JoinedIn P x y := (joinedIn_iff_joined hxP hyP).2 (Quotient.exact hcd)
  have hxc : ∀ a ∈ c.support, x ∈ componentCover f U a :=
    (mem_interMember_iff _).1 (c.carrier_subset hx)
  have hyd : ∀ b ∈ d.support, y ∈ componentCover f U b :=
    (mem_interMember_iff _).1 (d.carrier_subset hy)
  have hPU : ∀ i ∈ τ, P ⊆ f ⁻¹' U i := fun i hi z hz => Set.mem_iInter₂.1 hz i hi
  -- The member of one support over a label is the member of the other support over that label.
  have hsub : ∀ {c' d' : multiNerveMapper f U} {x' y' : X},
      c'.support.image Sigma.fst = τ → d'.support.image Sigma.fst = τ →
      (∀ a ∈ c'.support, x' ∈ componentCover f U a) →
      (∀ b ∈ d'.support, y' ∈ componentCover f U b) → JoinedIn P x' y' →
      c'.support ⊆ d'.support := by
    intro c' d' x' y' hc' hd' hx' hy' hxy' a ha
    have haτ : a.1 ∈ τ := hc' ▸ Finset.mem_image_of_mem _ ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 (hd'.symm ▸ haτ : a.1 ∈ d'.support.image Sigma.fst)
    have hab : a = b := componentIndex_eq_of_joinedIn f U (hx' a ha) (hy' b hb) hba.symm
      (hxy'.mono (hPU a.1 haτ))
    exact hab ▸ hb
  have hsupp : d.support = c.support :=
    Finset.Subset.antisymm (hsub hd hc hyd hxc hxy.symm) (hsub hc hd hxc hyd hxy)
  refine Subtype.ext (ext_of_support_eq hsupp ?_).symm
  apply interMemberPreimageMap_injective f U d.support
  obtain ⟨hx', hxcls⟩ := hx
  obtain ⟨hy', hycls⟩ := hy
  rw [← hxcls, ← hycls]
  have hdτ : ∀ a ∈ d.support, a.1 ∈ τ := fun a ha => hd ▸ Finset.mem_image_of_mem Sigma.fst ha
  change ZerothHomotopy.mk _ = ZerothHomotopy.mk _
  exact mk_eq_of_joinedIn f _ (hxy.mono fun z hz => mem_preimage_biInter_image f U hdτ hz) _ _

private theorem cellLabelsMap_surjective (τ : Finset I) (hτ : τ.Nonempty) :
    Function.Surjective (cellLabelsMap (f := f) (U := U) τ) := by
  let _ : DecidableEq (ComponentIndex f U) := Classical.decEq _
  let _ : DecidableEq ((i : I) × ZerothHomotopy (PullbackSpace f U i)) := Classical.decEq _
  intro z
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective z
  have hxU : ∀ i ∈ τ, f x.1 ∈ U i := fun i hi => Set.mem_iInter₂.1 x.2 i hi
  let s : Finset (ComponentIndex f U) :=
    τ.attach.image fun i => ⟨i.1, ZerothHomotopy.mk ⟨x.1, hxU i.1 i.2⟩⟩
  have hs : s.image Sigma.fst = τ := by
    ext i
    constructor
    · intro hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
      exact j.2
    · intro hi
      exact Finset.mem_image.2 ⟨⟨i, ZerothHomotopy.mk ⟨x.1, hxU i hi⟩⟩,
        Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩, rfl⟩
  have hsne : s.Nonempty := hτ.attach.image _
  have hxs : x.1 ∈ interMember (componentCover f U) s := by
    rw [mem_interMember_iff]
    intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact ⟨hxU i.1 i.2, rfl⟩
  exact ⟨⟨MultiNerveCell.mk s hsne (ZerothHomotopy.mk ⟨x.1, hxs⟩), hs⟩, rfl⟩

variable (f U)

/-- **Cells over a label set.** For a nonempty finite label set `τ`, the MultiNerve Mapper cells
whose support has label set `τ` are the path components of `f ⁻¹' ⋂ i ∈ τ, U i`. A cell goes to
the class of any point of its carrier (`cellsOverLabelsEquiv_apply_of_mem`). -/
def cellsOverLabelsEquiv (τ : Finset I) (hτ : τ.Nonempty) :
    {c : multiNerveMapper f U // c.support.image Sigma.fst = τ} ≃
      ZerothHomotopy (f ⁻¹' ⋂ i ∈ τ, U i) :=
  Equiv.ofBijective (cellLabelsMap τ) ⟨cellLabelsMap_injective τ, cellLabelsMap_surjective τ hτ⟩

/-- The forward map of `cellsOverLabelsEquiv` is the map on path components of the inclusion of
the intersection of the component members into the preimage of the label intersection. -/
theorem cellsOverLabelsEquiv_apply (τ : Finset I) (hτ : τ.Nonempty)
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ}) :
    cellsOverLabelsEquiv f U τ hτ c =
      componentMap (preimageSetInclusion (ContinuousMap.id X)
        (interMember_subset_preimage_of_labels f U c.2)) c.1.component := rfl

/-- A cell goes to the class of any point of its carrier. -/
theorem cellsOverLabelsEquiv_apply_of_mem (τ : Finset I) (hτ : τ.Nonempty)
    (c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ}) {x : X}
    (hx : x ∈ c.1.carrier) :
    cellsOverLabelsEquiv f U τ hτ c = ZerothHomotopy.mk
      ⟨x, interMember_subset_preimage_of_labels f U c.2 (c.1.carrier_subset hx)⟩ :=
  cellLabelsMap_of_mem τ c hx

/-- The intersection over a two-element label set is the binary intersection. -/
theorem preimage_biInter_pair (i j : I) :
    f ⁻¹' (⋂ x ∈ ({i, j} : Finset I), U x) = f ⁻¹' (U i ∩ U j) := by
  rw [Finset.set_biInter_insert, Finset.set_biInter_singleton]

/-- **Edge cells.** The MultiNerve Mapper cells with label set `{i, j}` are the path components of
`f ⁻¹' (U i ∩ U j)`. The hypothesis `i ≠ j` is not needed; for `i = j` the cells are the vertex
cells over `i`. -/
def edgeCellsEquiv (i j : I) :
    {c : multiNerveMapper f U // c.support.image Sigma.fst = {i, j}} ≃
      ZerothHomotopy (f ⁻¹' (U i ∩ U j)) :=
  (cellsOverLabelsEquiv f U {i, j} (Finset.insert_nonempty i {j})).trans
    (zerothHomotopySetCongr (preimage_biInter_pair f U i j))

/-- A cell with two distinct labels has support of size two. -/
theorem card_support_of_labels_pair {i j : I} (hij : i ≠ j) {c : multiNerveMapper f U}
    (hc : c.support.image Sigma.fst = {i, j}) : c.support.card = 2 := by
  have himage := Finset.card_image_of_injOn (componentLabel_injOn_face f U c.support_mem_nerve)
  calc c.support.card = (c.support.image Sigma.fst).card := himage.symm
    _ = ({i, j} : Finset I).card := by rw [hc]
    _ = 2 := Finset.card_pair hij

/-- **Mapper faces as images.** Every ordinary Mapper face with label set `τ` is the support of a
MultiNerve Mapper cell with label set `τ`. -/
theorem mapperFacesOverLabels_surjective (τ : Finset I) :
    Function.Surjective
      (fun c : {c : multiNerveMapper f U // c.support.image Sigma.fst = τ} =>
        (⟨c.1.support, c.1.support_mem_nerve, c.2⟩ :
          {s // s ∈ mapper f U ∧ s.image Sigma.fst = τ})) := by
  rintro ⟨s, hs, hsτ⟩
  obtain ⟨c, hc⟩ := exists_cell_of_mem_nerve hs
  subst hc
  exact ⟨⟨c, hsτ⟩, rfl⟩

/-- With finitely many path components of `f ⁻¹' (U i ∩ U j)`, the ordinary Mapper faces with
label set `{i, j}` are at most as many as these components. -/
theorem nat_card_mapperFacesOverLabels_le (i j : I)
    [Finite (ZerothHomotopy (f ⁻¹' (U i ∩ U j)))] :
    Nat.card {s // s ∈ mapper f U ∧ s.image Sigma.fst = {i, j}} ≤
      Nat.card (ZerothHomotopy (f ⁻¹' (U i ∩ U j))) := by
  have := Finite.of_equiv _ (edgeCellsEquiv f U i j).symm
  exact (Nat.card_le_card_of_surjective _ (mapperFacesOverLabels_surjective f U {i, j})).trans
    (Nat.card_congr (edgeCellsEquiv f U i j)).le

end labels

end

/-! ## Graph-PL edge cells -/

namespace GraphPL

open SimpleGraph
open TDA.Reeb TDA.Reeb.GraphPL TDA.Reeb.GraphRealization TDA.Reeb.OpenInterval

noncomputable section

variable {V : Type*} {I : Type*}

variable (G : SimpleGraph V) (h : V → ℝ)

/-- The preimage of a binary intersection of intervals is the preimage of their meet. -/
theorem plHeight_preimage_inter (K L : OpenInterval) :
    plHeight G h ⁻¹' ((K : Set ℝ) ∩ (L : Set ℝ)) = {p | plHeight G h p ∈ K ⊓ L} := rfl

/-- **Graph-PL edge cells.** The MultiNerve Mapper cells of a graph-PL height with label set
`{i, j}` are the connected components of the incidence graph over `U i ⊓ U j`. -/
def edgeCellsCellGraphEquiv [DecidableEq I] (U : I → OpenInterval) (i j : I) :
    {c : multiNerveMapper (plHeight G h) (fun i => (U i : Set ℝ)) //
        c.support.image Sigma.fst = {i, j}} ≃
      (cellGraph G h (U i ⊓ U j)).ConnectedComponent :=
  (edgeCellsEquiv (plHeight G h) (fun i => (U i : Set ℝ)) i j).trans
    ((zerothHomotopySetCongr (plHeight_preimage_inter G h (U i) (U j))).trans
      (preimageComponentsEquiv G h (U i ⊓ U j)))

/-- A finite graph has finitely many edge cells over every pair of labels. -/
theorem finite_edgeCells [DecidableEq I] [Finite V] (U : I → OpenInterval) (i j : I) :
    Finite {c : multiNerveMapper (plHeight G h) (fun i => (U i : Set ℝ)) //
      c.support.image Sigma.fst = {i, j}} :=
  Finite.of_equiv _ (edgeCellsCellGraphEquiv G h U i j).symm

/-- For a finite graph, the ordinary Mapper faces with label set `{i, j}` are at most as many as
the connected components of the incidence graph over `U i ⊓ U j`. -/
theorem nat_card_mapperEdges_le [DecidableEq I] [Finite V] (U : I → OpenInterval) (i j : I) :
    Nat.card {s // s ∈ mapper (plHeight G h) (fun i => (U i : Set ℝ)) ∧
        s.image Sigma.fst = {i, j}} ≤
      Nat.card (cellGraph G h (U i ⊓ U j)).ConnectedComponent := by
  have := finite_edgeCells G h U i j
  exact (Nat.card_le_card_of_surjective _
    (mapperFacesOverLabels_surjective (plHeight G h) (fun i => (U i : Set ℝ)) {i, j})).trans
      (Nat.card_congr (edgeCellsCellGraphEquiv G h U i j)).le

variable {G h}

/-- **No critical value.** If no vertex height lies in `K`, the connected components of the
incidence graph over `K` are its active edges: every node is an edge node, and no two edge nodes
are adjacent. -/
def cellGraphComponentsEquivActiveEdges {K : OpenInterval} (hK : ∀ v, h v ∉ K) :
    (cellGraph G h K).ConnectedComponent ≃ {e : G.edgeSet // EdgeActive G h K e} where
  toFun := ConnectedComponent.lift
    (Sum.elim (fun v => (hK v.1 v.2).elim) id) fun _ _ p _ => eq_of_walk (fun x y hxy => by
      rcases x with v | e
      · exact (hK v.1 v.2).elim
      · rcases y with w | e'
        · exact (hK w.1 w.2).elim
        · exact (not_cellGraph_adj_inr_inr hxy).elim) p
  invFun e := (cellGraph G h K).connectedComponentMk (Sum.inr e)
  left_inv c := by
    induction c using ConnectedComponent.ind with
    | h x =>
      rcases x with v | e
      · exact (hK v.1 v.2).elim
      · rfl
  right_inv _ := rfl

@[simp] theorem cellGraphComponentsEquivActiveEdges_symm_apply {K : OpenInterval}
    (hK : ∀ v, h v ∉ K) (e : {e : G.edgeSet // EdgeActive G h K e}) :
    (cellGraphComponentsEquivActiveEdges hK).symm e =
      (cellGraph G h K).connectedComponentMk (Sum.inr e) := rfl

/-- An edge whose height interval contains `[p, q]` with `p < q` is active over `(p, q)`, through
the parameter of height `(p + q) / 2`. -/
private theorem edgeActive_ioo_of_le {p q : ℝ} {d : G.Dart} (hp : h d.fst ≤ p) (hpq : p < q)
    (hq : q ≤ h d.snd) : EdgeActive G h (ioo p q) (dartEdge d) := by
  have hden : 0 < h d.snd - h d.fst := by linarith
  set s : ℝ := ((p + q) / 2 - h d.fst) / (h d.snd - h d.fst) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := (div_le_one hden).2 (by linarith)
  have hmul : s * (h d.snd - h d.fst) = (p + q) / 2 - h d.fst := div_mul_cancel₀ _ hden.ne'
  refine edgeActive_dartEdge_of_mem (t := ⟨s, hs0, hs1⟩) ?_
  rw [mem_ioo]
  change p < (1 - s) * h d.fst + s * h d.snd ∧ (1 - s) * h d.fst + s * h d.snd < q
  constructor <;> nlinarith

/-- **Active edges over a vertex-free bounded interval.** For `p < q` and a dart whose endpoint
heights avoid `(p, q)`, the edge is active over `(p, q)` exactly when its height interval contains
`[p, q]`. -/
theorem edgeActive_ioo_iff_of_endpoints {p q : ℝ} (hpq : p < q) (d : G.Dart)
    (h₁ : h d.fst ∉ Set.Ioo p q) (h₂ : h d.snd ∉ Set.Ioo p q) :
    EdgeActive G h (ioo p q) (dartEdge d) ↔
      min (h d.fst) (h d.snd) ≤ p ∧ q ≤ max (h d.fst) (h d.snd) := by
  constructor
  · intro hact
    obtain ⟨t, ht0, ht1, hy⟩ := (edgeActive_dartEdge_iff d).1 hact
    rw [mem_ioo] at hy
    change p < (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ∧
      (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd < q at hy
    have hmin : min (h d.fst) (h d.snd) ≤ (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht1.le) (sub_nonneg.2 (min_le_left (h d.fst) (h d.snd))),
        mul_nonneg ht0.le (sub_nonneg.2 (min_le_right (h d.fst) (h d.snd)))]
    have hmax : (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd ≤ max (h d.fst) (h d.snd) := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht1.le) (sub_nonneg.2 (le_max_left (h d.fst) (h d.snd))),
        mul_nonneg ht0.le (sub_nonneg.2 (le_max_right (h d.fst) (h d.snd)))]
    constructor
    · by_contra hlt
      have hlt' := not_le.1 hlt
      have hmq : min (h d.fst) (h d.snd) < q := lt_of_le_of_lt hmin hy.2
      rcases min_choice (h d.fst) (h d.snd) with hm | hm
      · rw [hm] at hlt' hmq
        exact h₁ ⟨hlt', hmq⟩
      · rw [hm] at hlt' hmq
        exact h₂ ⟨hlt', hmq⟩
    · by_contra hlt
      have hlt' := not_le.1 hlt
      have hpm : p < max (h d.fst) (h d.snd) := lt_of_lt_of_le hy.1 hmax
      rcases max_choice (h d.fst) (h d.snd) with hm | hm
      · rw [hm] at hlt' hpm
        exact h₁ ⟨hpm, hlt'⟩
      · rw [hm] at hlt' hpm
        exact h₂ ⟨hpm, hlt'⟩
  · rintro ⟨hmin, hmax⟩
    rcases le_total (h d.fst) (h d.snd) with hle | hle
    · rw [min_eq_left hle] at hmin
      rw [max_eq_right hle] at hmax
      exact edgeActive_ioo_of_le hmin hpq hmax
    · rw [min_eq_right hle] at hmin
      rw [max_eq_left hle] at hmax
      rw [← dartEdge_symm d]
      exact edgeActive_ioo_of_le (d := d.symm) hmin hpq hmax

/-! ## Uniform overlaps -/

/-- Consecutive members of the uniform family meet in the interval of length `g` at the later
index. -/
theorem uniformCover_inf_of_succ {a r g : ℝ} {n : ℕ} (hgr : g ≤ r) {k l : Fin n}
    (hkl : (k : ℕ) + 1 = l) :
    uniformCover a r g n k ⊓ uniformCover a r g n l =
      ioo (a + (l : ℕ) * (r - g)) (a + (l : ℕ) * (r - g) + g) := by
  rw [uniformCover_apply, uniformCover_apply, ← hkl, uniformInterval_inf_succ hgr]
  push_cast
  rfl

variable (G h)

/-- **Uniform overlaps.** For `g ≤ r` and consecutive labels `k`, `l = k + 1`, the edge cells of
the uniform family with labels `{k, l}` are the connected components of the incidence graph over
the overlap `(a + l(r - g), a + l(r - g) + g)`. -/
def uniformEdgeCellsEquiv {a r g : ℝ} {n : ℕ} (hgr : g ≤ r) {k l : Fin n}
    (hkl : (k : ℕ) + 1 = l) :
    {c : multiNerveMapper (plHeight G h) (fun i => (uniformCover a r g n i : Set ℝ)) //
        c.support.image Sigma.fst = {k, l}} ≃
      (cellGraph G h (ioo (a + (l : ℕ) * (r - g)) (a + (l : ℕ) * (r - g) + g))).ConnectedComponent :=
  (edgeCellsCellGraphEquiv G h (uniformCover a r g n) k l).trans
    (Equiv.cast (congrArg (fun K => (cellGraph G h K).ConnectedComponent)
      (uniformCover_inf_of_succ hgr hkl)))

/-- For `2g ≤ r`, labels of the uniform family at distance at least two carry no edge cell. -/
theorem isEmpty_uniformEdgeCells_of_far {a r g : ℝ} {n : ℕ} (hg : 2 * g ≤ r) {k l : Fin n}
    (hkl : (k : ℕ) + 2 ≤ l) :
    IsEmpty {c : multiNerveMapper (plHeight G h) (fun i => (uniformCover a r g n i : Set ℝ)) //
      c.support.image Sigma.fst = {k, l}} := by
  have hempty : (uniformCover a r g n k : Set ℝ) ∩ (uniformCover a r g n l : Set ℝ) = ∅ :=
    (uniformInterval_disjoint hg hkl).inter_eq
  have hZ : IsEmpty (ZerothHomotopy (plHeight G h ⁻¹'
      ((uniformCover a r g n k : Set ℝ) ∩ (uniformCover a r g n l : Set ℝ)))) := by
    rw [hempty, Set.preimage_empty]
    exact ⟨fun c => by
      obtain ⟨x, -⟩ := ZerothHomotopy.mk_surjective c
      exact absurd x.2 (Set.notMem_empty _)⟩
  exact (edgeCellsEquiv (plHeight G h) (fun i => (uniformCover a r g n i : Set ℝ)) k l).isEmpty

end

end GraphPL

end TDA.Mapper
