import TDA.Reeb.CriticalValues
import TDA.Reeb.FiniteDiagram
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Cylinder presentations and their realizations

A cylinder presentation `P : CylinderPresentation n` over `n + 1` levels consists of arbitrary
topological vertex pieces `V i` for `i : Fin (n + 1)`, edge pieces `E e` for `e : Fin n`, and
continuous endpoint maps `left e : E e → V e.castSucc` and `right e : E e → V e.succ`. The
critical levels `S : CriticalValues n` are not part of the presentation; every construction
takes them explicitly. This is the construction of de Silva–Munch–Patel, §2.2, with compactness
and local path-connectedness of the pieces moved from the data to theorem hypotheses.

* Realization. `P.Realization S` is the quotient of the finite sum of the vertex pieces and the
  cylinders `E e × [a e, a (e+1)]` by the equivalence closure of exactly the two endpoint
  identifications per edge (`EndpointRel`), with the quotient topology. The closure is
  characterized by a normal form that sends cylinder endpoints to their vertex images
  (`eqvGen_iff`). Vertex points are never merged with each other (`ofVertex_eq_ofVertex_iff`),
  and every point is a vertex point or an open-strip point (`exists_rep`); strip points are
  identified with nothing else (`ofStrip_injective`, `ofVertex_ne_ofStrip`).
* Constructors and height. `ofVertex` and `ofCylinder` are continuous, the cylinder ends satisfy
  `ofCylinder_segBot` and `ofCylinder_segTop`, and the continuous `height` is the level on a
  vertex piece and the real coordinate on a cylinder, by definition.
* Universal property. Continuous maps on all pieces satisfying the two endpoint equations
  (`CompatibleMaps`) descend uniquely (`lift`, `lift_unique`, `existsUnique_lift`); `liftEquiv`
  states this as an equivalence with both inverse laws.
* Normal forms. The open strip `E e × K e` is an open embedding (`isOpenEmbedding_ofStrip`), and
  the inverse image of the gap is homeomorphic to it as a subspace (`stripHomeomorph`). A regular
  fiber is homeomorphic to `E e` (`regularFiberHomeomorph`) and the fiber at the level `a i` to
  `V i` (`criticalFiberHomeomorph`). Fibers over the exterior tails are empty.
* Topology. The realization is Hausdorff when the pieces are (`t2Space`): different heights are
  separated by the height, equal regular heights inside one open strip, and points of one vertex
  piece by collars of disjoint open sets. Neither compactness nor properness is used. The
  realization is compact when the pieces are (`compactSpace`), and locally path-connected when the
  pieces are (`locallyPathConnectedSpace`). All three are conditional instances.
* Finite data. `ofFiniteData D` gives finite incidence data the discrete topology, so finite data
  are realized by the same quotient. A finite map gives a height-preserving continuous map
  (`realizeHom`), functorially (`realizeHom_id`, `realizeHom_comp`).

The closed cylinder `E e × [a e, a (e+1)]` does not embed in general: a noninjective endpoint map
identifies distinct cylinder ends. See `docs/math/reeb-constructible-space.md`.
-/

open Set Topology Filter

universe u w

namespace TDA.Reeb.CriticalValues

variable {n : ℕ} (S : CriticalValues n)

/-- The two endpoint levels of a gap are strictly ordered. -/
theorem value_castSucc_lt_succ (e : Fin n) : S.value e.castSucc < S.value e.succ :=
  S.strictMono Fin.castSucc_lt_succ

/-- A regular height lies in the closed segment of exactly one edge. -/
theorem eq_of_mem_K_of_mem_Icc {e e' : Fin n} {t : ℝ} (h : t ∈ (S.K e : Set ℝ))
    (h' : t ∈ Icc (S.value e'.castSucc) (S.value e'.succ)) : e = e' := by
  rcases lt_trichotomy e e' with hl | rfl | hl
  · have := S.strictMono.monotone (Fin.succ_le_castSucc_iff.2 hl)
    exact absurd (h.2.trans_le (this.trans h'.1)) (lt_irrefl _)
  · rfl
  · have := S.strictMono.monotone (Fin.succ_le_castSucc_iff.2 hl)
    exact absurd ((h'.2.trans this).trans_lt h.1) (lt_irrefl _)

/-- Collar widths: positive and at most half of every internal gap. -/
def IsCollarWidth (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ e : Fin n, 2 * δ ≤ S.value e.succ - S.value e.castSucc

/-- A collar width exists. -/
theorem exists_collarWidth : ∃ δ, S.IsCollarWidth δ := by
  have h : ∀ e : Fin n, ∀ᶠ δ in 𝓝[>] (0 : ℝ), 2 * δ ≤ S.value e.succ - S.value e.castSucc :=
    fun e => by
      have hg := sub_pos.2 (S.value_castSucc_lt_succ e)
      filter_upwards [Ioo_mem_nhdsGT (half_pos hg)] with δ hδ
      linarith [hδ.2]
  obtain ⟨δ, h₁, h₂⟩ := ((Filter.eventually_all.2 h).and self_mem_nhdsWithin).exists
  exact ⟨δ, h₂, h₁⟩

end TDA.Reeb.CriticalValues

namespace TDA.Reeb

noncomputable section

/-- A raw cylinder presentation over `n + 1` levels: arbitrary topological vertex pieces `V i`,
edge pieces `E e` and continuous endpoint maps `E e → V e.castSucc`, `E e → V e.succ`.
There is no compactness, Hausdorff or local path-connectedness field; the levels `S` are
separate. -/
structure CylinderPresentation (n : ℕ) : Type (u + 1) where
  /-- Vertex pieces, one per level. -/
  V : Fin (n + 1) → Type u
  /-- Edge pieces, one per regular gap. -/
  E : Fin n → Type u
  /-- Topology of the vertex pieces. -/
  [topV : ∀ i, TopologicalSpace (V i)]
  /-- Topology of the edge pieces. -/
  [topE : ∀ e, TopologicalSpace (E e)]
  /-- Continuous left endpoint map. -/
  left : ∀ e, C(E e, V e.castSucc)
  /-- Continuous right endpoint map. -/
  right : ∀ e, C(E e, V e.succ)

attribute [instance] CylinderPresentation.topV CylinderPresentation.topE

namespace CylinderPresentation

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n)

/-! ### Raw pieces -/

/-- The parameter segment `[a e, a (e+1)]` of edge `e`. -/
abbrev Seg (e : Fin n) : Set ℝ := Icc (S.value e.castSucc) (S.value e.succ)

/-- The bottom end `a e` of the segment of edge `e`. -/
def segBot (e : Fin n) : Seg S e := ⟨_, left_mem_Icc.2 (S.value_castSucc_lt_succ e).le⟩

/-- The top end `a (e+1)` of the segment of edge `e`. -/
def segTop (e : Fin n) : Seg S e := ⟨_, right_mem_Icc.2 (S.value_castSucc_lt_succ e).le⟩

/-- The sum of the vertex pieces. -/
abbrev VertexPiece := Σ i, P.V i

/-- The closed cylinder `E e × [a e, a (e+1)]`. -/
abbrev Cylinder (e : Fin n) := P.E e × Seg S e

/-- The sum of the closed cylinders. -/
abbrev CylinderPiece := Σ e, P.Cylinder S e

/-- The finite disjoint sum of the vertex pieces and the cylinders. -/
abbrev Raw := P.VertexPiece ⊕ P.CylinderPiece S

/-- The generating relation: exactly the two endpoint identifications per edge. -/
inductive EndpointRel : P.Raw S → P.Raw S → Prop
  /-- The bottom end `(y, a e)` is identified with `left e y`. -/
  | left (e : Fin n) (y : P.E e) :
      EndpointRel (.inr ⟨e, y, segBot S e⟩) (.inl ⟨e.castSucc, P.left e y⟩)
  /-- The top end `(y, a (e+1))` is identified with `right e y`. -/
  | right (e : Fin n) (y : P.E e) :
      EndpointRel (.inr ⟨e, y, segTop S e⟩) (.inl ⟨e.succ, P.right e y⟩)

/-- The equivalence closure of the endpoint relation. -/
def setoid : Setoid (P.Raw S) := Relation.EqvGen.setoid (P.EndpointRel S)

/-- The realization: the quotient of the raw sum with the quotient topology. -/
def Realization : Type u := Quotient (P.setoid S)

instance : TopologicalSpace (P.Realization S) :=
  inferInstanceAs (TopologicalSpace (Quotient (P.setoid S)))

/-- The quotient map from the raw sum. -/
def quotMk (x : P.Raw S) : P.Realization S := Quotient.mk (P.setoid S) x

theorem quotMk_surjective : Function.Surjective (P.quotMk S) := Quotient.mk_surjective

theorem isQuotientMap_quotMk : IsQuotientMap (P.quotMk S) := isQuotientMap_quotient_mk'

theorem continuous_quotMk : Continuous (P.quotMk S) := (P.isQuotientMap_quotMk S).continuous

/-! ### Normal form of the relation -/

/-- Canonical representative of a cylinder point: the ends go to their vertex images. -/
def nfCyl (c : P.CylinderPiece S) : P.Raw S :=
  if (c.2.2 : ℝ) = S.value c.1.castSucc then .inl ⟨c.1.castSucc, P.left c.1 c.2.1⟩
  else if (c.2.2 : ℝ) = S.value c.1.succ then .inl ⟨c.1.succ, P.right c.1 c.2.1⟩
  else .inr c

/-- Canonical representative: cylinder ends go to their vertex images, all other points are
fixed. -/
def nf : P.Raw S → P.Raw S := Sum.elim Sum.inl (P.nfCyl S)

@[simp] theorem nf_inl (p : P.VertexPiece) : P.nf S (.inl p) = .inl p := rfl

theorem nf_segBot (e : Fin n) (y : P.E e) :
    P.nf S (.inr ⟨e, y, segBot S e⟩) = .inl ⟨e.castSucc, P.left e y⟩ := by
  simp [nf, nfCyl, segBot]

theorem nf_segTop (e : Fin n) (y : P.E e) :
    P.nf S (.inr ⟨e, y, segTop S e⟩) = .inl ⟨e.succ, P.right e y⟩ := by
  simp [nf, nfCyl, segTop, (S.value_castSucc_lt_succ e).ne']

theorem eqvGen_nf (x : P.Raw S) : Relation.EqvGen (P.EndpointRel S) x (P.nf S x) := by
  rcases x with p | ⟨e, y, t⟩
  · exact .refl _
  · simp only [nf, Sum.elim_inr, nfCyl]
    split_ifs with h₁ h₂
    · obtain rfl : t = segBot S e := Subtype.ext h₁
      exact .rel _ _ (.left e y)
    · obtain rfl : t = segTop S e := Subtype.ext h₂
      exact .rel _ _ (.right e y)
    · exact .refl _

theorem nf_eq_of_eqvGen {x y : P.Raw S} (h : Relation.EqvGen (P.EndpointRel S) x y) :
    P.nf S x = P.nf S y := by
  induction h with
  | rel x y h =>
    cases h with
    | left e y => rw [nf_segBot]; rfl
    | right e y => rw [nf_segTop]; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The equivalence closure of the endpoint relation is exactly "same canonical
representative". -/
theorem eqvGen_iff {x y : P.Raw S} :
    Relation.EqvGen (P.EndpointRel S) x y ↔ P.nf S x = P.nf S y := by
  refine ⟨P.nf_eq_of_eqvGen S, fun h => ?_⟩
  have h₂ := Relation.EqvGen.symm _ _ (P.eqvGen_nf S y)
  rw [← h] at h₂
  exact .trans _ _ _ (P.eqvGen_nf S x) h₂

theorem quotMk_eq_iff {x y : P.Raw S} : P.quotMk S x = P.quotMk S y ↔ P.nf S x = P.nf S y :=
  ⟨fun h => (P.eqvGen_iff S).1 (Quotient.exact h), fun h => Quotient.sound ((P.eqvGen_iff S).2 h)⟩

theorem eq_of_nf_eq_inr {x : P.Raw S} {c : P.CylinderPiece S} (h : P.nf S x = .inr c) :
    x = .inr c := by
  rcases x with p | c'
  · cases h
  · simp only [nf, Sum.elim_inr, nfCyl] at h
    split_ifs at h
    exact h

/-! ### Constructors and endpoint identities -/

/-- A point of the vertex piece `V i`. -/
def ofVertex (i : Fin (n + 1)) (v : P.V i) : P.Realization S := P.quotMk S (.inl ⟨i, v⟩)

/-- A point of the closed cylinder of edge `e`. -/
def ofCylinder (e : Fin n) (p : P.Cylinder S e) : P.Realization S := P.quotMk S (.inr ⟨e, p⟩)

theorem ofCylinder_segBot (e : Fin n) (y : P.E e) :
    P.ofCylinder S e (y, segBot S e) = P.ofVertex S e.castSucc (P.left e y) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (EndpointRel.left e y))

theorem ofCylinder_segTop (e : Fin n) (y : P.E e) :
    P.ofCylinder S e (y, segTop S e) = P.ofVertex S e.succ (P.right e y) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (EndpointRel.right e y))

theorem continuous_ofVertex (i : Fin (n + 1)) : Continuous (P.ofVertex S i) :=
  (P.continuous_quotMk S).comp (continuous_inl.comp continuous_sigmaMk)

theorem continuous_ofCylinder (e : Fin n) : Continuous (P.ofCylinder S e) :=
  (P.continuous_quotMk S).comp (continuous_inr.comp continuous_sigmaMk)

theorem ofVertex_injective (i : Fin (n + 1)) : Function.Injective (P.ofVertex S i) := by
  intro v w h
  have := (P.quotMk_eq_iff S).1 h
  simp only [nf_inl, Sum.inl.injEq] at this
  exact sigma_mk_injective this

/-- Vertex classes are not merged with each other: two vertex points are identified only
when equal in the vertex sum. -/
theorem ofVertex_eq_ofVertex_iff {i j : Fin (n + 1)} {v : P.V i} {w : P.V j} :
    P.ofVertex S i v = P.ofVertex S j w ↔ (⟨i, v⟩ : P.VertexPiece) = ⟨j, w⟩ := by
  rw [ofVertex, ofVertex, quotMk_eq_iff, nf_inl, nf_inl, Sum.inl.injEq]

/-! ### Height -/

/-- The height on the raw sum: the level on a vertex piece, the real coordinate on a
cylinder. -/
def rawHeight : P.Raw S → ℝ := Sum.elim (fun p => S.value p.1) fun c => (c.2.2 : ℝ)

theorem continuous_rawHeight : Continuous (P.rawHeight S) :=
  Continuous.sumElim
    (continuous_sigma fun i => (continuous_const : Continuous fun _ : P.V i => S.value i))
    (continuous_sigma fun _ => continuous_subtype_val.comp continuous_snd)

theorem rawHeight_nf (x : P.Raw S) : P.rawHeight S (P.nf S x) = P.rawHeight S x := by
  rcases x with p | ⟨e, y, t⟩
  · rfl
  · simp only [nf, Sum.elim_inr, nfCyl]
    split_ifs with h₁ h₂
    · exact h₁.symm
    · exact h₂.symm
    · rfl

/-- The height of the realization, descended from the real coordinate. -/
def height : C(P.Realization S, ℝ) :=
  ⟨Quotient.lift (P.rawHeight S) fun x y h => by
      rw [← P.rawHeight_nf S x, ← P.rawHeight_nf S y, (P.eqvGen_iff S).1 h],
    (P.continuous_rawHeight S).quotient_lift _⟩

@[simp] theorem height_ofVertex (i : Fin (n + 1)) (v : P.V i) :
    P.height S (P.ofVertex S i v) = S.value i := rfl

@[simp] theorem height_ofCylinder (e : Fin n) (p : P.Cylinder S e) :
    P.height S (P.ofCylinder S e p) = p.2 := rfl

/-! ### Universal property -/

/-- Compatible continuous maps on all raw pieces: continuous maps on the vertex pieces and the
closed cylinders satisfying exactly the two endpoint equations. -/
@[ext]
structure CompatibleMaps (Z : Type w) [TopologicalSpace Z] where
  /-- The map on each vertex piece. -/
  vertex : ∀ i, C(P.V i, Z)
  /-- The map on each closed cylinder. -/
  cylinder : ∀ e, C(P.Cylinder S e, Z)
  /-- The bottom end of a cylinder goes where its left endpoint image goes. -/
  segBot_eq : ∀ e y, cylinder e (y, segBot S e) = vertex e.castSucc (P.left e y)
  /-- The top end of a cylinder goes where its right endpoint image goes. -/
  segTop_eq : ∀ e y, cylinder e (y, segTop S e) = vertex e.succ (P.right e y)

variable {S P} {Z : Type w} [TopologicalSpace Z]

namespace CompatibleMaps

/-- The induced map on the raw sum. -/
def raw (k : P.CompatibleMaps S Z) : P.Raw S → Z :=
  Sum.elim (fun p => k.vertex p.1 p.2) fun c => k.cylinder c.1 c.2

theorem continuous_raw (k : P.CompatibleMaps S Z) : Continuous k.raw :=
  Continuous.sumElim (continuous_sigma fun i => (k.vertex i).continuous)
    (continuous_sigma fun e => (k.cylinder e).continuous)

theorem raw_nf (k : P.CompatibleMaps S Z) (x : P.Raw S) : k.raw (P.nf S x) = k.raw x := by
  rcases x with p | ⟨e, y, t⟩
  · rfl
  · simp only [nf, Sum.elim_inr, nfCyl]
    split_ifs with h₁ h₂
    · obtain rfl : t = segBot S e := Subtype.ext h₁
      exact (k.segBot_eq e y).symm
    · obtain rfl : t = segTop S e := Subtype.ext h₂
      exact (k.segTop_eq e y).symm
    · rfl

end CompatibleMaps

/-- Descent of compatible continuous maps on the raw pieces. -/
def lift (k : P.CompatibleMaps S Z) : C(P.Realization S, Z) :=
  ⟨Quotient.lift k.raw fun x y h => by
      rw [← k.raw_nf x, ← k.raw_nf y, (P.eqvGen_iff S).1 h],
    k.continuous_raw.quotient_lift _⟩

@[simp] theorem lift_ofVertex (k : P.CompatibleMaps S Z) (i : Fin (n + 1)) (v : P.V i) :
    lift k (P.ofVertex S i v) = k.vertex i v := rfl

@[simp] theorem lift_ofCylinder (k : P.CompatibleMaps S Z) (e : Fin n) (p : P.Cylinder S e) :
    lift k (P.ofCylinder S e p) = k.cylinder e p := rfl

/-- Continuous maps out of the realization agreeing on all vertex and cylinder points are
equal. -/
theorem hom_ext {g g' : C(P.Realization S, Z)}
    (hv : ∀ i v, g (P.ofVertex S i v) = g' (P.ofVertex S i v))
    (hc : ∀ e p, g (P.ofCylinder S e p) = g' (P.ofCylinder S e p)) : g = g' := by
  ext q
  obtain ⟨x, rfl⟩ := P.quotMk_surjective S q
  rcases x with ⟨i, v⟩ | ⟨e, p⟩
  · exact hv i v
  · exact hc e p

theorem lift_unique (k : P.CompatibleMaps S Z) (g : C(P.Realization S, Z))
    (hv : ∀ i v, g (P.ofVertex S i v) = k.vertex i v)
    (hc : ∀ e p, g (P.ofCylinder S e p) = k.cylinder e p) : g = lift k :=
  hom_ext hv hc

variable (S P) in
/-- Restriction of a continuous map on the realization to the raw pieces. -/
def CompatibleMaps.ofMap (g : C(P.Realization S, Z)) : P.CompatibleMaps S Z where
  vertex i := g.comp ⟨_, P.continuous_ofVertex S i⟩
  cylinder e := g.comp ⟨_, P.continuous_ofCylinder S e⟩
  segBot_eq e y := congrArg g (P.ofCylinder_segBot S e y)
  segTop_eq e y := congrArg g (P.ofCylinder_segTop S e y)

variable (S P Z) in
/-- The universal property as an equivalence. -/
def liftEquiv : P.CompatibleMaps S Z ≃ C(P.Realization S, Z) where
  toFun := lift
  invFun := CompatibleMaps.ofMap S P
  left_inv _ := rfl
  right_inv g := (lift_unique _ g (fun _ _ => rfl) fun _ _ => rfl).symm

theorem existsUnique_lift (k : P.CompatibleMaps S Z) :
    ∃! g : C(P.Realization S, Z), (∀ i v, g (P.ofVertex S i v) = k.vertex i v) ∧
      ∀ e p, g (P.ofCylinder S e p) = k.cylinder e p :=
  ⟨lift k, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, fun g hg => lift_unique k g hg.1 hg.2⟩

variable (S P)

/-! ### Open strips -/

/-- Inclusion of the open gap into the closed segment. -/
def gapIncl (e : Fin n) : ↥(S.K e : Set ℝ) → Seg S e := fun t => ⟨t.1, Ioo_subset_Icc_self t.2⟩

/-- A point of the open strip `E e × K e` in the raw sum. -/
def rawStrip (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) : P.Raw S :=
  .inr ⟨e, p.1, gapIncl S e p.2⟩

/-- A point of the open strip `E e × K e`. -/
def ofStrip (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) : P.Realization S :=
  P.quotMk S (P.rawStrip S e p)

theorem ofStrip_eq_ofCylinder (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    P.ofStrip S e p = P.ofCylinder S e (p.1, gapIncl S e p.2) := rfl

@[simp] theorem height_ofStrip (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    P.height S (P.ofStrip S e p) = p.2 := rfl

theorem nf_rawStrip (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    P.nf S (P.rawStrip S e p) = P.rawStrip S e p := by
  simp [nf, nfCyl, rawStrip, gapIncl, p.2.2.1.ne', p.2.2.2.ne]

theorem rawStrip_injective (e : Fin n) : Function.Injective (P.rawStrip S e) := by
  intro p p' h
  simp only [rawStrip, gapIncl, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and,
    Prod.mk.injEq, Subtype.mk.injEq] at h
  exact Prod.ext h.1 (Subtype.ext h.2)

theorem ofStrip_injective (e : Fin n) : Function.Injective (P.ofStrip S e) := by
  intro p p' h
  have := (P.quotMk_eq_iff S).1 h
  rw [nf_rawStrip, nf_rawStrip] at this
  exact P.rawStrip_injective S e this

theorem continuous_ofStrip (e : Fin n) : Continuous (P.ofStrip S e) :=
  (P.continuous_ofCylinder S e).comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _))

theorem isOpenMap_gapIncl (e : Fin n) : IsOpenMap (gapIncl S e) := by
  intro O hO
  have hO' : IsOpen (Subtype.val '' O : Set ℝ) :=
    (S.K e).isOpen.isOpenEmbedding_subtypeVal.isOpenMap O hO
  have : gapIncl S e '' O = Subtype.val ⁻¹' (Subtype.val '' O) := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, hts⟩
      exact ⟨t, ht, Subtype.ext hts⟩
  rw [this]
  exact hO'.preimage continuous_subtype_val

theorem isOpenMap_rawStrip (e : Fin n) : IsOpenMap (P.rawStrip S e) :=
  isOpenMap_inr.comp (isOpenMap_sigmaMk.comp (IsOpenMap.id.prodMap (isOpenMap_gapIncl S e)))

/-- The open strip is an open embedding of `E e × K e`. -/
theorem isOpenEmbedding_ofStrip (e : Fin n) : IsOpenEmbedding (P.ofStrip S e) := by
  refine .of_continuous_injective_isOpenMap (P.continuous_ofStrip S e) (P.ofStrip_injective S e)
    fun O hO => ?_
  have : P.quotMk S ⁻¹' (P.ofStrip S e '' O) = P.rawStrip S e '' O := by
    ext x
    constructor
    · rintro ⟨p, hp, hpx⟩
      have := (P.quotMk_eq_iff S).1 hpx
      rw [nf_rawStrip] at this
      exact ⟨p, hp, (P.eq_of_nf_eq_inr S this.symm).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [← (P.isQuotientMap_quotMk S).isOpen_preimage, this]
  exact P.isOpenMap_rawStrip S e O hO

/-! ### Normal forms of points and fibers -/

/-- Every point is a vertex point or an open-strip point. -/
theorem exists_rep (q : P.Realization S) :
    (∃ i v, q = P.ofVertex S i v) ∨ ∃ e p, q = P.ofStrip S e p := by
  obtain ⟨x, rfl⟩ := P.quotMk_surjective S q
  rcases x with ⟨i, v⟩ | ⟨e, y, t⟩
  · exact .inl ⟨i, v, rfl⟩
  · by_cases h₁ : (t : ℝ) = S.value e.castSucc
    · obtain rfl : t = segBot S e := Subtype.ext h₁
      exact .inl ⟨_, _, P.ofCylinder_segBot S e y⟩
    by_cases h₂ : (t : ℝ) = S.value e.succ
    · obtain rfl : t = segTop S e := Subtype.ext h₂
      exact .inl ⟨_, _, P.ofCylinder_segTop S e y⟩
    exact .inr ⟨e, (y, ⟨t, lt_of_le_of_ne t.2.1 (Ne.symm h₁), lt_of_le_of_ne t.2.2 h₂⟩), rfl⟩

theorem ofVertex_ne_ofStrip (i : Fin (n + 1)) (v : P.V i) (e : Fin n)
    (p : P.E e × (S.K e : Set ℝ)) : P.ofVertex S i v ≠ P.ofStrip S e p := fun h => by
  have h' := congrArg (P.height S) h
  rw [height_ofVertex, height_ofStrip] at h'
  exact S.value_notMem_K e i (by rw [h']; exact p.2.2)

theorem range_ofVertex (i : Fin (n + 1)) :
    range (P.ofVertex S i) = P.height S ⁻¹' {S.value i} := by
  ext q
  constructor
  · rintro ⟨v, rfl⟩
    rfl
  · intro hq
    rcases P.exists_rep S q with ⟨j, v, rfl⟩ | ⟨e, p, rfl⟩
    · obtain rfl : j = i := S.strictMono.injective hq
      exact ⟨v, rfl⟩
    · have hq' : P.height S (P.ofStrip S e p) = S.value i := hq
      rw [height_ofStrip] at hq'
      exact absurd (hq' ▸ p.2.2) (S.value_notMem_K e i)

theorem range_ofStrip (e : Fin n) :
    range (P.ofStrip S e) = P.height S ⁻¹' (S.K e : Set ℝ) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    show P.height S (P.ofStrip S e p) ∈ (S.K e : Set ℝ)
    rw [height_ofStrip]
    exact p.2.2
  · intro hq
    rcases P.exists_rep S q with ⟨i, v, rfl⟩ | ⟨e', p, rfl⟩
    · exact absurd hq (S.value_notMem_K e i)
    · have hq' : P.height S (P.ofStrip S e' p) ∈ (S.K e : Set ℝ) := hq
      rw [height_ofStrip] at hq'
      obtain rfl : e = e' := S.eq_of_mem_K_of_mem_Icc hq' (Ioo_subset_Icc_self p.2.2)
      exact ⟨p, rfl⟩

theorem isOpen_strip (e : Fin n) : IsOpen (P.height S ⁻¹' (S.K e : Set ℝ)) :=
  (S.K e).isOpen.preimage (P.height S).continuous

/-- Open-strip normal form: the inverse image of `K e` with its subspace topology is
homeomorphic to `E e × K e`, compatibly with the height. -/
def stripHomeomorph (e : Fin n) :
    P.E e × (S.K e : Set ℝ) ≃ₜ P.height S ⁻¹' (S.K e : Set ℝ) :=
  (P.isOpenEmbedding_ofStrip S e).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.range_ofStrip S e))

@[simp] theorem stripHomeomorph_apply (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    (P.stripHomeomorph S e p : P.Realization S) = P.ofStrip S e p := rfl

theorem height_stripHomeomorph (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    P.height S (P.stripHomeomorph S e p) = p.2 := rfl

theorem isEmbedding_ofStrip_at (e : Fin n) (t : (S.K e : Set ℝ)) :
    IsEmbedding fun y : P.E e => P.ofStrip S e (y, t) :=
  (P.isOpenEmbedding_ofStrip S e).isEmbedding.comp (isEmbedding_prodMkLeft t)

theorem range_ofStrip_at (e : Fin n) (t : (S.K e : Set ℝ)) :
    range (fun y : P.E e => P.ofStrip S e (y, t)) = P.height S ⁻¹' {(t : ℝ)} := by
  ext q
  constructor
  · rintro ⟨y, rfl⟩
    exact P.height_ofStrip S e (y, t)
  · intro hq
    have hq' : q ∈ range (P.ofStrip S e) := by
      rw [range_ofStrip]
      show P.height S q ∈ (S.K e : Set ℝ)
      rw [show P.height S q = t from hq]
      exact t.2
    obtain ⟨⟨y, s⟩, rfl⟩ := hq'
    have hs : P.height S (P.ofStrip S e (y, s)) = t := hq
    rw [height_ofStrip] at hs
    obtain rfl : s = t := Subtype.ext hs
    exact ⟨y, rfl⟩

/-- Regular-fiber normal form: at a height `t` in the gap `K e`, the fiber is `E e`. -/
def regularFiberHomeomorph (e : Fin n) (t : (S.K e : Set ℝ)) :
    P.E e ≃ₜ P.height S ⁻¹' {(t : ℝ)} :=
  (P.isEmbedding_ofStrip_at S e t).toHomeomorph.trans
    (Homeomorph.setCongr (P.range_ofStrip_at S e t))

@[simp] theorem regularFiberHomeomorph_apply (e : Fin n) (t : (S.K e : Set ℝ)) (y : P.E e) :
    (P.regularFiberHomeomorph S e t y : P.Realization S) = P.ofStrip S e (y, t) := rfl

/-! ### Exterior heights -/

/-- Every height lies in the critical range `[a 0, a n]`. -/
theorem height_mem_Icc (q : P.Realization S) :
    P.height S q ∈ Icc (S.value 0) (S.value (Fin.last n)) := by
  rcases P.exists_rep S q with ⟨i, v, rfl⟩ | ⟨e, p, rfl⟩
  · exact ⟨S.strictMono.monotone (Fin.zero_le i), S.strictMono.monotone (Fin.le_last i)⟩
  · rw [height_ofStrip]
    exact ⟨(S.strictMono.monotone (Fin.zero_le _)).trans p.2.2.1.le,
      p.2.2.2.le.trans (S.strictMono.monotone (Fin.le_last _))⟩

/-- Fibers outside the critical range are empty. -/
theorem height_preimage_eq_empty {t : ℝ} (ht : t ∉ Icc (S.value 0) (S.value (Fin.last n))) :
    P.height S ⁻¹' {t} = ∅ :=
  eq_empty_iff_forall_notMem.2 fun q (hq : P.height S q = t) => ht (hq ▸ P.height_mem_Icc S q)

/-- No point lies over the lower tail `(-∞, a 0)`. -/
theorem height_preimage_lowerTail : P.height S ⁻¹' (S.lowerTail : Set ℝ) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun q hq =>
    absurd (S.mem_lowerTail.1 hq) (not_lt.2 (P.height_mem_Icc S q).1)

/-- No point lies over the upper tail `(a n, ∞)`. -/
theorem height_preimage_upperTail : P.height S ⁻¹' (S.upperTail : Set ℝ) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun q hq =>
    absurd (S.mem_upperTail.1 hq) (not_lt.2 (P.height_mem_Icc S q).2)

theorem height_preimage_eq_empty_of_mem_lowerTail {t : ℝ} (ht : t ∈ S.lowerTail) :
    P.height S ⁻¹' {t} = ∅ :=
  P.height_preimage_eq_empty S fun h => absurd h.1 (not_le.2 (S.mem_lowerTail.1 ht))

theorem height_preimage_eq_empty_of_mem_upperTail {t : ℝ} (ht : t ∈ S.upperTail) :
    P.height S ⁻¹' {t} = ∅ :=
  P.height_preimage_eq_empty S fun h => absurd h.2 (not_le.2 (S.mem_upperTail.1 ht))

/-! ### Collars around a critical level -/

/-- The left endpoint image of a cylinder point, in the vertex sum. -/
def leftEnd (c : P.CylinderPiece S) : P.VertexPiece := ⟨c.1.castSucc, P.left c.1 c.2.1⟩

/-- The right endpoint image of a cylinder point, in the vertex sum. -/
def rightEnd (c : P.CylinderPiece S) : P.VertexPiece := ⟨c.1.succ, P.right c.1 c.2.1⟩

/-- Raw collar of `W`: `W` itself, together with the cylinder points within `δ` of an end
whose endpoint image lies in `W`. -/
def InCollar (W : Set P.VertexPiece) (δ : ℝ) : P.Raw S → Prop :=
  Sum.elim (· ∈ W) fun c =>
    ((c.2.2 : ℝ) < S.value c.1.castSucc + δ ∧ P.leftEnd S c ∈ W) ∨
      (S.value c.1.succ - δ < c.2.2 ∧ P.rightEnd S c ∈ W)

variable {S} in
/-- The raw collar is saturated for a collar width. -/
theorem inCollar_nf {δ : ℝ} (hδ : S.IsCollarWidth δ) (W : Set P.VertexPiece) (x : P.Raw S) :
    P.InCollar S W δ (P.nf S x) ↔ P.InCollar S W δ x := by
  rcases x with p | ⟨e, y, t⟩
  · rfl
  · have h0 := hδ.1
    have hg := hδ.2 e
    simp only [nf, Sum.elim_inr, nfCyl]
    split_ifs with h₁ h₂
    · change _ ↔ ((t : ℝ) < _ ∧ _) ∨ (_ < (t : ℝ) ∧ _)
      rw [h₁]
      constructor
      · intro h
        exact .inl ⟨by linarith, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · linarith
    · change _ ↔ ((t : ℝ) < _ ∧ _) ∨ (_ < (t : ℝ) ∧ _)
      rw [h₂]
      constructor
      · intro h
        exact .inr ⟨by linarith, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · linarith
        · exact h
    · rfl

/-- The raw collar of an open set is open, by continuity of the endpoint maps. -/
theorem isOpen_inCollar {W : Set P.VertexPiece} (hW : IsOpen W) (δ : ℝ) :
    IsOpen {x | P.InCollar S W δ x} := by
  refine isOpen_sum_iff.2 ⟨hW, ?_⟩
  have hh : Continuous fun c : P.CylinderPiece S => (c.2.2 : ℝ) :=
    continuous_sigma fun _ => continuous_subtype_val.comp continuous_snd
  have hl : Continuous fun c : P.CylinderPiece S => S.value c.1.castSucc + δ :=
    continuous_sigma fun e =>
      (continuous_const : Continuous fun _ : P.Cylinder S e => S.value e.castSucc + δ)
  have hr : Continuous fun c : P.CylinderPiece S => S.value c.1.succ - δ :=
    continuous_sigma fun e =>
      (continuous_const : Continuous fun _ : P.Cylinder S e => S.value e.succ - δ)
  have hL : Continuous (P.leftEnd S) :=
    continuous_sigma fun e => continuous_sigmaMk.comp ((P.left e).continuous.comp continuous_fst)
  have hR : Continuous (P.rightEnd S) :=
    continuous_sigma fun e => continuous_sigmaMk.comp ((P.right e).continuous.comp continuous_fst)
  exact ((isOpen_lt hh hl).inter (hW.preimage hL)).union ((isOpen_lt hr hh).inter (hW.preimage hR))

variable {S} in
/-- The collar descended to the realization (the raw collar is saturated). -/
def collar (W : Set P.VertexPiece) {δ : ℝ} (hδ : S.IsCollarWidth δ) : Set (P.Realization S) :=
  {q | Quotient.lift (s := P.setoid S) (P.InCollar S W δ) (fun x y h => propext <|
    (P.inCollar_nf hδ W x).symm.trans (by rw [(P.eqvGen_iff S).1 h]; exact P.inCollar_nf hδ W y)) q}

variable {S} in
theorem isOpen_collar {W : Set P.VertexPiece} (hW : IsOpen W) {δ : ℝ} (hδ : S.IsCollarWidth δ) :
    IsOpen (P.collar W hδ) :=
  (P.isQuotientMap_quotMk S).isOpen_preimage.1 (P.isOpen_inCollar S hW δ)

variable {S} in
theorem ofVertex_mem_collar (W : Set P.VertexPiece) {δ : ℝ} (hδ : S.IsCollarWidth δ)
    (i : Fin (n + 1)) (v : P.V i) : P.ofVertex S i v ∈ P.collar W hδ ↔ ⟨i, v⟩ ∈ W := Iff.rfl

variable {S} in
/-- Collars of disjoint sets are disjoint (uses `2 δ ≤` every gap). -/
theorem disjoint_collar {W W' : Set P.VertexPiece} (hWW' : Disjoint W W') {δ : ℝ}
    (hδ : S.IsCollarWidth δ) : Disjoint (P.collar W hδ) (P.collar W' hδ) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  obtain ⟨x, rfl⟩ := P.quotMk_surjective S q
  rcases x with p | ⟨e, y, t⟩
  · exact Set.disjoint_left.1 hWW' hq hq'
  · have hg := hδ.2 e
    change ((t : ℝ) < _ ∧ _) ∨ (_ < (t : ℝ) ∧ _) at hq
    change ((t : ℝ) < _ ∧ _) ∨ (_ < (t : ℝ) ∧ _) at hq'
    rcases hq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hq' with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩
    · exact Set.disjoint_left.1 hWW' h₂ h₂'
    · linarith
    · linarith
    · exact Set.disjoint_left.1 hWW' h₂ h₂'

/-- A vertex piece carries the subspace topology: every open set of `V i` is the trace of an
open collar. No separation hypothesis is used. -/
theorem isInducing_ofVertex (i : Fin (n + 1)) : IsInducing (P.ofVertex S i) := by
  obtain ⟨δ, hδ⟩ := S.exists_collarWidth
  refine ⟨le_antisymm (P.continuous_ofVertex S i).le_induced ?_⟩
  rw [TopologicalSpace.le_def]
  intro U hU
  refine isOpen_induced_iff.2
    ⟨P.collar (Sigma.mk i '' U) hδ, P.isOpen_collar (isOpenMap_sigmaMk U hU) hδ, ?_⟩
  ext v
  exact sigma_mk_injective.mem_set_image

theorem isEmbedding_ofVertex (i : Fin (n + 1)) : IsEmbedding (P.ofVertex S i) :=
  ⟨P.isInducing_ofVertex S i, P.ofVertex_injective S i⟩

/-- Critical-fiber normal form: at the critical value `a i` the fiber is `V i`. -/
def criticalFiberHomeomorph (i : Fin (n + 1)) : P.V i ≃ₜ P.height S ⁻¹' {S.value i} :=
  (P.isEmbedding_ofVertex S i).toHomeomorph.trans (Homeomorph.setCongr (P.range_ofVertex S i))

@[simp] theorem criticalFiberHomeomorph_apply (i : Fin (n + 1)) (v : P.V i) :
    (P.criticalFiberHomeomorph S i v : P.Realization S) = P.ofVertex S i v := rfl

/-! ### Global topological properties -/

/-- Hausdorffness from Hausdorff pieces and continuous endpoint maps only (no compactness,
properness or local path-connectedness). -/
theorem t2Space [∀ i, T2Space (P.V i)] [∀ e, T2Space (P.E e)] : T2Space (P.Realization S) := by
  refine ⟨fun q q' hne => ?_⟩
  by_cases hh : P.height S q = P.height S q'
  · rcases P.exists_rep S q with ⟨i, v, rfl⟩ | ⟨e, p, rfl⟩ <;>
      rcases P.exists_rep S q' with ⟨i', v', rfl⟩ | ⟨e', p', rfl⟩
    · obtain rfl : i = i' := S.strictMono.injective hh
      have hv : v ≠ v' := fun h => hne (h ▸ rfl)
      obtain ⟨U, U', hU, hU', hvU, hvU', hUU'⟩ := t2_separation hv
      obtain ⟨δ, hδ⟩ := S.exists_collarWidth
      exact ⟨_, _, P.isOpen_collar (isOpenMap_sigmaMk U hU) hδ,
        P.isOpen_collar (isOpenMap_sigmaMk U' hU') hδ, ⟨v, hvU, rfl⟩, ⟨v', hvU', rfl⟩,
        P.disjoint_collar ((disjoint_image_iff sigma_mk_injective).2 hUU') hδ⟩
    · rw [height_ofVertex, height_ofStrip] at hh
      exact absurd (hh ▸ p'.2.2) (S.value_notMem_K e' i)
    · rw [height_ofVertex, height_ofStrip] at hh
      exact absurd (hh.symm ▸ p.2.2) (S.value_notMem_K e i')
    · rw [height_ofStrip, height_ofStrip] at hh
      obtain rfl : e = e' :=
        S.eq_of_mem_K_of_mem_Icc p.2.2 (by rw [hh]; exact Ioo_subset_Icc_self p'.2.2)
      have hp : p ≠ p' := fun h => hne (h ▸ rfl)
      obtain ⟨U, U', hU, hU', hpU, hpU', hUU'⟩ := t2_separation hp
      have hO := P.isOpenEmbedding_ofStrip S e
      exact ⟨_, _, hO.isOpenMap U hU, hO.isOpenMap U' hU', ⟨p, hpU, rfl⟩, ⟨p', hpU', rfl⟩,
        (disjoint_image_iff hO.injective).2 hUU'⟩
  · obtain ⟨U, U', hU, hU', h₁, h₂, hUU'⟩ := t2_separation hh
    exact ⟨_, _, hU.preimage (P.height S).continuous, hU'.preimage (P.height S).continuous,
      h₁, h₂, hUU'.preimage _⟩

/-- Compactness from compact pieces (finite sum, compact segments, quotient). -/
theorem compactSpace [∀ i, CompactSpace (P.V i)] [∀ e, CompactSpace (P.E e)] :
    CompactSpace (P.Realization S) :=
  Quotient.compactSpace

/-- Each closed segment is locally path-connected: a basis of convex neighbourhoods. -/
theorem locallyPathConnectedSpace_seg (e : Fin n) : LocallyPathConnectedSpace (Seg S e) := by
  refine LocallyPathConnectedSpace.of_bases (p := fun _ (ε : ℝ) => 0 < ε)
    (s := fun x ε => ((↑) : Seg S e → ℝ) ⁻¹' Ioo ((x : ℝ) - ε) (x + ε)) (fun x => ?_)
    fun x ε hε => ?_
  · rw [nhds_subtype]
    exact (nhds_basis_Ioo_pos (x : ℝ)).comap _
  · have hW : IsPathConnected (Seg S e ∩ Ioo ((x : ℝ) - ε) (x + ε)) :=
      ((convex_Icc (𝕜 := ℝ) _ _).inter (convex_Ioo _ _)).isPathConnected
        ⟨(x : ℝ), x.2, by constructor <;> linarith⟩
    have := hW.preimage_coe (U := Seg S e) inter_subset_left
    rwa [Subtype.preimage_coe_self_inter] at this

/-- Local path-connectedness from locally path-connected pieces. -/
theorem locallyPathConnectedSpace [∀ i, LocallyPathConnectedSpace (P.V i)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] : LocallyPathConnectedSpace (P.Realization S) := by
  have : ∀ e, LocallyPathConnectedSpace (Seg S e) := locallyPathConnectedSpace_seg S
  exact Quotient.locallyPathConnectedSpace

attribute [instance] t2Space compactSpace locallyPathConnectedSpace

/-- An empty vertex piece forces the adjacent edge pieces to be empty. -/
theorem isEmpty_E_of_left {e : Fin n} (h : IsEmpty (P.V e.castSucc)) : IsEmpty (P.E e) :=
  ⟨fun y => h.false (P.left e y)⟩

theorem isEmpty_E_of_right {e : Fin n} (h : IsEmpty (P.V e.succ)) : IsEmpty (P.E e) :=
  ⟨fun y => h.false (P.right e y)⟩

/-- Empty vertex pieces give an empty realization. -/
theorem isEmpty_realization [∀ i, IsEmpty (P.V i)] : IsEmpty (P.Realization S) :=
  ⟨fun q => by
    rcases P.exists_rep S q with ⟨i, v, -⟩ | ⟨e, p, -⟩
    · exact isEmptyElim v
    · exact (P.isEmpty_E_of_left (e := e) inferInstance).false p.1⟩

/-! ### Finite data: the discrete adapter -/

/-- Finite incidence data as a cylinder presentation with discrete pieces; its realization is
the same quotient as for any other presentation. -/
def ofFiniteData (D : FiniteReebData.{u} n) : CylinderPresentation.{u} n where
  V := D.V
  E := D.E
  topV _ := ⊥
  topE _ := ⊥
  left e := @ContinuousMap.mk _ _ ⊥ ⊥ (D.left e) continuous_bot
  right e := @ContinuousMap.mk _ _ ⊥ ⊥ (D.right e) continuous_bot

@[simp] theorem ofFiniteData_V (D : FiniteReebData.{u} n) : (ofFiniteData D).V = D.V := rfl
@[simp] theorem ofFiniteData_E (D : FiniteReebData.{u} n) : (ofFiniteData D).E = D.E := rfl
@[simp] theorem ofFiniteData_topV (D : FiniteReebData.{u} n) (i : Fin (n + 1)) :
    (ofFiniteData D).topV i = ⊥ := rfl
@[simp] theorem ofFiniteData_topE (D : FiniteReebData.{u} n) (e : Fin n) :
    (ofFiniteData D).topE e = ⊥ := rfl
@[simp] theorem ofFiniteData_left_apply (D : FiniteReebData.{u} n) (e : Fin n) (y : D.E e) :
    (ofFiniteData D).left e y = D.left e y := rfl
@[simp] theorem ofFiniteData_right_apply (D : FiniteReebData.{u} n) (e : Fin n) (y : D.E e) :
    (ofFiniteData D).right e y = D.right e y := rfl

instance (D : FiniteReebData.{u} n) (i : Fin (n + 1)) :
    DiscreteTopology ((ofFiniteData D).V i) := ⟨rfl⟩
instance (D : FiniteReebData.{u} n) (e : Fin n) :
    DiscreteTopology ((ofFiniteData D).E e) := ⟨rfl⟩
instance (D : FiniteReebData.{u} n) (i : Fin (n + 1)) : Finite ((ofFiniteData D).V i) :=
  inferInstanceAs (Finite (D.V i))
instance (D : FiniteReebData.{u} n) (e : Fin n) : Finite ((ofFiniteData D).E e) :=
  inferInstanceAs (Finite (D.E e))

/-! The conditional instances resolve for finite data with no further hypothesis. -/

theorem finiteData_t2Space (D : FiniteReebData.{u} n) :
    T2Space ((ofFiniteData D).Realization S) := inferInstance

theorem finiteData_compactSpace (D : FiniteReebData.{u} n) :
    CompactSpace ((ofFiniteData D).Realization S) := inferInstance

theorem finiteData_locallyPathConnectedSpace (D : FiniteReebData.{u} n) :
    LocallyPathConnectedSpace ((ofFiniteData D).Realization S) := inferInstance

/-- A finite map, interpreted with the same `S` on both sides, gives a height-preserving
continuous map of realizations. -/
def realizeHom {D D' : FiniteReebData.{u} n} (φ : D.Hom D') :
    C((ofFiniteData D).Realization S, (ofFiniteData D').Realization S) :=
  lift
    { vertex := fun i => ⟨fun v => (ofFiniteData D').ofVertex S i (φ.v i v),
        continuous_of_discreteTopology⟩
      cylinder := fun e => ⟨fun p => (ofFiniteData D').ofCylinder S e (φ.e e p.1, p.2),
        ((ofFiniteData D').continuous_ofCylinder S e).comp
          ((continuous_of_discreteTopology.comp continuous_fst).prodMk continuous_snd)⟩
      segBot_eq := fun e y =>
        ((ofFiniteData D').ofCylinder_segBot S e (φ.e e y)).trans
          (congrArg ((ofFiniteData D').ofVertex S e.castSucc) (φ.left_comm e y))
      segTop_eq := fun e y =>
        ((ofFiniteData D').ofCylinder_segTop S e (φ.e e y)).trans
          (congrArg ((ofFiniteData D').ofVertex S e.succ) (φ.right_comm e y)) }

theorem height_realizeHom {D D' : FiniteReebData.{u} n} (φ : D.Hom D')
    (q : (ofFiniteData D).Realization S) :
    (ofFiniteData D').height S (realizeHom S φ q) = (ofFiniteData D).height S q := by
  obtain ⟨x, rfl⟩ := (ofFiniteData D).quotMk_surjective S q
  rcases x with ⟨i, v⟩ | ⟨e, p⟩ <;> rfl

/-- The identity map of finite data realizes to the identity. -/
theorem realizeHom_id (D : FiniteReebData.{u} n) :
    realizeHom S (FiniteReebData.Hom.id D) = ContinuousMap.id _ :=
  hom_ext (fun _ _ => rfl) (fun _ _ => rfl)

/-- Realization of finite maps preserves composition. -/
theorem realizeHom_comp {D D' D'' : FiniteReebData.{u} n} (φ : D.Hom D') (ψ : D'.Hom D'') :
    realizeHom S (φ.comp ψ) = (realizeHom S ψ).comp (realizeHom S φ) :=
  hom_ext (fun _ _ => rfl) (fun _ _ => rfl)

end CylinderPresentation

end

end TDA.Reeb
