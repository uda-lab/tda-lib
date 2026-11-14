import TDA.Reeb.ThickeningWindow
import TDA.Reeb.ThickeningCylinder

/-!
# The thickening presentation of a cylinder presentation

For a cylinder presentation `P` over levels `S`, with realization `X = P.Realization S` and
height `f = P.height S`, and a half-width `ε ≥ 0`, the thickening `X × [-ε, ε]` with height
`f x + t` (`GeometricThickening.height`) is the realization of a cylinder presentation `P_ε`
(de Silva–Munch–Patel, *Categorified Reeb Graphs*, proof of Theorem 4.27). The pieces of `P` are
arbitrary topological spaces: no separation hypothesis is used anywhere, and `ε = 0` is allowed.

## The presentation

On any grid `G` listing every shifted level `S.value i ± ε` (`S.ContainsShifted ε G`),
`P.thick` has vertex piece `j` the window `P.Window S ε (b j)` at level `b j` and edge piece `k`
the window at the midpoint `mid k` of slab `k`; its endpoint maps are the window transfers to the
two slab ends. The
pieces are compact, resp. locally path-connected, when all pieces of `P` are
(`instCompactSpaceThickV`, …), as quotients of finite sums of compact (locally path-connected)
spaces. Coincident shifted values are merged by the grid, and pieces are empty where no piece of `P`
reaches.

## The comparison map

`toBand` is the universal map of the realization of `P.thick` into the band
`{(x, u) | u - ε ≤ f x ≤ u + ε}` (`BandSpace`): a vertex point `ξ` of level `b j` goes to
`(ξ, b j)`, a cylinder point `(ξ, u)` of slab `k` to `(transfer ξ, u)` by the joint transfer
`slabCylinder`. Composed with `GeometricThickening.bandHomeomorph` it is `toProd`, into
`X × [-ε, ε]`, which carries the height of `P.thick` to the thickened height (`height_toProd`).

## The attachment maps and the inverse

The per-piece thickening presentations of #707 on the common grid `G`,
`Thickening.cylinderThick (a e) (a (e+1)) ε (E e) G` for the cylinders and
`Thickening.cylinderThick (a i) (a i) ε (V i) G` for the vertex strips, map into `P.thick` by
presentation morphisms `edgeIncl e` and `vertexIncl i`: a slice point goes to its class in the
window. After the per-piece homeomorphisms of #707 they become the evident maps
`(y, s, t) ↦ ([y, s], t)` and `(v, t) ↦ ([v], t)` (`toProd_realize_edgeIncl`,
`toProd_realize_vertexIncl`).

The inverse is assembled on the thickened raw pieces: `rawInv` pushes the inverses of the per-piece
homeomorphisms into `P.thick` by `Hom.realize`. It satisfies the two endpoint identifications of `P`
(`rawInv_segBot`, `rawInv_segTop`): both sides of an identification are window points with the same
image in `X`, so they are equal in the window. Hence it depends only on normal forms
(`rawInv_nf`) and descends along the quotient map `quotMk × id : Raw × [-ε, ε] → X × [-ε, ε]`
(`isQuotientMap_rawBandMap`) to the continuous `ofProd`. This is the colimit description of
`X × [-ε, ε]` by its thickened pieces, used through the quotient map and the universal property
of the realization. Both inverse laws are checked on generators
(`toProd_ofProd`, `ofProd_toProd`); no compactness or Hausdorff argument is used.

## The main statement

`thickHomeomorph : (P.thick S ε G hG).Realization G ≃ₜ P.Realization S × Band ε` is a
height-preserving homeomorphism (`height_thickHomeomorph`), with the inverse at generators given by
`thickHomeomorph_symm_quotMk`, `thickHomeomorph_symm_windowToSpace_value` and
`thickHomeomorph_symm_windowToSpace_of_mem_K`. On the shifted witness `S.shifted ε`, whose levels
are the distinct values of `(S - ε) ∪ (S + ε)`, it is `shiftedThick` and
`shiftedThickHomeomorph`.

See `docs/math/reeb-thickening-constructible.md`.
-/

open Set Topology
open scoped NNReal

universe u

namespace TDA.Reeb

noncomputable section

open GeometricThickening (Band)
open RGraph (fragAff TransferOK)

/-! ### The inverse of one cylinder at generators -/

namespace Thickening

section Symm

variable {a d : ℝ} {ε : ℝ≥0} (E : Type*) [TopologicalSpace E] {m : ℕ}
  {G : CriticalValues m} (hG : G.HasEvents a d ε)

/-- The inverse of the one-cylinder homeomorphism at a point of height a level of the grid is a
vertex point. -/
theorem cylinderThickHomeomorph_symm_of_eq_value (j : Fin (m + 1)) (y : E) (s : Icc a d)
    (t : Band ε) (hs : (s : ℝ) ∈ slice a d ε (G.value j)) (ht : (s : ℝ) + t = G.value j) :
    (cylinderThickHomeomorph a d ε E G hG).symm (y, s, t) =
      (cylinderThick a d ε E G hG).ofVertex G j (y, ⟨s, hs⟩) :=
  (Homeomorph.symm_apply_eq _).2 (Prod.ext rfl (Prod.ext rfl (Subtype.ext
    (show (t : ℝ) = G.value j - s by linarith))))

/-- The inverse of the one-cylinder homeomorphism at a point of a closed slab is a cylinder point:
`(y, s, t)` with `s = fragAff (mid k) u σ` and `s + t = u` comes from `((y, σ), u)`. -/
theorem cylinderThickHomeomorph_symm_of_mem_seg (k : Fin m) (y : E) (σ : slice a d ε (G.mid k))
    (u : CylinderPresentation.Seg G k) (s : Icc a d) (t : Band ε)
    (hs : (s : ℝ) = fragAff a d ε (G.mid k) u σ) (ht : (s : ℝ) + t = u) :
    (cylinderThickHomeomorph a d ε E G hG).symm (y, s, t) =
      (cylinderThick a d ε E G hG).ofCylinder G k ((y, σ), u) :=
  (Homeomorph.symm_apply_eq _).2 (Prod.ext rfl (Prod.ext (Subtype.ext hs) (Subtype.ext
    (show (t : ℝ) = u - fragAff a d ε (G.mid k) u σ by rw [← hs]; linarith))))

end Symm

end Thickening

namespace CylinderPresentation

open Thickening

attribute [local instance] RGraph.locallyPathConnectedSpace_Icc

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n) (ε : ℝ≥0)
  {m : ℕ} (G : CriticalValues m) (hG : S.ContainsShifted ε G)

/-! ### The presentation -/

/-- **The thickening presentation** `P_ε` on a grid listing the shifted levels: vertex piece `j`
is the window at the level `b j`, edge piece `k` the window at the midpoint of slab `k`, and the
endpoint maps are the window transfers to the two slab ends. -/
def thick : CylinderPresentation.{u} m where
  V j := P.Window S ε (G.value j)
  E k := P.Window S ε (G.mid k)
  left k := P.transfer S ε (hG.transferOK_of_mem (G.mid_mem_K k) (segBot G k).2)
  right k := P.transfer S ε (hG.transferOK_of_mem (G.mid_mem_K k) (segTop G k).2)

theorem thick_left_apply (k : Fin m) (ξ : (P.thick S ε G hG).E k) :
    (P.thick S ε G hG).left k ξ =
      P.transfer S ε (hG.transferOK_of_mem (G.mid_mem_K k) (segBot G k).2) ξ :=
  rfl

theorem thick_right_apply (k : Fin m) (ξ : (P.thick S ε G hG).E k) :
    (P.thick S ε G hG).right k ξ =
      P.transfer S ε (hG.transferOK_of_mem (G.mid_mem_K k) (segTop G k).2) ξ :=
  rfl

instance instCompactSpaceThickV [∀ i, CompactSpace (P.V i)] [∀ e, CompactSpace (P.E e)]
    (j : Fin (m + 1)) : CompactSpace ((P.thick S ε G hG).V j) :=
  inferInstanceAs (CompactSpace (P.Window S ε (G.value j)))

instance instCompactSpaceThickE [∀ i, CompactSpace (P.V i)] [∀ e, CompactSpace (P.E e)]
    (k : Fin m) : CompactSpace ((P.thick S ε G hG).E k) :=
  inferInstanceAs (CompactSpace (P.Window S ε (G.mid k)))

instance instLocallyPathConnectedSpaceThickV [∀ i, LocallyPathConnectedSpace (P.V i)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] (j : Fin (m + 1)) :
    LocallyPathConnectedSpace ((P.thick S ε G hG).V j) :=
  inferInstanceAs (LocallyPathConnectedSpace (P.Window S ε (G.value j)))

instance instLocallyPathConnectedSpaceThickE [∀ i, LocallyPathConnectedSpace (P.V i)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] (k : Fin m) :
    LocallyPathConnectedSpace ((P.thick S ε G hG).E k) :=
  inferInstanceAs (LocallyPathConnectedSpace (P.Window S ε (G.mid k)))

/-! ### The comparison map -/

/-- The band `{(x, u) | u - ε ≤ f x ≤ u + ε}` of the realization: the codomain of
`GeometricThickening.bandHomeomorph (P.height S) ε`. -/
abbrev BandSpace : Type u :=
  {p : P.Realization S × ℝ // p.2 - ε ≤ P.height S p.1 ∧ P.height S p.1 ≤ p.2 + ε}

/-- **The joint slab cylinder** `W(mid k) × [b k, b (k+1)] → BandSpace`,
`(ξ, u) ↦ (transfer ξ, u)`: DMP's `α_k (ξ, u) = (α_k^u ξ, u)`, continuous by the joint
transfer `transferFamily`. -/
def slabCylinder (k : Fin m) : C(P.Window S ε (G.mid k) × Seg G k, P.BandSpace S ε) where
  toFun p := ⟨(P.transferFamily S ε (G.mid k)
      (fun u : Seg G k => hG.transferOK_of_mem (G.mid_mem_K k) u.2) p, (p.2 : ℝ)),
    P.height_transferFamily_mem S ε (G.mid k) _ p⟩
  continuous_toFun := ((P.transferFamily S ε (G.mid k) _).continuous.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem coe_slabCylinder (k : Fin m) (ξ : P.Window S ε (G.mid k)) (u : Seg G k) :
    (P.slabCylinder S ε G hG k (ξ, u) : P.Realization S × ℝ) =
      (P.windowToSpace S ε u (P.transfer S ε (hG.transferOK_of_mem (G.mid_mem_K k) u.2) ξ),
        (u : ℝ)) :=
  rfl

/-- The compatible maps into the band: a vertex point at its level, a cylinder point by the joint
slab cylinder. -/
def toBandMaps : (P.thick S ε G hG).CompatibleMaps G (P.BandSpace S ε) where
  vertex j := ⟨fun ξ => ⟨(P.windowToSpace S ε (G.value j) ξ, G.value j),
      P.height_windowToSpace_mem S ε (G.value j) ξ⟩,
    ((P.windowToSpace S ε (G.value j)).continuous.prodMk continuous_const).subtype_mk _⟩
  cylinder k := P.slabCylinder S ε G hG k
  segBot_eq _ _ := rfl
  segTop_eq _ _ := rfl

/-- The comparison map from the realization of `P_ε` to the band. -/
def toBand : C((P.thick S ε G hG).Realization G, P.BandSpace S ε) :=
  lift (P.toBandMaps S ε G hG)

/-- The comparison map preserves height: its second coordinate is the height of `P_ε`. -/
theorem toBand_snd (x : (P.thick S ε G hG).Realization G) :
    (P.toBand S ε G hG x : P.Realization S × ℝ).2 = (P.thick S ε G hG).height G x := by
  obtain ⟨r, rfl⟩ := (P.thick S ε G hG).quotMk_surjective G x
  rcases r with ⟨j, ξ⟩ | ⟨k, ξ, u⟩ <;> rfl

/-- **The comparison map** `|P_ε| → X × [-ε, ε]`: a vertex point `ξ` of level `b j` goes to
`(ξ, b j - f ξ)`, a cylinder point `(ξ, u)` to `(transfer ξ, u - f (transfer ξ))`. -/
def toProd : C((P.thick S ε G hG).Realization G, P.Realization S × Band ε) :=
  (⟨_, (GeometricThickening.bandHomeomorph (P.height S) ε).symm.continuous⟩ :
    C(P.BandSpace S ε, P.Realization S × Band ε)).comp (P.toBand S ε G hG)

@[simp] theorem toProd_ofVertex (j : Fin (m + 1)) (ξ : P.Window S ε (G.value j)) :
    P.toProd S ε G hG ((P.thick S ε G hG).ofVertex G j ξ) =
      (P.windowToSpace S ε _ ξ, ⟨G.value j - P.height S (P.windowToSpace S ε _ ξ),
        GeometricThickening.sub_mem_band _ (P.height_windowToSpace_mem S ε _ ξ)⟩) :=
  rfl

@[simp] theorem toProd_ofCylinder (k : Fin m) (ξ : P.Window S ε (G.mid k)) (u : Seg G k) :
    P.toProd S ε G hG ((P.thick S ε G hG).ofCylinder G k (ξ, u)) =
      (P.windowToSpace S ε u (P.transfer S ε (hG.transferOK_of_mem (G.mid_mem_K k) u.2) ξ),
        ⟨u - P.height S (P.windowToSpace S ε u
            (P.transfer S ε (hG.transferOK_of_mem (G.mid_mem_K k) u.2) ξ)),
          GeometricThickening.sub_mem_band _ (P.height_windowToSpace_mem S ε _ _)⟩) :=
  rfl

/-- **Height preservation.** The comparison map carries the height of `P_ε` to the thickened
height `f x + t`. -/
theorem height_toProd (x : (P.thick S ε G hG).Realization G) :
    GeometricThickening.height (P.height S) ε (P.toProd S ε G hG x) =
      (P.thick S ε G hG).height G x := by
  rw [← GeometricThickening.snd_bandHomeomorph]
  show ((GeometricThickening.bandHomeomorph (P.height S) ε)
    ((GeometricThickening.bandHomeomorph (P.height S) ε).symm (P.toBand S ε G hG x)) :
      P.Realization S × ℝ).2 = _
  rw [Homeomorph.apply_symm_apply]
  exact P.toBand_snd S ε G hG x

/-! ### The attachment maps -/

/-- **The cylinder attachment.** The thickening presentation of the cylinder `E e × [a e, a (e+1)]`
on the common grid maps into `P_ε`: a slice point `(y, σ)` goes to its class in the window. -/
def edgeIncl (e : Fin n) :
    (cylinderThick (S.value e.castSucc) (S.value e.succ) ε (P.E e) G
      (hG.hasEvents_edge e)).Hom (P.thick S ε G hG) where
  vertex j := ⟨fun p => P.windowMk S ε (G.value j) (.inr ⟨e, p.1, p.2⟩),
    (P.continuous_windowMk S ε _).comp
      (continuous_inr.comp (continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd)))⟩
  edge k := ⟨fun p => P.windowMk S ε (G.mid k) (.inr ⟨e, p.1, p.2⟩),
    (P.continuous_windowMk S ε _).comp
      (continuous_inr.comp (continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd)))⟩
  left_comm _ _ := rfl
  right_comm _ _ := rfl

/-- **The vertex attachment.** The thickening presentation of the vertex strip `V i × {a i}` on
the common grid maps into `P_ε`: a slice point `(v, σ)` goes to its class in the window. -/
def vertexIncl (i : Fin (n + 1)) :
    (cylinderThick (S.value i) (S.value i) ε (P.V i) G
      (hG.hasEvents_vertex i)).Hom (P.thick S ε G hG) where
  vertex j := ⟨fun p => P.windowMk S ε (G.value j) (.inl ⟨i, p.1, p.2⟩),
    (P.continuous_windowMk S ε _).comp
      (continuous_inl.comp (continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd)))⟩
  edge k := ⟨fun p => P.windowMk S ε (G.mid k) (.inl ⟨i, p.1, p.2⟩),
    (P.continuous_windowMk S ε _).comp
      (continuous_inl.comp (continuous_sigmaMk.comp (continuous_fst.prodMk continuous_snd)))⟩
  left_comm _ _ := rfl
  right_comm _ _ := rfl

@[simp] theorem edgeIncl_vertex_apply (e : Fin n) (j : Fin (m + 1))
    (p : P.E e × slice (S.value e.castSucc) (S.value e.succ) ε (G.value j)) :
    (P.edgeIncl S ε G hG e).vertex j p = P.windowMk S ε (G.value j) (.inr ⟨e, p.1, p.2⟩) :=
  rfl

@[simp] theorem edgeIncl_edge_apply (e : Fin n) (k : Fin m)
    (p : P.E e × slice (S.value e.castSucc) (S.value e.succ) ε (G.mid k)) :
    (P.edgeIncl S ε G hG e).edge k p = P.windowMk S ε (G.mid k) (.inr ⟨e, p.1, p.2⟩) :=
  rfl

@[simp] theorem vertexIncl_vertex_apply (i : Fin (n + 1)) (j : Fin (m + 1))
    (p : P.V i × slice (S.value i) (S.value i) ε (G.value j)) :
    (P.vertexIncl S ε G hG i).vertex j p = P.windowMk S ε (G.value j) (.inl ⟨i, p.1, p.2⟩) :=
  rfl

@[simp] theorem vertexIncl_edge_apply (i : Fin (n + 1)) (k : Fin m)
    (p : P.V i × slice (S.value i) (S.value i) ε (G.mid k)) :
    (P.vertexIncl S ε G hG i).edge k p = P.windowMk S ε (G.mid k) (.inl ⟨i, p.1, p.2⟩) :=
  rfl

/-- **The cylinder square.** After the one-cylinder homeomorphism, the cylinder attachment followed
by the comparison map is `(y, s, t) ↦ ([y, s], t)`. -/
theorem toProd_realize_edgeIncl (e : Fin n)
    (z : (cylinderThick (S.value e.castSucc) (S.value e.succ) ε (P.E e) G
      (hG.hasEvents_edge e)).Realization G) :
    P.toProd S ε G hG ((P.edgeIncl S ε G hG e).realize G z) =
      (P.ofCylinder S e ((cylinderThickHomeomorph _ _ ε (P.E e) G (hG.hasEvents_edge e) z).1,
          (cylinderThickHomeomorph _ _ ε (P.E e) G (hG.hasEvents_edge e) z).2.1),
        (cylinderThickHomeomorph _ _ ε (P.E e) G (hG.hasEvents_edge e) z).2.2) := by
  obtain ⟨r, rfl⟩ :=
    (cylinderThick _ _ ε (P.E e) G (hG.hasEvents_edge e)).quotMk_surjective G z
  rcases r with ⟨j, p⟩ | ⟨k, p⟩ <;> rfl

/-- **The vertex square.** After the vertex strip homeomorphism, the vertex attachment followed by
the comparison map is `(v, t) ↦ ([v], t)`. -/
theorem toProd_realize_vertexIncl (i : Fin (n + 1))
    (z : (cylinderThick (S.value i) (S.value i) ε (P.V i) G
      (hG.hasEvents_vertex i)).Realization G) :
    P.toProd S ε G hG ((P.vertexIncl S ε G hG i).realize G z) =
      (P.ofVertex S i (vertexStripHomeomorph _ ε (P.V i) G (hG.hasEvents_vertex i) z).1,
        (vertexStripHomeomorph _ ε (P.V i) G (hG.hasEvents_vertex i) z).2) := by
  obtain ⟨r, rfl⟩ :=
    (cylinderThick _ _ ε (P.V i) G (hG.hasEvents_vertex i)).quotMk_surjective G z
  rcases r with ⟨j, v, σ⟩ | ⟨k, ⟨v, σ⟩, u⟩
  · refine Prod.ext rfl (Subtype.ext ?_)
    show G.value j - S.value i = G.value j - σ
    rw [eq_of_mem_slice_self σ.2]
  · refine Prod.ext rfl (Subtype.ext ?_)
    show (u : ℝ) - S.value i = u - fragAff (S.value i) (S.value i) ε (G.mid k) u σ
    have h : fragAff (S.value i) (S.value i) ε (G.mid k) u σ = S.value i :=
      eq_of_mem_slice_self (slabTransfer _ _ ε G (hG.hasEvents_vertex i) k u σ).2
    rw [h]

/-! ### The inverse on the thickened raw pieces -/

/-- **The inverse on the thickened raw pieces**: on a vertex piece the inverse of the vertex strip
homeomorphism, on a cylinder the inverse of the one-cylinder homeomorphism, pushed into `P_ε` by
the attachment maps. -/
def rawInv : C(P.Raw S × Band ε, (P.thick S ε G hG).Realization G) where
  toFun := Sum.elim
      ((fun q : Σ i, P.V i × Band ε => (P.vertexIncl S ε G hG q.1).realize G
          ((vertexStripHomeomorph _ ε (P.V q.1) G (hG.hasEvents_vertex q.1)).symm q.2)) ∘
        Homeomorph.sigmaProdDistrib)
      ((fun q : Σ e, P.Cylinder S e × Band ε => (P.edgeIncl S ε G hG q.1).realize G
          ((cylinderThickHomeomorph _ _ ε (P.E q.1) G (hG.hasEvents_edge q.1)).symm
            (q.2.1.1, q.2.1.2, q.2.2))) ∘
        Homeomorph.sigmaProdDistrib) ∘ Homeomorph.sumProdDistrib
  continuous_toFun := by
    refine (Continuous.sumElim ?_ ?_).comp Homeomorph.sumProdDistrib.continuous
    · refine Continuous.comp ?_ Homeomorph.sigmaProdDistrib.continuous
      exact continuous_sigma fun i => ((P.vertexIncl S ε G hG i).realize G).continuous.comp
        (vertexStripHomeomorph _ ε (P.V i) G (hG.hasEvents_vertex i)).symm.continuous
    · refine Continuous.comp ?_ Homeomorph.sigmaProdDistrib.continuous
      exact continuous_sigma fun e => ((P.edgeIncl S ε G hG e).realize G).continuous.comp
        ((cylinderThickHomeomorph _ _ ε (P.E e) G (hG.hasEvents_edge e)).symm.continuous.comp
          ((continuous_fst.comp continuous_fst).prodMk
            ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

@[simp] theorem rawInv_inl (i : Fin (n + 1)) (v : P.V i) (t : Band ε) :
    P.rawInv S ε G hG (.inl ⟨i, v⟩, t) = (P.vertexIncl S ε G hG i).realize G
      ((vertexStripHomeomorph _ ε (P.V i) G (hG.hasEvents_vertex i)).symm (v, t)) :=
  rfl

@[simp] theorem rawInv_inr (e : Fin n) (y : P.E e) (s : Seg S e) (t : Band ε) :
    P.rawInv S ε G hG (.inr ⟨e, y, s⟩, t) = (P.edgeIncl S ε G hG e).realize G
      ((cylinderThickHomeomorph _ _ ε (P.E e) G (hG.hasEvents_edge e)).symm (y, s, t)) :=
  rfl

/-- The band coordinate `c - f r` of a raw window point `r` at height `c`. -/
theorem sub_rawHeight_mem_band {c : ℝ} (r : P.WindowRaw S ε c) :
    c - P.rawHeight S (P.windowIncl S ε c r) ∈ Band ε := by
  have h := P.rawHeight_windowIncl_mem S ε c r
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- A raw window point `r` at height `c` as a thickened raw point `(r, c - f r)`. -/
def windowBand (c : ℝ) (r : P.WindowRaw S ε c) : P.Raw S × Band ε :=
  (P.windowIncl S ε c r,
    ⟨c - P.rawHeight S (P.windowIncl S ε c r), P.sub_rawHeight_mem_band S ε r⟩)

/-- **The inverse at a level.** A thickened raw point of height a level `b j` goes to the vertex
point of its window class. -/
theorem rawInv_windowBand_value (j : Fin (m + 1)) (r : P.WindowRaw S ε (G.value j)) :
    P.rawInv S ε G hG (P.windowBand S ε _ r) =
      (P.thick S ε G hG).ofVertex G j (P.windowMk S ε _ r) := by
  rcases r with ⟨i, v, σ⟩ | ⟨e, y, σ⟩
  · have hσ : (σ : ℝ) = S.value i := eq_of_mem_slice_self σ.2
    have hs : S.value i ∈ slice (S.value i) (S.value i) ε (G.value j) := by
      have := σ.2
      rwa [hσ] at this
    have h := cylinderThickHomeomorph_symm_of_eq_value (P.V i) (hG.hasEvents_vertex i) j v
      ⟨S.value i, left_mem_Icc.2 le_rfl⟩
      ⟨G.value j - S.value i, P.sub_rawHeight_mem_band S ε (.inl ⟨i, v, σ⟩)⟩ hs (by ring)
    refine (congrArg ((P.vertexIncl S ε G hG i).realize G) h).trans ?_
    exact congrArg
      (fun σ => (P.thick S ε G hG).ofVertex G j (P.windowMk S ε _ (.inl ⟨i, v, σ⟩)))
      (Subtype.ext hσ.symm)
  · have h := cylinderThickHomeomorph_symm_of_eq_value (P.E e) (hG.hasEvents_edge e) j y
      ⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩
      ⟨G.value j - σ, P.sub_rawHeight_mem_band S ε (.inr ⟨e, y, σ⟩)⟩ σ.2 (by ring)
    exact congrArg ((P.edgeIncl S ε G hG e).realize G) h

/-- **The inverse over an open slab.** A thickened raw point of height `u` in the open slab `k`
goes to the cylinder point of slab `k` whose window class at the midpoint transfers to it. -/
theorem rawInv_windowBand_of_mem_K (k : Fin m) {u : ℝ} (hu : u ∈ (G.K k : Set ℝ))
    (r : P.WindowRaw S ε u) :
    P.rawInv S ε G hG (P.windowBand S ε u r) =
      (P.thick S ε G hG).ofCylinder G k (P.windowMk S ε _ (P.rawTransfer S ε
        (hG.transferOK_of_mem hu (Ioo_subset_Icc_self (G.mid_mem_K k))) r),
          ⟨u, Ioo_subset_Icc_self hu⟩) := by
  rcases r with ⟨i, v, σ⟩ | ⟨e, y, σ⟩
  · have hT := (hG.hasEvents_vertex i).sliceTransfer_of_mem hu
      (Ioo_subset_Icc_self (G.mid_mem_K k))
    let σ' : slice (S.value i) (S.value i) ε (G.mid k) :=
      ⟨fragAff (S.value i) (S.value i) ε u (G.mid k) σ, hT.fragAff_mem σ.2⟩
    have hs : S.value i = fragAff (S.value i) (S.value i) ε (G.mid k) u σ' :=
      (eq_of_mem_slice_self (slabTransfer _ _ ε G (hG.hasEvents_vertex i) k
        ⟨u, Ioo_subset_Icc_self hu⟩ σ').2).symm
    have h := cylinderThickHomeomorph_symm_of_mem_seg (P.V i) (hG.hasEvents_vertex i) k v σ'
      ⟨u, Ioo_subset_Icc_self hu⟩ ⟨S.value i, left_mem_Icc.2 le_rfl⟩
      ⟨u - S.value i, P.sub_rawHeight_mem_band S ε (.inl ⟨i, v, σ⟩)⟩ hs (by ring)
    exact congrArg ((P.vertexIncl S ε G hG i).realize G) h
  · have hT := (hG.hasEvents_edge e).sliceTransfer_of_mem hu
      (Ioo_subset_Icc_self (G.mid_mem_K k))
    have hT' := (hG.hasEvents_edge e).sliceTransfer_of_mem (G.mid_mem_K k)
      (Ioo_subset_Icc_self hu)
    let σ' : slice (S.value e.castSucc) (S.value e.succ) ε (G.mid k) :=
      ⟨fragAff (S.value e.castSucc) (S.value e.succ) ε u (G.mid k) σ, hT.fragAff_mem σ.2⟩
    have h := cylinderThickHomeomorph_symm_of_mem_seg (P.E e) (hG.hasEvents_edge e) k y σ'
      ⟨u, Ioo_subset_Icc_self hu⟩ ⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩
      ⟨u - σ, P.sub_rawHeight_mem_band S ε (.inr ⟨e, y, σ⟩)⟩
      (hT.fragAff_fragAff hT' σ.2).symm (by ring)
    exact congrArg ((P.edgeIncl S ε G hG e).realize G) h

/-- The inverse at a height that is a level or lies in an open slab depends only on the window
class. -/
theorem rawInv_windowBand_congr {c : ℝ}
    (hc : (∃ j, G.value j = c) ∨ ∃ k, c ∈ (G.K k : Set ℝ)) {r r' : P.WindowRaw S ε c}
    (h : P.windowMk S ε c r = P.windowMk S ε c r') :
    P.rawInv S ε G hG (P.windowBand S ε c r) = P.rawInv S ε G hG (P.windowBand S ε c r') := by
  rcases hc with ⟨j, rfl⟩ | ⟨k, hk⟩
  · rw [rawInv_windowBand_value, rawInv_windowBand_value, h]
  · rw [P.rawInv_windowBand_of_mem_K S ε G hG k hk, P.rawInv_windowBand_of_mem_K S ε G hG k hk,
      P.windowMk_rawTransfer_eq S ε _ h]

/-- Every height within `ε` of the segment of an edge is a level or lies in an open slab. -/
private theorem eq_value_or_mem_K_of_edge {S : CriticalValues n} {ε : ℝ≥0}
    {G : CriticalValues m} (hG : S.ContainsShifted ε G) (e : Fin n) {c : ℝ}
    (hc : c ∈ Icc (S.value e.castSucc - ε) (S.value e.succ + ε)) :
    (∃ j, G.value j = c) ∨ ∃ k, c ∈ (G.K k : Set ℝ) :=
  ((hG.hasEvents_edge e).eq_value_or_mem_K hc).imp id fun ⟨k, hk, _⟩ => ⟨k, hk⟩

/-- **The bottom identification.** The inverse identifies the bottom end `(y, a e)` of a thickened
cylinder with the thickened vertex point `left e y`: both are window points with the same image in
the realization. -/
theorem rawInv_segBot (e : Fin n) (y : P.E e) (t : Band ε) :
    P.rawInv S ε G hG (.inr ⟨e, y, segBot S e⟩, t) =
      P.rawInv S ε G hG (.inl ⟨e.castSucc, P.left e y⟩, t) := by
  have had := (S.value_castSucc_lt_succ e).le
  have h1 : S.value e.castSucc ∈
      slice (S.value e.castSucc) (S.value e.succ) ε (S.value e.castSucc + t) :=
    mem_slice_iff.2 ⟨left_mem_Icc.2 had, by linarith [t.2.2], by linarith [t.2.1]⟩
  have h2 : S.value e.castSucc ∈
      slice (S.value e.castSucc) (S.value e.castSucc) ε (S.value e.castSucc + t) :=
    mem_slice_iff.2 ⟨left_mem_Icc.2 le_rfl, by linarith [t.2.2], by linarith [t.2.1]⟩
  have hr : ((.inr ⟨e, y, segBot S e⟩ : P.Raw S), t) =
      P.windowBand S ε _ (.inr ⟨e, y, ⟨_, h1⟩⟩) :=
    Prod.ext rfl (Subtype.ext
      (show (t : ℝ) = S.value e.castSucc + t - S.value e.castSucc by ring))
  have hr' : ((.inl ⟨e.castSucc, P.left e y⟩ : P.Raw S), t) =
      P.windowBand S ε _ (.inl ⟨e.castSucc, P.left e y, ⟨_, h2⟩⟩) :=
    Prod.ext rfl (Subtype.ext
      (show (t : ℝ) = S.value e.castSucc + t - S.value e.castSucc by ring))
  rw [hr, hr']
  refine P.rawInv_windowBand_congr S ε G hG (eq_value_or_mem_K_of_edge hG e
    ⟨by linarith [t.2.1], by linarith [t.2.2]⟩) ((P.windowMk_eq_iff S ε _).2 ?_)
  exact P.nf_segBot S e y

/-- **The top identification.** The inverse identifies the top end `(y, a (e+1))` of a thickened
cylinder with the thickened vertex point `right e y`. -/
theorem rawInv_segTop (e : Fin n) (y : P.E e) (t : Band ε) :
    P.rawInv S ε G hG (.inr ⟨e, y, segTop S e⟩, t) =
      P.rawInv S ε G hG (.inl ⟨e.succ, P.right e y⟩, t) := by
  have had := (S.value_castSucc_lt_succ e).le
  have h1 : S.value e.succ ∈
      slice (S.value e.castSucc) (S.value e.succ) ε (S.value e.succ + t) :=
    mem_slice_iff.2 ⟨right_mem_Icc.2 had, by linarith [t.2.2], by linarith [t.2.1]⟩
  have h2 : S.value e.succ ∈ slice (S.value e.succ) (S.value e.succ) ε (S.value e.succ + t) :=
    mem_slice_iff.2 ⟨left_mem_Icc.2 le_rfl, by linarith [t.2.2], by linarith [t.2.1]⟩
  have hr : ((.inr ⟨e, y, segTop S e⟩ : P.Raw S), t) =
      P.windowBand S ε _ (.inr ⟨e, y, ⟨_, h1⟩⟩) :=
    Prod.ext rfl (Subtype.ext (show (t : ℝ) = S.value e.succ + t - S.value e.succ by ring))
  have hr' : ((.inl ⟨e.succ, P.right e y⟩ : P.Raw S), t) =
      P.windowBand S ε _ (.inl ⟨e.succ, P.right e y, ⟨_, h2⟩⟩) :=
    Prod.ext rfl (Subtype.ext (show (t : ℝ) = S.value e.succ + t - S.value e.succ by ring))
  rw [hr, hr']
  refine P.rawInv_windowBand_congr S ε G hG (eq_value_or_mem_K_of_edge hG e
    ⟨by linarith [t.2.1], by linarith [t.2.2]⟩) ((P.windowMk_eq_iff S ε _).2 ?_)
  exact P.nf_segTop S e y

/-- The inverse depends only on normal forms. -/
theorem rawInv_nf (x : P.Raw S) (t : Band ε) :
    P.rawInv S ε G hG (P.nf S x, t) = P.rawInv S ε G hG (x, t) := by
  rcases x with p | ⟨e, y, s⟩
  · rfl
  · simp only [nf, Sum.elim_inr, nfCyl]
    split_ifs with h₁ h₂
    · obtain rfl : s = segBot S e := Subtype.ext h₁
      exact (P.rawInv_segBot S ε G hG e y t).symm
    · obtain rfl : s = segTop S e := Subtype.ext h₂
      exact (P.rawInv_segTop S ε G hG e y t).symm
    · rfl

/-- The inverse is constant on the fibres of `quotMk × id`. -/
theorem rawInv_factorsThrough :
    Function.FactorsThrough (P.rawInv S ε G hG) (Prod.map (P.quotMk S) _root_.id) := by
  rintro ⟨x, t⟩ ⟨x', t'⟩ h
  obtain ⟨hx, ht⟩ := (P.prodMap_quotMk_eq_iff S).1 h
  dsimp only at hx ht
  subst ht
  rw [← P.rawInv_nf S ε G hG x, hx, P.rawInv_nf]

/-! ### The inverse and the homeomorphism -/

/-- `quotMk × id` as a continuous map. -/
private def rawBandMap : C(P.Raw S × Band ε, P.Realization S × Band ε) :=
  ⟨Prod.map (P.quotMk S) _root_.id, (P.continuous_quotMk S).prodMap continuous_id⟩

/-- **The inverse** `X × [-ε, ε] → |P_ε|`, descended from the thickened raw pieces along the
quotient map `quotMk × id`. -/
def ofProd : C(P.Realization S × Band ε, (P.thick S ε G hG).Realization G) :=
  IsQuotientMap.lift (f := P.rawBandMap S ε) (P.isQuotientMap_rawBandMap S ε) (P.rawInv S ε G hG)
    (P.rawInv_factorsThrough S ε G hG)

@[simp] theorem ofProd_quotMk (x : P.Raw S) (t : Band ε) :
    P.ofProd S ε G hG (P.quotMk S x, t) = P.rawInv S ε G hG (x, t) := by
  have h := DFunLike.congr_fun (IsQuotientMap.lift_comp (f := P.rawBandMap S ε)
    (P.isQuotientMap_rawBandMap S ε) (P.rawInv S ε G hG) (P.rawInv_factorsThrough S ε G hG))
    (x, t)
  rw [ContinuousMap.comp_apply] at h
  exact h

theorem toProd_ofProd (p : P.Realization S × Band ε) :
    P.toProd S ε G hG (P.ofProd S ε G hG p) = p := by
  obtain ⟨⟨x, t⟩, rfl⟩ := (P.isQuotientMap_rawBandMap S ε).surjective p
  change P.toProd S ε G hG (P.ofProd S ε G hG (P.quotMk S x, t)) = (P.quotMk S x, t)
  rw [ofProd_quotMk]
  rcases x with ⟨i, v⟩ | ⟨e, y, s⟩
  · rw [rawInv_inl, toProd_realize_vertexIncl, Homeomorph.apply_symm_apply]
    rfl
  · rw [rawInv_inr, toProd_realize_edgeIncl, Homeomorph.apply_symm_apply]
    rfl

theorem ofProd_toProd (x : (P.thick S ε G hG).Realization G) :
    P.ofProd S ε G hG (P.toProd S ε G hG x) = x := by
  refine DFunLike.congr_fun (hom_ext (g := (P.ofProd S ε G hG).comp (P.toProd S ε G hG))
    (g' := ContinuousMap.id _) (fun j ξ => ?_) fun k p => ?_) x
  · obtain ⟨r, rfl⟩ := P.windowMk_surjective S ε _ ξ
    exact (P.ofProd_quotMk S ε G hG _ _).trans (P.rawInv_windowBand_value S ε G hG j r)
  · obtain ⟨ξ, u⟩ := p
    obtain ⟨r, rfl⟩ := P.windowMk_surjective S ε _ ξ
    have hok := hG.transferOK_of_mem (G.mid_mem_K k) u.2
    have h0 : (P.ofProd S ε G hG).comp (P.toProd S ε G hG)
        ((P.thick S ε G hG).ofCylinder G k (P.windowMk S ε _ r, u)) =
          P.rawInv S ε G hG (P.windowBand S ε u (P.rawTransfer S ε hok r)) :=
      P.ofProd_quotMk S ε G hG _ _
    rw [h0]
    rcases eq_or_lt_of_le u.2.1 with hb | hb
    · obtain rfl : u = segBot G k := Subtype.ext hb.symm
      refine (P.rawInv_windowBand_value S ε G hG k.castSucc (P.rawTransfer S ε hok r)).trans ?_
      exact ((P.thick S ε G hG).ofCylinder_segBot G k (P.windowMk S ε _ r)).symm
    rcases eq_or_lt_of_le u.2.2 with ht | ht
    · obtain rfl : u = segTop G k := Subtype.ext ht
      refine (P.rawInv_windowBand_value S ε G hG k.succ (P.rawTransfer S ε hok r)).trans ?_
      exact ((P.thick S ε G hG).ofCylinder_segTop G k (P.windowMk S ε _ r)).symm
    · refine (P.rawInv_windowBand_of_mem_K S ε G hG k ⟨hb, ht⟩ _).trans ?_
      rw [rawTransfer_rawTransfer]
      rfl

/-- **Issue #708.** The realization of the thickening presentation is homeomorphic to the
thickening `X × [-ε, ε]` of the realization, for every presentation with arbitrary topological
pieces, every `ε ≥ 0` and every grid listing the shifted levels. -/
def thickHomeomorph : (P.thick S ε G hG).Realization G ≃ₜ P.Realization S × Band ε where
  toFun := P.toProd S ε G hG
  invFun := P.ofProd S ε G hG
  left_inv := P.ofProd_toProd S ε G hG
  right_inv := P.toProd_ofProd S ε G hG
  continuous_toFun := (P.toProd S ε G hG).continuous
  continuous_invFun := (P.ofProd S ε G hG).continuous

@[simp] theorem coe_thickHomeomorph : ⇑(P.thickHomeomorph S ε G hG) = P.toProd S ε G hG :=
  rfl

@[simp] theorem coe_thickHomeomorph_symm :
    ⇑(P.thickHomeomorph S ε G hG).symm = P.ofProd S ε G hG :=
  rfl

/-- **Height preservation.** The homeomorphism carries the height of `P_ε` to the thickened height
`f x + t`. -/
theorem height_thickHomeomorph (x : (P.thick S ε G hG).Realization G) :
    GeometricThickening.height (P.height S) ε (P.thickHomeomorph S ε G hG x) =
      (P.thick S ε G hG).height G x :=
  P.height_toProd S ε G hG x

/-- The inverse homeomorphism preserves height. -/
theorem height_thickHomeomorph_symm (p : P.Realization S × Band ε) :
    (P.thick S ε G hG).height G ((P.thickHomeomorph S ε G hG).symm p) =
      GeometricThickening.height (P.height S) ε p := by
  rw [← height_thickHomeomorph, Homeomorph.apply_symm_apply]

/-- The inverse at a thickened raw point. -/
theorem thickHomeomorph_symm_quotMk (x : P.Raw S) (t : Band ε) :
    (P.thickHomeomorph S ε G hG).symm (P.quotMk S x, t) = P.rawInv S ε G hG (x, t) :=
  P.ofProd_quotMk S ε G hG x t

/-- **The inverse at a level.** A point `(ξ, b j - f ξ)` of thickened height the level `b j` comes
from the vertex point `ξ` of the window at `b j`. -/
theorem thickHomeomorph_symm_windowToSpace_value (j : Fin (m + 1))
    (ξ : P.Window S ε (G.value j)) :
    (P.thickHomeomorph S ε G hG).symm (P.windowToSpace S ε _ ξ,
        ⟨G.value j - P.height S (P.windowToSpace S ε _ ξ),
          GeometricThickening.sub_mem_band _ (P.height_windowToSpace_mem S ε _ ξ)⟩) =
      (P.thick S ε G hG).ofVertex G j ξ :=
  (Homeomorph.symm_apply_eq _).2 rfl

/-- **The inverse over an open slab.** A point `(ξ, u - f ξ)` of thickened height `u` in the open
slab `k` comes from the cylinder point `(transfer ξ, u)`, where the transfer moves `ξ` to the
window at the midpoint. -/
theorem thickHomeomorph_symm_windowToSpace_of_mem_K (k : Fin m) {u : ℝ}
    (hu : u ∈ (G.K k : Set ℝ)) (ξ : P.Window S ε u) :
    (P.thickHomeomorph S ε G hG).symm (P.windowToSpace S ε _ ξ,
        ⟨u - P.height S (P.windowToSpace S ε _ ξ),
          GeometricThickening.sub_mem_band _ (P.height_windowToSpace_mem S ε _ ξ)⟩) =
      (P.thick S ε G hG).ofCylinder G k (P.transfer S ε
        (hG.transferOK_of_mem hu (Ioo_subset_Icc_self (G.mid_mem_K k))) ξ,
          ⟨u, Ioo_subset_Icc_self hu⟩) := by
  refine (Homeomorph.symm_apply_eq _).2 ?_
  have h := P.transfer_transfer S ε (hG.transferOK_of_mem hu (Ioo_subset_Icc_self (G.mid_mem_K k)))
    (hG.transferOK_of_mem (G.mid_mem_K k) (Ioo_subset_Icc_self hu)) ξ
  rw [coe_thickHomeomorph, toProd_ofCylinder]
  exact Prod.ext (congrArg (P.windowToSpace S ε u) h.symm)
    (Subtype.ext (congrArg (fun ξ => u - P.height S (P.windowToSpace S ε u ξ)) h.symm))

/-! ### The shifted grid -/

/-- **The thickening presentation on the shifted witness**, whose levels are the distinct values of
`(S - ε) ∪ (S + ε)` in increasing order. -/
abbrev shiftedThick : CylinderPresentation.{u} (S.shiftedCount ε) :=
  P.thick S ε (S.shifted ε) (S.containsShifted_shifted ε)

/-- **Issue #708 on the shifted witness.** -/
def shiftedThickHomeomorph :
    (P.shiftedThick S ε).Realization (S.shifted ε) ≃ₜ P.Realization S × Band ε :=
  P.thickHomeomorph S ε (S.shifted ε) (S.containsShifted_shifted ε)

theorem height_shiftedThickHomeomorph (x : (P.shiftedThick S ε).Realization (S.shifted ε)) :
    GeometricThickening.height (P.height S) ε (P.shiftedThickHomeomorph S ε x) =
      (P.shiftedThick S ε).height (S.shifted ε) x :=
  P.height_thickHomeomorph S ε _ _ x

end CylinderPresentation

end

end TDA.Reeb
