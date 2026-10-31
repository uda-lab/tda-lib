import TDA.Reeb.ThickeningSlice
import TDA.Reeb.ConstructibleHom

/-!
# The thickening presentation of one cylinder

The thickening of a cylinder `E × [a, d]`, for `a ≤ d` and `ε ≥ 0`, as a finite cylinder
presentation (de Silva–Munch–Patel, *Categorified Reeb Graphs*, proof of Theorem 4.27), with no
hypothesis on the space `E`. The thickened space is `E × [a, d] × [-ε, ε]` with height `s + t`
(`cylinderHeight`), the thickening of `E × [a, d]` with the segment coordinate as height
(`cylinderHeight_eq`).

## The presentation

On any grid `G` listing the four events `a ± ε`, `d ± ε` (`G.HasEvents a d ε`),
`cylinderThick a d ε E G hG` has vertex piece `E × J(b j)` at level `b j` and edge piece
`E × J(mid k)` over slab `k`, where `J(u) = [max a (u - ε), min d (u + ε)]` is the slice of the
segment. The endpoint maps move the slice parameter by the affine transfer `RGraph.fragAff` to the
two slab ends (`slabTransfer`); at an end with a point slice they collapse the reference slice, and
no inverse is asked of them. A piece is empty exactly where its slice is. The pieces are compact
and locally path-connected when `E` is. A vertex strip is the case `a = d`, and `ε = 0` needs no
separate treatment.

## The homeomorphism

`toCylinder` sends a vertex point `(y, σ)` at level `b j` to `(y, σ, b j - σ)` and a cylinder
point `((y, σ), u)` to `(y, s, u - s)` with `s = fragAff (mid k) u σ`; it preserves height
(`cylinderHeight_toCylinder`). Its inverse `ofCylinder'` is built in the coordinates
`(s, u = s + t)` of the parallelogram (`bandParallelogramHomeomorph`). On each slab polygon it
descends `((y, σ), u) ↦ ofCylinder k ((y, σ), u)` along `id_E × polygonMap k`, which is a quotient
map for every `E` because the scalar polygon map is proper (`isQuotientMap_prodMap_polygonMap`);
on each level slice it is the vertex inclusion. The pieces agree on overlaps because a collapsed
slab end is identified with its vertex point in the realization, and they are pasted along the
finite closed cover. Both inverse laws hold, so `cylinderThickHomeomorph` is a height-preserving
homeomorphism (`cylinderHeight_cylinderThickHomeomorph`) for every topological space `E`, every
`ε ≥ 0` and every `a ≤ d`: no Hausdorff, compactness or nondegeneracy hypothesis is used. The
vertex strip `E × [-ε, ε]` with height `a + t` is `vertexStripHomeomorph`
(`height_vertexStripHomeomorph`).

## Boundary strips and naturality

On a common grid listing the events of `[a, d]`, `[a, a]` and `[d, d]`, the boundary strips are
presentation morphisms `botIncl : cylinderThick a a ε E → cylinderThick a d ε E` and
`topIncl : cylinderThick d d ε E → cylinderThick a d ε E`. Their endpoint equations are the boundary
compatibility of the slices: a slice parameter at the segment end `a` or `d` stays there under
every transfer. A continuous map `f : E → E'` gives `mapSpace f`, functorially (`mapSpace_id`,
`mapSpace_comp`), and the boundary inclusions are natural in `E` (`botIncl_comp_mapSpace`,
`topIncl_comp_mapSpace`). The homeomorphisms turn these morphisms into the evident maps: the strip
inclusion `(y, t) ↦ (y, a, t)` or `(y, d, t)` (`cylinderThickHomeomorph_realize_botIncl`,
`cylinderThickHomeomorph_realize_topIncl`) and `f × id` (`cylinderThickHomeomorph_realize_mapSpace`,
`vertexStripHomeomorph_realize_mapSpace`). In particular, for an endpoint map `f : E → V`, the
square formed by the bottom strip inclusion of `E × [a, d]` and `mapSpace f` into the vertex strip
of `V` commutes after the homeomorphisms.

## The shifted grid of one segment

For `a < d`, `pairThick` is the construction on the shifted witness of the two-level grid
`pair a d`, whose levels are exactly the distinct values among `a ± ε`, `d ± ε`
(`CriticalValues.range_shifted_pair`), with its homeomorphism `pairThickHomeomorph` and the
boundary strip inclusions `pairBotIncl`, `pairTopIncl` on that grid.

See `docs/math/reeb-thickening-constructible.md`.
-/

open Set Topology
open scoped NNReal

universe u v w

namespace TDA.Reeb

noncomputable section

open CylinderPresentation
open RGraph (fragAff)
open GeometricThickening (Band)

namespace Thickening

/-! ### Slice facts -/

section SliceFacts

variable {a d : ℝ} {ε : ℝ≥0}

/-- The thickening coordinate `u - s` of a slice parameter `s` at height `u` lies in the band. -/
theorem sub_mem_band_of_mem_slice {s u : ℝ} (hs : s ∈ slice a d ε u) : u - s ∈ Band ε := by
  have h := slice_subset_window a d ε u hs
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- A point of the parallelogram is a slice parameter at its height. -/
theorem mem_slice_of_mem_parallelogram {p : ℝ × ℝ} (hp : p ∈ parallelogram a d ε) :
    p.1 ∈ slice a d ε p.2 :=
  hp

/-- A parameter of the slice of the degenerate segment `[a, a]` is `a`. -/
theorem eq_of_mem_slice_self {s u : ℝ} (hs : s ∈ slice a a ε u) : s = a :=
  le_antisymm (slice_subset_Icc a a ε u hs).2 (slice_subset_Icc a a ε u hs).1

/-- The slice of the bottom strip `[a, a]` lies in the slice of `[a, d]`. -/
theorem slice_self_subset_left (had : a ≤ d) (u : ℝ) : slice a a ε u ⊆ slice a d ε u :=
  fun _ hs => ⟨hs.1, hs.2.trans (le_min ((min_le_left _ _).trans had) (min_le_right _ _))⟩

/-- The slice of the top strip `[d, d]` lies in the slice of `[a, d]`. -/
theorem slice_self_subset_right (had : a ≤ d) (u : ℝ) : slice d d ε u ⊆ slice a d ε u :=
  fun _ hs => ⟨(max_le (had.trans (le_max_left _ _)) (le_max_right _ _)).trans hs.1, hs.2⟩

end SliceFacts

/-! ### The presentation -/

section Presentation

variable (a d : ℝ) (ε : ℝ≥0) (E : Type u) [TopologicalSpace E] {m : ℕ} (G : CriticalValues m)
  (hG : G.HasEvents a d ε)

/-- The transfer of the reference slice at the midpoint of slab `k` to the slice at a height `u` of
the closed slab, by the affine fragment map. At a slab end with a point slice it is constant. -/
def slabTransfer (k : Fin m) (u : Seg G k) : C(slice a d ε (G.mid k), slice a d ε u) where
  toFun σ := ⟨fragAff a d ε (G.mid k) u σ,
    (hG.sliceTransfer_of_mem (G.mid_mem_K k) u.2).fragAff_mem σ.2⟩
  continuous_toFun := ((RGraph.continuous_fragAff a d ε (G.mid k)).comp
    (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

@[simp] theorem coe_slabTransfer (k : Fin m) (u : Seg G k) (σ : slice a d ε (G.mid k)) :
    (slabTransfer a d ε G hG k u σ : ℝ) = fragAff a d ε (G.mid k) u σ :=
  rfl

/-- **The thickening presentation of the cylinder `E × [a, d]`** (of the vertex strip `E × {a}`
when `a = d`) on a grid listing the four events: vertex piece `j` is `E × J(b j)`, edge piece `k`
is `E × J(mid k)`, and the endpoint maps transfer the slice parameter to the slab ends, collapsing
when the end slice is a point. Pieces are empty where the slice is. -/
def cylinderThick : CylinderPresentation.{u} m where
  V j := E × slice a d ε (G.value j)
  E k := E × slice a d ε (G.mid k)
  left k := (ContinuousMap.id E).prodMap (slabTransfer a d ε G hG k (segBot G k))
  right k := (ContinuousMap.id E).prodMap (slabTransfer a d ε G hG k (segTop G k))

theorem cylinderThick_left_apply (k : Fin m) (p : E × slice a d ε (G.mid k)) :
    (cylinderThick a d ε E G hG).left k p = (p.1, slabTransfer a d ε G hG k (segBot G k) p.2) :=
  rfl

theorem cylinderThick_right_apply (k : Fin m) (p : E × slice a d ε (G.mid k)) :
    (cylinderThick a d ε E G hG).right k p = (p.1, slabTransfer a d ε G hG k (segTop G k) p.2) :=
  rfl

instance instCompactSpaceCylinderThickV [CompactSpace E] (j : Fin (m + 1)) :
    CompactSpace ((cylinderThick a d ε E G hG).V j) :=
  inferInstanceAs (CompactSpace (E × slice a d ε (G.value j)))

instance instCompactSpaceCylinderThickE [CompactSpace E] (k : Fin m) :
    CompactSpace ((cylinderThick a d ε E G hG).E k) :=
  inferInstanceAs (CompactSpace (E × slice a d ε (G.mid k)))

instance instLocallyPathConnectedSpaceCylinderThickV [LocallyPathConnectedSpace E]
    (j : Fin (m + 1)) : LocallyPathConnectedSpace ((cylinderThick a d ε E G hG).V j) :=
  haveI := locallyPathConnectedSpace_slice a d ε (G.value j)
  inferInstanceAs (LocallyPathConnectedSpace (E × slice a d ε (G.value j)))

instance instLocallyPathConnectedSpaceCylinderThickE [LocallyPathConnectedSpace E] (k : Fin m) :
    LocallyPathConnectedSpace ((cylinderThick a d ε E G hG).E k) :=
  haveI := locallyPathConnectedSpace_slice a d ε (G.mid k)
  inferInstanceAs (LocallyPathConnectedSpace (E × slice a d ε (G.mid k)))

end Presentation

/-! ### The thickened cylinder and the parallelogram coordinates -/

section Space

variable (a d : ℝ) (ε : ℝ≥0) (E : Type u) [TopologicalSpace E]

/-- The segment coordinate of the cylinder `E × [a, d]`, its height. -/
def segmentHeight : C(E × Icc a d, ℝ) :=
  ⟨fun q => q.2, continuous_subtype_val.comp continuous_snd⟩

@[simp] theorem segmentHeight_apply (q : E × Icc a d) : segmentHeight a d E q = q.2 := rfl

/-- The thickened height `s + t` on `E × [a, d] × [-ε, ε]`. -/
def cylinderHeight : C(E × Icc a d × Band ε, ℝ) :=
  ⟨fun p => p.2.1 + p.2.2, (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).add
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))⟩

@[simp] theorem cylinderHeight_apply (p : E × Icc a d × Band ε) :
    cylinderHeight a d ε E p = (p.2.1 : ℝ) + p.2.2 :=
  rfl

/-- The thickened height is the geometric thickening height of the cylinder `E × [a, d]` with its
segment coordinate, after reassociating the product. -/
theorem cylinderHeight_eq (p : E × Icc a d × Band ε) :
    cylinderHeight a d ε E p =
      GeometricThickening.height (segmentHeight a d E) ε ((p.1, p.2.1), p.2.2) :=
  rfl

/-- The reparametrization `(y, s, t) ↦ (y, (s, s + t))` of the thickened cylinder onto `E` times
the parallelogram `{(s, u) | s ∈ J(u)}`, with inverse `(y, (s, u)) ↦ (y, s, u - s)`. -/
def bandParallelogramHomeomorph : E × Icc a d × Band ε ≃ₜ E × parallelogram a d ε where
  toFun p := (p.1, ⟨((p.2.1 : ℝ), p.2.1 + p.2.2),
    show (p.2.1 : ℝ) ∈ slice a d ε (p.2.1 + p.2.2) from mem_slice_iff.2
      ⟨p.2.1.2, by linarith [p.2.2.2.2], by linarith [p.2.2.2.1]⟩⟩)
  invFun q := (q.1,
    ⟨(q.2 : ℝ × ℝ).1, slice_subset_Icc a d ε _ (mem_slice_of_mem_parallelogram q.2.2)⟩,
    ⟨(q.2 : ℝ × ℝ).2 - (q.2 : ℝ × ℝ).1,
      sub_mem_band_of_mem_slice (mem_slice_of_mem_parallelogram q.2.2)⟩)
  left_inv p := Prod.ext rfl (Prod.ext rfl (Subtype.ext (show (p.2.1 : ℝ) + p.2.2 - p.2.1 = p.2.2
    by ring)))
  right_inv q := Prod.ext rfl (Subtype.ext (Prod.ext rfl
    (show (q.2 : ℝ × ℝ).1 + ((q.2 : ℝ × ℝ).2 - (q.2 : ℝ × ℝ).1) = (q.2 : ℝ × ℝ).2 by ring)))
  continuous_toFun := continuous_fst.prodMk
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).add
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).subtype_mk _)
  continuous_invFun := continuous_fst.prodMk
    (((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _).prodMk
      (((continuous_snd.comp (continuous_subtype_val.comp continuous_snd)).sub
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _))

@[simp] theorem coe_bandParallelogramHomeomorph_apply (p : E × Icc a d × Band ε) :
    ((bandParallelogramHomeomorph a d ε E p).2 : ℝ × ℝ) = ((p.2.1 : ℝ), (p.2.1 : ℝ) + p.2.2) :=
  rfl

end Space

/-! ### The comparison map -/

section Comparison

variable (a d : ℝ) (ε : ℝ≥0) (E : Type u) [TopologicalSpace E] {m : ℕ} (G : CriticalValues m)
  (hG : G.HasEvents a d ε)

/-- The pieces of the comparison into the parallelogram coordinates: a vertex point `(y, σ)` at
level `b j` goes to `(y, (σ, b j))`, a cylinder point `((y, σ), u)` to
`(y, (fragAff (mid k) u σ, u))`. -/
def toParallelogramMaps :
    (cylinderThick a d ε E G hG).CompatibleMaps G (E × parallelogram a d ε) where
  vertex j := ⟨fun p => (p.1, ⟨((p.2 : ℝ), G.value j), p.2.2⟩),
    continuous_fst.prodMk (((continuous_subtype_val.comp continuous_snd).prodMk
      continuous_const).subtype_mk _)⟩
  cylinder k := ⟨fun p => (p.1.1, ⟨(fragAff a d ε (G.mid k) p.2 p.1.2, (p.2 : ℝ)),
      (slabTransfer a d ε G hG k p.2 p.1.2).2⟩),
    (continuous_fst.comp continuous_fst).prodMk ((((RGraph.continuous_fragAff a d ε (G.mid k)).comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd))).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk _)⟩
  segBot_eq _ _ := rfl
  segTop_eq _ _ := rfl

/-- The comparison map in the parallelogram coordinates. -/
def toParallelogram : C((cylinderThick a d ε E G hG).Realization G, E × parallelogram a d ε) :=
  lift (toParallelogramMaps a d ε E G hG)

/-- **The comparison map** `|cylinderThick| → E × [a, d] × [-ε, ε]` (DMP's map `α`): a vertex
point `(y, σ)` at level `b j` goes to `(y, σ, b j - σ)`, a cylinder point `((y, σ), u)` to
`(y, s, u - s)` with `s = fragAff (mid k) u σ`. -/
def toCylinder : C((cylinderThick a d ε E G hG).Realization G, E × Icc a d × Band ε) :=
  (⟨(bandParallelogramHomeomorph a d ε E).symm,
    (bandParallelogramHomeomorph a d ε E).symm.continuous⟩ :
      C(E × parallelogram a d ε, E × Icc a d × Band ε)).comp (toParallelogram a d ε E G hG)

@[simp] theorem toCylinder_ofVertex (j : Fin (m + 1)) (p : E × slice a d ε (G.value j)) :
    toCylinder a d ε E G hG ((cylinderThick a d ε E G hG).ofVertex G j p) =
      (p.1, ⟨p.2, slice_subset_Icc a d ε _ p.2.2⟩,
        ⟨G.value j - p.2, sub_mem_band_of_mem_slice p.2.2⟩) :=
  rfl

@[simp] theorem toCylinder_ofCylinder (k : Fin m)
    (p : (E × slice a d ε (G.mid k)) × Seg G k) :
    toCylinder a d ε E G hG ((cylinderThick a d ε E G hG).ofCylinder G k p) =
      (p.1.1, ⟨fragAff a d ε (G.mid k) p.2 p.1.2,
          slice_subset_Icc a d ε _ (slabTransfer a d ε G hG k p.2 p.1.2).2⟩,
        ⟨p.2 - fragAff a d ε (G.mid k) p.2 p.1.2,
          sub_mem_band_of_mem_slice (slabTransfer a d ε G hG k p.2 p.1.2).2⟩) :=
  rfl

theorem bandParallelogramHomeomorph_toCylinder (x : (cylinderThick a d ε E G hG).Realization G) :
    bandParallelogramHomeomorph a d ε E (toCylinder a d ε E G hG x) =
      toParallelogram a d ε E G hG x :=
  (bandParallelogramHomeomorph a d ε E).apply_symm_apply _

/-- The comparison map preserves height. -/
theorem cylinderHeight_toCylinder (x : (cylinderThick a d ε E G hG).Realization G) :
    cylinderHeight a d ε E (toCylinder a d ε E G hG x) = (cylinderThick a d ε E G hG).height G x := by
  obtain ⟨r, rfl⟩ := (cylinderThick a d ε E G hG).quotMk_surjective G x
  rcases r with ⟨j, p⟩ | ⟨k, p⟩
  · show (p.2 : ℝ) + (G.value j - p.2) = G.value j
    ring
  · show fragAff a d ε (G.mid k) p.2 p.1.2 + (p.2 - fragAff a d ε (G.mid k) p.2 p.1.2) = p.2
    ring

end Comparison

/-! ### The inverse -/

section Inverse

variable {a d : ℝ} {ε : ℝ≥0} (E : Type u) [TopologicalSpace E] {m : ℕ} {G : CriticalValues m}
  (hG : G.HasEvents a d ε)

/-- The cylinder map of slab `k` on the reference slice, before descent. -/
private def slabRaw (k : Fin m) :
    C(E × (slice a d ε (G.mid k) × Seg G k), (cylinderThick a d ε E G hG).Realization G) :=
  ⟨fun p => (cylinderThick a d ε E G hG).ofCylinder G k ((p.1, p.2.1), p.2.2),
    ((cylinderThick a d ε E G hG).continuous_ofCylinder G k).comp
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))⟩

/-- `id_E × polygonMap k` as a continuous map. -/
private def slabQuot (k : Fin m) :
    C(E × (slice a d ε (G.mid k) × Seg G k), E × polygon a d ε G k) :=
  (ContinuousMap.id E).prodMap (polygonMap a d ε G hG k)

private theorem isQuotientMap_slabQuot (k : Fin m) : IsQuotientMap (slabQuot E hG k) :=
  isQuotientMap_prodMap_polygonMap hG k E

/-- **Collapse at the slab ends.** The cylinder map is constant on the fibres of
`id_E × polygonMap k`: in the open slab the transfer is injective, and at a slab end the
realization identifies the cylinder end with its vertex image. -/
private theorem slabRaw_factorsThrough (k : Fin m) :
    Function.FactorsThrough (slabRaw E hG k) (slabQuot E hG k) := by
  rintro ⟨y, σ, u⟩ ⟨y', σ', u'⟩ h
  have hy : y = y' := congrArg Prod.fst h
  have hp : polygonMap a d ε G hG k (σ, u) = polygonMap a d ε G hG k (σ', u') :=
    congrArg Prod.snd h
  obtain ⟨hu, hf⟩ := (polygonMap_eq_iff hG k).1 hp
  obtain rfl := hy
  obtain rfl : u = u' := Subtype.ext hu
  show (cylinderThick a d ε E G hG).ofCylinder G k ((y, σ), u) =
    (cylinderThick a d ε E G hG).ofCylinder G k ((y, σ'), u)
  rcases eq_or_lt_of_le u.2.1 with hb | hb
  · obtain rfl : u = segBot G k := Subtype.ext hb.symm
    exact ((cylinderThick a d ε E G hG).ofCylinder_segBot G k (y, σ)).trans
      ((congrArg ((cylinderThick a d ε E G hG).ofVertex G k.castSucc)
        (show (cylinderThick a d ε E G hG).left k (y, σ) = (cylinderThick a d ε E G hG).left k (y, σ')
          from Prod.ext rfl (Subtype.ext hf))).trans
        ((cylinderThick a d ε E G hG).ofCylinder_segBot G k (y, σ')).symm)
  rcases eq_or_lt_of_le u.2.2 with ht | ht
  · obtain rfl : u = segTop G k := Subtype.ext ht
    exact ((cylinderThick a d ε E G hG).ofCylinder_segTop G k (y, σ)).trans
      ((congrArg ((cylinderThick a d ε E G hG).ofVertex G k.succ)
        (show (cylinderThick a d ε E G hG).right k (y, σ) = (cylinderThick a d ε E G hG).right k (y, σ')
          from Prod.ext rfl (Subtype.ext hf))).trans
        ((cylinderThick a d ε E G hG).ofCylinder_segTop G k (y, σ')).symm)
  · have hK : (u : ℝ) ∈ (G.K k : Set ℝ) := G.mem_K.2 ⟨hb, ht⟩
    have h1 := hG.sliceTransfer_of_mem (G.mid_mem_K k) u.2
    have h2 := hG.sliceTransfer_of_mem hK ⟨(G.mid_mem_K k).1.le, (G.mid_mem_K k).2.le⟩
    obtain rfl : σ = σ' := Subtype.ext (h1.fragAff_injOn h2 σ.2 σ'.2 hf)
    rfl

/-- The slab piece of the inverse, descended to `E × polygon k`. -/
private def slabPiece (k : Fin m) :
    C(E × polygon a d ε G k, (cylinderThick a d ε E G hG).Realization G) :=
  (isQuotientMap_slabQuot E hG k).lift (slabRaw E hG k) (slabRaw_factorsThrough E hG k)

private theorem slabPiece_polygonMap (k : Fin m) (y : E) (σ : slice a d ε (G.mid k))
    (u : Seg G k) :
    slabPiece E hG k (y, polygonMap a d ε G hG k (σ, u)) =
      (cylinderThick a d ε E G hG).ofCylinder G k ((y, σ), u) :=
  DFunLike.congr_fun ((isQuotientMap_slabQuot E hG k).lift_comp (slabRaw E hG k)
    (slabRaw_factorsThrough E hG k)) (y, σ, u)

/-- At a level, the slab piece is the vertex inclusion. -/
private theorem slabPiece_of_eq_value (k : Fin m) (j : Fin (m + 1)) (y : E)
    (p : polygon a d ε G k) (hj : (p : ℝ × ℝ).2 = G.value j)
    (hs : (p : ℝ × ℝ).1 ∈ slice a d ε (G.value j)) :
    slabPiece E hG k (y, p) = (cylinderThick a d ε E G hG).ofVertex G j (y, ⟨_, hs⟩) := by
  obtain ⟨⟨σ, u⟩, rfl⟩ := polygonMap_surjective hG k p
  rw [slabPiece_polygonMap]
  have hj' : (u : ℝ) = G.value j := hj
  rcases eq_or_lt_of_le u.2.1 with hb | hb
  · obtain rfl : j = k.castSucc := G.strictMono.injective (hj'.symm.trans hb.symm)
    obtain rfl : u = segBot G k := Subtype.ext hb.symm
    exact (cylinderThick a d ε E G hG).ofCylinder_segBot G k (y, σ)
  rcases eq_or_lt_of_le u.2.2 with ht | ht
  · obtain rfl : j = k.succ := G.strictMono.injective (hj'.symm.trans ht)
    obtain rfl : u = segTop G k := Subtype.ext ht
    exact (cylinderThick a d ε E G hG).ofCylinder_segTop G k (y, σ)
  · exact absurd (G.mem_K.2 ⟨hj' ▸ hb, hj' ▸ ht⟩) (G.value_notMem_K k j)

/-- The finite closed cover of `E × parallelogram`: level slices and slab polygons. -/
private def cover (G : CriticalValues m) : Fin (m + 1) ⊕ Fin m → Set (E × parallelogram a d ε) :=
  Sum.elim (fun j => {x | (x.2 : ℝ × ℝ).2 = G.value j})
    (fun k => {x | (x.2 : ℝ × ℝ).2 ∈ Seg G k ∧ Seg G k ⊆ Icc (a - ε) (d + ε)})

omit [TopologicalSpace E] in
variable {E} in
private theorem mem_cover_inl {j : Fin (m + 1)} {x : E × parallelogram a d ε} :
    x ∈ cover E G (Sum.inl j) ↔ (x.2 : ℝ × ℝ).2 = G.value j :=
  Iff.rfl

omit [TopologicalSpace E] in
variable {E} in
private theorem mem_cover_inr {k : Fin m} {x : E × parallelogram a d ε} :
    x ∈ cover E G (Sum.inr k) ↔ (x.2 : ℝ × ℝ).2 ∈ Seg G k ∧ Seg G k ⊆ Icc (a - ε) (d + ε) :=
  Iff.rfl

private theorem isClosed_cover (i : Fin (m + 1) ⊕ Fin m) :
    IsClosed (cover (a := a) (d := d) (ε := ε) E G i) := by
  have hc : Continuous fun x : E × parallelogram a d ε => (x.2 : ℝ × ℝ).2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  rcases i with j | k
  · have : cover (a := a) (d := d) (ε := ε) E G (Sum.inl j) =
        {x : E × parallelogram a d ε | (x.2 : ℝ × ℝ).2 = G.value j} :=
      Set.ext fun _ => mem_cover_inl
    rw [this]
    exact isClosed_eq hc continuous_const
  · have : cover (a := a) (d := d) (ε := ε) E G (Sum.inr k) =
        (fun x : E × parallelogram a d ε => (x.2 : ℝ × ℝ).2) ⁻¹' Seg G k ∩
          {_x | Seg G k ⊆ Icc (a - ε) (d + ε)} :=
      Set.ext fun _ => mem_cover_inr
    rw [this]
    exact (isClosed_Icc.preimage hc).inter isClosed_const

omit [TopologicalSpace E] in
private theorem iUnion_cover (hG : G.HasEvents a d ε) : ⋃ i, cover (a := a) (d := d) (ε := ε) E G i = univ := by
  refine eq_univ_of_forall fun x => ?_
  have hx : (x.2 : ℝ × ℝ) ∈ (⋃ k, polygon a d ε G k) ∪ ⋃ j, levelSet a d ε G j :=
    (iUnion_polygon_union_levelSet hG).symm.subset x.2.2
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨.inr k, mem_cover_inr.2 ⟨hk.2.1, hk.2.2⟩⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨.inl j, mem_cover_inl.2 hj.2⟩

omit [TopologicalSpace E] in
private theorem mem_slice_of_mem_cover_inl {j : Fin (m + 1)} {x : E × parallelogram a d ε}
    (hx : x ∈ cover E G (Sum.inl j)) : (x.2 : ℝ × ℝ).1 ∈ slice a d ε (G.value j) := by
  have h : (x.2 : ℝ × ℝ).1 ∈ slice a d ε (x.2 : ℝ × ℝ).2 := mem_slice_of_mem_parallelogram x.2.2
  rw [← mem_cover_inl.1 hx]
  exact h

omit [TopologicalSpace E] in
private theorem mem_polygon_of_mem_cover_inr {k : Fin m} {x : E × parallelogram a d ε}
    (hx : x ∈ cover E G (Sum.inr k)) : (x.2 : ℝ × ℝ) ∈ polygon a d ε G k :=
  ⟨x.2.2, (mem_cover_inr.1 hx).1, (mem_cover_inr.1 hx).2⟩

/-- The inverse on each member of the cover. -/
private def coverMap :
    ∀ i, cover (a := a) (d := d) (ε := ε) E G i → (cylinderThick a d ε E G hG).Realization G
  | .inl j => fun x => (cylinderThick a d ε E G hG).ofVertex G j
      (x.1.1, ⟨_, mem_slice_of_mem_cover_inl E x.2⟩)
  | .inr k => fun x => slabPiece E hG k (x.1.1, ⟨_, mem_polygon_of_mem_cover_inr E x.2⟩)

private theorem coverMap_inl (j : Fin (m + 1)) (x : cover (a := a) (d := d) (ε := ε) E G (.inl j)) :
    coverMap E hG (.inl j) x = (cylinderThick a d ε E G hG).ofVertex G j
      (x.1.1, ⟨_, mem_slice_of_mem_cover_inl E x.2⟩) :=
  rfl

private theorem coverMap_inr (k : Fin m) (x : cover (a := a) (d := d) (ε := ε) E G (.inr k)) :
    coverMap E hG (.inr k) x =
      slabPiece E hG k (x.1.1, ⟨_, mem_polygon_of_mem_cover_inr E x.2⟩) :=
  rfl

private theorem continuous_coverMap (i : Fin (m + 1) ⊕ Fin m) :
    Continuous (coverMap E hG i) := by
  rcases i with j | k
  · have : coverMap E hG (.inl j) = fun x => (cylinderThick a d ε E G hG).ofVertex G j
        (x.1.1, ⟨_, mem_slice_of_mem_cover_inl E x.2⟩) := funext (coverMap_inl E hG j)
    rw [this]
    exact ((cylinderThick a d ε E G hG).continuous_ofVertex G j).comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_fst.comp (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _))
  · have : coverMap E hG (.inr k) = fun x =>
        slabPiece E hG k (x.1.1, ⟨_, mem_polygon_of_mem_cover_inr E x.2⟩) :=
      funext (coverMap_inr E hG k)
    rw [this]
    exact (slabPiece E hG k).continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))

private theorem coverMap_agree :
    ∀ (i i' : Fin (m + 1) ⊕ Fin m) (x : E × parallelogram a d ε) (hxi : x ∈ cover E G i)
      (hxi' : x ∈ cover E G i'), coverMap E hG i ⟨x, hxi⟩ = coverMap E hG i' ⟨x, hxi'⟩
  | .inl j, .inl j', x, hxi, hxi' => by
    obtain rfl : j = j' :=
      G.strictMono.injective ((mem_cover_inl.1 hxi).symm.trans (mem_cover_inl.1 hxi'))
    rfl
  | .inl j, .inr k, x, hxi, hxi' => by
    rw [coverMap_inl, coverMap_inr]
    exact (slabPiece_of_eq_value E hG k j x.1 ⟨_, mem_polygon_of_mem_cover_inr E hxi'⟩
      (mem_cover_inl.1 hxi) (mem_slice_of_mem_cover_inl E hxi)).symm
  | .inr k, .inl j, x, hxi, hxi' => by
    rw [coverMap_inl, coverMap_inr]
    exact slabPiece_of_eq_value E hG k j x.1 ⟨_, mem_polygon_of_mem_cover_inr E hxi⟩
      (mem_cover_inl.1 hxi') (mem_slice_of_mem_cover_inl E hxi')
  | .inr k, .inr k', x, hxi, hxi' => by
    rw [coverMap_inr, coverMap_inr]
    by_cases hv : ∃ j, G.value j = (x.2 : ℝ × ℝ).2
    · obtain ⟨j, hj⟩ := hv
      have hs : (x.2 : ℝ × ℝ).1 ∈ slice a d ε (G.value j) := by
        rw [hj]
        exact mem_slice_of_mem_parallelogram x.2.2
      exact (slabPiece_of_eq_value E hG k j x.1 ⟨_, mem_polygon_of_mem_cover_inr E hxi⟩
        hj.symm hs).trans
          (slabPiece_of_eq_value E hG k' j x.1 ⟨_, mem_polygon_of_mem_cover_inr E hxi'⟩
            hj.symm hs).symm
    · have hxk := (mem_cover_inr.1 hxi).1
      have hK : (x.2 : ℝ × ℝ).2 ∈ (G.K k : Set ℝ) := G.mem_K.2
        ⟨lt_of_le_of_ne hxk.1 fun h => hv ⟨_, h⟩, lt_of_le_of_ne hxk.2 fun h => hv ⟨_, h.symm⟩⟩
      obtain rfl : k = k' := G.eq_of_mem_K_of_mem_Icc hK (mem_cover_inr.1 hxi').1
      rfl

/-- The inverse in the parallelogram coordinates, pasted from the level slices and the descended
slab pieces along the finite closed cover. -/
private def ofParallelogram :
    C(E × parallelogram a d ε, (cylinderThick a d ε E G hG).Realization G) where
  toFun := liftCover (cover E G) (coverMap E hG) (coverMap_agree E hG) (iUnion_cover E hG)
  continuous_toFun := (locallyFinite_of_finite _).continuous (iUnion_cover E hG)
    (isClosed_cover E) fun i => continuousOn_iff_continuous_domRestrict.2
      ((continuous_coverMap E hG i).congr fun x =>
        (liftCover_coe (S := cover E G) (f := coverMap E hG) (hf := coverMap_agree E hG)
          (hS := iUnion_cover E hG) x).symm)

private theorem ofParallelogram_of_mem {i : Fin (m + 1) ⊕ Fin m} {x : E × parallelogram a d ε}
    (hx : x ∈ cover E G i) : ofParallelogram E hG x = coverMap E hG i ⟨x, hx⟩ :=
  liftCover_of_mem (S := cover E G) (f := coverMap E hG) (hf := coverMap_agree E hG)
    (hS := iUnion_cover E hG) hx

private theorem ofParallelogram_toParallelogram (x : (cylinderThick a d ε E G hG).Realization G) :
    ofParallelogram E hG (toParallelogram a d ε E G hG x) = x := by
  have : (ofParallelogram E hG).comp (toParallelogram a d ε E G hG) = ContinuousMap.id _ := by
    refine hom_ext (fun j p => ?_) fun k p => ?_
    · rw [ContinuousMap.comp_apply, ContinuousMap.id_apply,
        ofParallelogram_of_mem E hG (i := .inl j) (mem_cover_inl.2 rfl), coverMap_inl]
      rfl
    · obtain ⟨⟨y, σ⟩, u⟩ := p
      rw [ContinuousMap.comp_apply, ContinuousMap.id_apply,
        ofParallelogram_of_mem E hG (i := .inr k)
          (mem_cover_inr.2 ⟨u.2, (polygonMap a d ε G hG k (σ, u)).2.2.2⟩), coverMap_inr]
      exact slabPiece_polygonMap E hG k y σ u
  exact DFunLike.congr_fun this x

private theorem toParallelogram_slabPiece (k : Fin m) (y : E) (p : polygon a d ε G k) :
    toParallelogram a d ε E G hG (slabPiece E hG k (y, p)) =
      (y, Set.inclusion (polygon_subset a d ε G k) p) := by
  obtain ⟨⟨σ, u⟩, rfl⟩ := polygonMap_surjective hG k p
  rw [slabPiece_polygonMap]
  rfl

private theorem toParallelogram_ofParallelogram (x : E × parallelogram a d ε) :
    toParallelogram a d ε E G hG (ofParallelogram E hG x) = x := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 ((iUnion_cover E hG).symm ▸ mem_univ x :
    x ∈ ⋃ i, cover (a := a) (d := d) (ε := ε) E G i)
  rw [ofParallelogram_of_mem E hG hi]
  rcases i with j | k
  · rw [coverMap_inl]
    exact Prod.ext rfl (Subtype.ext (Prod.ext rfl (mem_cover_inl.1 hi).symm))
  · rw [coverMap_inr]
    exact toParallelogram_slabPiece E hG k x.1 _

variable (a d ε G)

/-- **The inverse** `E × [a, d] × [-ε, ε] → |cylinderThick|`: in the coordinates `(s, u = s + t)`,
the vertex inclusion on each level slice and, on each slab polygon, the cylinder map descended along
`id_E × polygonMap k`, pasted along the finite closed cover. -/
def ofCylinder' : C(E × Icc a d × Band ε, (cylinderThick a d ε E G hG).Realization G) :=
  (ofParallelogram E hG).comp (⟨bandParallelogramHomeomorph a d ε E,
    (bandParallelogramHomeomorph a d ε E).continuous⟩ : C(E × Icc a d × Band ε, E × parallelogram a d ε))

theorem toCylinder_ofCylinder' (p : E × Icc a d × Band ε) :
    toCylinder a d ε E G hG (ofCylinder' a d ε E G hG p) = p := by
  rw [← (bandParallelogramHomeomorph a d ε E).injective.eq_iff,
    bandParallelogramHomeomorph_toCylinder]
  exact toParallelogram_ofParallelogram E hG _

theorem ofCylinder'_toCylinder (x : (cylinderThick a d ε E G hG).Realization G) :
    ofCylinder' a d ε E G hG (toCylinder a d ε E G hG x) = x := by
  show ofParallelogram E hG (bandParallelogramHomeomorph a d ε E (toCylinder a d ε E G hG x)) = x
  rw [bandParallelogramHomeomorph_toCylinder]
  exact ofParallelogram_toParallelogram E hG x

/-- On a level slice, the inverse is the vertex inclusion. -/
theorem ofCylinder'_vertex (j : Fin (m + 1)) (y : E) {s : ℝ} (hs : s ∈ slice a d ε (G.value j)) :
    ofCylinder' a d ε E G hG (y, ⟨s, slice_subset_Icc a d ε _ hs⟩,
        ⟨G.value j - s, sub_mem_band_of_mem_slice hs⟩) =
      (cylinderThick a d ε E G hG).ofVertex G j (y, ⟨s, hs⟩) :=
  (congrArg (ofCylinder' a d ε E G hG) (toCylinder_ofVertex a d ε E G hG j (y, ⟨s, hs⟩))).symm.trans
    (ofCylinder'_toCylinder a d ε E G hG _)

/-- **Issue #707, one cylinder.** The realization of the thickening presentation is homeomorphic
to the thickened cylinder `E × [a, d] × [-ε, ε]`, for every topological space `E`, every `ε ≥ 0`
and every `a ≤ d` on every grid listing the four events. -/
def cylinderThickHomeomorph :
    (cylinderThick a d ε E G hG).Realization G ≃ₜ E × Icc a d × Band ε where
  toFun := toCylinder a d ε E G hG
  invFun := ofCylinder' a d ε E G hG
  left_inv := ofCylinder'_toCylinder a d ε E G hG
  right_inv := toCylinder_ofCylinder' a d ε E G hG
  continuous_toFun := (toCylinder a d ε E G hG).continuous
  continuous_invFun := (ofCylinder' a d ε E G hG).continuous

@[simp] theorem coe_cylinderThickHomeomorph :
    ⇑(cylinderThickHomeomorph a d ε E G hG) = toCylinder a d ε E G hG :=
  rfl

@[simp] theorem coe_cylinderThickHomeomorph_symm :
    ⇑(cylinderThickHomeomorph a d ε E G hG).symm = ofCylinder' a d ε E G hG :=
  rfl

/-- The homeomorphism preserves height. -/
theorem cylinderHeight_cylinderThickHomeomorph (x : (cylinderThick a d ε E G hG).Realization G) :
    cylinderHeight a d ε E (cylinderThickHomeomorph a d ε E G hG x) =
      (cylinderThick a d ε E G hG).height G x :=
  cylinderHeight_toCylinder a d ε E G hG x

/-- The inverse homeomorphism preserves height. -/
theorem height_cylinderThickHomeomorph_symm (p : E × Icc a d × Band ε) :
    (cylinderThick a d ε E G hG).height G ((cylinderThickHomeomorph a d ε E G hG).symm p) =
      cylinderHeight a d ε E p := by
  rw [← cylinderHeight_cylinderThickHomeomorph, Homeomorph.apply_symm_apply]

end Inverse

/-! ### The vertex strip -/

section Strip

variable (a : ℝ) (ε : ℝ≥0) (E : Type u) [TopologicalSpace E] {m : ℕ} (G : CriticalValues m)
  (hGa : G.HasEvents a a ε)

/-- Forgetting the one-point segment `[a, a]`. -/
def pointSegmentHomeomorph : E × Icc a a × Band ε ≃ₜ E × Band ε where
  toFun p := (p.1, p.2.2)
  invFun q := (q.1, ⟨a, left_mem_Icc.2 le_rfl⟩, q.2)
  left_inv p := Prod.ext rfl (Prod.ext (Subtype.ext (le_antisymm p.2.1.2.1 p.2.1.2.2)) rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_const.prodMk continuous_snd)

/-- **The vertex strip.** The thickening presentation of `E × {a}` realizes `E × [-ε, ε]`, for
every topological space `E` and every `ε ≥ 0`. -/
def vertexStripHomeomorph : (cylinderThick a a ε E G hGa).Realization G ≃ₜ E × Band ε :=
  (cylinderThickHomeomorph a a ε E G hGa).trans (pointSegmentHomeomorph a ε E)

@[simp] theorem vertexStripHomeomorph_apply (x : (cylinderThick a a ε E G hGa).Realization G) :
    vertexStripHomeomorph a ε E G hGa x =
      ((toCylinder a a ε E G hGa x).1, (toCylinder a a ε E G hGa x).2.2) :=
  rfl

/-- The vertex strip carries the height `a + t`. -/
theorem height_vertexStripHomeomorph (x : (cylinderThick a a ε E G hGa).Realization G) :
    GeometricThickening.height (ContinuousMap.const E a) ε (vertexStripHomeomorph a ε E G hGa x) =
      (cylinderThick a a ε E G hGa).height G x := by
  have h := cylinderHeight_toCylinder a a ε E G hGa x
  have ha : ((toCylinder a a ε E G hGa x).2.1 : ℝ) = a :=
    le_antisymm (toCylinder a a ε E G hGa x).2.1.2.2 (toCylinder a a ε E G hGa x).2.1.2.1
  rw [← h, cylinderHeight_apply, ha]
  rfl

end Strip

/-! ### Boundary strips and naturality -/

section Boundary

variable (a d : ℝ) (ε : ℝ≥0) (E : Type u) [TopologicalSpace E] {m : ℕ} (G : CriticalValues m)
  (hG : G.HasEvents a d ε)

/-- **The bottom strip.** The inclusion of the thickening presentation of `E × {a}` into that of
`E × [a, d]` on a common grid. Its endpoint equations hold because a slice parameter at the segment
end `a` stays there under every transfer. -/
def botIncl (had : a ≤ d) (hGa : G.HasEvents a a ε) :
    (cylinderThick a a ε E G hGa).Hom (cylinderThick a d ε E G hG) where
  vertex _ := (ContinuousMap.id E).prodMap (ContinuousMap.inclusion (slice_self_subset_left had _))
  edge _ := (ContinuousMap.id E).prodMap (ContinuousMap.inclusion (slice_self_subset_left had _))
  left_comm k y := Prod.ext rfl (Subtype.ext
    (((hG.sliceTransfer_of_mem (G.mid_mem_K k) (segBot G k).2).fragAff_eq_left
      (slice_self_subset_left had _ y.2.2) (eq_of_mem_slice_self y.2.2)).trans
        (eq_of_mem_slice_self ((cylinderThick a a ε E G hGa).left k y).2.2).symm))
  right_comm k y := Prod.ext rfl (Subtype.ext
    (((hG.sliceTransfer_of_mem (G.mid_mem_K k) (segTop G k).2).fragAff_eq_left
      (slice_self_subset_left had _ y.2.2) (eq_of_mem_slice_self y.2.2)).trans
        (eq_of_mem_slice_self ((cylinderThick a a ε E G hGa).right k y).2.2).symm))

/-- **The top strip.** The inclusion of the thickening presentation of `E × {d}` into that of
`E × [a, d]` on a common grid. Its endpoint equations hold because a slice parameter at the segment
end `d` stays there under every transfer. -/
def topIncl (had : a ≤ d) (hGd : G.HasEvents d d ε) :
    (cylinderThick d d ε E G hGd).Hom (cylinderThick a d ε E G hG) where
  vertex _ := (ContinuousMap.id E).prodMap (ContinuousMap.inclusion (slice_self_subset_right had _))
  edge _ := (ContinuousMap.id E).prodMap (ContinuousMap.inclusion (slice_self_subset_right had _))
  left_comm k y := Prod.ext rfl (Subtype.ext
    (((hG.sliceTransfer_of_mem (G.mid_mem_K k) (segBot G k).2).fragAff_eq_right
      (slice_self_subset_right had _ y.2.2) (eq_of_mem_slice_self y.2.2)).trans
        (eq_of_mem_slice_self ((cylinderThick d d ε E G hGd).left k y).2.2).symm))
  right_comm k y := Prod.ext rfl (Subtype.ext
    (((hG.sliceTransfer_of_mem (G.mid_mem_K k) (segTop G k).2).fragAff_eq_right
      (slice_self_subset_right had _ y.2.2) (eq_of_mem_slice_self y.2.2)).trans
        (eq_of_mem_slice_self ((cylinderThick d d ε E G hGd).right k y).2.2).symm))

/-- A continuous map of spaces as a morphism of thickening presentations, `f × id` on every
piece. -/
def mapSpace {E' : Type v} [TopologicalSpace E'] (f : C(E, E')) :
    (cylinderThick a d ε E G hG).Hom (cylinderThick a d ε E' G hG) where
  vertex _ := f.prodMap (ContinuousMap.id _)
  edge _ := f.prodMap (ContinuousMap.id _)
  left_comm _ _ := rfl
  right_comm _ _ := rfl

theorem mapSpace_id : mapSpace a d ε E G hG (ContinuousMap.id E) = Hom.id _ :=
  rfl

theorem mapSpace_comp {E' : Type v} {E'' : Type w} [TopologicalSpace E'] [TopologicalSpace E'']
    (f : C(E, E')) (g : C(E', E'')) :
    mapSpace a d ε E G hG (g.comp f) =
      (mapSpace a d ε E G hG f).comp (mapSpace a d ε E' G hG g) :=
  rfl

/-- The bottom strip inclusion is natural in the space. -/
theorem botIncl_comp_mapSpace (had : a ≤ d) (hGa : G.HasEvents a a ε) {E' : Type v}
    [TopologicalSpace E'] (f : C(E, E')) :
    (botIncl a d ε E G hG had hGa).comp (mapSpace a d ε E G hG f) =
      (mapSpace a a ε E G hGa f).comp (botIncl a d ε E' G hG had hGa) :=
  rfl

/-- The top strip inclusion is natural in the space. -/
theorem topIncl_comp_mapSpace (had : a ≤ d) (hGd : G.HasEvents d d ε) {E' : Type v}
    [TopologicalSpace E'] (f : C(E, E')) :
    (topIncl a d ε E G hG had hGd).comp (mapSpace a d ε E G hG f) =
      (mapSpace d d ε E G hGd f).comp (topIncl a d ε E' G hG had hGd) :=
  rfl

/-- **Naturality in the space.** The homeomorphism turns `mapSpace f` into `f × id`. -/
theorem cylinderThickHomeomorph_realize_mapSpace {E' : Type v} [TopologicalSpace E']
    (f : C(E, E')) (x : (cylinderThick a d ε E G hG).Realization G) :
    cylinderThickHomeomorph a d ε E' G hG ((mapSpace a d ε E G hG f).realize G x) =
      (f (cylinderThickHomeomorph a d ε E G hG x).1, (cylinderThickHomeomorph a d ε E G hG x).2) := by
  obtain ⟨r, rfl⟩ := (cylinderThick a d ε E G hG).quotMk_surjective G x
  rcases r with ⟨j, p⟩ | ⟨k, p⟩ <;> rfl

/-- **The bottom strip square.** The homeomorphisms turn the bottom strip inclusion into
`(y, t) ↦ (y, a, t)`. -/
theorem cylinderThickHomeomorph_realize_botIncl (had : a ≤ d) (hGa : G.HasEvents a a ε)
    (x : (cylinderThick a a ε E G hGa).Realization G) :
    cylinderThickHomeomorph a d ε E G hG ((botIncl a d ε E G hG had hGa).realize G x) =
      ((vertexStripHomeomorph a ε E G hGa x).1, ⟨a, left_mem_Icc.2 had⟩,
        (vertexStripHomeomorph a ε E G hGa x).2) := by
  obtain ⟨r, rfl⟩ := (cylinderThick a a ε E G hGa).quotMk_surjective G x
  rcases r with ⟨j, p⟩ | ⟨k, ⟨⟨y, σ⟩, u⟩⟩
  · exact Prod.ext rfl (Prod.ext (Subtype.ext (eq_of_mem_slice_self p.2.2)) rfl)
  · have h1 : fragAff a d ε (G.mid k) u σ = a :=
      (hG.sliceTransfer_of_mem (G.mid_mem_K k) u.2).fragAff_eq_left
        (slice_self_subset_left had _ σ.2) (eq_of_mem_slice_self σ.2)
    have h2 : fragAff a a ε (G.mid k) u σ = a :=
      (hGa.sliceTransfer_of_mem (G.mid_mem_K k) u.2).fragAff_eq_left σ.2 (eq_of_mem_slice_self σ.2)
    refine Prod.ext rfl (Prod.ext (Subtype.ext h1) (Subtype.ext ?_))
    show (u : ℝ) - fragAff a d ε (G.mid k) u σ = u - fragAff a a ε (G.mid k) u σ
    rw [h1, h2]

/-- **The top strip square.** The homeomorphisms turn the top strip inclusion into
`(y, t) ↦ (y, d, t)`. -/
theorem cylinderThickHomeomorph_realize_topIncl (had : a ≤ d) (hGd : G.HasEvents d d ε)
    (x : (cylinderThick d d ε E G hGd).Realization G) :
    cylinderThickHomeomorph a d ε E G hG ((topIncl a d ε E G hG had hGd).realize G x) =
      ((vertexStripHomeomorph d ε E G hGd x).1, ⟨d, right_mem_Icc.2 had⟩,
        (vertexStripHomeomorph d ε E G hGd x).2) := by
  obtain ⟨r, rfl⟩ := (cylinderThick d d ε E G hGd).quotMk_surjective G x
  rcases r with ⟨j, p⟩ | ⟨k, ⟨⟨y, σ⟩, u⟩⟩
  · exact Prod.ext rfl (Prod.ext (Subtype.ext (eq_of_mem_slice_self p.2.2)) rfl)
  · have h1 : fragAff a d ε (G.mid k) u σ = d :=
      (hG.sliceTransfer_of_mem (G.mid_mem_K k) u.2).fragAff_eq_right
        (slice_self_subset_right had _ σ.2) (eq_of_mem_slice_self σ.2)
    have h2 : fragAff d d ε (G.mid k) u σ = d :=
      (hGd.sliceTransfer_of_mem (G.mid_mem_K k) u.2).fragAff_eq_left σ.2 (eq_of_mem_slice_self σ.2)
    refine Prod.ext rfl (Prod.ext (Subtype.ext h1) (Subtype.ext ?_))
    show (u : ℝ) - fragAff a d ε (G.mid k) u σ = u - fragAff d d ε (G.mid k) u σ
    rw [h1, h2]

/-- **Endpoint maps on the vertex strip.** For a continuous map `f : E → V`, the vertex strip
homeomorphisms turn `mapSpace f` into `f × id`. Together with
`cylinderThickHomeomorph_realize_botIncl` this is the commuting square of the bottom strip
inclusion and an endpoint map `E → V`. -/
theorem vertexStripHomeomorph_realize_mapSpace (hGa : G.HasEvents a a ε) {V : Type v}
    [TopologicalSpace V] (f : C(E, V)) (x : (cylinderThick a a ε E G hGa).Realization G) :
    vertexStripHomeomorph a ε V G hGa ((mapSpace a a ε E G hGa f).realize G x) =
      (f (vertexStripHomeomorph a ε E G hGa x).1, (vertexStripHomeomorph a ε E G hGa x).2) := by
  obtain ⟨r, rfl⟩ := (cylinderThick a a ε E G hGa).quotMk_surjective G x
  rcases r with ⟨j, p⟩ | ⟨k, p⟩ <;> rfl

end Boundary

/-! ### The shifted grid of one segment -/

section Pair

variable (a d : ℝ) (ε : ℝ≥0) (E : Type u) [TopologicalSpace E] (had : a < d)

/-- The shifted witness of `pair a d` lists the events of the bottom strip `[a, a]`. -/
theorem _root_.TDA.Reeb.CriticalValues.pair_hasEvents_left {a d : ℝ} (had : a < d) (ε : ℝ≥0) :
    ((CriticalValues.pair a d had).shifted ε).HasEvents a a ε :=
  ((CriticalValues.pair a d had).containsShifted_shifted ε).hasEvents_vertex 0

/-- The shifted witness of `pair a d` lists the events of the top strip `[d, d]`. -/
theorem _root_.TDA.Reeb.CriticalValues.pair_hasEvents_right {a d : ℝ} (had : a < d) (ε : ℝ≥0) :
    ((CriticalValues.pair a d had).shifted ε).HasEvents d d ε :=
  ((CriticalValues.pair a d had).containsShifted_shifted ε).hasEvents_vertex 1

/-- **Issue #707 literal.** The thickening presentation of `E × [a, d]` on the grid of the distinct
values among `a ± ε`, `d ± ε`. -/
abbrev pairThick : CylinderPresentation.{u} ((CriticalValues.pair a d had).shiftedCount ε) :=
  cylinderThick a d ε E ((CriticalValues.pair a d had).shifted ε)
    (CriticalValues.pair_hasEvents had ε)

/-- The height-preserving homeomorphism of `pairThick` with `E × [a, d] × [-ε, ε]`. -/
def pairThickHomeomorph :
    (pairThick a d ε E had).Realization ((CriticalValues.pair a d had).shifted ε) ≃ₜ
      E × Icc a d × Band ε :=
  cylinderThickHomeomorph a d ε E _ _

theorem cylinderHeight_pairThickHomeomorph
    (x : (pairThick a d ε E had).Realization ((CriticalValues.pair a d had).shifted ε)) :
    cylinderHeight a d ε E (pairThickHomeomorph a d ε E had x) =
      (pairThick a d ε E had).height ((CriticalValues.pair a d had).shifted ε) x :=
  cylinderHeight_cylinderThickHomeomorph a d ε E _ _ x

/-- The bottom strip `E × {a} × [-ε, ε]` on the grid of `pairThick`. -/
def pairBotIncl :
    (cylinderThick a a ε E ((CriticalValues.pair a d had).shifted ε)
      (CriticalValues.pair_hasEvents_left had ε)).Hom (pairThick a d ε E had) :=
  botIncl a d ε E _ _ had.le _

/-- The top strip `E × {d} × [-ε, ε]` on the grid of `pairThick`. -/
def pairTopIncl :
    (cylinderThick d d ε E ((CriticalValues.pair a d had).shifted ε)
      (CriticalValues.pair_hasEvents_right had ε)).Hom (pairThick a d ε E had) :=
  topIncl a d ε E _ _ had.le _

end Pair

end Thickening

end

end TDA.Reeb
