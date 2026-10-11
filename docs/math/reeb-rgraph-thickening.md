# Constructible thickenings of finite ℝ-graphs

## Setting

For finite data `D` over a list of levels `S : CriticalValues n`, write `X` for the realization
`(ofFiniteData D).Realization S` and `f` for its height (see `reeb-constructible-space.md` and
`reeb-rgraph.md`). An edge `e` with label `y` runs over the segment `[a, d] = Seg S e`, with
`a = S.value e.castSucc < d = S.value e.succ`. `X` is compact and Hausdorff. Two raw points have the
same image under `quotMk` exactly when their normal forms `nf` agree (`quotMk_eq_iff`); the normal
form sends a parameter equal to `a` or `d` to the corresponding vertex and fixes every other raw
point.

For `ε : ℝ≥0`, `GeometricThickening.functor ε` sends a space over `ℝ` to `X × Band ε` with height
`f x + t`, and `bandHomeomorph f ε` identifies `X × Band ε` with the band
`{(x, u) | u - ε ≤ f x ≤ u + ε}`, on which the height is `u` (see `reeb-geometric-thickening.md`).
`S.shifted ε` is the sorted deduplicated list of the shifted levels `S - ε` and `S + ε`, with
`shiftedCount ε + 1` levels `b 0 < ⋯ < b m`; every `a ± ε` is one of them, `b 0 = S.value 0 - ε`
and `b m = S.value (Fin.last n) + ε` (see `reeb-constructible-smoothing.md`).
`IsConstructibleSpace` and `ConstructibleSpaceCat` are the constructible ℝ-spaces and their full
subcategory of the slice (see `reeb-constructible-quotient.md`).

The construction uses these merged library declarations:

- `TDA.Reeb.ConstructibleSpace`: `CylinderPresentation` with `V`, `E`, `left`, `right`, `Seg`,
  `segBot`, `segTop`, `gapIncl`, `Cylinder`, `CylinderPiece`, `VertexPiece`, `Raw`,
  `Realization`, `quotMk`, `continuous_quotMk`, `quotMk_surjective`, `quotMk_eq_iff`, `nf`,
  `nf_segBot`, `nf_segTop`, `exists_rep`, `ofVertex`, `ofCylinder`, `continuous_ofCylinder`,
  `ofStrip`, `height`, `height_ofVertex`, `height_ofStrip`, `height_mem_Icc`, `CompatibleMaps`,
  `lift`, the `compactSpace` and `t2Space` instances, `ofFiniteData` with its discrete and finite
  piece instances, and `CriticalValues.value_castSucc_lt_succ` and
  `CriticalValues.eq_of_mem_K_of_mem_Icc`;
- `TDA.Reeb.CriticalValues`: `CriticalValues`, `K`, `value_notMem_K`, `value_mem_J`, `Piece`,
  `piece` and `exists_piece`; `TDA.Reeb.FiniteDiagram`: `FiniteReebData`;
  `TDA.Reeb.Interval`: `OpenInterval`;
- `TDA.Reeb.CriticalValuesShift`: `shifted`, `shiftedCount`, `exists_shifted_value_eq_sub`,
  `exists_shifted_value_eq_add`, `shifted_value_zero` and `shifted_value_last`;
- `TDA.Reeb.GeometricThickening`: `Band`, `height`, `height_apply`, `bandHomeomorph`,
  `snd_bandHomeomorph`, `functor` and `zeroIso`;
- `TDA.Reeb.RGraph`: `IsRGraph`, `RGraphCat` and `toOver`; `TDA.Reeb.ConstructibleQuotient`:
  `IsConstructibleSpace`, `ConstructibleSpaceCat`, `isConstructibleSpace_of_isRGraph` and
  `quotientRGraphFunctor`; `TDA.Reeb.QuotientComparison`: `ReebQuotient.quotientFunctor`.

From the pinned mathlib it relies on `Convex.locallyPathConnectedSpace` (through
`Mathlib.Topology.Algebra.Module.LocallyConvex`), `IsQuotientMap.of_surjective_continuous`,
`IsQuotientMap.lift`, `IsQuotientMap.locallyPathConnectedSpace` and
`Continuous.homeoOfEquivCompactToT2`.

The fixtures additionally use `shiftedSet`, `mem_shiftedSet`, `sub_mem_shiftedSet`,
`add_mem_shiftedSet`, `card_shiftedSet` and `range_shifted`, `isEmpty_realization`,
`ofCylinder_segBot`, `ofCylinder_segTop`, `ofVertex_injective`, `ofStrip_injective`, `toRGraph`,
`GeometricThickening.zero_mem_band`, and the fixture data `S01`, `parallelData`, `twoSegData`,
`twoSegLabel`, `emptyData`, `emptyData_isEmpty`, `ofVertex_surjective_zero`, `singleEdge` and
`pt0`.

## The affine fragment map

For a segment `[a, d]` and heights `c`, `u`, write `L(u) = max a (u - ε)` and
`R(u) = min d (u + ε)`, so that `[L(u), R(u)]` is the part of the segment at heights in
`[u - ε, u + ε]`. The affine fragment map is

```text
fragAff a d ε c u s = L(u) + (s - L(c)) · (R(u) - L(u)) / (R(c) - L(c)).
```

Its denominator depends on `c` only, so it is jointly continuous in `(s, u)`
(`continuous_fragAff`). It maps `[L(c), R(c)]` into `[L(u), R(u)]` whenever the target is nonempty
(`fragAff_mem`), sends `L(c)` to `L(u)` (`fragAff_left`), sends `R(c)` to `R(u)` when
`L(c) < R(c)` (`fragAff_right`), is constant when `L(u) = R(u)` (`fragAff_collapse`), and the maps
`c → u` and `u → c` are mutually inverse when both fragments are nondegenerate (`fragAff_fragAff`).
If `ε > 0` and `c` avoids the events `a ± ε` and `d ± ε`, a nonempty fragment at `c` is
nondegenerate (`fragLo_lt_fragHi`).

On an edge contained in the window it is the identity, on an edge crossing one window end it is a
linear stretch, and on an edge covering the whole window it is a translation.

## Closed windows

`window S D lo hi = {x | lo ≤ f x ≤ hi}` is a subset of `X`; membership is `f x ∈ [lo, hi]` by
`Iff.rfl` (`mem_window`), so the subtype is definitionally `{x // f x ∈ Icc lo hi}`. Its raw cover
is the finite sum

```text
WindowRaw S D lo hi = WindowV ⊕ WindowE,
WindowV = {vertices whose level lies in [lo, hi]}   (discrete),
WindowE = Σ (edge e, label y), frag S e lo hi,     frag S e lo hi = [max a lo, min d hi],
```

where a fragment may be empty or a point. `windowCover S D lo hi` sends a raw point to its image
under the merged `quotMk`, so two raw points are identified exactly when their merged normal forms
agree (`windowCover_eq_iff`): a fragment end is glued to its original vertex precisely when it
equals that vertex's level, and nothing else is glued. A point fragment at a vertex is glued to
that vertex; a point fragment inside an edge stays an isolated point. Every point of the window is
a window vertex or an edge point whose height lies in the window (`windowCover_surjective`).

Every closed real interval, including an empty or degenerate one, is locally path-connected as a
convex subset of `ℝ` (`locallyPathConnectedSpace_Icc`). The pinned mathlib has no such instance; the
window module activates this theorem as a local instance and adds no global instance on real
intervals. The raw window is therefore compact and locally path-connected, and the window is
Hausdorff as a subspace of `X`. A continuous surjection from a compact space onto a Hausdorff space
is a quotient map, so `windowCover` is a quotient map (`isQuotientMap_windowCover`). This is the
exact topology of the window, not only an enumeration of its points. Quotient maps transfer local
path-connectedness, so the window is compact, Hausdorff and locally path-connected
(`instCompactSpaceWindow`, `window_t2Space`, `instLocallyPathConnectedSpaceWindow`).
Local path-connectedness of a closed subset does not follow from that of `X` in general; here it
comes from the fragment presentation.

## Slabs and window transfer

`win S D ε c` is the window `[c - ε, c + ε]`. Every level of a critical list lies weakly below or
weakly above each closed gap (`value_le_or_le`). `TransferOK S ε c u` states that `c` avoids every
event `S.value i ± ε` and that, for every original level `a`, `c - ε ≤ a` implies `u - ε ≤ a`
and `a ≤ c + ε` implies `a ≤ u + ε`. Because every event is a level of `S.shifted ε`, these hold
from any height `c` of an open gap `(b k, b (k+1))` to any height `u` of the closed gap
(`transferOK_of_mem`). Under them, window vertices persist (`TransferOK.vertex_mem`), a nonempty
fragment stays nonempty (`TransferOK.frag_le`, `TransferOK.fragAff_mem`), it is nondegenerate when
`ε > 0` (`TransferOK.frag_lt`), and a fragment end at a vertex stays at that vertex
(`TransferOK.fragAff_eq_left`, `TransferOK.fragAff_eq_right`).

The raw maps that fix window vertices and move an edge parameter `s` to `fragAff a d ε c u s`
commute with the merged normal forms, so they respect the window gluing and descend along the
window quotient to

```lean
windowTransfer S D ε h : C(win S D ε c, win S D ε u)
```

for `h : TransferOK S ε c u`. An included vertex is fixed (`coe_windowTransfer_ofVertex`), and an
edge point of parameter `s` goes to the point of the same labelled edge with parameter
`fragAff a d ε c u s` (`coe_windowTransfer_ofCylinder`). For `ε > 0` and transfer hypotheses in
both directions, for instance for two heights of one open gap, the two transfers are mutually
inverse (`windowTransfer_windowTransfer`), which gives `windowTransferHomeomorph`. A slab end `b k`
is itself an event, so `TransferOK S ε (b k) c` fails there and no homeomorphism is asserted at slab
ends. The raw maps and the product cover used for the descents are private.

## The presentation

`mid S ε k` is the midpoint of gap `k` of `S.shifted ε` (`mid_mem_K`). The presentation

```lean
thickPresentation S D ε : CylinderPresentation (S.shiftedCount ε)
V j = win S D ε (b j),   E k = win S D ε (mid S ε k),
left k = windowTransfer to b k,   right k = windowTransfer to b (k+1)
```

has compact, Hausdorff and locally path-connected pieces, as instances on the specific pieces
(`instCompactSpaceThickV`, `instLocallyPathConnectedSpaceThickV`, `instT2SpaceThickV` and their
`ThickE` counterparts). Empty pieces are allowed.

On the slab `[b k, b (k+1)]`, the product of the window cover at the midpoint with the identity of
the closed gap is a continuous surjection from a compact space onto a Hausdorff space, hence a
quotient map. The raw joint map `(r, u) ↦ (transfer of r to u, u)` respects it and descends to the
joint cylinder map

```lean
slabCylinder S D ε k : C(win S D ε (mid S ε k) × Seg (S.shifted ε) k, BandSpace S D ε)
```

with first coordinate the window transfer to the height and second coordinate the height
(`coe_slabCylinder`, `snd_slabCylinder`). Here `BandSpace S D ε` is the band of `X`, the codomain of
`bandHomeomorph`. With the vertex maps `x ↦ (x, b j)` these maps are compatible: at the two slab
ends the joint map restricts to the attaching maps (`thickCompat`). The merged
`CylinderPresentation.lift` gives the continuous map `thickMap S D ε` from the realization of the
presentation to the band, with `thickMap_ofVertex`, `coe_thickMap_ofStrip` and height preservation
`thickMap_snd`.

## The homeomorphism

For `ε > 0` the map `thickMap` is bijective.

- **Injective** (`thickMap_injective`). Two points with the same image have the same height. At a
  level both are vertex points of one piece with equal first coordinates. A level is never the
  height of a strip point. Two strip points of the same height lie in the same gap, and the
  interior inverse transfer cancels the transfer.
- **Surjective** (`thickMap_surjective`). A band point `(y, u)` has `u ∈ [b 0, b m]`. If `u = b j`
  then `y` lies in `V j`. Otherwise `u` lies in an open gap, by the merged `exists_piece`, and the
  strip point over the inverse transfer of `y` to the midpoint maps to `(y, u)`.

The realization is compact and the band is Hausdorff as a subspace of `X × ℝ`, so the bijection is
a homeomorphism (`thickHomeomorph`). Followed by the inverse of `bandHomeomorph`, it gives

```lean
thickProdHomeomorph S D ε hε : realization ≃ₜ X × Band ε
```

which carries the presentation height to the thickened height `f x + t`
(`height_thickProdHomeomorph`). On the critical fiber at `b j`, a vertex point `x` goes to
`(x, b j - f x)` (`fst_thickProdHomeomorph_ofVertex`, `snd_thickProdHomeomorph_ofVertex`). On the
strip of gap `k`, a point `(x, t)` goes to `(y, t - f y)`, where `y` is the window transfer of `x`
to height `t` (`fst_thickProdHomeomorph_ofStrip`, `snd_thickProdHomeomorph_ofStrip`).

## The real slice

`thickOverIso S D ε hε` is the isomorphism over `ℝ` from `(GeometricThickening.functor ε).obj
(toOver S D)` to `Over.mk` of the presentation height, given by the inverse of
`thickProdHomeomorph`. At `ε = 0` the merged `zeroIso` identifies the thickening with the graph
object itself, which is constructible by `isConstructibleSpace_of_isRGraph`. Hence the actual
thickening of every graph object is constructible:

```lean
isConstructibleSpace_thickening (hA : IsRGraph A) (ε : ℝ≥0) :
    IsConstructibleSpace ((GeometricThickening.functor ε).obj A)
```

For an arbitrary graph object `A`, an isomorphism `A ≅ toOver S D` is carried through the actual
thickening functor and composed with the isomorphism above, so the statement does not depend on
the chosen presentation. The lift

```lean
thickeningToConstructible ε : RGraphCat ⥤ ConstructibleSpaceCat
```

is the actual `IsRGraph.ι ⋙ GeometricThickening.functor ε` with values in the full subcategory, so
it acts on every height-preserving continuous map between graph objects
(`thickeningToConstructible_comp_ι`, `thickeningToConstructible_obj_obj`,
`thickeningToConstructible_map_hom`, all by `rfl`). Followed by `quotientRGraphFunctor` and the
graph inclusion, it is literally the Reeb quotient of the actual product thickening:
`thickeningToConstructible ε ⋙ quotientRGraphFunctor ⋙ IsRGraph.ι =
IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ`, by `rfl`
(`thickeningToConstructible_comp_quotientRGraphFunctor`).

## Names and universes

`window`, `frag`, `WindowRaw`, `windowCover`, `fragAff`, `TransferOK`, `windowTransfer`,
`thickPresentation` and the other declarations live in namespace `TDA.Reeb.RGraph`. The unbundled
construction holds for finite data at an arbitrary value universe `u`; the slice packaging uses
universe `0`, as `RGraphCat` and `ConstructibleSpaceCat` do.

## Fixtures

`TDA.Reeb.RGraphThickeningExamples` works with actual windows, presentations and thickenings. The
two-parallel-edge loop `parallelData` over `0 < 1` and the levels `S01` are the merged fixtures of
`reeb-constructible-space.md`.

- **Window gluing.** In the window `[-1/2, 1/2]` both parallel fragments are glued to the common
  lower vertex (`pw_glued`), and their interior points at parameter `1/4` stay distinct
  (`pw_separate`). In the window `[-1/2, 3/2]`, which contains both common endpoints, both edges
  are glued to the lower vertex and to the upper vertex (`pwFull_glued_bot`, `pwFull_glued_top`).
  The window `[-1/2, 1/2]` is compact, Hausdorff and locally path-connected (`pw_compactSpace`,
  `pw_t2Space`, `pw_locallyPathConnectedSpace`).
- **Endpoint collapse.** At `ε = 1`, gap `k0` of the thickened loop runs from `b 0 = -1` to a level
  `b 1 ≤ 0`. Its left attaching map sends two distinct interior points of the two parallel edges to
  the common vertex (`left_collapse_apply`, `left_collapse`), so it is not injective
  (`left_not_injective`). This is a two-incident-edge attachment: the window at `-1` meets each
  edge only at the common lower vertex.
- **A window touching a vertex.** The window `[1, 3/2]` meets each parallel edge in the point
  fragment `{1}`, which is glued to the upper vertex (`touch_glued`). Every raw point is glued to
  that vertex (`touch_eq_vertex`), so the window is a single point (`pwTouch_subsingleton`).
- **A window containing no old level.** The window `[1/4, 3/4]` has no window vertex
  (`pwMid_isEmpty_V`). The edge label of its raw points respects the gluing and descends along the
  window quotient to a continuous map (`pwMidLabel`, `pwMidLabel_windowCover`), so the window is
  not preconnected (`pwMid_not_preconnected`).
- **The empty graph.** For every list of levels and every `ε`, the actual thickening of the empty
  graph is empty (`emptyThick_isEmpty`), the realization of its thickening presentation is empty
  (`emptyPresentation_isEmpty`), and the thickening is constructible
  (`emptyThick_isConstructibleSpace`).
- **A singleton at height `a`.** For the single vertex at an arbitrary height `a`, the actual
  thickening is homeomorphic to the closed segment `Band ε = [-ε, ε]` (`singletonHomeomorph`), and
  the thickened height of the point `t` of the segment is `a + t`
  (`height_singletonHomeomorph_symm`).
- **`ε = 0`.** `thickeningToConstructible 0` followed by the inclusion of constructible spaces is
  isomorphic to the inclusion of graph objects, with components the merged zero isomorphism
  (`thickeningZeroIso`, `thickeningZeroIso_hom_app`).
- **A single edge.** At `ε = 1`, on gap `k0`, a strip point at height `t` over the edge point of
  parameter `s` lies over the edge point of height `s (t + 1) / (mid + 1)`
  (`singleEdge_strip_height`): the edge crosses the upper window end, and the transfer is a linear
  stretch.
- **Disjoint edges.** For two disjoint segments `twoSegData`, the left attaching map of gap `k0` at
  `ε = 1` sends the points of the two segments to their own, distinct lower vertices
  (`twoSeg_left_apply`, `twoSeg_left_ne`), and for every `ε` the actual thickening is not
  preconnected (`twoSegThick_not_preconnected`).
- **A shifted-level collision.** For `0 < 1` at `ε = 1/2`, the shifts `0 + ε` and `1 - ε` coincide:
  the shifted set is `{-1/2, 1/2, 3/2}` (`S01_shiftedSet_half`), so the witness has three levels,
  not four (`S01_shiftedCount_half`), with middle level `1/2` (`S01_shifted_half_middle`). For the
  single edge, the vertex piece at the collision level is the whole graph
  (`collision_window_eq_univ`), and the right attaching map of the first gap sends the upper
  fragment end `c + ε = 1/2` at the midpoint `c = 0` to the original upper vertex
  (`collision_right_apply`).
- **The bundled lift.** On the parallel-edge loop at `ε = 1`, the underlying object of the lift is
  the actual thickening (`parallelThick_obj`).

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3:

- **Proposition 4.26** states that `T_ε` carries ℝ-graphs to constructible ℝ-spaces. With
  `IsRGraph` and `IsConstructibleSpace` for the source's **Reeb** and ℝ-**Top**ᶜ, this is
  `isConstructibleSpace_thickening`, for every `ε ≥ 0` and with no hypothesis beyond the graph
  input. The source proves it through piecewise linear polyhedra; here it is proved by the
  sliding-window construction of the proof of Theorem 4.27, applied to graph input.
- **The proof of Theorem 4.27**, step by step:
  - the reparametrization to `{(x, u) | u - ε ≤ f(x) ≤ u + ε}` with height `u` is `bandHomeomorph`;
  - Step 1 (compact locally path-connected fibers, from local cylinder neighbourhoods) is replaced
    by the explicit fragment quotient of the windows above;
  - Steps 2 and 3: `S_ε = {a ± ε | a ∈ S}` written in increasing order is `S.shifted ε`, and the
    critical fiber `W_k = f⁻¹[b_k - ε, b_k + ε]` is the vertex piece `V k`;
  - Step 4 writes `F_k = f⁻¹(b)` for some `b ∈ (b_k, b_{k+1})`. Its displayed decomposition
    `E_{i-1} × [b - ε, a_i] ∪ f⁻¹[a_i, a_j] ∪ E_j × [a_j, b + ε]`, its alternative
    `E_i × [b - ε, b + ε]` and Step 5's maps `α_k^u : F_k → f⁻¹[u - ε, u + ε]` all require the
    closed window `F_k = f⁻¹[b - ε, b + ε]`, the fiber of the new height over `b`. Here `F_k` is
    that window at the midpoint, the edge piece `E k`;
  - Step 5's maps `α_k(ξ, u) = (α_k^u ξ, u)`, the identity M on edges inside the window, the linear
    stretches L and R on edges crossing one window end, and the translation on an edge covering the
    window, are `slabCylinder` with `fragAff` on each edge. Step 5 calls L and R homeomorphisms,
    and then notes that the endpoint maps `α_k^{b_k}` and `α_k^{b_{k+1}}` need not be
    homeomorphisms; here they are the attaching maps `left k` and `right k`, bundled only as
    continuous maps, and the collapse fixture shows that `left k` need not be injective;
  - Step 6, the quotient principle, a fiberwise bijection and the compact-to-Hausdorff theorem, is
    `CylinderPresentation.lift`, `thickMap_injective`, `thickMap_surjective` and
    `thickHomeomorph`. Hausdorffness of the windows and of the band comes from the realization of
    the graph input.

Not claimed here: Theorem 4.27 for the broader class of constructible ℝ-spaces of the library,
whose pieces need not be Hausdorff; the Corollary after Theorem 4.27, that the critical set of
`f_ε` is exactly `S_ε`; minimality of the shifted witness; homeomorphy or injectivity of the
attaching maps; and a cylinder presentation over the shifted witness at `ε = 0`, where the zero
isomorphism is used instead.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3, Proposition 4.26 and the proof
of Theorem 4.27](https://arxiv.org/html/1501.04147v1).
