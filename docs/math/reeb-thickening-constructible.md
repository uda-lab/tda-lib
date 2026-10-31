# Thickenings of constructible ℝ-spaces: shared tools

## Setting

A cylinder presentation `P : CylinderPresentation n` with levels `S : CriticalValues n` has vertex
pieces `V i`, edge pieces `E e` and continuous endpoint maps; its realization `X = P.Realization S`
is the quotient of `(Σ i, V i) ⊕ (Σ e, E e × [a e, a (e+1)])` by the two endpoint identifications
per edge (see `reeb-constructible-space.md`). The thickening is `X × Band ε` with
`Band ε = [-ε, ε]` and height `f x + t` (see `reeb-geometric-thickening.md`).

The pieces are arbitrary topological spaces. Nothing below assumes that a piece, the realization
or the thickening is Hausdorff, compact or locally path-connected. This note records the shared
point-set tools and the morphisms of presentations used to describe the thickening of such a
realization; no statement of the source is claimed by them alone.

## Point-set tools

`TDA.Topology.QuotientProduct` proves two product facts for quotient maps.

- Locally compact factor. For a quotient map `q : A → B` and a locally compact space `I`, the maps
  `q × id_I` and `id_I × q` are quotient maps (`isQuotientMap_prodMap_id_left`,
  `isQuotientMap_prodMap_id_right`). There is no separation hypothesis on `A` or `B`. The proof
  identifies open sets with continuous maps to the Sierpiński space and uses the exponential law
  for the locally compact factor (mathlib's `IsQuotientMap.continuous_lift_prod_left`). Compact
  real intervals `[a, b]`, including empty and one-point intervals, are the case used
  (`isQuotientMap_prodMap_id_Icc`).
- Proper factor. A proper surjection `f` stays a quotient map after product with the identity of
  an arbitrary space `E` (`isQuotientMap_prodMap_id_of_isProperMap`): `id_E × f` is proper,
  hence closed, continuous and surjective. A continuous surjection from a compact space onto a
  Hausdorff space is proper, so the same holds for it with `E` arbitrary
  (`isQuotientMap_prodMap_id_of_compactSpace`). Only the source and the target of `f` carry these
  hypotheses. This is the form intended for the scalar polygon and gluing maps of a thickened
  cylinder, which go between compact subsets of `ℝ` or `ℝ × ℝ`. Product stability is not claimed
  for arbitrary quotient maps; it fails in general.

Fixtures (`TDA.Topology.QuotientProductExamples`): the sign map `x ↦ 0 < x` from `ℝ` onto the
Sierpiński space is a quotient map onto a non-Hausdorff space, and its product with `[0, 1]` is a
quotient map onto the non-Hausdorff space `Prop × [0, 1]`; the map `(s, u) ↦ (s u, u)` from the
square onto the triangle `0 ≤ x ≤ u ≤ 1` collapses the edge `u = 0` to a corner and stays a
quotient map after product with any space.

## Presentation morphisms

`TDA.Reeb.ConstructibleHom` defines morphisms of presentations over the same number of levels.

- `CylinderPresentation.Hom P Q` consists of continuous maps `V i → V' i` and `E e → E' e` with
  `left' ∘ edge e = vertex e.castSucc ∘ left` and `right' ∘ edge e = vertex e.succ ∘ right`.
  Identity, composition and their laws hold componentwise.
- On a fixed level list `S`, `Hom.realize` is the continuous map of realizations that is the
  vertex map on vertex points and `edge e × id` on cylinder points (`realize_ofVertex`,
  `realize_ofCylinder`, `realize_ofStrip`). It is the descent of `Hom.compatibleMaps` through the
  universal property `lift`, preserves height (`height_realize`) and is functorial (`realize_id`,
  `realize_comp`). In universe `0`, `Hom.toOverHom` is the corresponding morphism of the real
  slice, with identity and composition laws.
- A map of finite data is a morphism of the discrete presentations
  (`FiniteReebData.Hom.toPresentationHom`), and its realization is `realizeHom`
  (`realize_toPresentationHom`).

Such morphisms keep the grid and the cylinder parameter: a height-preserving map of realizations
that moves cylinder points along the parameter, or changes the level list, is in general not a
realized morphism.

## Thickened raw pieces

For every locally compact `I`, `quotMk × id_I : Raw × I → X × I` is a quotient map
(`isQuotientMap_prodMap_quotMk`), and two raw pairs have the same image exactly when their normal
forms and their second coordinates agree (`prodMap_quotMk_eq_iff`). For `I = Band ε`
(`isQuotientMap_rawBandMap`), `X × Band ε` is the quotient of the thickened raw pieces
`Σ V i × Band ε ⊕ Σ E e × [a e, a (e+1)] × Band ε` by the endpoint identifications, each times the
identity of the band. A continuous map out of `X × Band ε` is therefore the same as a family of
continuous maps on the thickened vertex pieces and cylinders satisfying the two endpoint equations.

This replaces a general statement that realization commutes with colimits of attachment diagrams:
the diagrams used for the thickening are over one fixed grid, their maps are presentation
morphisms, and their colimit is described by this quotient together with `lift` and `hom_ext`.
No theorem about arbitrary colimits of constructible spaces, and no general restriction of
quotient maps to subsets, is claimed.

Fixtures (`TDA.Reeb.ConstructibleHomExamples`): the collapse of two disjoint segments onto two
parallel edges between single vertices identifies the two vertex points at level `0` and keeps
regular points apart; a presentation whose pieces are the Sierpiński space, with non-Hausdorff
realization, admits morphisms from discrete segments and onto a single segment, and its thickened
raw pieces present its thickening; the presentation with empty pieces maps uniquely to every
presentation.

## One cylinder

`TDA.Reeb.ThickeningSlice` and `TDA.Reeb.ThickeningCylinder` present the thickening of one
cylinder `E × [a, d]`, for `a ≤ d`, `ε ≥ 0` and an arbitrary topological space `E`. The thickened
space is `E × [a, d] × [-ε, ε]` with height `s + t` (`cylinderHeight`); it is the geometric
thickening of `E × [a, d]` with the segment coordinate as height, after reassociating the product
(`cylinderHeight_eq`).

- Slices. Under `(s, t) ↦ (s, u = s + t)` the thickened segment becomes the parallelogram
  `{(s, u) | s ∈ J(u)}` with `J(u) = [max a (u - ε), min d (u + ε)]`, possibly empty or a point.
  When `a` (or `d`) lies in `J(u)` it is the lower (or upper) end. Between grid levels the ends
  move affinely; the transfer `fragAff` from the slice at `c` to the slice at `u` fixes a parameter
  at a segment end (`SliceTransfer.fragAff_eq_left`, `fragAff_eq_right`), and with transfer
  hypotheses in both directions the transfers are mutually inverse, with no nondegeneracy
  assumption (`SliceTransfer.fragAff_fragAff`). For a point slice the denominator of `fragAff`
  is `0`, Lean's division returns `0`, and the transfer is the constant lower end.
- Presentation. On any grid `G` listing the four events `a ± ε`, `d ± ε`, `cylinderThick` has
  vertex piece `E × J(b j)`, edge piece `E × J(mid k)` and endpoint maps the transfers to the slab
  ends. The endpoint maps collapse the reference slice at an end with a point slice; no inverse is
  asked of them. Pieces are empty where the slice is, and compact and locally path-connected when
  `E` is. The vertex strip is `a = d`; `ε = 0` is not treated separately.
- Homeomorphism. `toCylinder` sends `(y, σ)` at level `b j` to `(y, σ, b j - σ)` and
  `((y, σ), u)` to `(y, s, u - s)`, `s = fragAff (mid k) u σ`, and preserves height. The inverse
  is built in parallelogram coordinates on the finite closed cover by level slices and slab
  polygons. On a level slice it is the vertex inclusion. On a slab polygon it is the cylinder map
  descended along `id_E × polygonMap k`, which is a quotient map for every `E` because the scalar
  polygon map `(σ, u) ↦ (fragAff (mid k) u σ, u)` is a continuous surjection from a compact space
  onto a subset of `ℝ × ℝ`, hence proper. The cylinder map is constant on its fibres: inside the
  slab the transfer is injective, and at a collapsing end the realization identifies the cylinder
  end with its vertex image. Both inverse laws hold, so `cylinderThickHomeomorph` is a
  height-preserving homeomorphism for every topological `E`, with no Hausdorff or compactness
  hypothesis; `vertexStripHomeomorph` is the vertex strip `E × [-ε, ε]` with height `a + t`.
- Boundary strips. On a common grid listing the events of `[a, d]`, `[a, a]` and `[d, d]`,
  `botIncl` and `topIncl` are presentation morphisms from the strip presentations into the
  cylinder presentation, and `mapSpace f` is the morphism `f × id` for a continuous `f : E → E'`.
  The homeomorphisms turn them into `(y, t) ↦ (y, a, t)`, `(y, t) ↦ (y, d, t)` and `f × id`. For
  an endpoint map `f : E → V`, the bottom strip inclusion and `mapSpace f` into the vertex strip
  of `V` are therefore described by the pair of identities `cylinderThickHomeomorph_realize_botIncl`
  and `vertexStripHomeomorph_realize_mapSpace`, and `botIncl_comp_mapSpace` records their
  compatibility with `mapSpace` at the level of presentation morphisms.
- The grid of one segment. For `a < d`, `pairThick` is the construction on the shifted witness of
  the two-level grid `pair a d`, whose levels are exactly the distinct values among `a ± ε`,
  `d ± ε`, with `pairThickHomeomorph` and the strip inclusions `pairBotIncl`, `pairTopIncl`.

Global assembly of a whole presentation and the constructibility of its thickening are not part
of these modules.

Fixtures (`TDA.Reeb.ThickeningSliceExamples`, `TDA.Reeb.ThickeningCylinderExamples`): point slices
and constant transfers at `ε = 0`; a vertex strip; coincident events `d - ε = a + ε`; a slab
meeting `[a - ε, d + ε]` in a corner only, with empty polygon, empty edge piece and a point vertex
piece at the corner; a non-injective collapsing endpoint map; and the Sierpiński space `E = Prop`,
whose pieces and realization are not Hausdorff while the homeomorphism applies.

## Windows and transfers

`TDA.Reeb.ThickeningWindow` defines the pieces of the thickening presentation. For a height `c`,
write `J(c) = [max a (c - ε), min d (c + ε)]` for the slice of a segment `[a, d]`
(`Thickening.slice`); for a vertex strip `[a i, a i]` it is `{a i}` or empty.

- Window. The raw window at `c` is `Σ V i × J_i(c) ⊕ Σ E e × J_e(c)`, with
  `J_i(c) = slice (a i) (a i) ε c` and `J_e(c) = slice (a e) (a (e+1)) ε c`. The window
  `P.Window S ε c` is its quotient by "same point of `X`", with the quotient topology. So `windowMk`
  is a quotient map by definition, also after product with a locally compact space
  (`isQuotientMap_prodMap_windowMk`), and two raw window points are identified exactly when their
  normal forms in `P` agree (`windowMk_eq_iff`). `windowToSpace` is a continuous injection into `X`
  with height in `[c - ε, c + ε]`. The window is compact, resp. locally path-connected, when all
  pieces are, as a quotient of a finite sum of products of pieces with compact intervals; it is
  empty when all pieces are. That the window is homeomorphic to the subspace `f⁻¹[c - ε, c + ε]`
  of `X` is not claimed; without a Hausdorff hypothesis, the quotient topology is the one used.
- Transfer. Under `RGraph.TransferOK S ε c u`, every slice parameter moves by the affine fragment
  map `RGraph.fragAff` of its segment (`rawTransfer`); vertex parameters stay at `a i`. Slice ends
  at segment ends stay there, so glued points stay glued and the map descends to the continuous
  `transfer : Window c → Window u` (`windowMk_rawTransfer_eq`). In `X` it fixes vertex points and
  moves an edge point at parameter `σ` to `fragAff … c u σ` (`windowToSpace_transfer_inl`,
  `windowToSpace_transfer_inr`). At a slab end with a point slice it collapses a whole edge
  slice, so it need not be injective. Along a locally compact set `U` of target heights the
  transfers form one jointly continuous map `transferFamily : Window c × U → X`, descended along
  `windowMk × id_U`.
- Interior inverse. With transfer hypotheses in both directions, for instance two heights of one
  open slab of a grid listing the shifted levels, the transfers are mutually inverse
  (`transfer_transfer`, `transferHomeomorph`). This holds for every `ε ≥ 0`: at a point slice the
  affine map is the constant lower end, by Lean's division by zero.

Fixtures (`TDA.Reeb.ThickeningWindowExamples`): for the single segment at `ε = 1/4`, the transfer
of the window at `0` to the slab end `-1/4` identifies two distinct edge points; at `ε = 0` the
transfer between `1/2` and `1/4` is a homeomorphism; a window of the presentation whose pieces are
the Sierpiński space is compact and locally path-connected but not Hausdorff; windows far from the
levels, and all windows of the presentation with empty pieces, are empty.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.2, define constructible ℝ-spaces as
realizations of compact locally path-connected pieces, and Theorem 4.27 states that the thickening
of a constructible ℝ-space is constructible; its proof builds the thickening from the thickenings
of the pieces (see `reeb-rgraph-thickening.md` for the graph case formalized here). The tools and
the one-cylinder presentation above are prerequisites for that argument on the library's
presentations, whose pieces need not be Hausdorff. They are library statements; Theorem 4.27
itself is not claimed by this note.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.2 and §4.3](https://arxiv.org/html/1501.04147v1).
