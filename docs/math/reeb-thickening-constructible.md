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
of the pieces (see `reeb-rgraph-thickening.md` for the graph case formalized here). The tools above
are prerequisites for that argument on the library's presentations, whose pieces need not be
Hausdorff. They are library statements; Theorem 4.27 itself is not claimed by this note.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.2 and §4.3](https://arxiv.org/html/1501.04147v1).
