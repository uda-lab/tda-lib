# Cylinder presentations and constructible ℝ-spaces

## Presentations

Levels are `S : CriticalValues n`, a strictly increasing `a : Fin (n + 1) → ℝ` (see
`reeb-constructible-cosheaf.md`). A cylinder presentation `P : CylinderPresentation n` has

- vertex pieces `V i` for `i : Fin (n + 1)` and edge pieces `E e` for `e : Fin n`, each an
  arbitrary topological space;
- continuous endpoint maps `left e : E e → V e.castSucc` and `right e : E e → V e.succ`.

The levels are not stored in the presentation; every construction takes `S` explicitly. Endpoint
maps need not be injective, surjective or embeddings. Empty pieces, isolated vertices and parallel
edges are allowed. There are no edge pieces below `a 0` or above `a n`.

## Realization and normal form

`P.Realization S` is the quotient of the finite sum

```text
(Σ i, V i) ⊕ (Σ e, E e × [a e, a (e+1)])
```

by the equivalence closure of exactly two identifications per edge (`EndpointRel`):
`(y, a e) ~ left e y` and `(y, a (e+1)) ~ right e y`. It carries the quotient topology, with
quotient map `CylinderPresentation.quotMk`.

The closure has a normal form (`nf`): a cylinder end goes to its vertex image, and every other
point is fixed. Two raw points are identified exactly when their normal forms agree (`eqvGen_iff`).
Hence:

- distinct vertex points are never identified (`ofVertex_eq_ofVertex_iff`);
- distinct points of an open strip `E e × K e`, with `K e = (a e, a (e+1))`, are never identified
  (`ofStrip_injective`), and no strip point equals a vertex point (`ofVertex_ne_ofStrip`);
- every point is a vertex point or a strip point (`exists_rep`).

Two cylinder ends of different edges are identified when their endpoint images coincide, through
transitivity.

## Constructors, height and universal property

`ofVertex i : V i → P.Realization S` and `ofCylinder e : E e × [a e, a (e+1)] → P.Realization S`
are continuous, and `ofCylinder_segBot`, `ofCylinder_segTop` are the two endpoint identities. The
continuous height `P.height S` is `a i` on `V i` and the real coordinate on a cylinder, by
definition.

A family of continuous maps on all vertex pieces and closed cylinders satisfying the two endpoint
equations (`CompatibleMaps`) descends to a unique continuous map on the realization (`lift`,
`lift_unique`, `existsUnique_lift`). `liftEquiv` is this correspondence as an equivalence, with
both inverse laws; the inverse restricts a map to the pieces.

## Strip and fiber normal forms

The first three are homeomorphisms onto subspaces of the realization, not only bijections.

- **Open strip.** `ofStrip e` is an open embedding of `E e × K e`, and `stripHomeomorph`
  identifies `E e × K e` with `height ⁻¹' K e`, compatibly with the height.
- **Regular fiber.** For `t ∈ K e`, `regularFiberHomeomorph` identifies `E e` with
  `height ⁻¹' {t}`.
- **Critical fiber.** `criticalFiberHomeomorph` identifies `V i` with `height ⁻¹' {a i}`. The
  subspace topology on `V i` comes from collars: an open `U ⊆ V i` is the trace of the open set
  consisting of `U` and the cylinder points within a fixed width of an end whose endpoint image
  lies in `U` (`isInducing_ofVertex`).
- **Exterior.** Heights lie in `[a 0, a n]` (`height_mem_Icc`), so nothing lies over the tails
  `lowerTail = (-∞, a 0)` and `upperTail = (a n, ∞)` (`height_preimage_lowerTail`,
  `height_preimage_upperTail`).

The closed cylinder does not embed in general. When `left e` is not injective, distinct bottom
ends of `E e × [a e, a (e+1)]` are identified (`pinch_ofCylinder_not_injective` in the fixtures).

## Topological properties

**Hausdorffness.** If every `V i` and every `E e` is Hausdorff, so is the realization
(`t2Space`). Two distinct points are separated as follows.

1. Different heights: by preimages of disjoint open sets under the continuous height.
2. Equal regular heights: both points lie in one open strip, since a regular height determines its
   edge. They are separated in the Hausdorff space `E e × K e` and carried over by the open
   embedding.
3. Equal critical heights: both are points of one `V i`. Disjoint open sets of `V i` extend to
   disjoint open collars. A collar width `δ` with `0 < δ` and `2δ ≤ a (e+1) - a e` for every `e`
   makes collars saturated and keeps collars of disjoint sets disjoint (`exists_collarWidth`,
   `disjoint_collar`).

The proof uses neither compactness nor properness. It uses no separation property of the quotient
itself. With Hausdorff pieces, no non-Hausdorff example exists, so none is included among the
fixtures.

**Compactness and local path-connectedness.** If all pieces are compact, the realization is compact
(`compactSpace`): it is a quotient of a finite sum of compact spaces. If all pieces are locally
path-connected, so is the realization (`locallyPathConnectedSpace`), since closed segments are
locally path-connected (`locallyPathConnectedSpace_seg`). All three results are registered as
conditional instances.

## Finite data

`ofFiniteData D` turns finite incidence data `D : FiniteReebData n` into a presentation with
discrete pieces. Its realization is the same `Realization`, not a separate model, and it is
Hausdorff, compact and locally path-connected with no further hypothesis. Six `simp` lemmas expose
its projections. A map of finite data `φ : D.Hom D'` gives a continuous map
`realizeHom S φ` between the realizations at the same `S`, defined through `lift`. It preserves
height (`height_realizeHom`), sends the identity to the identity (`realizeHom_id`) and preserves
composition (`realizeHom_comp`).

## Fixtures

`TDA.Reeb.ConstructibleSpaceExamples` states every fixture about the actual quotient:

- `n = 0`: every presentation realizes `V 0` at the single height (`homeomorphZero`);
- all pieces empty: an empty realization;
- missing edges: a point at each of two levels and no edge gives a realization that is not
  preconnected;
- an empty vertex piece forces the adjacent edge pieces empty; nothing lies over `[a e, a (e+1))`
  when `V e.castSucc` is empty, and for concrete data the critical fiber at an empty `V 0` is empty;
- noninjective attachment: a two-point edge piece with constant left endpoint map; the bottom ends
  are identified, while the top ends and regular points stay apart;
- parallel edges: two edges between the same vertices give a regular fiber with two points;
- a disconnected realization, two disjoint segments, separated by a label obtained from `lift`;
- empty fibers below `a 0` and above `a n`.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.2, define a constructible ℝ-space from
critical values `a 0 < ⋯ < a n`, locally path-connected compact spaces `𝕍ᵢ` and `𝔼ᵢ`, and
continuous maps `𝕝ᵢ : 𝔼ᵢ → 𝕍ᵢ`, `𝕣ᵢ : 𝔼ᵢ → 𝕍ᵢ₊₁`. The space is the quotient of the disjoint
union of `𝕍ᵢ × {aᵢ}` and `𝔼ᵢ × [aᵢ, aᵢ₊₁]` by the two endpoint identifications, and the height is
the projection to the second factor.

- `Realization` is this quotient. Compactness and local path-connectedness are hypotheses of
  `compactSpace` and `locallyPathConnectedSpace`, not part of the data. Hausdorffness is proved
  from Hausdorff pieces alone.
- The source's constructible ℝ-spaces form a full subcategory of ℝ-spaces: morphisms are all
  continuous height-preserving maps. A map between cylinder pieces may vary with height, so finite
  data maps do not describe all morphisms. `realizeHom` realizes only maps of finite data.
- Lemma 2.4, the cylinder principle, states that the fiber inclusions `𝕍ᵢ → f⁻¹(aᵢ₋₁, aᵢ₊₁)` and
  `𝔼ᵢ → f⁻¹(aᵢ, aᵢ₊₁)` are homotopy equivalences. The open-strip homeomorphism
  `E e × K e ≃ height ⁻¹' K e` is the geometric input for the second; neither homotopy
  equivalence is formalized here.

Not claimed here: the category of constructible ℝ-spaces as objects over ℝ isomorphic to a
realization, its `TopCat` or `Over` packaging, maps of general presentations, the comparison with
the Reeb quotient, the homotopy equivalences of Lemma 2.4 over stars, changes of the critical
levels, and any embedding of a closed cylinder.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.2](https://arxiv.org/html/1501.04147v1).
