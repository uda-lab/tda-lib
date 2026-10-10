# Constructible cosheaves from finite data

## Setting

Levels are `S : CriticalValues n` with `a 0 < ⋯ < a n`, stars `J i = (a (i-1), a (i+1))` and gaps
`K e = (a e, a (e+1))`, with infinite ends at the extremes (see `reeb-constructible-cosheaf.md`).
Finite incidence data `D : FiniteReebData.{u} n` consist of finite vertex sets `V i`, finite edge
sets `E e` and endpoint functions `left e : E e → V e.castSucc` and `right e : E e → V e.succ`, in
an arbitrary universe `u`. A map of data `D.Hom D'` consists of vertex and edge functions commuting
with both endpoint functions; `Hom.id`, `Hom.comp` and, for bijective components, `Hom.inv` are
the only operations used. No category instance on `FiniteReebData` is used.

For `F : OpenInterval ⥤ Type u` with finite values, `S.extract F` has `V i = F (J i)`,
`E e = F (K e)` and the actual inclusion maps `F (K e ≤ J e.castSucc)` and `F (K e ≤ J e.succ)`
as endpoint functions.

## The cosheaf of finite data

`D.toCosheaf S` is the actual path-component cosheaf `intervalComponents ((ofFiniteData D).height S)`
of the cylinder realization of `D`, whose pieces are discrete (see `reeb-constructible-space.md`).
Write `C_D` for it. No second, combinatorial cosheaf is constructed.

- `C_D` is constructible at `S` (`toCosheaf_isConstructibleAt`, from
  `finiteData_isConstructibleAt`).
- `C_D` is an interval cosheaf for covers indexed in any universe (`toCosheaf_isIntervalCosheaf`,
  from `intervalComponents_isIntervalCosheaf`).

No compactness, Hausdorffness or local path-connectedness hypothesis enters, and the value universe
is arbitrary.

## Labels

A discrete space is its own set of path components (`zerothHomotopyEquivOfDiscrete`). Composing
the inverse of this equivalence with the component bijections of the cylinder realization (see
`reeb-constructible-cylinder.md`) gives the labels, which run from the data to components:

```text
vertexLabel S i : D.V i ≃ C_D (J i)     v ↦ class of the vertex point ofVertex i v
edgeLabel S e   : D.E e ≃ C_D (K e)     y ↦ class of the strip point ofStrip e (y, t)
```

The edge label is defined at `t = gapMidpoint e`, the midpoint of `K e`. Because the edge component
bijection does not depend on the regular height, the edge label equals the composite at every
`t ∈ K e` (`edgeLabel_eq`), and `edgeLabel_apply` holds at every regular height. No retraction is
claimed to be natural.

The incidence maps of `C_D` correspond to the endpoint functions of `D`:

```text
C_D (K e ≤ J e.castSucc) (edgeLabel e y) = vertexLabel e.castSucc (left e y)
C_D (K e ≤ J e.succ)     (edgeLabel e y) = vertexLabel e.succ (right e y)
```

(`map_K_le_J_castSucc_edgeLabel`, `map_K_le_J_succ_edgeLabel`), by the incidence theorems for
component bijections applied to discrete pieces.

## Finite round trip

The labels form a map `toExtractHom : D.Hom (S.extract C_D)` with bijective components. Its
inverse `fromExtractHom` is `Hom.inv`, with the inverse labels as components
(`fromExtractHom_v_apply`, `fromExtractHom_e_apply`). `extract_toCosheaf_iso` states both
composition laws. The data `D` and `S.extract C_D` are thus isomorphic as finite data, and the
identification is the specific label map, not an abstract bijection.

## Labelled existence and uniqueness

Let `G : OpenInterval ⥤ Type u` be constructible at `S` with `IsIntervalCosheaf.{0} G`, and let
`j : D.Hom (S.extract G)` be any map of finite data. The labelled lift
`toCosheafLift hG hGc j : C_D ⟶ G` is the extension `ShortMaps.extend` of the short maps
`ShortMaps.ofHom (fromExtractHom.comp j)` (`labelledShortMaps`).

- On labels it computes as `j`: `α (J i) (vertexLabel i x) = j.v i x` and
  `α (K e) (edgeLabel e x) = j.e e x` (`toCosheafLift_app_J`, `toCosheafLift_app_K`).
- It is the only natural transformation with these values (`toCosheafLift_unique`,
  `existsUnique_natTrans_labelled`). The labels are surjective, so two such transformations agree
  on every star and gap, and a transformation is determined by its star and gap components
  (`natTrans_ext`).
- If `j` has bijective components, the lift is an isomorphism (`isIso_toCosheafLift`), by the
  isomorphism criterion `ShortMaps.isIso_extend`.
- Its restriction to extracted data is `fromExtractHom.comp j`
  (`natTransEquivDiagramHom_toCosheafLift`).

Uniqueness needs no bijectivity of `j`. It is uniqueness relative to the specified labels: it is
neither equality of cosheaf objects nor uniqueness of unlabelled automorphisms, since different
labellings of the same data can give different transformations. `IsIntervalCosheaf.{0} G` is the
hypothesis of the extension theorem.

## Reconstruction

For `F` constructible at `S` with `IsIntervalCosheaf.{0} F`, apply the labelled lift to the
extracted data `D = S.extract F` and the identity map:

```text
realizeExtractIso hF hFc : (S.extract F hF.finite).toCosheaf S ≅ F
```

- The hom sends the canonical labels back to the original elements:
  `hom (J i) (vertexLabel i x) = x` and `hom (K e) (edgeLabel e x) = x`
  (`realizeExtractIso_hom_app_J`, `realizeExtractIso_hom_app_K`).
- The inverse is the label map on stars and gaps (`realizeExtractIso_inv_app_J`,
  `realizeExtractIso_inv_app_K`).
- It is the unique transformation with these values (`realizeExtractIso_hom_unique`), and its
  restriction to extracted data is `fromExtractHom` (`natTransEquivDiagramHom_realizeExtractIso`).
- On an interval inside a gap containing a regular height `t`, or inside a star containing its
  level, its value on the class of a strip or vertex point of the realization maps to the original
  element in the gap or star (`map_realizeExtractIso_hom_app_strip`,
  `map_realizeExtractIso_hom_app_vertex`). That inclusion is bijective by constructibility, so
  this determines the value.

This is an isomorphism in the functor category on the whole interval category, including `⊥`,
bounded intervals, rays and `⊤`. On an interval meeting several levels its components are those of
the glued extension, not star or gap values.

**Refinement of the levels.** If the levels of `S` are among those of `T`, a cosheaf constructible
at `S` is constructible at `T` (`IsConstructibleAt.of_refines`). Its reconstructions at `S` and at
`T` compare through `F`. Their finite data have different numbers of levels, so no map of finite
data with a common index relates them.

## Fixtures

`TDA.Reeb.ConstructibleRepresentationExamples` uses actual component cosheaves of realized finite
data and arbitrary constructible interval cosheaves:

- the pinch over levels `0 < 1`, whose two edges both start at vertex `0`: the left incidence
  merges the two labelled edges and the right incidence separates them; the edge label is computed
  at the regular height `3/4`; the reconstruction preserves named labels on the ray stars
  `J 0 = (-∞, 1)` and `J 1 = (0, ∞)` and on the gap, the reconstructed cosheaf still merges the two
  edges, and both inverse identities of the natural isomorphism hold;
- the pinch reconstruction on intervals meeting both levels: on any interval containing a level it
  sends the class of each realized vertex point to the class of the original vertex, and on any
  interval containing a regular height it does the same for strip points; these are stated on
  `⊤`, on `(-1, 2)` and on the rays `(-∞, 2)` and `(-1, ∞)`; on `ℝ` the class of vertex `0` at
  level `0` equals the class of each vertex at level `1`, in the original and in the reconstructed
  cosheaf, so the two stars glue along the gap, and the reconstruction sends the class coming from
  one star to the class coming from the other;
- pinch boundary cases: on `(1/4, 3/4)`, which contains no level, the reconstruction is computed
  on strip classes; `⊥` and both exterior tails have empty values for the reconstructed and the
  original cosheaf;
- the pinch at value universe `1`;
- empty data: the zero cosheaf maps uniquely to every `Type`-valued constructible interval cosheaf
  at the same levels, and the vertex and edge sets of its extracted data are empty;
- `n = 0` with one vertex: the value on `ℝ` has one element, and the reconstruction on `ℝ = J 0`
  is computed through `J 0 ≤ ⊤`;
- two parallel edges with equal endpoints: the identity labelling lifts to the identity and the
  swap labelling to a different automorphism;
- insertion of the level `1` into `{0, 2}` for the same `F` constructible at `{0, 2}`: the new
  middle star `(0, 2)` is the old gap; both inserted incidences of the data extracted at
  `{0, 1, 2}` are bijective; transported along that equality of intervals they are the covariant
  inclusions of the new gaps `(0, 1)` and `(1, 2)` into the old gap
  (`insertion_right_transport`, `insertion_left_transport`); the two reconstructions compare
  through `F`.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §3.3–§3.4:

- **Proposition 3.18**, existence: finite sets `V_i`, `E_i` and maps `ℓ_i : E_i → V_i`,
  `r_i : E_i → V_{i+1}` give a constructible cosheaf with critical set `S` and bijections
  `V^F_i ≅ V_i`, `E^F_i ≅ E_i` under which `ℓ^F_i`, `r^F_i` correspond to `ℓ_i`, `r_i`. As in the
  source proof, the cosheaf is the Reeb cosheaf of the realized ℝ-graph, here `toCosheaf`, and its
  cosheaf and constructibility properties are Propositions 3.15 and 3.16. The bijections are the
  labels in the direction from the data to the cosheaf, and their compatibility with the endpoint
  maps is `toExtractHom`. Notation 3.11 is `extract`, with the same indices and directions.
- **Proposition 3.18**, uniqueness, "any two such cosheaves are canonically isomorphic": the source
  proof composes the identifications through the data and applies Corollary 3.14. Here the
  statement is `existsUnique_natTrans_labelled` for arbitrary data and an arbitrary compatible map
  `j`, with `isIso_toCosheafLift` when `j` is bijective. Unique existence of the transformation is
  the map classification of **Proposition 3.12** (`natTransEquivShortMaps`) applied to the labelled
  short maps, so this formulation combines Propositions 3.18 and 3.12; the isomorphism conclusion
  is **Corollary 3.14**. The source's two-cosheaf form follows by composing one bijective lift with
  the inverse of another; it is not stated as a separate theorem.
- The reconstruction `realizeExtractIso` is Proposition 3.18 applied to the data extracted from a
  constructible cosheaf, with the identity as compatible map.
- The existence proof follows the topological route of the proof of Proposition 3.18, not the
  colimit construction sketched in Remark 3.19.

Not claimed here: an equivalence of categories between constructible cosheaves and finite data, a
comparison of the reconstructions at a refined list of levels with geometric subdivision of
ℝ-graphs, an executable extraction algorithm, and uniqueness of unlabelled isomorphisms. The
category structure on finite data of `reeb-rgraph.md` is not used here.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/html/1501.04147v1).
