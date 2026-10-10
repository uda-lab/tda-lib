# Finite ℝ-graphs: maps, critical refinements and the Reeb quotient

## Setting

Levels are `S : CriticalValues n` with `a 0 < ⋯ < a n` and gaps `K e = (a e, a (e+1))` (see
`reeb-constructible-cosheaf.md`). Finite data `D : FiniteReebData n` consist of finite types
`V i` and `E e` and endpoint maps `left e : E e → V e.castSucc` and `right e : E e → V e.succ`.
A map `D.Hom D'` is a family of maps on vertex and edge sets commuting with both endpoint maps.
Empty sets, isolated vertices, parallel edges and noninjective endpoint maps are allowed, and
edges are not encoded by a relation on vertices, so parallel edges stay distinct.

The realization `X = (ofFiniteData D).Realization S` gives every piece the discrete topology
and is compact and Hausdorff (see `reeb-constructible-space.md`). Write `h` for its height.

## Maps over a common level list

`HeightMap S D D'` is the type of **all** continuous maps `g : X → X'` with `h' ∘ g = h`. No
cellwise condition is imposed. The classification `homEquiv S : D.Hom D' ≃ HeightMap S D D'` has
the forward map `realizeHom` and both inverse laws.

1. **Vertex component.** `g` maps the critical fiber `h⁻¹{a i} ≅ V i` into `h'⁻¹{a i} ≅ V' i`;
   this is `vertexFiberMap g i` (`apply_ofVertex`).
2. **Edge component.** For `t ∈ K e`, the regular fiber map `regularFiberMap g e t : E e → E' e`
   reads the strip label of `g (y, t)`. On path components it does not depend on `t`, and since
   `E' e` is discrete the map itself does not (`regularFiberMap_indep_of_discrete`). `edgeMap`
   reads it at the chosen base point `basePt S e`, so `g (y, t) = (edgeMap y, t)` on the whole
   open strip (`apply_ofStrip`).
3. **Incidence.** On the closed segment `[a e, a (e+1)]`, `t ↦ g (y, t)` and `t ↦ (edgeMap y, t)`
   are continuous and agree on the dense open gap. The target is Hausdorff, so they agree at both
   ends (`apply_ofCylinder`). The ends are the vertex points of `left y` and `left (edgeMap y)`
   (respectively `right`), and `ofVertex` is injective, so both incidence squares hold (`toHom`).
   No injectivity of `left` or `right` is used.
4. **Inverse laws.** `g` and the realization of `toHom g` agree on generators, so they are equal
   (`hom_ext`). Conversely, the data of a realized map are recovered from vertex points by
   injectivity of `ofVertex` and from strip points by `regularFiberMap_realizeHom`.

## Graph objects

Finite data form a category (`FiniteReebData.instCategory`). The realization functor
`realizationFunctor S : FiniteReebData n ⥤ Over (TopCat.of ℝ)` takes values in the real slice,
where `reeb-quotient-comparison.md` defines the Reeb quotient endofunctor. Slice morphisms
between realizations are exactly height-preserving maps (`overHomEquiv`), so the functor is
fully faithful (`realizationFullyFaithful`).

A slice object `A` is a graph object, `IsRGraph A`, when `A ≅ toOver T D` for some `m`,
`T : CriticalValues m` and `D : FiniteReebData m`. Graph objects form the full subcategory
`RGraphCat`, so their morphisms are all height-preserving continuous maps. A presentation is
evidence for the property, not an object. The packaging lives in universe `0`, the universe of the
real slice; the classification above holds in every universe.

## Refinement

Let `T : CriticalValues m` with `range S.value ⊆ range T.value`. The refined data
`refineData hST D` take as vertex set at the `T`-level `t j` the fiber `h⁻¹{t j}`, and as edge set
of the `T`-gap `j` the fiber over its base point `basePt T j`. Both are finite (`finite_fiber`).

- **Endpoints.** A point `y` of the base fiber of `j` is a strip point of some `S`-gap `e`
  (`exists_strip_rep`). Since `T` refines `S`, the closed `T`-segment of `j` lies in the closed
  `S`-segment of `e` (`Icc_subset_of_mem`). Following the cylinder of `y` gives a continuous
  `edgePoint y` on the `T`-segment, independent of the chosen strip description
  (`edgePoint_eq`). Its two ends are the refined `left` and `right`.
- **Homeomorphism.** The universal property gives `refineMap` from the refined realization over
  `T`: vertex points go to themselves and `(y, t)` goes to `edgePoint y t`. It preserves height.
  It is injective, because points at a `T`-level are fiber points and distinct edges through a
  base fiber stay apart at heights that are not `S`-levels (`edgePoint_inj`). It is surjective,
  because a point whose height is not a `T`-level lies in a `T`-gap and on an `S`-strip whose
  `S`-gap contains the base point of that `T`-gap. The source is compact and the target Hausdorff,
  so it is a homeomorphism (`refineHomeomorph`), and `refineIso` is the slice isomorphism.
- **Inserted levels.** If `t j ∈ K e`, the vertex set at `t j` is `E e` (`refineVEquiv`). Both
  adjacent `T`-gaps have base points in `K e` (`basePt_mem_K_of_succ`,
  `basePt_mem_K_of_castSucc`), so their edge sets are `E e` (`refineEEquiv`), and both incidences
  are the identity (`refine_right_eq`, `refine_left_eq`). The endpoint maps into a level that is
  not an `S`-level are bijective (`right_bijective`, `left_bijective`): the inserted vertices have
  degree two.
- **Old levels.** If `t j = a i`, the vertex set is `V i` (`refineVEquivOld`). A `T`-gap based in
  `K e` ends at an old level only at `a (e+1)` and starts at one only at `a e`
  (`old_level_succ`, `old_level_castSucc`); there the refined incidences are `D.right e` and
  `D.left e` (`refine_right_old`, `refine_left_old`).
- **Exterior levels and gaps** outside `[a 0, a n]` carry empty sets (`isEmpty_refine_V`,
  `isEmpty_refine_E`, from `isEmpty_fiber`).

These identifications cover every vertex set, edge set and incidence of the refined data. Up to
them, inserting a regular level into `K e` replaces the edge set `E e` by a new vertex set and two
copies of `E e` with identity incidences, and exterior levels add empty pieces. The refined data
are built from fibers; no separate insertion constructor is used.

## Common refinement, coherence and presentation independence

The sorted union of two level lists refines both (`exists_common_refinement`), so any two graph
objects have presentations over one list (`exists_common_presentation`).

For `iA : A ≅ toOver T DA` and `iB : B ≅ toOver T DB`, the classification
`homEquivOfIso iA iB : (A ⟶ B) ≃ (DA ⟶ DB)` conjugates by the presentations and applies full
faithfulness (`homEquivOfIso_apply`). It preserves identities and composition
(`homEquivOfIso_id`, `homEquivOfIso_comp`). For two presentations of each object:

- over the same `T`, the bijections are conjugate by the data isomorphisms `presIso`
  (`homEquivOfIso_conj`);
- refining both presentations along `T ⊆ U` commutes with the classification through the
  transfer `refineHom` (`homEquivOfIso_refine`);
- for presentations over `T` and `T'` and any common refinement `U`,

  ```text
  refineHom hTU (homEquivOfIso iA iB f) ≫ σ_B = σ_A ≫ refineHom hT'U (homEquivOfIso iA' iB' f)
  ```

  where `σ_A` and `σ_B` are the `presIso` of the presentations transferred to `U`
  (`homEquivOfIso_independent`).

So the finite description of a morphism is independent of the presentations up to these
canonical data isomorphisms; mere equicardinality of the Hom sets is not what is stated. For
`S ⊆ T ⊆ U`, the two refinements of `D` over `U` are related by the explicit data isomorphism
`refineCoherentIso`, whose square with the refinement isomorphisms commutes
(`refineCoherentIso_comm`); it is the unique finite map with that property (`refine_coherent`).
`refineHom`, `presIso` and `refineCoherentIso` are obtained from full faithfulness rather than
combinatorially, and the lemmas above determine them.

## The Reeb quotient

Every fiber of `X` is homeomorphic to a vertex set or an edge set, or is empty, so it is discrete
(`discreteTopology_fiber`). A path of constant height is a path in one discrete fiber and is
constant, so the Reeb relation of `h` is equality (`reebRel_iff_eq`). The identity of `X`
therefore descends through the universal property of the quotient to an inverse `projInv` of the
projection, and `ReebQuotient.proj` is a height-preserving homeomorphism (`projHomeomorph`,
`height_projHomeomorph`). Neither compactness nor injectivity of the height is used; the height
of a graph is usually not injective.

Naturality: for every height-preserving `g`, `projInv ∘ ReebQuotient.map g = g ∘ projInv`
(`projInv_natural`). The point `projNatTrans : 𝟭 ⟶ Q` of the Reeb quotient endofunctor has an
invertible component at every realization (`isIso_projNatTrans_app_toOver`), hence at every graph
object by transport along a presenting isomorphism. Its restriction to graph objects is a natural
isomorphism (`isIso_projNatTrans_rgraph`, `projNatIso`).

## Fibers of arbitrary presentations

For an arbitrary presentation `P`, fibers outside `[a 0, a n]` are empty (`isEmpty_fiber`), and a
point whose height is not a level is an open-strip point (`exists_strip_rep`). Neither statement
uses finiteness or discreteness of the pieces.

## Fixtures

`TDA.Reeb.RGraphExamples` works with actual realizations and actual slice morphisms:

- two parallel edges over `0 < 1` and a single edge are not isomorphic graph objects;
- exchanging the two parallel edges is an involutive non-identity automorphism of the data and of
  the graph object, and it moves the regular point `(true, 1/2)`;
- with two vertices per level and one edge attached to the vertices `false`, every
  height-preserving self-map fixes the attached bottom vertex, and the realized collapse sends the
  isolated vertex onto it;
- the 0–1–2 path and the 0–1–2–1 cycle over `0 < 1 < 2` are not isomorphic; the cycle has a
  noninjective `left` at gap `0` and is its own Reeb quotient;
- inserting the level `1/2` into a single edge gives a one-point vertex set with bijective
  incoming and outgoing endpoint maps, and the refined graph object is isomorphic to the original;
- refining `0 < 1` to `0 < 1 < 2` adds an empty vertex set at `2` and an empty edge set over
  `(1, 2)`;
- for `n = 0`, finite maps are functions on the single vertex set, so the slice endomorphisms of
  two points at one level are all functions `Bool → Bool`;
- the realization of the empty data is empty, and any graph object with an empty carrier, in
  particular the empty graph over any level list, is initial in `RGraphCat`.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*:

- §2.2, Remark 2.3: the critical set is not uniquely specified, since extra critical points can
  be added by splitting the cylinders. Here this is `refineData` with `refineHomeomorph` and the
  identifications of all vertex sets, edge sets and incidences.
- §2.3, Notation 2.7: an ℝ-graph is specified by finite vertex sets `Vᵢ`, finite edge sets `Eᵢ`
  over `[aᵢ, aᵢ₊₁]` and attaching maps `ℓᵢ : Eᵢ → Vᵢ`, `rᵢ : Eᵢ → Vᵢ₊₁`. These are
  `FiniteReebData` with `left` and `right`. The category **Reeb** consists of the constructible
  ℝ-spaces with 0-dimensional pieces, with the morphisms of ℝ-**Top**. Here it is `RGraphCat`, the
  full subcategory of the real slice on objects isomorphic to realizations of finite data.
- §2.3, Proposition 2.8: for ℝ-graphs with a common critical set, morphisms are precisely
  vertex and edge maps satisfying both consistency conditions. Here this is `homEquiv`, with both
  inverse laws, and `realizationFullyFaithful`. The remark after it that a common critical set is
  no restriction, by taking the union of critical sets, is `exists_common_refinement` and
  `exists_common_presentation`; `homEquivOfIso_independent` states that the resulting finite
  description does not depend on the presentations.
- §2.4, Proposition 2.13: each ℝ-graph is naturally isomorphic to its Reeb graph, because its
  levelsets are finite discrete and the canonical projection is a homeomorphism. Here this is
  `projHomeomorph` and the natural isomorphism `projNatIso` on `RGraphCat`.

Not claimed here: a minimal or canonical critical set; a literal insertion constructor for
refinements; a description of maps between realizations over different level lists without
passing to a common refinement; simple-graph, tree, Hasse-diagram or ordering descriptions of
graph objects; the comparison of graph objects with constructible cosheaves; horizontal edges of
piecewise-linear inputs; the packaging in universes other than `0`.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/html/1501.04147v1).
