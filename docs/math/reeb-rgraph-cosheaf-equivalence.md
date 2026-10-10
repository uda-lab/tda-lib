# Finite ℝ-graphs and constructible cosheaves

## Setting

Levels are `S : CriticalValues n`, a nonempty strictly increasing list `a 0 < ⋯ < a n`, with stars
`J i = (a (i-1), a (i+1))` and gaps `K e = (a e, a (e+1))`, with infinite ends at the extremes (see
`reeb-constructible-cosheaf.md`). Finite data `D : FiniteReebData n` consist of finite vertex sets
`V i`, finite edge sets `E e` and endpoint maps `left e : E e → V e.castSucc` and
`right e : E e → V e.succ`.

Graph objects form `RGraphCat`, the full subcategory of the real slice `Over (TopCat.of ℝ)` on
objects isomorphic to a realization `toOver T D` of finite data over some list `T`. Its morphisms
are all continuous height-preserving maps, and it lives in universe `0` (see `reeb-rgraph.md`).

For `F : OpenInterval ⥤ Type u` constructible at `S`, the extracted data `S.extract F` have
`V i = F (J i)` and `E e = F (K e)`. Their endpoint maps are the covariant maps
`F (K e ≤ J e.castSucc)` and `F (K e ≤ J e.succ)` induced by the interval inclusions. For finite
data `D`, `D.toCosheaf S` is the path-component cosheaf of the realization of `D`, and the labels
`vertexLabel S i : D.V i ≃ C_D (J i)` and `edgeLabel S e : D.E e ≃ C_D (K e)` run from the data to
components (see `reeb-constructible-representation.md`). The levels `S` are explicit in every
extraction, realization and comparison formula.

## Constructible cosheaves

`IsConstructibleCosheaf F` is a `Prop` structure with two fields:

- `IsIntervalCosheaf.{0} F`, the cosheaf condition for covers indexed in universe `0`;
- the existence of `n` and `S : CriticalValues n` with `S.IsConstructibleAt F`.

The witness is a property, not part of the object, and any larger list containing its levels is
also a witness (`IsConstructibleAt.of_refines`). The property is invariant under natural
isomorphism (`IsConstructibleCosheaf.of_iso`, `isClosedUnderIsomorphisms`).
`ConstructibleCosheafCat.{u}` is the full subcategory of `OpenInterval ⥤ Type u` on this property,
so its morphisms are all natural transformations. The value at `⊥` is empty by the cosheaf
condition. The zero cosheaf is an object, constructible at a one-level list.

## The component functor

`intervalComponentsOver : Over (TopCat.of ℝ) ⥤ (OpenInterval ⥤ Type)` is the slice component
functor `ReebQuotient.componentFunctorOver ℝ` of `reeb-quotient-comparison.md`, followed by
precomposition with `toOpensFunctor`. By definition:

```text
intervalComponentsOver.obj A       = intervalComponents (overBaseMap A)
intervalComponentsOver.map f       = componentNatTrans f.left.hom, precomposed with toOpensFunctor
intervalComponentsOver.obj (toOver S D) = D.toCosheaf S
```

(`intervalComponentsOver_obj`, `intervalComponentsOver_map`, `intervalComponentsOver_obj_toOver`).
On a class of a point `x` over `I`, the map gives the class of `f x`
(`intervalComponentsOver_map_app_mk`).

The interval components of a graph object form a constructible cosheaf
(`isConstructibleCosheaf_intervalComponentsOver`): a presentation `A ≅ toOver T D` carries them to
`D.toCosheaf T`, which is an interval cosheaf and constructible at `T`. The lift is

```text
RGraph.cosheafFunctor : RGraphCat ⥤ ConstructibleCosheafCat.{0}
```

with `cosheafFunctor ⋙ ι = IsRGraph.ι ⋙ intervalComponentsOver` (`cosheafFunctor_comp_ι`). Its
object and morphism formulas `cosheafFunctor_obj_obj` and `cosheafFunctor_map_hom` hold by `rfl`:
the functor is the actual path-component functor on underlying spaces, not a combinatorial model.

## Finite level

For finite data `D`, `D'` over a common `S` and `φ : D.Hom D'`, `realizeNatTrans S φ` is
`componentNatTrans` of the realized map `realizeHom S φ`, precomposed with `toOpensFunctor`. On
labels it acts by `φ`:

```text
realizeNatTrans S φ (J i) (vertexLabel S i v) = vertexLabel S i (φ.v i v)
realizeNatTrans S φ (K e) (edgeLabel S e y)   = edgeLabel S e (φ.e e y)
```

(`realizeNatTrans_vertexLabel`, by `rfl`; `realizeNatTrans_edgeLabel`, through the evaluation of
the edge label at the gap midpoint). Hence the classification `natTransEquivDiagramHom` of maps
between constructible cosheaves sends it to `fromExtractHom.comp (φ.comp toExtractHom)`
(`natTransEquivDiagramHom_realizeNatTrans`). With the round trip `extract_toCosheaf_iso`, this
gives the bijection

```text
realizeNatTransEquiv S D D' : D.Hom D' ≃ (D.toCosheaf S ⟶ D'.toCosheaf S)
```

whose forward map is `realizeNatTrans S` (`realizeNatTransEquiv_apply`), for data in any universe.
Realization followed by interval components acts by `realizeNatTrans`
(`realizationFunctor_comp_intervalComponentsOver_map`) and is fully faithful over a common `S`
(`realizationCosheafFullyFaithful`).

## Full faithfulness

Graph objects `A` and `B` have presentations `iA : A ≅ toOver T DA` and `iB : B ≅ toOver T DB` over
one common list `T` (`exists_common_presentation`). For every slice morphism `g`, the actual
component map is the realized transformation of the classified finite map, conjugated by the images
of the presentations (`intervalComponentsOver_map_eq`). For a morphism `f : A ⟶ B` of graph
objects:

```text
intervalComponentsOver.map iA.inv ≫ (cosheafFunctor.map f).hom ≫ intervalComponentsOver.map iB.hom
  = realizeNatTrans T (homEquivOfIso iA iB f.hom)
```

(`cosheafFunctor_map_conj`). Through the classification of maps between constructible cosheaves,
the conjugated map is the classified finite map conjugated by the labels,
`fromExtractHom.comp ((homEquivOfIso iA iB f.hom).comp toExtractHom)`
(`natTransEquivDiagramHom_cosheafFunctor_map`). Pointwise, the conjugated map sends the vertex
label of `v` to the vertex label of the image of `v`, and likewise for edges
(`cosheafFunctor_map_conj_vertexLabel`, `cosheafFunctor_map_conj_edgeLabel`).

`cosheafHomEquiv iA iB` is the composite of five bijections: the morphisms of `RGraphCat` as slice
morphisms, the classification `homEquivOfIso iA iB` of `reeb-rgraph.md`, `realizeNatTransEquiv T`,
conjugation by the images of the presentations, and the morphisms of `ConstructibleCosheafCat` as
natural transformations. It equals the functor's map (`cosheafHomEquiv_apply`). Hence
`cosheafFunctor.map` is bijective on every Hom set (`cosheafFunctor_map_bijective`), which gives
the `Full` and `Faithful` instances and `cosheafFullyFaithful`. The statement concerns the actual
map of the functor on all continuous height-preserving maps between graph objects; no objectwise
bijection of Hom sets replaces it.

## Essential surjectivity

For `F` constructible at `S`, `ofCosheaf S hF = (toRGraph S).obj (S.extract F _)` is the graph
object of the extracted data. The functor sends it to `(S.extract F _).toCosheaf S` by definition,
and the reconstruction `realizeExtractIso` of `reeb-constructible-representation.md` identifies
that cosheaf with `F`:

```text
cosheafFunctorObjIso hF hFc hP : cosheafFunctor.obj (ofCosheaf S hF) ≅ ⟨F, hP⟩
```

with hom the reconstruction (`cosheafFunctorObjIso_hom`). Every object is reached through its own
witness (`cosheafFunctor_essSurj`), so `cosheafFunctor` is an equivalence
(`cosheafFunctor_isEquivalence`).

## Witnesses, the inverse functor and the equivalence

- **Two witnesses.** For witnesses `S` and `S'` of the same `F`, possibly of different lengths,
  `ofCosheafIso hS hS' hFc : ofCosheaf S hS ≅ ofCosheaf S' hS'` is the preimage under full
  faithfulness of the composite of the two reconstructions. Its image is
  `(realizeExtractIso hS hFc).hom ≫ (realizeExtractIso hS' hFc).inv`
  (`cosheafFunctor_map_ofCosheafIso`).
- **Chosen witness.** `witnessLength G`, `witness G` and `isConstructibleAt_witness G` choose a
  witness of an object `G` with `Classical.choose`, and `ofCosheafObjIso G` is the reconstruction
  at it. Only the isomorphism class of the result matters.
- **Inverse functor.** `ofCosheafFunctor : ConstructibleCosheafCat.{0} ⥤ RGraphCat` sends `G` to
  `ofCosheaf (witness G) _` (`ofCosheafFunctor_obj`). It sends `α : G ⟶ G'` to the unique graph
  map whose image is `ε_G.hom ≫ α ≫ ε_G'.inv`, where `ε` is `ofCosheafObjIso`
  (`cosheafFunctor_map_ofCosheafFunctor_map`). It is `@[reducible]`, so that
  `ofCosheafFunctor.obj G` and `ofCosheaf (witness G) _` unify in the unit and counit.
- **Counit and unit.** `ofCosheafCounitIso : ofCosheafFunctor ⋙ cosheafFunctor ≅ 𝟭` has the
  components `ofCosheafObjIso`. `ofCosheafUnitIso : 𝟭 ≅ cosheafFunctor ⋙ ofCosheafFunctor` has as
  component at `A` the preimage of the inverse reconstruction at `cosheafFunctor.obj A`.
- **Equivalence.**

  ```text
  RGraph.cosheafEquivalence : RGraphCat ≌ ConstructibleCosheafCat.{0}
    := Equivalence.mk cosheafFunctor ofCosheafFunctor ofCosheafUnitIso ofCosheafCounitIso
  ```

  Its functor is `cosheafFunctor`, its inverse is `ofCosheafFunctor` and its counit is
  `ofCosheafCounitIso`, all by `rfl` (`cosheafEquivalence_functor`, `cosheafEquivalence_inverse`,
  `cosheafEquivalence_counitIso`). `Equivalence.mk` keeps both functors and the counit and replaces
  the given unit by its adjointification, so the unit of `cosheafEquivalence` is the adjointified
  unit, not `ofCosheafUnitIso`.
- **Independence of choices.** At any witness `S` of `G`, `ofCosheafFunctorObjIso G hS` identifies
  `ofCosheafFunctor.obj G` with `ofCosheaf S hS` through `ofCosheafIso`. Any equivalence whose
  functor is isomorphic to `cosheafFunctor` has an inverse naturally isomorphic to
  `ofCosheafFunctor` (`inverseIsoOfFunctorIso`). Presentations, witnesses and inverse choices are
  related by these isomorphisms; no definitional equality among them is claimed.

## Universes and hypotheses

`IsConstructibleCosheaf.{u}` and `ConstructibleCosheafCat.{u}` are defined at every value universe
`u`, and the finite-level results hold for data in every universe. The functor, its inverse and the
equivalence are at value universe `0`, matching `RGraphCat`; the equivalence is not stated at other
value universes. Covers are indexed in universe `0`, as the classification
`natTransEquivDiagramHom` requires. No compactness, Hausdorff or local path-connectedness
hypothesis appears, since graph realizations have discrete pieces.

## Fixtures

`TDA.Reeb.RGraphCosheafEquivalenceExamples` works with actual graph objects and actual component
transformations:

- **Automorphism.** The swap of two parallel edges over `0 < 1` is a non-identity involutive graph
  automorphism. Its image is the identity on both stars and exchanges the two edge labels on the
  gap, so it is a non-identity involutive automorphism of the cosheaf (`swap_cosheaf_ne_id`,
  `swap_cosheaf_comp_self`).
- **Collapse.** The graph map collapsing two parallel edges onto one edge sends both edge labels to
  the single edge label. Its gap component is not injective, so its image is not an isomorphism
  (`collapse_cosheaf_not_isIso`).
- **Two subdivisions.** The single edge over `0 < 1` and over `0 < 1/2 < 1` are isomorphic graph
  objects through `refineIso`, and so are their cosheaves. The cosheaf is constructible at both
  lists, and the graph objects extracted at the two witnesses are isomorphic by a map whose image
  is the composite of the two reconstructions (`single_ofCosheafIso_image`).
- **Disconnected object.** Two points at one level have two components over `ℝ`, and their cosheaf
  has exactly four endomorphisms, the functions `Fin 2 → Fin 2` (`twoPoint_end_card`).
- **Empty object.** The empty graph goes to the zero cosheaf `Examples.Constructible.zeroCosheaf`
  of the constructible-cosheaf fixtures. That cosheaf is an object through its cosheaf condition
  and its constructibility at one level, and every precosheaf with empty values is isomorphic to
  it (`isoZeroOfIsEmpty`, `emptyGraph_cosheafIso`). It is initial (`zeroObj_isInitial`). The
  inverse functor sends it to a graph object with empty carrier, which is initial
  (`ofCosheafFunctor_zeroObj_isEmpty`, `ofCosheafFunctor_zeroObj_isInitial`).
- **Negative boundary.** `[0, 1]` at constant height `0` is the realization of a one-piece
  presentation. Its collapse onto the point is bijective on every interval, so the two component
  cosheaves are isomorphic and constructible. The two objects are not isomorphic over `ℝ`, and
  `[0, 1]` is not a graph object, because its fiber over `0` is connected while every fiber of a
  graph object is discrete (`negative_boundary`). The source category of the equivalence is
  therefore restricted to graph objects. The pinned mathlib has no `PathConnectedSpace` instance
  for `unitInterval`; the fixture module proves it from convexity as a private local instance.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*:

- §2.3: **Reeb** is the full subcategory of ℝ-**Top** on ℝ-graphs, with all morphisms of
  ℝ-**Top**. Here it is `RGraphCat` (see `reeb-rgraph.md`).
- §3.3, Definition 3.9: **Csh**ᶜ is the full subcategory of cosheaves that are constructible:
  finite values and a finite critical set `S` such that inclusions with the same intersection
  with `S` induce bijections and values outside `[min S, max S]` are empty. Here it is
  `ConstructibleCosheafCat` with `IsConstructibleCosheaf`, with the bijection condition for
  nonempty intervals only, a nonempty list of levels and covers indexed in universe `0` (see
  `reeb-constructible-cosheaf.md`).
- §3.4: `𝒞(f)(I) = π₀ f⁻¹(I)` with `𝒞[α]_I = π₀[f⁻¹(I) → g⁻¹(I)]`, where `π₀` is path
  components. Here it is `intervalComponentsOver`, and `cosheafFunctor` is the restriction `𝒞''`
  of `𝒞` to **Reeb**.
- §3.5, Theorem 3.22: `𝒞'' : Reeb → Cshᶜ` is an equivalence of categories. Here it is
  `cosheafEquivalence` together with the instance `cosheafFunctor.IsEquivalence`.
  - Proof part (i): over a common critical set, the source identifies the vertex and edge data of
    `f` and of `𝒞(f)` compatibly with `ℓ` and `r`, obtains a bijection of Hom sets from
    Propositions 2.8 and 3.12, and shows by the cylinder diagrams that it is given by `𝒞[−]`.
    Here the common list is `exists_common_presentation`. The bijection `cosheafHomEquiv`
    composes `homEquivOfIso` (Proposition 2.8) with `realizeNatTransEquiv`, built from
    `natTransEquivDiagramHom` (Proposition 3.12) and the labels. `cosheafHomEquiv_apply` and the
    label equations `realizeNatTrans_vertexLabel`, `realizeNatTrans_edgeLabel` are the statement
    that it is given by the functor.
  - Proof part (ii): the source takes `Vᵢ = 𝖥((aᵢ₋₁, aᵢ₊₁))`, `Eᵢ = 𝖥((aᵢ, aᵢ₊₁))` and the maps
    induced by the inclusions, and concludes by Corollary 3.14. Here these data are `S.extract F`,
    and `cosheafFunctorObjIso` is the reconstruction `realizeExtractIso`: Proposition 3.18 applied
    to the extracted data with the identity as compatible map, whose isomorphism conclusion is
    Corollary 3.14 (see `reeb-constructible-representation.md`).
  - The source cites Mac Lane, §IV.4, for the passage from full faithfulness and essential
    surjectivity to an equivalence. Here the instances give `Functor.IsEquivalence`, and
    `cosheafEquivalence` is built explicitly.
- §3.5, after the proof of Theorem 3.22: the display locale functor `𝒟 : Cshᶜ → Reeb` is defined
  by the same data at a critical set; the identifications give a natural isomorphism `𝒞𝒟 ⇒ 1`
  and determine `𝒟[α]`, and the result is unique up to canonical natural isomorphism. Here `𝒟`
  is `ofCosheafFunctor` at a chosen witness, with counit `ofCosheafCounitIso` and the morphism
  formula `cosheafFunctor_map_ofCosheafFunctor_map`. Uniqueness is `ofCosheafIso` across
  witnesses and `inverseIsoOfFunctorIso` across inverse functors.

Not claimed here: an equivalence on all ℝ-spaces, on all constructible ℝ-spaces or on
Reeb-ordering objects; the equivalence at value universes other than `0`; a minimal or canonical
critical witness; definitional equality of presentations, witnesses or inverse functors; the
corollary after Theorem 3.22 comparing the Reeb graph of a constructible ℝ-space with the display
locale of its cosheaf.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/html/1501.04147v1).
