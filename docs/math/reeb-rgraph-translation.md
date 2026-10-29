# Vertical translation of finite ℝ-graphs

## Setting

`RGraphCat` is the full subcategory of graph objects of the real slice `Over (TopCat.of ℝ)`: objects
isomorphic to a realization `toOver S D` of finite data `D` at critical values `S` (see
`reeb-rgraph.md`). `overBaseMap A` is the height of a slice object, `cosheafFunctor` sends a graph
object to its path-component cosheaf with underlying precosheaf `intervalComponents (overBaseMap A)`
(see `reeb-rgraph-cosheaf-equivalence.md`), and `geometricInterleavingDistance` equals the
interleaving distance of these precosheaves (see `reeb-geometric-interleaving-equivalence.md`).
For `c : ℝ`, `translate c I = {y | y + c ∈ I}` and `translatePre c F = F ∘ translate c` are the
translations of open intervals and of interval precosheaves (see `reeb-graph-pl.md`).

## Translation functor

`RGraph.translateOver c = Over.map (· + c)` keeps the total space of a slice object and replaces its
height `f` by `f + c`; `overBaseMap_translateOver` holds by `rfl`. `translateOverZeroIso` and
`translateOverCompIso c d` give `translateOver 0 ≅ 𝟭` and
`translateOver c ⋙ translateOver d ≅ translateOver (c + d)` from `Over.mapId`, `Over.mapComp` and
`Over.mapCongr`.

A finite realization stays a finite realization. `CriticalValues.translate S c` has levels
`S.value i + c`, and the change of levels `levelHomeomorph S (S.translate c)` of the same
presentation satisfies `height (S.translate c) ∘ levelMap = height S + c`
(`height_levelMap_translate`). Hence

```lean
toOverTranslateIso S D c : (translateOver c).obj (toOver S D) ≅ toOver (S.translate c) D
```

so `translateOver c` preserves `IsRGraph` (`isRGraph_translateOver`) and restricts to
`translateRGraph c : RGraphCat ⥤ RGraphCat`, with `translateRGraph_comp_ι` by `rfl` and the lifted
isomorphisms `translateRGraphZeroIso` and `translateRGraphCompIso`. The segments transform as
`Seg (S.translate c) e = (· + c) '' Seg S e` (`seg_translate`).

## Distance

The component cosheaf of the translate is the translate of the component cosheaf:

```lean
(cosheafFunctor.obj ((translateRGraph c).obj A)).obj = translatePre c (cosheafFunctor.obj A).obj
```

by `rfl` (`cosheafFunctor_translateRGraph_obj`), since `f x + c ∈ I` and `f x ∈ translate c I` are
the same proposition. For precosheaves into any category, an `ε`-interleaving `(φ, ψ)` of `F` and
`G` gives the `ε`-interleaving `Interleaving.translatePre c` of the translates, with components
`φ_(I - c)` and `ψ_(I - c)` followed by the identification `T_ε (I - c) = (T_ε I) - c`
(`translate_thicken`). Translating back by `-c` shows

```lean
interleavingDistance (translatePre c F) (translatePre c G) = interleavingDistance F G
```

(`interleavingDistance_translatePre`), and therefore `translateRGraph c` is an isometry of the
geometric interleaving distance (`geometricInterleavingDistance_translateRGraph`).

A graph object is within `|c|` of its translate
(`geometricInterleavingDistance_translateRGraph_self_le`). If its total space is nonempty, the
distance is exactly `|c|`:

```lean
geometricInterleavingDistance A ((translateRGraph c).obj A) = ENNReal.ofReal |c|
```

(`geometricInterleavingDistance_translateRGraph_self`), from the exact distance of the interval
components of `f` and `f + c` (`interleavingDistance_intervalComponents_add_const`) with the lower
bound of the height range supplied by `bddBelow_heightRange`. With an empty total space the
distance is `0` (`geometricInterleavingDistance_translateRGraph_self_of_isEmpty`), so the
nonemptiness hypothesis cannot be dropped. With the triangle inequality, translating the second
argument by `c` changes the distance by at most `|c|`
(`geometricInterleavingDistance_translateRGraph_le`,
`geometricInterleavingDistance_le_translateRGraph_add`).

## Reeb quotient and smoothing

A path along which `f + c` is constant is a path along which `f` is constant, so the Reeb relations
of `f` and `f + c` coincide (`reebRel_add_const_iff`) and the identity on representatives is a
homeomorphism of the two Reeb quotients (`ReebQuotient.addConstHomeomorph`). Its height equation
holds on representatives, which gives the natural isomorphism

```lean
quotientTranslateIso c :
    translateOver c ⋙ ReebQuotient.quotientFunctor ℝ ≅ ReebQuotient.quotientFunctor ℝ ⋙ translateOver c
```

The product thickening commutes with translation by the identity of `X × [-ε, ε]`, since
`(f x + c) + t = (f x + t) + c` (`thickeningTranslateIso`). Composing the two on graph objects
gives `geometricSmoothingTranslateIso c ε :
translateRGraph c ⋙ geometricSmoothing ε ≅ geometricSmoothing ε ⋙ translateRGraph c`.

## Fixtures

`TDA.Reeb.RGraphTranslationExamples`: the 0–1–2–1 cycle translated by `c` is the cycle at the levels
`c < 1 + c < 2 + c` and is at distance `|c|` from the cycle; translation of the cycle by `0` is
isomorphic to the cycle, and by `1` then `2` to translation by `3`; the empty graph over `0 < 1` has
an empty translate at distance `0`, which differs from `|1|`.

`TDA.Mapper.GraphPLReebTranslationExamples`: on the single edge with heights `(0, 2)`, the graph-PL
Reeb quotient of `(1, 3)` is the translate by `1` of that of `(0, 2)`, and the exact
self-translation distance gives distance `1`, the value of
`geometricInterleavingDistance_graphPLReebGraph_add_const`; the flat and tilted single edges stay
at distance `1` after translation by `5`. The reversed single edge is at distance `0` from the
tilted one without being a translate of it, so the exact value `|c|` concerns a graph object and its
own translate only.

## Scope

Not claimed: translation of the display locale `𝒟`, or of categorical Mapper reconstructions as
graph objects; scaling on `RGraphCat` or its commutation with the Reeb quotient and geometric
smoothing; nonlinear reparametrizations; translation of a Mapper cover without its height.
Scaling interval precosheaves and nonzero affine changes of graph-PL heights satisfy the distance
homogeneity law in [reeb-graph-pl.md](reeb-graph-pl.md#scaling-heights).

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.1–4.4, is the context: the expansion
`I^ε`, the interleavings and distance of Definitions 4.1 and 4.4, the thickening of Definition 4.22,
the smoothing `U_ε` of Definition 4.30 and the geometric interleavings of Definition 4.36. No
numbered result of the paper states translation equivariance; the translation functor, the
transport of interleavings, the isometry, the exact self-translation distance and the commutation
with the Reeb quotient and with smoothing are library statements.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/html/1501.04147v1).
