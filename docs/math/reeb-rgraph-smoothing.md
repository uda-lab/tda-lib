# Geometric smoothing of finite ℝ-graphs

## Setting

`RGraphCat` is the full subcategory of graph objects of the real slice `Over (TopCat.of ℝ)` (see
`reeb-rgraph.md`). `RGraph.cosheafFunctor : RGraphCat ⥤ ConstructibleCosheafCat.{0}` is the
path-component cosheaf `C''` of a graph object, with underlying precosheaf
`intervalComponents (overBaseMap A.obj)` (see `reeb-rgraph-cosheaf-equivalence.md`), and
`constructibleCosheafFunctor` is the cosheaf `C'` of a constructible ℝ-space. For `ε : ℝ≥0`,
`GeometricThickening.functor ε` is the product thickening `T_ε`, with `X × Band ε`,
`Band ε = [-ε, ε]` and height `f x + t` (see `reeb-geometric-thickening.md`). On graph input it
lands in constructible ℝ-spaces: `RGraph.thickeningToConstructible ε : RGraphCat ⥤
ConstructibleSpaceCat` (see `reeb-rgraph-thickening.md`). `quotientRGraphFunctor :
ConstructibleSpaceCat ⥤ RGraphCat` is the Reeb functor `ℛ` on constructible ℝ-spaces (see
`reeb-constructible-quotient.md`). `smoothing ε` is the smoothing `S_ε` of interval precosheaves,
`F ↦ F ∘ (·)^ε`, with unit `σ = smoothingUnit ε` (see `reeb-smoothing.md`), and
`constructibleSmoothing ε` is its lift to constructible cosheaves (see
`reeb-constructible-smoothing.md`).

The construction uses these merged library declarations:

- `TDA.Reeb.RGraphThickening`: `RGraph.thickeningToConstructible`;
  `TDA.Reeb.ConstructibleQuotient`: `IsConstructibleSpace`, `ConstructibleSpaceCat` and
  `quotientRGraphFunctor`;
- `TDA.Reeb.GeometricThickening`: `Band`, `height`, `functor`, `zeroSection`,
  `zeroSectionNatTrans`, `zeroIso`, `zeroIso_inv`, `componentComparison`,
  `componentComparisonNatIso`, `fst_mem_thicken`,
  `map_zeroSectionNatTrans_comp_componentComparisonNatIso` and `map_zeroIso_hom_app`;
- `TDA.Reeb.ConstructibleComparison`: `constructibleCosheafComparisonIso`,
  `constructibleComponentComparisonIso`, `constructibleCosheafFunctor` and
  `ReebQuotient.intervalComponentComparison`;
- `TDA.Reeb.ConstructibleSmoothing`: `constructibleSmoothing`, `constructibleSmoothingUnit` and
  `constructibleSmoothingZeroIso`; `TDA.Reeb.Smoothing`: `smoothing`, `smoothingUnit` and
  `smoothingZeroIso`; `TDA.Reeb.InterleavingDistance`: `interleavingDistance`,
  `interleavingDistance_congr` and `interleavingDistance_smoothing_le`;
- `TDA.Reeb.RGraphCosheafEquivalence`: `IsConstructibleCosheaf`, `ConstructibleCosheafCat`,
  `RGraph.cosheafFunctor` and `intervalComponentsOver`; `TDA.Reeb.RGraph`: `IsRGraph`,
  `RGraphCat` and `projNatIso`;
- `TDA.Reeb.QuotientComparison`: `overBaseMap`, `ReebQuotient.quotientFunctor` and
  `ReebQuotient.projNatTrans`; `TDA.Reeb.Quotient`: `ReebQuotient`, `ReebQuotient.mk`,
  `ReebQuotient.height` and the topology `instTopologicalSpaceReebQuotient`;
- `TDA.Reeb.IntervalComponents`: `intervalComponents`; `TDA.Reeb.Interval`: `OpenInterval` with
  the instances `instSetLikeReal` and `instPartialOrder`, `toOpensFunctor`, `thicken`,
  `le_thicken` and `le_iff_subset`.

From the pinned mathlib it relies on `NatIso.ofComponents`, `ObjectProperty.isoMk`,
`ObjectProperty.homMk`, `ObjectProperty.hom_ext`, `Functor.isoWhiskerLeft`,
`Functor.isoWhiskerRight`, `Iso.hom_inv_id_app_assoc`, `cancel_epi`, `NatTrans.congr_app` and
`ConcreteCategory.congr_hom`.

The fixtures additionally use, from the library, `ReebQuotient.mk_surjective`, `overBaseMap_comm`,
`intervalComponents_obj_bot_isEmpty`, `joined_eq_of_discrete`, `mem_thicken`, `thicken_zero`,
`iio`, `ioi`, `ioo`, `mem_ioo`, `ordConnected` and the `⊥`, `⊤` and meet instances of
`OpenInterval`; `GeometricThickening.zero_mem_band` and `GeometricThickening.neg_le_band`;
`CriticalValues` with `value`, `strictMono`, `J`, `K`, `lowerTail`, `upperTail`, `mem_J_iff`,
`mem_K`, `mem_lowerTail`, `mem_upperTail`, `value_mem_J_iff`, `value_notMem_K`, `K_le_J_castSucc`,
`K_le_J_succ` and `eq_of_K_inf_K_nonempty`; `CriticalValues.IsConstructibleAt` with `bijective`,
`isEmpty_of_le_lowerTail` and `isEmpty_of_le_upperTail`; `FiniteReebData` with `V`, `E`, `left`,
`right`, the category instance, `toCosheaf`, `toCosheaf_isConstructibleAt`, `vertexLabel`,
`edgeLabel`, `edgeLabel_apply`, `map_K_le_J_castSucc_edgeLabel` and `map_K_le_J_succ_edgeLabel`;
`CylinderPresentation` with `V`, `E`, `Realization` and its topology, `topV`, `ofFiniteData`,
`ofVertex`, `ofStrip`, `height`, `height_mem_Icc` and `exists_rep`; `RGraph.toOver`,
`RGraph.toRGraph` and `RGraph.exists_strip_rep`. The fixture data are `S01`, `S01_value_zero`,
`S01_value_one`, `half`, `parallelData`, `twoSegData`, `twoSegLabel`, `emptyData`,
`emptyData_isEmpty`, `height_zero` and `homeomorphZero` (`ConstructibleSpaceExamples`); `S0` and
`pinch_J0_mem_iff` (`ConstructibleCylinderExamples`); `singleEdge` (`RGraphExamples`); `pt0`
(`ConstructibleRepresentationExamples`); `parallelGraph`, `swapGraph`, `singleGraph`,
`singleHalfGraph`, `subdivisionIso` and `emptyGraph` (`RGraphCosheafEquivalenceExamples`);
`quarter`, `coe_quarter`, `quarter_thicken` and `smoothedSwap_quarter_ne_id`
(`ConstructibleSmoothingExamples`); and `halfNN`, `coe_halfNN` and `single`
(`RGraphThickeningExamples`).

## The functor

```lean
geometricSmoothing ε : RGraphCat ⥤ RGraphCat :=
  thickeningToConstructible ε ⋙ quotientRGraphFunctor
```

is `U_ε = ℛ T_ε`: the actual product thickening, constructible on graph input, followed by the
Reeb functor. Under the graph inclusion it is literally
`IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ`, on objects and on
all maps (`geometricSmoothing_comp_ι`, `geometricSmoothing_obj_obj`, `geometricSmoothing_map_hom`,
all by `rfl`). The underlying precosheaf of `C'' U_ε A` is the interval-component precosheaf of the
Reeb quotient of `T_ε A` (`geometricSmoothing_comp_cosheafFunctor_comp_ι`, by `rfl`).

## The comparison

Write `η = constructibleCosheafComparisonIso : C' ≅ C'' ℛ` on constructible ℝ-spaces, whose
component at a space is `C'` of its Reeb projection, and
`ρ = GeometricThickening.componentComparisonNatIso ε : C T_ε ≅ S_ε C` on the real slice, whose
component on an interval `I` sends the class of `(x, t)` in `f_ε⁻¹(I)` to the class of `x` in
`f⁻¹(I^ε)`. On graph objects `ρ` lifts componentwise to

```lean
thickeningCosheafComparisonIso ε :
    thickeningToConstructible ε ⋙ constructibleCosheafFunctor ≅
      cosheafFunctor ⋙ constructibleSmoothing ε
```

(`thickeningCosheafComparisonIso_hom_app_hom`). The principal isomorphism is

```lean
geometricSmoothingComparisonIso ε :
    geometricSmoothing ε ⋙ cosheafFunctor ≅ cosheafFunctor ⋙ constructibleSmoothing ε
```

with component `β_A = η_(T_ε A).inv ≫ ρ_A.hom` at a graph object `A`, in the full subcategory and on
the underlying precosheaves (`geometricSmoothingComparisonIso_hom_app`,
`geometricSmoothingComparisonIso_hom_app_hom`, both by `rfl`). Its naturality square is that of
`isoWhiskerLeft (thickeningToConstructible ε) η.symm ≪≫ thickeningCosheafComparisonIso ε`, so it
holds for every graph map, whatever critical lists present its source and target.

The canonical hom-component equation `η_(T_ε A).hom ≫ β_A = ρ_A.hom` holds in three forms:

- in the full subcategory,
  `constructibleCosheafComparisonIso_hom_app_comp_geometricSmoothingComparisonIso_hom_app`;
- for the functor-level comparison `constructibleComponentComparisonIso` and
  `componentComparisonNatIso`,
  `constructibleComponentComparisonIso_hom_app_comp_geometricSmoothingComparisonIso_hom_app`;
- for the unbundled `ReebQuotient.intervalComponentComparison` of the thickened height and
  `GeometricThickening.componentComparison`,
  `intervalComponentComparison_comp_geometricSmoothingComparisonIso_hom_app_hom`.

On representatives (`geometricSmoothingComparisonIso_hom_app_hom_app_mk`), for every open interval
`I` and every `z = (x, t)` of `X × Band ε` with `f x + t ∈ I`,

```text
β_A(I) [q (x, t)] = [x],
```

where `q` is the Reeb projection, the left class lies in the components of
`{q | q̄ q ∈ I}` of the Reeb quotient and the right class in the components of
`{x | f x ∈ I^ε}`. This identifies components; no map from points of the Reeb quotient to `X` is
asserted, and none is well defined in general.

## The unit

`geometricSmoothingUnit ε : 𝟭 RGraphCat ⟶ geometricSmoothing ε` has component the actual zero
section `x ↦ (x, 0)` followed by the actual Reeb projection of `T_ε A`
(`geometricSmoothingUnit_app_hom`); on points `ζ x = q (x, 0)`
(`geometricSmoothingUnit_app_hom_left_apply`). The comparison sends `C''(ζ)` to the lifted
smoothing unit:

```lean
cosheafFunctor.map ((geometricSmoothingUnit ε).app A) ≫
    (geometricSmoothingComparisonIso ε).hom.app A =
  (constructibleSmoothingUnit ε).app (cosheafFunctor.obj A)
```

(`cosheafFunctor_map_geometricSmoothingUnit_comp_geometricSmoothingComparisonIso`). `C''` of the
Reeb projection of `T_ε A` is `η_(T_ε A).hom`, so `C''(ζ) = C(τ) ≫ η.hom`; `η` cancels against
`η.inv` in `β`, and the unit equation `C(τ) ≫ ρ = σ` of the first-projection comparison
(`map_zeroSectionNatTrans_comp_componentComparisonNatIso`) remains. The same equation holds on the
underlying precosheaves with `smoothingUnit`
(`intervalComponentsOver_map_geometricSmoothingUnit_comp`) and on representatives,
`[x] ↦ [q (x, 0)] ↦ [x]`
(`geometricSmoothingComparisonIso_hom_app_hom_app_unit_mk`).

## `ε = 0`

`T_0` is isomorphic to the identity of the real slice by `GeometricThickening.zeroIso`, and on graph
objects the Reeb projection is the natural isomorphism `projNatIso`. The zero isomorphism

```lean
geometricSmoothingZeroIso : geometricSmoothing 0 ≅ 𝟭 RGraphCat
```

has component `ℛ(zeroIso) ≫ projNatIso⁻¹`, composed in the slice and lifted to graph objects
(`geometricSmoothingZeroIso_hom_app_hom`). On an arbitrary space the Reeb quotient at `ε = 0` is
the Reeb quotient of the space, not the space. Naturality of the projection and
`projNatIso ≫ projNatIso⁻¹ = 𝟙` give `proj_(T_0 A) ≫ U_0(A) = zeroIso`
(`projNatTrans_app_comp_geometricSmoothingZeroIso_hom_app_hom`). The zero comparison

```lean
cosheafFunctor.map (geometricSmoothingZeroIso.hom.app A) =
  (geometricSmoothingComparisonIso 0).hom.app A ≫
    constructibleSmoothingZeroIso.hom.app (cosheafFunctor.obj A)
```

(`cosheafFunctor_map_geometricSmoothingZeroIso_hom_app`) follows by cancelling the epimorphism
`η_(T_0 A).hom`, after which it is `C(zeroIso.hom) = ρ⁰ ≫ smoothingZeroIso.hom`
(`GeometricThickening.map_zeroIso_hom_app`). With `zeroIso_inv`, the geometric unit at `ε = 0` is
the inverse of the zero isomorphism (`geometricSmoothingUnit_zero`).

## Underlying precosheaves, values and distance

`geometricSmoothingPrecosheafIso ε` is the comparison on the underlying interval precosheaves,

```lean
IsRGraph.ι ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ ⋙
    intervalComponentsOver ≅
  IsRGraph.ι ⋙ intervalComponentsOver ⋙ smoothing ε
```

with components `β_A` (`geometricSmoothingPrecosheafIso_hom_app`), and
`geometricSmoothingValueEquiv ε A I : C(U_ε A)(I) ≃ C(A)(I^ε)` is its value at one interval
(`geometricSmoothingValueEquiv_apply`). For the interleaving distance of the underlying
precosheaves,

```lean
interleavingDistance_geometricSmoothing_le (ε : ℝ≥0) (A B : RGraphCat) :
    interleavingDistance (cosheafFunctor.obj ((geometricSmoothing ε).obj A)).obj
        (cosheafFunctor.obj ((geometricSmoothing ε).obj B)).obj ≤
      interleavingDistance (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj
```

follows from the comparison at `A` and `B` (`interleavingDistance_congr`) and the contraction
property of smoothing (`interleavingDistance_smoothing_le`). No new distance is defined.

## Names and universes

The declarations live in namespace `TDA.Reeb.RGraph`. The packaging is in universe `0`, as
`RGraphCat`, the real slice and `ConstructibleCosheafCat.{0}` are.

## Fixtures

`TDA.Reeb.RGraphSmoothingExamples` works with actual graph objects. The levels `S01` are `0 < 1`;
the parallel-edge loop, the single edge and two disjoint segments over `0 < 1` are the merged
fixtures of `reeb-constructible-space.md`, `reeb-rgraph.md` and
`reeb-rgraph-cosheaf-equivalence.md`. A value `C(U_ε A)(I)` is transported to `C(A)(I^ε)` by
`geometricSmoothingValueEquiv`.

- **Every kind of open interval.** For an arbitrary graph object, the representative comparison
  and unit formulas hold on `ioo a b`, `iio b`, `ioi a` and `⊤` (`rep_unit_ioo`, `rep_unit_iio`,
  `rep_unit_ioi`, `rep_unit_top`), and the value at `⊥` is empty (`smoothed_bot_isEmpty`).
- **`ε = 0`.** `parallelZeroIso` and `parallel_zero_comparison` are the zero isomorphism and the
  zero comparison on the loop. `U_0` keeps the loop: on `(1/4, 3/4)` its value has two distinct
  elements (`parallel_zero_not_subsingleton`).
- **The empty graph.** Every smoothed value is empty, for every `ε` (`smoothedEmpty_isEmpty`).
- **A singleton at height `a`.** The one-vertex graph object `singletonGraph a` has at most one
  point (`singleton_subsingleton`). For every `ε` every value has at most one element
  (`singleton_smoothed_subsingleton`), the values on the rays below `a - ε` and above `a + ε` are
  empty (`singleton_smoothed_isEmpty_iio`, `singleton_smoothed_isEmpty_ioi`), and the support is
  sharp at both ends: for every `δ > 0` the values on `iio (a - ε + δ)` and `ioi (a + ε - δ)` are
  nonempty (`singleton_smoothed_nonempty_iio`, `singleton_smoothed_nonempty_ioi`).
- **Two levels.** For finite data over `0 < 1` with one vertex per level and an edge, the star
  `J 1` is `(0, ∞)` (`S01_J1_mem_iff`), and the two stars glue on `ℝ` along the edge (`top_glue`).
  So a value on an interval meeting a level has at most one element (`subsingleton_top`,
  `subsingleton_of_mem`, through the constructibility bijections); values below `0` or above `1`
  are empty (`isEmpty_of_lt`, `isEmpty_of_gt`); an interval containing `[c - 1/2, c + 1/2]` has at
  most one component (`subsingleton_of_long`), hence so does every thickened interval for
  `ε ≥ 1/2` (`thicken_subsingleton_of_half_le`). With one edge as well, every value has at most one
  element, a nonempty interval inside the gap `(0, 1)` being labelled by the edge
  (`subsingleton_of_one_edge`). On `(1/4, 3/4)` the loop has two distinct components
  (`parallel_mid_not_subsingleton`).
- **Height fibers of graph objects.** In a finite realization, the fiber over a level `a i`
  consists of the vertex points of level `i`, and every point at any other height is a strip point
  of the one gap containing that height. Through the vertex and edge labels, if every value of the
  component cosheaf has at most one element then every height fiber has at most one point
  (`realization_fiber_subsingleton`), and the same holds for every graph object, through an
  isomorphism with a finite realization (`fiber_subsingleton_of_cosheaf`). For a graph object over
  `0 < 1` with an edge and every `ε`, the fiber of `U_ε` over `t` is nonempty exactly when
  `t ∈ [-ε, 1 + ε]` (`smoothed_fiber_nonempty_iff`): a point `q (x, s)` has height `f x + s` with
  `f x ∈ [0, 1]` and `|s| ≤ ε`, and conversely `q (v₀, t)`, `q (v₁, t - 1)` or, for `ε < t < 1 - ε`,
  the class of the edge point at height `t` lies over `t`. Hence every value on an interval meeting
  `[-ε, 1 + ε]` is nonempty (`smoothed_nonempty_of_edge`), and for `ε ≥ 1/2` the vertices alone
  suffice (`smoothed_nonempty`). The values on the rays below `-ε` and above `1 + ε` are empty for
  every `ε` (`smoothed_isEmpty_rays`).
- **The parallel-edge loop, height span `1 ≤ 2ε`.** For every `ε ≥ 1/2` every smoothed value has at
  most one element (`parallel_smoothed_subsingleton`; the equality case `ε = 1/2` is
  `parallel_half_subsingleton`), values are nonempty on every interval meeting `[-ε, 1 + ε]`
  (`parallel_smoothed_nonempty`) and empty on both outer rays (`parallel_smoothed_isEmpty_rays`).
  For the actual height fibers of `U_ε`: for `ε ≥ 1/2` every fiber has at most one point
  (`parallel_smoothed_fiber_subsingleton`, with `parallel_half_fiber_subsingleton` at `ε = 1/2`);
  for every `ε` the fiber over `t` is nonempty exactly when `t ∈ [-ε, 1 + ε]`
  (`parallel_smoothed_fiber_nonempty_iff`) and empty outside (`parallel_smoothed_fiber_isEmpty`).
  So for `ε ≥ 1/2` every nonempty fiber is a single point
  (`parallel_smoothed_fiber_existsUnique`). At `ε = 1/2` the fibers at both ends `-1/2` and `3/2`
  are single points and the fibers just outside are empty (`parallel_half_fiber_ends`). At
  `ε = 1/4` the loop survives: the value on `(1/4, 3/4)`, whose thickening is the gap `(0, 1)`, has
  the two edges as distinct elements (`parallel_quarter_not_subsingleton`), and the fiber over `1/2`
  has two distinct points, the classes of the two edge points, which the comparison sends to the two
  edge labels (`parallel_quarter_fiber_not_subsingleton`).
- **The single edge, every `ε`.** The line is stretched to `[-ε, 1 + ε]`. Every smoothed value has
  at most one element (`single_stretched_subsingleton`); for `ε < 1/2` this includes the intervals
  whose thickening lies in the gap `(0, 1)`. Values are nonempty on every interval meeting
  `[-ε, 1 + ε]` (`single_stretched_nonempty`); for `ε < 1/2` an interior height is reached by an
  edge point. On `(1/4, 3/4)` at `ε = 1/4`, where the loop has two distinct elements, the single
  edge has exactly one (`single_quarter_gap`). Values on both outer rays are empty
  (`single_smoothed_isEmpty_rays`). The actual fibers have at most one point
  (`single_smoothed_fiber_subsingleton`) and are nonempty exactly over `[-ε, 1 + ε]`
  (`single_smoothed_fiber_nonempty_iff`). For `ε ≥ 1/2`, `single_smoothed_subsingleton` and
  `single_smoothed_nonempty` are the long-interval forms.
- **Disjoint segments stay distinct.** For the two disjoint segments `twoSegGraph` and every `ε`,
  the classes on `ℝ` of `q (v_b, 0)` for the lower vertices of the two segments are distinct
  (`twoSegClass`, `twoSeg_smoothed_distinct`): the comparison sends them to the classes of the two
  lower vertices, which the continuous segment label separates. This is the disjoint-edge
  counterfixture; the merging fixture is the loop with common endpoints.
- **Graph maps.** Naturality at the edge swap of the loop (`swap_naturality`); at `ε = 1/4` the
  smoothed swap is not the identity (`swap_smoothed_quarter_ne_id`,
  `swap_geometric_quarter_ne_id`). Naturality across the critical lists `0 < 1/2 < 1` and `0 < 1`
  along the subdivision isomorphism of the single edge (`subdivision_naturality`,
  `subdivisionSmoothedIso`).
- **Contraction.** `parallel_single_contraction` is the contraction corollary for the loop and the
  single edge.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3–4.4:

- **Definition 4.30** defines `U_ε = ℛT_ε : Reeb → Reeb` for `ε ≥ 0`; this is `geometricSmoothing`,
  with `ε : ℝ≥0`. That `T_ε` carries ℝ-graphs to constructible ℝ-spaces, so that `ℛT_ε` lands in
  **Reeb**, is **Proposition 4.26**, formalized as `isConstructibleSpace_thickening` behind
  `thickeningToConstructible` (see `reeb-rgraph-thickening.md`).
- The paragraph after Definition 4.30 identifies the fiber of `U_ε f` over `t` with the set of
  components of `f⁻¹[t - ε, t + ε]` and places the vertices of `U_ε f` over `(S + ε) ∪ (S - ε)`,
  citing Theorem 4.27 and Corollary 4.28. Neither statement is formalized in general here; the
  fixtures prove the fiber statements of the loop and the single edge directly.
- **Example 4.31**, items (1), the line stretched by `ε` in both directions, and (3), the loop with
  height `b - a ≤ 2ε` whose thickening has one component in every levelset, are the single-edge and
  loop fixtures over `[a, b] = [0, 1]`, both for values on intervals and for the actual fibers.
- **Proposition 4.32** states `C''U_ε ≅ S_εC'' : Reeb → Cshᶜ`, proved by
  `C''ℛT_ε ≃ C'T_ε ≃ S_εC''` with Theorems 3.17 and 4.24. `geometricSmoothingComparisonIso` is that
  composite: the inverse of `η` (Theorem 3.17, see `reeb-constructible-comparison.md`) whiskered by
  the thickening, followed by `ρ` (Theorem 4.24, see `reeb-geometric-thickening.md`) lifted to graph
  objects.
- **Observation 4.33**, second bullet, `d_R(U_ε f, U_ε g) ≤ d_R(f, g)`, with
  `d_R(f, g) = d_I(C(f), C(g))` (Definition 4.4), follows from Proposition 4.32 as the source says;
  this is `interleavingDistance_geometricSmoothing_le`. Of the first bullet, `U_0 ≃ 1` is
  `geometricSmoothingZeroIso`, constructed geometrically from `T_0 ≅ 1` and the Reeb projection of
  graph objects instead of through the equivalence of categories.
- **Observation 4.34** gives `ζ^ε_f` as the zero section followed by the Reeb quotient; this is
  `geometricSmoothingUnit`.
- **Proposition 4.35** states that `C(ζ)` and `σ` agree through the isomorphism of Proposition 4.32,
  whose arrow is drawn from `S_ε C(f)` to `C U_ε(f)`, that is, as `β⁻¹`. The library states the
  equivalent form `C(ζ) ≫ β = σ`; the drawn form `C(ζ) = σ ≫ β⁻¹` follows by composing with `β⁻¹`.
  The source's proof passes through the homotopy inverse of Lemma 4.25 and a fiberwise homotopy;
  here `η` cancels exactly and the pointwise equation `p ∘ L = R` of the first projection closes
  the square, with no homotopy.

Not claimed here: the geometric interleavings of Definition 4.36 and their distance; composition
coherences of geometric smoothing and the semigroup isomorphisms `U_{ε₁+ε₂} ≃ U_{ε₁}U_{ε₂}` of
Observation 4.33, which are proved independently in
[reeb-quotient-thickening-absorption.md](reeb-quotient-thickening-absorption.md) (the corresponding statement `T_ε T_δ ≅ T_{ε+δ}` for product thickening is false
in general: a point thickens to a rectangle on one side and to an interval on the other; the
addition map `T_ε T_δ → T_(ε+δ)`, its lax coherence and a machine-checked one-point
non-isomorphism are in `reeb-geometric-thickening-addition.md`, and the natural isomorphism
`ℛ T_ε T_δ ≅ U_(ε+δ)` induced by the addition map on graph objects is in
`reeb-quotient-thickening-addition.md`); any new
distance on ℝ-graphs or on constructible cosheaves; ordered-space or Reeb-ordering results; the
general identification of the fibers of `U_ε f` and of its vertex set after Definition 4.30.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.3, Proposition 4.26, and §4.4,
Definition 4.30, Example 4.31, Proposition 4.32, Observations 4.33 and 4.34 and Proposition
4.35](https://arxiv.org/html/1501.04147v1).
