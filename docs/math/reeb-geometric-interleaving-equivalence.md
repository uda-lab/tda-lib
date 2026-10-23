# Geometric and cosheaf interleavings of graph objects coincide

## Setting

This digest continues `reeb-geometric-interleaving.md` and uses its objects without redefinition:
`U_ε = geometricSmoothing ε`, `ζ^ε` the geometric unit, `μ_(ε,δ) : U_ε U_δ ≅ U_(ε+δ)`,
`C = cosheafFunctor : RGraphCat ⥤ ConstructibleCosheafCat`,
`β^ε : U_ε ⋙ C ≅ C ⋙ constructibleSmoothing ε`, `S_ε = smoothing ε` on interval precosheaves, and
the shifted map

```lean
cosheafShiftMap φ = (C φ).hom ≫ β^ε_B : (C A).obj ⟶ S_ε (C B).obj      (φ : A ⟶ U_ε B).
```

The outer parameter comes first, interleaving parameters are the literal `ε + ε` and `ε + δ`, and
everything is in universe `0`.

## The shifted-map bijection

`cosheafShiftEquiv ε A B : (A ⟶ U_ε B) ≃ ((C A).obj ⟶ S_ε (C B).obj)` has `cosheafShiftMap` as
its forward map, by definition. Its inverse sends `f` to the preimage under `C` of
`f ≫ (β^ε_B)⁻¹`. Three facts make this work.

* **Maps need no constructibility proof.** `ConstructibleCosheafCat` is a full subcategory, so a
  morphism of constructible cosheaves is exactly a natural transformation of the underlying
  precosheaves. The composite `f ≫ (β^ε_B)⁻¹ : (C A).obj ⟶ (C (U_ε B)).obj` is therefore a morphism
  `C A ⟶ C (U_ε B)` as it stands.
* **`C` is fully faithful** (`cosheafFullyFaithful`), on all graph objects and without
  hypotheses, so that morphism has a unique preimage `A ⟶ U_ε B`.
* **`β^ε_B` is an isomorphism**, so composing with it and with its inverse cancel.

`S_ε (C B).obj` is not definitionally `(C (U_ε B)).obj`; the two are related only through `β^ε_B`.
Consequently `cosheafShiftMap` is injective, and every natural transformation
`(C A).obj ⟶ S_ε (C B).obj` is a shifted map.

The shifted map also has a direct formulation in `ConstructibleCosheafCat`:

```lean
constructibleShiftMap φ : C A ⟶ (constructibleSmoothing ε).obj (C B)      (φ : A ⟶ U_ε B)
```

Its underlying map is `cosheafShiftMap φ` (`constructibleShiftMap_hom`), and the geometric unit
maps to the constructible smoothing unit (`constructibleShiftMap_unit`). The `μ` square is
available componentwise as `cosheafFunctor_map_geometricSmoothingCompIso_hom_app_comp` and as
the natural-transformation equation `geometricSmoothingComparisonIso_compIso`. In particular, the
three-object composite law is an equation in `ConstructibleCosheafCat`, with no inclusion functor
or underlying-map projection:

```lean
constructibleShiftMap (φ ≫ (geometricSmoothing ε).map ψ ≫
    (geometricSmoothingCompIso ε δ).hom.app D) =
  constructibleShiftMap φ ≫ (constructibleSmoothing ε).map (constructibleShiftMap ψ) ≫
    (constructibleSmoothingCompIso ε δ).hom.app (cosheafFunctor.obj D)
```

Taking underlying maps recovers `cosheafShiftMap_comp'` through
`cosheafShiftMap_comp_of_constructible`.

The composite law of `reeb-geometric-interleaving.md` returns to the source object. Its proof never
uses that, and it holds in the three-object form

```lean
cosheafShiftMap (φ ≫ U_ε ψ ≫ μ_(ε,δ) at D) =
  cosheafShiftMap φ ≫ S_ε (cosheafShiftMap ψ) ≫ smoothingCompIso ε δ at (C D).obj
```

for `φ : A ⟶ U_ε B` and `ψ : B ⟶ U_δ D` (`cosheafShiftMap_comp'`).

## The equivalence of interleavings

A precosheaf `ε`-interleaving `j` of `(C A).obj` and `(C B).obj` gives a geometric one,
`GeometricInterleaving.ofCosheaf j`, whose maps are the preimages of `j.φ` and `j.ψ` under the
bijection. For its first triangle, apply `cosheafShiftMap` to both sides. The composite law and
the bijection turn the left side into `j.φ ≫ S_ε j.ψ ≫ smoothingCompIso ε ε`, which is the
precosheaf unit at `ε + ε` by the triangle of `j`. The unit law turns the right side `ζ^(ε+ε)` into
the same unit. Injectivity gives the geometric triangle. The mirror triangle is the same argument.

`ofCosheaf` and `toCosheaf` are mutually inverse, so

```lean
GeometricInterleaving.cosheafEquiv ε A B :
  GeometricInterleaving ε A B ≃ Interleaving ε (C A).obj (C B).obj
```

with forward map `toCosheaf`, at every parameter `ε`. In particular a geometric `ε`-interleaving
exists exactly when a precosheaf one does.

## `d_geo = d_cosheaf`

```lean
geometricInterleavingDistance A B = interleavingDistance (C A).obj (C B).obj.
```

The inequality `≥` is the merged `d_cosheaf ≤ d_geo`. The inequality `≤` is new: every precosheaf
witness gives a geometric witness at the same parameter. The approximation-from-above form

```lean
geometricInterleavingDistance A B < r ↔ ∃ ε : ℝ≥0, ε < r ∧ Nonempty (GeometricInterleaving ε A B)
```

holds directly from the infimum. Zero distance is transported from the precosheaf law: it means
geometric witnesses at every positive parameter. It is not a statement about `0`-witnesses, and
zero distance does not give `A ≅ B`.

## Composition and the triangle inequality

Composition is defined by transport,

```lean
GeometricInterleaving.trans i j = ofCosheaf (i.toCosheaf.trans j.toCosheaf)
```

for `i` at `ε` and `j` at `δ`, landing at `ε + δ`. So its cosheaf image is the precosheaf composite
with no triangle proof. Its first component is the geometric shifted composite
`A ⟶ U_ε B ⟶ U_ε U_δ D ≅ U_(ε+δ) D`, by the three-object composite law and injectivity
(`GeometricInterleaving.trans_φ`).

A direct geometric definition would also have to produce the second component of the precosheaf
composite, which ends with the band inclusion of `δ + ε = ε + δ`. Its geometric counterpart is the
band-inclusion isomorphism `geometricSmoothingEqIso`; the resulting formula is recorded by
`GeometricInterleaving.trans_ψ` and `GeometricInterleaving.trans_ψ'`.

The triangle inequality for `d_geo` and invariance under isomorphism of graph objects, in both
arguments, follow from the equality and the precosheaf results. The distance stays a plain
function; no `EDist`, `PseudoEMetricSpace` or `MetricSpace` instance is installed.

## Fixtures

* **Round trip.** The geometric `1/2`-interleaving of the single edge and its midpoint is
  recovered from its precosheaf interleaving, and its first precosheaf map is the shifted map of
  its preimage.
* **Exact cosheaf distance.** The component precosheaves of the edge and its midpoint are at
  interleaving distance exactly `1/2`, sharpening the merged upper bound, and they admit no
  precosheaf `ε`-interleaving for `ε < 1/2`. The component precosheaves of the two parallel edges
  and the single edge admit no `0`-interleaving.
* **Composite witness.** The `1/4`-interleaving of the parallel edges with the edge, composed with
  the `1/2`-interleaving of the edge with its midpoint, is a geometric `(1/4 + 1/2)`-interleaving,
  with its cosheaf image and its first component written out. The triangle inequality gives
  `d_geo(parallel edges, midpoint) ≤ 1/4 + 1/2`; no exact value is claimed.
* **Presentations.** The edge over `0 < 1/2 < 1` is at distance `1/2` from the midpoint, by
  invariance under the subdivision isomorphism.
* **Zero distance.** The two presentations of the edge have witnesses at every positive parameter;
  the edge and its midpoint do not.
* **Lifted triangle.** The `1/4` parallel-single interleaving satisfies both triangles after
  applying `constructibleShiftMap`, `constructibleSmoothing` and the lifted composition
  isomorphism, once at the parallel graph and once at the single graph.
* **Range and component controls.** The two-point graph and the singleton at `0` have equal height
  ranges but distance `⊤` by the component obstruction. The parallel edges and the single
  edge have range bound `0`, no `0`-interleaving, and distance exactly `1/4`.
* **Interval-local controls.** For every parameter below `1/4`, the parallel edges and the single
  edge have no geometric interleaving in either direction, with explicit instances at `1/8` and
  `6/25` (`0.24`). At `1/4`, the double thickening of every nonempty interval is not contained in
  `(0,1)`. In the edge--midpoint pair, the nontriviality form of the local obstruction never
  applies with the single edge as source, while the two disjoint edges and the single edge have
  distance `⊤` via the top-component obstruction at `⊤`. Together, these are controls for the
  independence of the nontriviality form of the obstruction from the range and top-component
  bounds.
* **Smoothing controls.** Smoothing the edge--midpoint and parallel--single witnesses gives
  computed components, coherence laws, an unchanged edge--midpoint threshold, an exact smoothed
  distance, and two distance bounds.

## Enlargement, monotonicity and self-smoothing

The following are library statements proved from the merged thickening, quotient, comparison and
precosheaf facts; no numbered source result is claimed.

**(A) Enlargement.** For `h : ε ≤ δ`, `geometricEnlargement h : U_ε ⟶ U_δ` is the merged band
inclusion followed by the Reeb quotient. Its representative formula is
`geometricEnlargement_app_hom_left_mk`; its identity, composition, unit and parameter-equality
laws are `geometricEnlargement_refl`, `geometricEnlargement_comp`,
`geometricSmoothingUnit_comp_geometricEnlargement` and
`geometricSmoothingEqIso_hom_eq`. The comparison square is
`cosheafFunctor_map_geometricEnlargement_app`, and the shifted-map law is
`cosheafShiftMap_comp_geometricEnlargement`. These are statements on `RGraphCat` after the Reeb
quotient; no composite claim on `Over ℝ` is made.

**(B) Monotonicity.** `GeometricInterleaving.mono` enlarges both components of a witness, with
the component formulas `GeometricInterleaving.mono_φ` and `GeometricInterleaving.mono_ψ`.
Witness nonemptiness is monotone by `nonempty_mono`, witnesses above the distance are supplied by
`nonempty_of_geometricInterleavingDistance_lt`, and the threshold characterization is
`geometricInterleavingDistance_le_iff`.

**(C) Composition.** The second component of geometric composition is explicit in
`GeometricInterleaving.trans_ψ` and `GeometricInterleaving.trans_ψ'`, using the equality
isomorphism after the outer-parameter-first `geometricSmoothingCompIso`.

**(D) Self-smoothing.** `GeometricInterleaving.selfSmoothing` gives every graph object a witness
from the object to its `ε`-smoothing. The witness is obtained by transporting precosheaf
self-smoothing along the comparison isomorphism with the generic `Interleaving.isoRight`. Its
components are described by
`GeometricInterleaving.selfSmoothing_φ` and `GeometricInterleaving.selfSmoothing_ψ`, and the
distance consequences are `geometricInterleavingDistance_geometricSmoothing_self_le` and
`geometricInterleavingDistance_geometricSmoothing_le`, expressing nonexpansiveness of `U_ε` for
`d_geo`. The fixtures exhibit the collapse of the two parallel edges under enlargement `1/4 → 1/2`;
for the point graph, smoothing produces a segment, so only the upper bound is claimed, not
smoothing invariance.

## Lower bounds and exact values

`heightRange A` is the set of heights attained by `A`. The smoothed range is given by
`heightRange_geometricSmoothing`: `heightRange (U_ε A) = heightRange A + Icc (-ε) ε`.

The range obstruction is `hausdorffEDist_heightRange_le_geometricInterleavingDistance`. It bounds
the Hausdorff edistance of the two height ranges by `d_geo`, using only the existence of both maps
in a geometric interleaving. If one graph is empty and the other is nonempty, the distance is `⊤`.

The supremum lemma `ofReal_abs_sSup_sub_le_hausdorffEDist` bounds the difference of the suprema of
two nonempty bounded real sets by their Hausdorff edistance. Together with the smoothed-range
formula, it gives `d_geo(A, U_ε A) = ε` for nonempty `A`.

The component obstruction uses `Interleaving.topEquiv` at `⊤`. Here
`thicken ε ⊤ = ⊤`, so every geometric interleaving induces an equivalence of the top component
types. The singleton graphs satisfy `d_geo(P_a, P_b) = |a − b|`, and the edge and its midpoint
have distance `1/2`.

The two-point graph and the singleton at `0` have equal height ranges, so the range bound gives only
`0`, while their distance is `⊤` by the component obstruction. The parallel edges and the single
edge have range bound `0`, but no `0`-interleaving; an existing witness gives distance at most
`1/4`.

The interval-local obstruction starts with `Interleaving.φ_app_injective`: if the double-thickening
restriction of `F` at `I` is injective, then the first map of any interleaving is injective. A
nontrivial source value and a subsingleton shifted target value therefore exclude an interleaving.
The cardinality version uses a finite target with smaller cardinality. The two forms transport to
geometric interleavings through `GeometricInterleaving.toCosheaf`, and
`le_geometricInterleavingDistance_of_isEmpty` turns exclusion below `r` into a distance lower bound.

For `0 ≤ ε < 1/4`, take `I = ioo (2ε) (1 − 2ε)`. It is nonempty, and two applications of
`thicken_ioo` give `I^ε = ioo ε (1 − ε)` and `I^(2ε) = ioo 0 1 = S01.K 0`. The parallel-edge
restriction is bijective on this gap, so its value at `I` is nontrivial. The single-edge value at
`I^ε` is a subsingleton. Thus `parallelSingle_isEmpty` excludes every geometric interleaving
below `1/4`.

Together with the merged witness, this proves
`geometricInterleavingDistance parallelGraph singleGraph = 1/4`. The cosheaf distance has the same
value by `geometricInterleavingDistance_eq_interleavingDistance`. At the boundary `ε = 1/4`, no
nonempty interval has its double thickening contained in `(0,1)`, so the injectivity hypothesis is
unavailable. In particular the pair has positive distance, while its height-range bound is `0`, a
strict gap `0 < 1/4`.

The nontriviality (subsingleton-target) form of the local obstruction is independent of the
edge-versus-midpoint obstruction: every single-edge value is a subsingleton, so the local
hypothesis never applies with the single edge as source. The cardinality form is not excluded by
this argument: at `ε = 0`, an interval above height `1/2` meets the edge in one component while
the midpoint value is empty. The positive edge-midpoint result below `1/2` instead comes from the
height-range bound. For two disjoint edges versus the single edge, the same local theorem at `⊤`
gives geometric distance `⊤`.

## Smoothing of geometric interleavings

The commutation isomorphism `geometricSmoothingCommIso` is the three-term composite
`geometricSmoothingCompIso δ ε ≪≫ geometricSmoothingEqIso (add_comm δ ε) ≪≫
(geometricSmoothingCompIso ε δ).symm`. Its zero law is
`geometricSmoothingCommIso_zero_hom_app`, and its naturality along
`geometricEnlargement` is `geometricSmoothing_map_geometricEnlargement_comp_commIso`.

`Interleaving.isoLeft` transports a precosheaf interleaving on its first argument. The witness
`GeometricInterleaving.smooth` keeps the parameter `ε`: it smooths the underlying precosheaf
witness and transports its two arguments through the geometric precosheaf comparison
isomorphisms. Its components are given by `smooth_φ` and `smooth_ψ`.

The witness has the zero laws `smooth_zero_φ` and `smooth_zero_ψ`, the additivity laws
`smooth_add_φ` and `smooth_add_ψ`, and the monotonicity law `smooth_mono`. The bound
`geometricInterleavingDistance_geometricSmoothing_le` also follows witness-wise from
`geometricInterleavingDistance_smooth_le` by `le_iInf₂`.

The four shift bounds
`geometricInterleavingDistance_geometricSmoothing_left_le`,
`geometricInterleavingDistance_le_geometricSmoothing_left`,
`geometricInterleavingDistance_geometricSmoothing_right_le` and
`geometricInterleavingDistance_le_geometricSmoothing_right` are the two-sided form of
`|d_geo(U_η A, C) − d_geo(A, C)| ≤ η` in `ℝ≥0∞`, with subtraction truncated.

Smoothing the edge and its midpoint by `1/4` keeps their distance exactly `1/2`; the fixtures
also show that no witness exists below `1/2`. Compatibility of smoothing with `trans` is not
claimed here.

## Interleavings of constructible ℝ-spaces

Let `q_X` denote the unit of
`quotientRGraphAdjunction : quotientRGraphFunctor ⊣ rgraphToConstructible` at a constructible
space `X`. The functor `rgraphToConstructible` includes graph objects as constructible spaces,
and `quotientRGraphAdjunction_unit_app_hom` identifies `q_X` with the Reeb projection. At a graph
object `A`, the counit is the inverse `q_A⁻¹` of the graph projection isomorphism, as recorded by
`quotientRGraphAdjunction_counit_app_hom`.

The constructible-space smoothing is the endofunctor
`RGraph.constructibleSmoothing ε = thickeningQuotient ε ⋙ rgraphToConstructible`, namely
`ℛ T_ε` on `ConstructibleSpaceCat`. Its unit is `constructibleSmoothingUnit ε`, given on points
by `x ↦ [(x, 0)]`, and its additive coherence is
`constructibleSmoothingCompIso ε δ : constructibleSmoothing δ ⋙ constructibleSmoothing ε ≅
constructibleSmoothing (ε + δ)`. This smoothing is distinct from the cosheaf
`constructibleSmoothing` used earlier. The absorption component is exactly constructible
thickening of the reflection unit, by `thickeningQuotientAbsorptionIso_hom_app_eq`; and
`homEquiv_symm_constructibleSmoothingUnit` says that the constructible smoothing unit transposes
to the geometric unit `ζ^ε` after absorption.

A `ConstructibleInterleaving ε X Y` has maps
`φ : X ⟶ ℛ T_ε Y` and `ψ : Y ⟶ ℛ T_ε X`, with both composites equal to the smoothing unit at
the literal parameter `ε + ε`. Its coherence is built from `thickeningQuotientCompIso`, so this
is a priori different from a graph interleaving of `ℛ X` and `ℛ Y`: its maps start at `X` and `Y`
themselves, and its composite law uses constructible thickening rather than only the graph-object
semigroup. The core calculation is `ConstructibleInterleaving.coherence_iff`.

After transposing along the reflection and applying absorption, the equivalence
`ConstructibleInterleaving.equivGeometric` gives a bijection

```lean
ConstructibleInterleaving ε X Y ≃
  GeometricInterleaving ε (quotientRGraphFunctor.obj X) (quotientRGraphFunctor.obj Y)
```

Thus
`constructibleInterleavingDistance_eq_geometricInterleavingDistance` identifies the constructible
distance with `d_geo (ℛ X, ℛ Y)`. The same distance is

```lean
interleavingDistance (intervalComponents (overBaseMap X.obj))
  (intervalComponents (overBaseMap Y.obj))
```

by `constructibleInterleavingDistance_eq_interleavingDistance`, using
`constructibleComponentComparisonIso` and the merged comparison corresponding to DMP15-v1
Theorem 3.17. The distance has the self, symmetry, triangle and isomorphism-invariance laws
`constructibleInterleavingDistance_self`, `constructibleInterleavingDistance_comm`,
`constructibleInterleavingDistance_triangle` and `constructibleInterleavingDistance_congr`.
`constructibleInterleavingDistance_eq_zero_iff` specifies zero distance as witnesses at every
positive parameter, not necessarily a witness at `0`.

`ConstructibleInterleaving.toQuotient` gives a zero-parameter witness from `X` to its Reeb graph,
and `constructibleInterleavingDistance_quotient` gives distance zero. On graph inputs,
`constructibleInterleavingDistance_rgraphToConstructible` recovers the geometric graph distance.
The bounds `constructibleInterleavingDistance_constructibleSmoothing_self_le` and
`constructibleInterleavingDistance_constructibleSmoothing_le` give the smoothing bound and
nonexpansiveness, while `constructibleInterleavingDistance_le_edist` gives the sup-norm stability
bound for two constructible heights on a common carrier.

Fixture F1 is the boundary control: the constant-height interval and the point satisfy
`constructibleInterleavingDistance_interval_point`, so their distance is `0`, while
`not_nonempty_interval_iso_point` proves that they are not isomorphic as spaces over `ℝ`.
Therefore the distance sees the Reeb graph and zero distance does not imply an isomorphism of
spaces. The other fixtures give exact values `1` and `1/2` for the two singleton graphs and the
edge--midpoint pair (`constructibleInterleavingDistance_singleton_zero_one` and
`constructibleInterleavingDistance_single_mid`), emptiness below `1/2` for the latter
(`single_mid_isEmpty`), the pinch smoothing bound
(`constructibleInterleavingDistance_pinch_smoothing_le`), and distance at most `1` between the
constant heights `0` and `1` (`constructibleInterleavingDistance_const_zero_one_le`).
Only the statement shape of DMP15-v1 Definition 4.36 is attributed here; the reflection,
constructible smoothing, interleaving equivalence and distance results are library statements.
Constructibility of `T_ε X` itself is not claimed.

## Level perturbations of a fixed presentation

Let `P : CylinderPresentation n` and let `S T : CriticalValues n` have the same number of
levels. The presentation pieces and endpoint maps stay fixed. On each segment, `segMap S T`
is the affine map sending the lower and upper `S` endpoints to the corresponding `T`
endpoints. Its endpoint and inverse laws allow `levelMap` to descend through `CompatibleMaps`
and `lift`; `levelHomeomorph` is a homeomorphism `P.Realization S ≃ₜ P.Realization T`.
These constructions and the pointwise height bound are universe-polymorphic and need no
compactness or local path-connectedness assumptions.

The transported height on the fixed carrier `P.Realization S` is
`(P.height T).comp (P.levelMap S T)`. The segment displacement is a convex combination of
the endpoint displacements, so `abs_height_sub_height_levelMap_le` and
`edist_height_levelMap_le` bound its difference from `P.height S` by the literal mathlib sup
distance `edist S.value T.value`.

For the constructible-space interfaces, `P` is in universe `0` and all vertex and edge pieces
are compact and locally path-connected. `isConstructibleSpace_realization` packages its
realization as `P.realizationSpace S`. `levelOverIso` identifies the transported height with
the realization at `T`, proving `isConstructibleSpace_height_comp_levelMap`. Thus the second
height is constructible by construction. Sup-norm stability gives

```lean
constructibleInterleavingDistance (P.realizationSpace S) (P.realizationSpace T) ≤
  edist S.value T.value
```

by `constructibleInterleavingDistance_realizationSpace_le`.

More generally, a specified presentation isomorphism
`i : A ≅ Over.mk (TopCat.ofHom (P.height S))` determines `P.levelPerturbation i T` on the
original carrier `A.left`. Both objects are constructible, by
`isConstructibleSpace_of_iso_realization` and `isConstructibleSpace_levelPerturbation`.
The carrier form `constructibleInterleavingDistance_levelPerturbation_le` bounds their
distance by the sup distance of their heights on `A.left`; `edist_levelPerturbation_le`
then bounds that quantity by `edist S.value T.value`. On fixed finite incidence data `D`,
`geometricInterleavingDistance_toRGraph_le` gives the graph-object form

```lean
geometricInterleavingDistance ((toRGraph S).obj D) ((toRGraph T).obj D) ≤
  edist S.value T.value
```

`heightRange_quotientRGraphFunctor_obj` proves that passing to the Reeb graph preserves the
height range. For nonempty constructible spaces `X` and `Y`, the boundedness of these ranges
and the Hausdorff height-range obstruction give

```lean
ENNReal.ofReal |sSup (Set.range (overBaseMap X.obj)) -
    sSup (Set.range (overBaseMap Y.obj))| ≤ constructibleInterleavingDistance X Y
```

by `ofReal_abs_sSup_range_sub_le_constructibleInterleavingDistance`. Both nonempty carrier
hypotheses are explicit. The ranges are the sets of attained heights; extreme listed
levels need not be occupied.

`CriticalValues.translate S c` adds `c` to every level and retains strict monotonicity.
`edist_translate` identifies the level-list distance with `ENNReal.ofReal |c|`, and
`height_levelMap_translate` says that every point's height increases by `c`. For a nonempty
realization, the translated height range is the image of the original range under addition
by `c`, so its supremum also increases by `c`. The upper bound and the general supremum
lower bound therefore agree:

```lean
constructibleInterleavingDistance (P.realizationSpace S)
    (P.realizationSpace (S.translate c)) = ENNReal.ofReal |c|
```

This is `constructibleInterleavingDistance_realizationSpace_translate`, with
`[Nonempty (P.Realization S)]` and no sign restriction on `c`.

The acceptance fixtures in `TDA.Reeb.ConstructiblePerturbationExamples` cover:

- **P1:** `singleton_stability_attained` applies the new finite-data bound to arbitrary singleton
  heights and reuses the exact singleton distance to show attainment.
- **P2:** `singleEdge_geometric_distance_eq_one` moves the top level from `1` to `2`; the upper
  bound and the supremum lower bound both give distance `1`.
- **P3:** `cycle_translation_distance` gives the exact translation value for `cycleData` over
  `S012`, for every real `c`.
- **P4:** `pinchI_transported_height_constructible` and `pinchI_constructible_stability_le_one`
  exercise the thickened pinch, with continuous pieces and a noninjective attachment. The
  carrier fixtures also use a nonidentity presentation isomorphism.
- **N1:** `reversed_levels_not_criticalValues` rejects the assignment `![1, 0]`.
- **N2:** `empty_translation_distance_zero` proves that an empty realization has distance `0`
  from its unit translate, which differs from `ENNReal.ofReal |1|`. The nonempty hypothesis
  of the exact translation theorem is necessary.
- **N3:** `pinchI_identity` gives the identity level map and distance at most `0` on the
  thickened pinch.

This API changes only the level list of a fixed presentation with the same `n`. It does not
compare different presentations or level counts; for piecewise-linear heights on a fixed
finite graph, where vertex heights may cross and the number of levels may change, see
[vertex-height perturbations](reeb-graph-pl.md#vertex-height-perturbations-of-a-fixed-graph). Arbitrary continuous perturbations, such
as a bump on a cylinder, need not preserve constructibility and are outside this API. The
homeomorphism, constructibility transfer, stability compositions, supremum lower bound and
exact translation value are library derivations from the cylinder-presentation and sup-norm
stability APIs; no new numbered source result is attributed to them.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4. As in `reeb-geometric-interleaving.md`,
only the statement shapes of **Definition 4.36** and **Definition 4.4** are attributed. The
bijection, the equivalence of geometric and cosheaf interleavings, `d_geo = d_cosheaf`,
composition, the triangle inequality, isomorphism invariance, the zero-distance law, the
interval-local obstruction and its geometric transport, the exact value `1/4` and its cosheaf twin,
positivity and the strict range gap are **library statements proved from merged facts**: full
faithfulness of `C`, invertibility of `β^ε` and the unit and composite laws of the shifted map. None
is attributed to a numbered source result.
Essential surjectivity of `C` is not used, so no critical-value scope is inherited.

Not claimed here: absorption beyond (H2); a comparison with Mapper; interleavings of precosheaves
that do not come from graph objects; and interleavings internal to `ConstructibleCosheafCat` and a
lift of `GeometricInterleaving.toCosheaf` to them.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §4.4, Definition
4.36](https://arxiv.org/html/1501.04147v1).
