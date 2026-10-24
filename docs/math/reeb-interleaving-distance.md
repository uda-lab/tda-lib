# The extended interleaving distance

## Definition

Let `C` be any category and `F G : OpenInterval ⥤ C` precosheaves on the interval category.
The interleaving distance is the extended infimum

```lean
interleavingDistance F G = ⨅ (ε : ℝ≥0) (_ : Nonempty (Interleaving ε F G)), (ε : ℝ≥0∞)
```

of the nonnegative parameters admitting an `ε`-interleaving, with values in `[0, ∞]`. The
infimum of the empty set is `⊤`, so the distance is `⊤` exactly when no interleaving exists at
any parameter (`interleavingDistance_eq_top_iff`). An explicit `ε`-interleaving bounds the
distance by `ε` (`Interleaving.interleavingDistance_le`, `interleavingDistance_le_of_nonempty`).
The infimum is characterized by its lower-envelope property (`le_interleavingDistance_iff`) and
by approximation from above (`interleavingDistance_lt_iff`), without assuming that it is
attained.

The distance is a plain function. No `EDist`, `PseudoEMetricSpace` or `MetricSpace` instance
is installed on `OpenInterval ⥤ C`.

## Laws

- **Zero.** A `0`-interleaving gives distance `0`
  (`Interleaving.interleavingDistance_eq_zero`). Hence `interleavingDistance F F = 0`
  (`interleavingDistance_self`), and isomorphic precosheaves are at distance `0`
  (`interleavingDistance_eq_zero_of_iso`).
- **Symmetry.** `interleavingDistance_comm`, since `Interleaving.symm` swaps the witnesses.
- **Triangle inequality.** `interleavingDistance_triangle`. An `ε`-interleaving of `F, G` and a
  `δ`-interleaving of `G, H` compose to an `(ε + δ)`-interleaving of `F, H`, so the distance of
  `F, H` is at most the double infimum of `ε + δ` over witnessed pairs. Addition distributes over
  infima in `ℝ≥0∞` for every index type, including an empty one, where both sides are `⊤`. No
  case split on infinite summands and no attainment are needed.
- **Isomorphism invariance.** `interleavingDistance_congr`: natural isomorphisms `F ≅ F'` and
  `G ≅ G'` give `interleavingDistance F G = interleavingDistance F' G'`. Each isomorphism is a
  `0`-interleaving, and composing with it does not increase the parameter.
- **Zero distance.** `interleavingDistance_eq_zero_iff`: the distance is `0` exactly when an
  `ε`-interleaving exists for every `ε > 0`. In general this does not give a `0`-interleaving,
  so zero distance does not imply isomorphism (`point_closure_distance`).
- **Smoothing.** Smoothing is nonexpansive: the distance of `(smoothing ε).obj F` and
  `(smoothing ε).obj G` is at most that of `F, G` (`interleavingDistance_smoothing_le`), since an
  interleaving of `F, G` smooths to one of the same parameter. A precosheaf is within `ε` of its
  smoothing (`interleavingDistance_smoothing_self_le`).

## Uniform perturbation

For continuous `f g : C(X, ℝ)` on the same space with `∀ x, |f x - g x| ≤ ε`, the explicit
`perturbationInterleaving` gives

```lean
interleavingDistance (intervalComponents f) (intervalComponents g) ≤ ε
```

(`interleavingDistance_intervalComponents_le`). By nonexpansiveness the same bound holds after
smoothing both sides by any `δ` (`interleavingDistance_smoothing_intervalComponents_le`). These
two theorems take the pointwise hypothesis and form no supremum of `|f - g|`; the bound by the
supremum distance itself is stated in the next section. These corollaries live in a separate
module, so the distance core depends only on the interleaving and smoothing API.

## Supremum distance

For arbitrary `f g : X → ℝ`, the supremum distance `‖f − g‖_∞` is mathlib's extended distance
on the type `X →ᵤ ℝ` of functions with the uniform structure. Its real-valued presentation is

```lean
edist (UniformFun.ofFun f) (UniformFun.ofFun g) = ⨆ x, ENNReal.ofReal |f x - g x|
```

(`edist_uniformFun_ofFun_eq_iSup`), with values in `[0, ∞]`. An unbounded difference has
distance `⊤` (for example `edist_id_twiceId_eq_top`); no boundedness is assumed and no finite
real supremum is formed. The zero, symmetry and triangle laws are those of mathlib's
`PseudoEMetricSpace (X →ᵤ ℝ)` instance; the library adds no wrapper, structure or instance.
For `ε : ℝ≥0` the distance is at most `ε` exactly when `∀ x, |f x - g x| ≤ ε`
(`edist_uniformFun_ofFun_le_coe_iff`).

For continuous `f g : C(X, ℝ)` on any topological space `X`,

```lean
interleavingDistance (intervalComponents f) (intervalComponents g) ≤
  edist (UniformFun.ofFun ⇑f) (UniformFun.ofFun ⇑g)
```

(`interleavingDistance_intervalComponents_le_edist`). No compactness, boundedness, finiteness or
nonemptiness of `X` is assumed. If the right side is `⊤` the bound is trivial. Otherwise the
right side is the coercion of its `toNNReal`, and the finite-bound characterization turns it
into the pointwise hypothesis of `interleavingDistance_intervalComponents_le`. The same bound
holds after smoothing both sides by any `δ`
(`interleavingDistance_smoothing_intervalComponents_le_edist`). These theorems live in their own
module, which adds the import of mathlib's uniform-convergence distance.

The fixtures cover four cases.

- **Empty domain.** Both sides are `0`: the supremum over an empty domain is `0`, and the left
  side follows from the theorem (`stability_of_isEmpty`).
- **Unbounded difference.** For `id` and `x ↦ 2x` on `ℝ` the supremum distance is `⊤`
  (`edist_id_twiceId_eq_top`), so the theorem is the trivial bound, and no `ε : ℝ≥0` satisfies
  the pointwise hypothesis.
- **Constant translation.** For `x ↦ f x + c` the theorem gives distance at most `|c|` on every
  domain (`interleavingDistance_heightShift_le`). The supremum distance is exactly `|c|` on a
  nonempty domain (`edist_heightShift`). For the constant functions `0` and `c` on a one-point
  domain both sides equal `|c|`, by the sharpness of the constant translation
  (`stability_const_eq`). No optimality of the bound on other domains is claimed.
- **Equal heights.** Both sides are `0` (`stability_self`).

## Fixtures

All fixtures are at `C := Type`.

- **Zero distance without isomorphism.** The precosheaves `I ↦ {0 ∈ I}` and
  `I ↦ {0 ∈ closure I}` are `ε`-interleaved for every `ε > 0`, so their distance is `0`. They are
  not `0`-interleaved and hence not isomorphic (`point_closure_distance`).
- **Infinite distance.** The constant empty precosheaf and the constant one-point precosheaf
  admit no interleaving: a reverse witness would send the point to the empty set at the whole
  line. Their distance is `⊤` (`const_empty_const_unit_distance`).
- **Exact finite distance.** The point precosheaves `I ↦ {0 ∈ I}` and `I ↦ {1 ∈ I}` are at
  distance exactly `1` (`point_distance_eq_one`). The upper bound is the explicit
  `1`-interleaving. For `ε < 1` and `r = (1 - ε) / 2`, a witness would send `0 ∈ (-r, r)` into
  `thicken ε (-r, r) = (-r - ε, r + ε)`, which does not contain `1` because
  `r + ε = (1 + ε) / 2 < 1`.

## Cardinality obstructions

For `F G : OpenInterval ⥤ Type v`, an `ε`-interleaving `i` and an interval `I`, the restriction
`F(I) → F(T_ε T_ε I)` equals `ψ_(T_ε I) ∘ φ_I`. Its range therefore lies in the range of
`ψ_(T_ε I)` (`Interleaving.range_map_subset_range_ψ`), and

```lean
Nat.card (range (F.map (I ⟶ T_ε T_ε I))) ≤ Nat.card (G.obj (T_ε I))
```

when `G(T_ε I)` is finite (`Interleaving.card_range_map_le`; `card_range_map_add_le` for the
restriction to `T_(ε+ε) I`). If the restriction is injective, then `φ_I` is injective
(`Interleaving.φ_app_injective`), `F(I)` is finite and `Nat.card (F I) ≤ Nat.card (G (T_ε I))`
(`Interleaving.finite_of_injective`, `Interleaving.card_le_of_injective`).

A strict reverse inequality excludes every `ε`-interleaving: in the range form
(`Interleaving.isEmpty_of_card_lt_card_range`) and in the injective form
(`Interleaving.isEmpty_of_injective_of_card_lt`). If for every `ε` with `ε < r` some `I` has an
injective restriction, a finite value `G(T_ε I)` and `Nat.card (G (T_ε I)) < Nat.card (F I)`, then
`r ≤ interleavingDistance F G` (`le_interleavingDistance_of_forall_exists_card_lt`);
`le_interleavingDistance_of_forall_exists_card_lt_symm` places the obstruction on the second
argument. At `⊤`, every interleaving gives `F(⊤) ≃ G(⊤)` (`Interleaving.topEquiv`), so
`Nat.card (F ⊤) ≠ Nat.card (G ⊤)` gives distance `⊤` (`interleavingDistance_eq_top_of_card_ne`;
`RGraph.geometricInterleavingDistance_eq_top_of_card_ne` for graph objects).

`Nat.card` of an infinite type is `0`, so these bounds assume finiteness of the target value where
they use it, and the `⊤` form gives nothing when both top values are infinite. The injectivity
hypothesis cannot be dropped from the injective form; `reeb-graph-pl.md` § Vertex-height
perturbations has a graph-PL pair with the counts `2` and `1` and an interleaving.

The fixtures in `TDA/Reeb/InterleavingCardinalityExamples.lean` recover the distance `1` of the
point precosheaves at `0` and `1` from the counts `1` and `0` (`point_distance_eq_one_of_card`),
the nonempty-against-empty obstruction for finite `F(I)` from the range form
(`isEmpty_of_nonempty_of_isEmpty_of_finite`), and the distance `⊤` between an empty and a
nonempty graph object with finitely many top components
(`geometricInterleavingDistance_eq_top_of_isEmpty_of_nonempty_of_card`). These are library
statements; no numbered result of de Silva, Munch and Patel states them.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, Definition 4.4, define the interleaving
distance of set-valued pre-cosheaves on **Int** as the infimum of the parameters admitting an
interleaving, with the infimum of the empty set equal to `∞`. Proposition 4.5 states that it is
an extended pseudometric with values in `[0, ∞]`: symmetric, satisfying the triangle inequality,
and zero on equal arguments. Its proof composes witnesses for the triangle inequality.
Theorem 4.6(i) bounds the distance of the component cosheaves of `(X, f)` and `(X, g)` by
`‖f − g‖_∞`, and Proposition 4.17 states that smoothing is a contraction.

- `interleavingDistance` is Definition 4.4 for an arbitrary target category `C`; the source's
  case is `C := Type`. Admitting `∅`, rays and `ℝ` as intervals and taking `ε : ℝ≥0` are choices
  of the library.
- The pseudometric laws of Proposition 4.5 are `interleavingDistance_self`,
  `interleavingDistance_comm` and `interleavingDistance_triangle`. Isomorphism invariance is
  stated separately.
- `interleavingDistance_intervalComponents_le_edist` is Theorem 4.6(i) in its literal form, with
  `‖f − g‖_∞` mathlib's extended supremum distance, which may be `∞`.
  `interleavingDistance_intervalComponents_le` is the same theorem with the pointwise
  hypothesis, which is equivalent to `‖f − g‖_∞ ≤ ε` (`edist_uniformFun_ofFun_le_coe_iff`).
  Theorem 4.6(ii) is not addressed.
- Proposition 4.8 of the source states that zero Reeb distance implies isomorphism for
  ℝ-graphs, through their constructible cosheaves. No such inference is made here for arbitrary
  precosheaves.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147).
