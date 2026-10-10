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
smoothing both sides by any `δ` (`interleavingDistance_smoothing_intervalComponents_le`). The
bound is pointwise; no supremum of `|f - g|` is formed. These corollaries live in a separate
module, so the distance core depends only on the interleaving and smoothing API.

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
- `interleavingDistance_intervalComponents_le` is Theorem 4.6(i) with the pointwise hypothesis,
  which is equivalent to `‖f − g‖_∞ ≤ ε`. Theorem 4.6(ii) is not addressed.
- Proposition 4.8 of the source states that zero Reeb distance implies isomorphism for
  ℝ-graphs, through their constructible cosheaves. No such inference is made here for arbitrary
  precosheaves.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147).
