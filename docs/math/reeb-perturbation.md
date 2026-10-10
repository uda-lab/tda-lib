# Uniform perturbation and component interleavings

## Interval restriction of components

For a topological space `X : Type u` and a continuous `f : C(X, ℝ)`, the path-component functor
`componentFunctor f : Opens ℝ ⥤ Type u` restricts along the inclusion
`toOpensFunctor : OpenInterval ⥤ Opens ℝ` of the interval category:

```lean
intervalComponents f = toOpensFunctor ⋙ componentFunctor f
(intervalComponents f).obj I = ZerothHomotopy {x : X // f x ∈ I}
```

The second equation holds by `rfl` (`intervalComponents_obj`). An inclusion `I ≤ J` sends the
class of `x` to the class of the same point in the larger inverse image
(`intervalComponents_map_mk`), and the empty interval has no components
(`intervalComponents_obj_bot_isEmpty`). Components are path components of the inverse-image
subspace. `intervalComponents f` is a precosheaf on the interval category; no cosheaf condition
is stated for it here.

## Uniform perturbation

Let `f g : C(X, ℝ)` be continuous functions on the same space and `ε : ℝ≥0` with

```lean
hfg : ∀ x, |f x - g x| ≤ ε
```

The bound is pointwise. No supremum of `|f - g|` is formed, so an unbounded difference never
becomes a finite real number: the hypothesis simply fails for every `ε`.

If `f x ∈ I` then `g x ∈ T_ε I`, with witness `f x` (`mem_thicken_of_abs_sub_le`). Hence
`f ⁻¹' I ⊆ g ⁻¹' T_ε I` (`preimage_subset_preimage_thicken`), and the bound is symmetric
(`perturbationBound_symm`). The inclusion of subspaces is the continuous map
`perturbationInclusion hfg I`, the identity on points; it is mathlib's `ContinuousMap.inclusion`
on the two inverse images by `rfl`.

The witness `perturbationNatTrans hfg : intervalComponents f ⟶ S_ε (intervalComponents g)` has
component `componentMap (perturbationInclusion hfg I)` at `I`, sending the class of `x` to the
class of `x`. Naturality holds on representatives. The reverse witness is the same construction
for the swapped bound. Both interleaving triangles send the class of `x` to the class of `x`, as
does the structure map for `I ⊆ T_ε T_ε I`, so `Interleaving.ofApp` packages the two witnesses
as

```lean
perturbationInterleaving hfg : Interleaving ε (intervalComponents f) (intervalComponents g)
```

`Interleaving` is data, so this is a definition with explicit witnesses;
`nonempty_interleaving_of_abs_sub_le` is the existence statement. The construction is
compatible with the interleaving laws:

- at `f = g` it is `Interleaving.refl ε` for every `ε` (`perturbationInterleaving_self`), and at
  `ε = 0` its isomorphism is the identity (`perturbationInterleaving_self_toIso`);
- `symm` gives the construction for the swapped bound (`perturbationInterleaving_symm`);
- `mono` along `ε ≤ ε'` gives the construction for the weakened bound
  (`perturbationInterleaving_mono`);
- `trans` of the constructions for `f, g` at `ε` and `g, h` at `δ` gives the construction for
  any proof of the bound `ε + δ` for `f, h` (`perturbationInterleaving_trans`).

No cosheaf condition and no Reeb quotient is used.

## Constant translation and sharpness

For `c : ℝ`, the translation `x ↦ f x + c` satisfies the pointwise bound `|c|` with equality, so
`f` and `f + c` are `|c|`-interleaved for every `X` and `f`. The bound is attained by the
construction and sharp on a point: for the constant functions `0` and `c` on a one-point space
there is no `ε`-interleaving with `ε < |c|`. A witness at the interval `(-η, η)`, with
`η = (|c| - ε) / 2`, would place `c` within `ε` of a point of absolute value less than `η`,
giving `|c| < ε + η < |c|`.

The bound is not optimal in general. For `X = ℝ` and `f = id`, every inverse image of a
nonempty interval under `f` or under `f + c` is a nonempty interval, so every value of
`intervalComponents f` and `intervalComponents (f + c)` is a singleton for `I ≠ ∅` and empty
for `I = ∅`. The two functors are therefore isomorphic, hence `0`-interleaved, for every `c`. For
empty `X` every parameter admits an interleaving.

The fixtures also cover a nontrivial disconnected domain: the discrete space `Bool` with
heights `{0, 1}` and `{0, 2}`. These are `1`-interleaved with `φ` injective at every interval,
have two distinct components over `(-1/2, 3/2)`, and are not `0`-interleaved, since over
`(1/2, 3/2)` the first has a component and the second has none.

## Source correspondence

de Silva, Munch and Patel, *Categorified Reeb Graphs*, Theorem 4.6(i), state that for ℝ-spaces
`(X, f)` and `(X, g)` on the same total space the interleaving distance of the component
cosheaves is at most `‖f − g‖_∞`. The proof assumes `‖f − g‖_∞ ≤ ε`, takes the inclusions
`f⁻¹(I) ⊆ g⁻¹(I^ε)` and `g⁻¹(I) ⊆ f⁻¹(I^ε)`, defines `φ_I` and `ψ_I` as the induced maps on
path components, and observes that naturality and the interleaving conditions hold because
diagrams of inclusions commute. `perturbationInterleaving` is this witness construction.

- The hypothesis is the pointwise bound. For a finite `ε` it is equivalent to
  `‖f − g‖_∞ ≤ ε`. The distance inequality itself is not stated here.
- The source calls the component functors cosheaves; the construction uses only the
  precosheaves, and the source notes that the cosheaf condition is not needed for the stability
  theorem.
- `X` is an arbitrary topological space and `f`, `g` are continuous. Admitting `∅`, rays and `ℝ`
  as intervals and taking `ε : ℝ≥0` are choices of the library.
- Theorem 4.6(ii), the stability of Reeb graphs of constructible ℝ-spaces, is not addressed,
  and no stability of Mapper over a fixed cover is claimed.

Source: [de Silva, Munch and Patel, *Categorified Reeb Graphs*](https://arxiv.org/abs/1501.04147).
