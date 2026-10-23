# Reeb quotient functor and comparison with path components

## The induced map `Q_h`

Let `f : C(X, Y)` and `g : C(Z, Y)` be continuous maps into an arbitrary topological space `Y`,
and let `h : C(X, Z)` satisfy `g (h x) = f x` for every `x`. Composing a constant-value path with
`h` gives a constant-value path, so `h` respects the Reeb relation (`ReebRel.map`). Descending
`q_g ∘ h` through the universal property of the Reeb quotient gives

```lean
ReebQuotient.map h comm : C(ReebQuotient f, ReebQuotient g)
```

written `Q_h`. It is the unique continuous map with `Q_h ∘ q_f = q_g ∘ h` (`map_comp_proj`,
`map_unique`), it preserves the descended map, `ḡ ∘ Q_h = f̄` (`height_comp_map`), and it
preserves identities and composition (`map_id`, `map_comp`). A surjective `h` induces a
surjective `Q_h`. The carrier universes of `X`, `Y` and `Z` are independent.

## The comparison `η`

The projection `q_f` commutes with the base maps, `f̄ ∘ q_f = f`. Applying the path-component
natural transformation `componentNatTrans` to it gives

```lean
ReebQuotient.componentComparison f : componentFunctor f ⟶ componentFunctor (height f)
```

written `η_f : C_f ⟶ C_{f̄}`. It sends the path component of `x` in `f ⁻¹ U` to the path component
of `q_f x` in `f̄ ⁻¹ U`. It is natural in the open set `U` and in height-preserving maps:
`C_h ≫ η_g = η_f ≫ C_{Q_h}` (`componentComparison_natural`). It is surjective at every open,
because every point of `f̄ ⁻¹ U` is `q_f x` for some `x` with `f x ∈ U`. `η_f` itself allows
independent universes for `X` and `Y`; naturality in `h` requires `X` and `Z` to share a carrier
universe, as `componentNatTrans` does.

`η_f` need not be injective: for the topologist's sine curve with the first-coordinate projection
it is not injective at `U = ⊤` (see [the sine-curve witness](#the-topologists-sine-curve)). No
injectivity, bijectivity or natural isomorphism is claimed for `η` in general. On constructible
inputs, `η` restricted to open intervals is a natural isomorphism (see
`reeb-constructible-comparison.md`).

A separate, weaker fact is machine-checked. A continuous height-preserving surjection need not
induce injections on path components of inverse images. The fold `Bool × ℝ → ℝ` over `(ℝ, id)`
merges the two sheets at `U = ⊤` (`Examples.componentNatTrans_fold_not_injective`), and its
induced `Q_fold` is not injective (`Examples.map_fold_not_injective`).

## The topologist's sine curve

Let `S` be the graph of `x ↦ sin x⁻¹` over `0 < x ≤ 1`, `Z = {0} × [-1, 1]` the vertical segment,
`T = S ∪ Z ⊆ ℝ × ℝ`, and `f : C(T, ℝ)` the first coordinate. The fixture module
`TDA.Reeb.QuotientComparisonSineCurveExamples` (namespace `TDA.Reeb.Examples.TopologistsSineCurve`,
height `fstHeight`) proves

```lean
theorem componentComparison_not_injective :
    ¬ Function.Injective ((componentComparison fstHeight).app ⊤)
theorem intervalComponentComparison_not_injective :
    ¬ Function.Injective ((intervalComponentComparison fstHeight).app ⊤)
```

with no hypotheses; the second is the same statement on the open interval `ℝ`.

Take `z = (0, 0)` and `w = (1, sin 1⁻¹)`.

1. *No path in `T` joins `z` to `w`* (`not_joinedIn_T`). Suppose `p` is one, and let `t₀` be the
   last time with `p(t₀)` on the segment. Continuity at `t₀` gives `δ > 0` with
   `‖p(t) - p(t₀)‖ < 1` whenever `|t - t₀| < δ`. Pick `t₁ ∈ (t₀, t₀ + δ) ∩ [0, 1]` (`t₀ < 1`
   since `p(1) = w` has first coordinate 1). Then `p(t₁) ∈ S`, so `a = p(t₁)₁ > 0`, and the first coordinate of `p` takes every value in `[0, a]` on `[t₀, t₁]`.
   Since `sin x⁻¹` attains both `1` and `-1` for some `x ∈ (0, a]`, two times within `δ` of `t₀`
   have second coordinates `1` and `-1`. Their images are at distance at least `2`, but both
   lie within `1` of `p(t₀)`.
2. *The classes of `z` and `w` in the Reeb quotient `Q` are joined* (`joined_mk_zero_mk_w`). The
   segment `Z` is the fibre `f⁻¹(0)` and is path connected, so it is a single point `q(Z)` of `Q`.
   Let `γ(0) = q(Z)` and `γ(t) = q(t, sin t⁻¹)` for `0 < t ≤ 1`. Continuity at `t > 0` is that of
   a composite. At `0`: an open `V ∋ q(Z)` has open preimage `q⁻¹V = N ∩ T` with `N` open in
   `ℝ²`, and `Z ⊆ q⁻¹V` gives `{0} × [-1, 1] ⊆ N`. The tube lemma yields an open `u ∋ 0` with
   `u × [-1, 1] ⊆ N`, so `γ(t) ∈ V` for every `t ∈ u ∩ [0, 1]`.
3. The comparison sends the classes of `z` and `w` in `π₀(f⁻¹ℝ) = π₀(T)` to the classes of
   `q(z)` and `q(w)` in `π₀(Q)`. By (1) the former are distinct, and by (2) the latter are equal.

Connectedness of `T` is not used.

Source correspondence: de Silva, Munch and Patel, Example 3.21, take the space `𝕊` of §3.4, the
graph of `sin(1/x)` over `0 < x ≤ 1` together with `{0} × [-1, 1]`, with the first-coordinate
map. They observe that every level set over `[0, 1]` is path connected, so the Reeb graph is
homeomorphic to `[0, 1]` and has one path component while `𝕊` has more than one; hence `𝒞(𝕊, x)`
and `𝒞ℛ(𝕊, x)` differ at the interval `ℝ` (or any interval containing `0`) and are not isomorphic.
`T` is `𝕊`. The Lean results establish that the specific comparison `η` is not injective at `ℝ`.
They do not prove that the two cosheaves admit no isomorphism, that the Reeb quotient is
homeomorphic to `[0, 1]`, or the failure at smaller intervals containing `0`.

The sine-curve definitions and the proof of (1) are adapted from mathlib's
[`Counterexamples/TopologistsSineCurve.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Counterexamples/TopologistsSineCurve.lean)
(Daniele Bolla and David Loeffler, Apache-2.0). That file lies outside the `Mathlib` library
target and takes the graph over all `0 < x`; the adapted copy restricts the graph to
`0 < x ≤ 1` and keeps the upstream notice.

## Slice-category packaging

On `Over (TopCat.of Y)`, `ReebQuotient.quotientFunctor Y` sends an object with structure map `f`
to `(Q_f, f̄)`, and `ReebQuotient.projNatTrans Y : 𝟭 ⟶ quotientFunctor Y` is `q_f` at each object.
Mathlib has no bundled pointed-endofunctor structure, so the pair is the pointed endofunctor.
Idempotence is not claimed. `ReebQuotient.componentFunctorOver Y` sends an object to its
path-component functor on the open sets of `Y`, and

```lean
ReebQuotient.componentComparisonOver Y :
    componentFunctorOver Y ⟶ quotientFunctor Y ⋙ componentFunctorOver Y
```

is `η` as a natural transformation of functors. `toOver f` and `projOver f` present `(Q_f, f̄)` and
`q_f` as an object and a morphism over `Y`. Because `TopCat.{u}` has a single universe, the slice
packaging places `Y` and every carrier in one universe `u`. The real-valued case is `u = 0`.

## Source correspondence

de Silva, Munch and Patel, §2.4, define the Reeb functor on ℝ-spaces by `ℛ(𝕏, f) = (𝕏_f, f̄)` and
`ℛ[α] = ᾱ` (Proposition 2.10). The canonical projections form a natural transformation from the
identity, so `ℛ` is a pointed endofunctor (Observation 2.11). `ReebQuotient.map` is `ᾱ`, and
`(quotientFunctor ℝ, projNatTrans ℝ)` is `(ℛ, ρ)`. In the proof of Theorem 3.17 they define
`η = 𝒞ρ` by applying the path-component functor `𝒞` of §3.4 to `ρ`; `componentComparisonOver` is
this transformation. Theorem 3.17 states that `𝒞` and `𝒞ℛ` are naturally isomorphic on
constructible ℝ-spaces, and its proof shows that `η` is that isomorphism. That theorem, for `η`
restricted to open intervals, is formalized in `TDA.Reeb.ConstructibleComparison` (see
`reeb-constructible-comparison.md`).

The arbitrary target `Y` and the indexing by all open sets of `Y` are library generalizations,
not source claims. The source case is the specialization `Y = ℝ` restricted to open intervals.

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.4, §3.4, Theorem 3.17 and
Example 3.21](https://arxiv.org/html/1501.04147v1);
[pinned mathlib over categories](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/CategoryTheory/Comma/Over/Basic.lean);
[pinned mathlib topologist's sine curve](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Counterexamples/TopologistsSineCurve.lean).
