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

`η_f` need not be injective. For the topologist's sine curve with the first-coordinate projection,
de Silva, Munch and Patel show that `C(f)` and `C(f̄)` are not isomorphic (Example 3.21): over the
interval `ℝ`, the curve has more than one path component while its Reeb quotient has one, so the
surjective `η_f` is not injective there. This limitation is source-established and is not machine-checked here. No injectivity, bijectivity or
natural isomorphism is claimed for `η` in general. On constructible inputs, `η` restricted to open
intervals is a natural isomorphism (see `reeb-constructible-comparison.md`).

A separate, weaker fact is machine-checked. A continuous height-preserving surjection need not
induce injections on path components of inverse images. The fold `Bool × ℝ → ℝ` over `(ℝ, id)`
merges the two sheets at `U = ⊤` (`Examples.componentNatTrans_fold_not_injective`), and its
induced `Q_fold` is not injective (`Examples.map_fold_not_injective`).

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
[pinned mathlib over categories](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/CategoryTheory/Comma/Over/Basic.lean).
