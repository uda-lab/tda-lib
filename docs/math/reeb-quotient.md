# Path-component Reeb quotient

## Relation and quotient

Let `X` and `Y` be topological spaces and `f : X → Y` continuous. Two points `x, x'` are
Reeb-related, `x ~_f x'`, when some path `γ` from `x` to `x'` satisfies `f (γ t) = f x` for every
`t`. This is the Lean definition `ReebRel`. It is literally `JoinedIn (f ⁻¹' {f x}) x x'`, and it is
equivalent to `f x' = f x` together with `x` and `x'` being joined by a path inside the fibre
subtype `f ⁻¹' {f x}` (`reebRel_iff_joined_fiber`). Components are therefore path components of the
fibre as a subspace, not connected components and not intersections of ambient components.
Constant, reversed and concatenated paths give reflexivity, symmetry and transitivity.

`ReebQuotient f` is `X / ~_f` with the quotient topology, `ReebQuotient.mk f` is the projection
`q_f`, and `ReebQuotient.height f : C(ReebQuotient f, Y)` is the descended map `f̄` with
`f̄ ∘ q_f = f` by definition. When `Y = ℝ` this is the height of the Reeb graph. The projection is
surjective and a quotient map. No openness of `q_f` and no Hausdorff property of the quotient is
claimed.

## Universal property

For every topological space `Z` and continuous `k : X → Z` that is constant on Reeb classes,
`ReebQuotient.lift` gives the continuous `k̄ : ReebQuotient f → Z` with `k̄ ∘ q_f = k`, and
`ReebQuotient.existsUnique_lift` states existence and uniqueness. Continuity is the quotient
principle; uniqueness uses only surjectivity of `q_f`. The map `k` need not preserve height.
Conversely, every continuous map out of the quotient is constant on Reeb classes after composing
with `q_f` (`ReebQuotient.apply_eq_of_reebRel`).

## Acceptance cases

- An empty `X` gives an empty quotient (`ReebQuotient.instIsEmpty`).
- An injective `f` gives `ReebQuotient.homeomorphOfInjective : ReebQuotient f ≃ₜ X`, inverse to
  `q_f`. The identity of `ℝ` and of `ℝ × ℝ` are instances.
- A constant `f` gives `ReebQuotient.homeomorphZerothHomotopy`, a homeomorphism with mathlib's
  path-component quotient `ZerothHomotopy X` and its quotient topology.
- A constant map has a subsingleton quotient when `X` is path connected
  (`ReebQuotient.subsingleton_of_const`). The hypothesis cannot be dropped: for the discrete
  two-point space `Bool` and a constant real map, the quotient has exactly two classes
  (`Examples.boolConst_mk_false_ne_true`, `Examples.boolConst_eq_mk_false_or_mk_true`).

## Source correspondence

de Silva, Munch and Patel, §2.4, work with ℝ-spaces `(𝕏, f)`, `f : 𝕏 → ℝ` continuous. They
identify points on the same levelset and the same path component of that levelset, form the
quotient `𝕏_f` with the inherited function `f̄` and the canonical projection `ρ_f`, and use the
quotient principle (Lemma 2.9) for continuity of induced maps. Proposition 2.10 states that this
construction is a functor on ℝ-spaces with `ρ` a natural transformation; this module provides the
object-level construction and the universal property, not the functor or the slice-category
packaging.

The arbitrary target `Y` is a library generalization, not a source claim. The proofs use only the
topology of `Y`, and the source's real-valued case is the specialization `Y = ℝ`.

Sources: [de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.4](https://arxiv.org/html/1501.04147v1);
[pinned mathlib path-connectedness source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Connected/PathConnected.lean);
[pinned mathlib quotient homeomorphisms](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Homeomorph/Quotient.lean).
